import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KunnethCupTensorInjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Kunneth

section Pairs

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
  {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
  {C : Type} [Category.{0} C] (A : C ⥤ AffOp X') (B : C ⥤ AffOp X)
  (hle : ∀ T, (A.obj T).unop.1 ≤ φ ⁻¹ᵁ (B.obj T).unop.1)

def toPair : C ⥤ (Pair φ)ᵒᵖ where
  obj T := Opposite.op ⟨((A.obj T).unop, (B.obj T).unop), hle T⟩
  map {T T'} a := (homOfLE (Subtype.coe_le_coe.1
    (Prod.mk_le_mk.2 ⟨leOfHom (A.map a).unop, leOfHom (B.map a).unop⟩) :
      (⟨((A.obj T').unop, (B.obj T').unop), hle T'⟩ : Pair φ) ≤ ⟨((A.obj T).unop, (B.obj T).unop), hle T⟩)).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem restrict_pullHO1 (h : φ ≫ s = s' ≫ spMap σ) (c : HO1 s) :
    (CoefMap.restrict (OAff s') A).pull1 (pullHO1 h c) =
      ((pairPull h).comp (CoefMap.restrict (OPair φ s') (toPair A B hle))).pull1 c := by
  rw [CoefMap.pullCohomologyOne_comp, (isPullO_pullHO1 h c : (pairPull h).pull1 c = (pairRes φ s').pull1 (pullHO1 h c))]
  exact CoefMap.pullCohomologyOne_comp (pairRes φ s') (CoefMap.restrict (OPair φ s') (toPair A B hle)) (pullHO1 h c)

end Pairs

end GlobalTheory.Kunneth

namespace GlobalTheory.Kunneth

def prodFun {J J' : Type} [Preorder J] [Preorder J'] {Z : Scheme.{0}} (W : J × J' → Z.affineOpens)
    (hW : Monotone W) : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp Z where
  obj T := Opposite.op (W (T.1.unop, T.2.unop))
  map a := (homOfLE (hW (Prod.mk_le_mk.2 ⟨leOfHom a.1.unop, leOfHom a.2.unop⟩))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem cup_tmul_injective : ∀ (K : Type) [Field K] (X Y : Over (Sp K)), IsSeparated X.hom → QuasiCompact X.hom →
    IsSeparated Y.hom → QuasiCompact Y.hom → ∀ (n : ℕ) (x : Fin n → HO1 X.hom) (y : Fin n → HO1 Y.hom),
    ∑ i, cup (OAff (X ⊗ Y).hom) (pO1 (fst X Y) (x i)) (pO1 (snd X Y) (y i)) = 0 →
    ∑ i, x i ⊗ₜ[K] y i = 0 := by
  intro K _ X Y hXs hXq hYs hYq n x y hsum
  obtain ⟨J, _, _, U, hU, hUi, hUc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed K X.left X.hom hXs hXq
  obtain ⟨J', _, _, V, hV, hVi, hVc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed K Y.left Y.hom hYs hYq
  choose Wf h1 h2 i1 i2 hWe hi1 hi2 hbij using fun p : J × J' ↦ GlobalTheory.T.exists_affine_open_product_sections_iso K X Y (U p.1) (V p.2)
  have hWm : Monotone Wf := fun p q hpq ↦ by
    show (Wf p).1 ≤ (Wf q).1
    rw [hWe p, hWe q]
    exact inf_le_inf (Scheme.Hom.preimage_mono _ (hU hpq.1)) (Scheme.Hom.preimage_mono _ (hV hpq.2))
  haveI : Finite J'ᵒᵖ := Finite.of_equiv J' Opposite.equivToOpposite
  let Ψ := prodFun Wf hWm
  let F := hU.functor.op ⋙ OAff X.hom
  let G := hV.functor.op ⋙ OAff Y.hom
  let E := Ψ ⋙ OAff (X ⊗ Y).hom
  let B₁ : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp X.left := CategoryTheory.Prod.fst Jᵒᵖ J'ᵒᵖ ⋙ hU.functor.op
  let B₂ : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp Y.left := CategoryTheory.Prod.snd Jᵒᵖ J'ᵒᵖ ⋙ hV.functor.op
  have hle₁ : ∀ T, (Ψ.obj T).unop.1 ≤ (fst X Y).left ⁻¹ᵁ (B₁.obj T).unop.1 := fun T ↦ h1 (T.1.unop, T.2.unop)
  have hle₂ : ∀ T, (Ψ.obj T).unop.1 ≤ (snd X Y).left ⁻¹ᵁ (B₂.obj T).unop.1 := fun T ↦ h2 (T.1.unop, T.2.unop)
  let m₁ := (pairPull (ovw (fst X Y))).comp (CoefMap.restrict (OPair (fst X Y).left (X ⊗ Y).hom) (toPair Ψ B₁ hle₁))
  let m₂ := (pairPull (ovw (snd X Y))).comp (CoefMap.restrict (OPair (snd X Y).left (X ⊗ Y).hom) (toPair Ψ B₂ hle₂))
  let j₁ : ∀ T : Jᵒᵖ × J'ᵒᵖ, F.obj T.1 →ₐ[K] E.obj T := fun T ↦ i1 (T.1.unop, T.2.unop)
  let j₂ : ∀ T : Jᵒᵖ × J'ᵒᵖ, G.obj T.2 →ₐ[K] E.obj T := fun T ↦ i2 (T.1.unop, T.2.unop)
  have nat₁ : ∀ (T T' : Jᵒᵖ × J'ᵒᵖ) (a : T ⟶ T') (b : F.obj T.1), j₁ T' (mp F a.1 b) = mp E a (j₁ T b) := by
    intro T T' a b
    refine (hi1 _ _).trans (Eq.trans ?_ (congrArg (mp E a) (hi1 (T.1.unop, T.2.unop) b).symm))
    exact m₁.naturality a b
  have nat₂ : ∀ (T T' : Jᵒᵖ × J'ᵒᵖ) (a : T ⟶ T') (b : G.obj T.2), j₂ T' (mp G a.2 b) = mp E a (j₂ T b) := by
    intro T T' a b
    refine (hi2 _ _).trans (Eq.trans ?_ (congrArg (mp E a) (hi2 (T.1.unop, T.2.unop) b).symm))
    exact m₂.naturality a b
  let n₁ : CoefMap (RingHom.id K) F E :=
    { G := CategoryTheory.Prod.fst Jᵒᵖ J'ᵒᵖ
      α := fun T ↦ (j₁ T).toRingHom
      naturality := fun {T T'} a b ↦ nat₁ T T' a b
      smul := fun T r b ↦ map_smul (j₁ T) r b }
  let n₂ : CoefMap (RingHom.id K) G E :=
    { G := CategoryTheory.Prod.snd Jᵒᵖ J'ᵒᵖ
      α := fun T ↦ (j₂ T).toRingHom
      naturality := fun {T T'} a b ↦ nat₂ T T' a b
      smul := fun T r b ↦ map_smul (j₂ T) r b }
  let rU := CoefMap.restrict (OAff X.hom) hU.functor.op
  let rV := CoefMap.restrict (OAff Y.hom) hV.functor.op
  let rE := CoefMap.restrict (OAff (X ⊗ Y).hom) Ψ
  have key₁ : ∀ a, rE.pull1 (pO1 (fst X Y) a) = n₁.pull1 (rU.pull1 a) := fun a ↦ by
    refine (restrict_pullHO1 Ψ B₁ hle₁ (ovw (fst X Y)) a).trans ?_
    refine (CoefMap.pullCohomologyOne_eq_of_natTrans m₁ (rU.comp n₁) (𝟙 B₁) (fun T b ↦ ?_) a).trans
      (CoefMap.pullCohomologyOne_comp rU n₁ a)
    refine (congrArg ((rU.comp n₁).α T) (mp_id (OAff X.hom) _ b)).trans ?_
    exact hi1 (T.1.unop, T.2.unop) b
  have key₂ : ∀ a, rE.pull1 (pO1 (snd X Y) a) = n₂.pull1 (rV.pull1 a) := fun a ↦ by
    refine (restrict_pullHO1 Ψ B₂ hle₂ (ovw (snd X Y)) a).trans ?_
    refine (CoefMap.pullCohomologyOne_eq_of_natTrans m₂ (rV.comp n₂) (𝟙 B₂) (fun T b ↦ ?_) a).trans
      (CoefMap.pullCohomologyOne_comp rV n₂ a)
    refine (congrArg ((rV.comp n₂).α T) (mp_id (OAff Y.hom) _ b)).trans ?_
    exact hi2 (T.1.unop, T.2.unop) b
  have hbU : Function.Bijective rU.pull1 := GlobalTheory.T.cech_pull_one_bijective_lattice_cover K X.left X.hom J U hU hUi hUc
  have hbV : Function.Bijective rV.pull1 := GlobalTheory.T.cech_pull_one_bijective_lattice_cover K Y.left Y.hom J' V hV hVi hVc
  choose x' hx' using fun i ↦ H1.mk_surjective F (rU.pull1 (x i))
  choose y' hy' using fun i ↦ H1.mk_surjective G (rV.pull1 (y i))
  have hz : H2.mk E (∑ i, cupZ E (n₁.pullbackOneCocycle (x' i)) (n₂.pullbackOneCocycle (y' i))) = 0 := by
    have h0 := congrArg rE.pull2 hsum
    rw [map_zero, map_sum] at h0
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
    rw [CoefMap.pullCohomologyTwo_cup, key₁, key₂, ← hx', ← hy']
    rfl
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 hz
  have e := GlobalTheory.T.tensor_algebra_product_diagram_compat K Jᵒᵖ J'ᵒᵖ F G E j₁ j₂ nat₁ nat₂ (fun T ↦ hbij (T.1.unop, T.2.unop)) n x' y' f
    (fun T T' T'' a b ↦ by
      rw [hf]
      simp only [Submodule.coe_sum, Finset.sum_apply]
      rfl)
  simp only [hx', hy'] at e
  let eU := LinearEquiv.ofBijective rU.pull1 hbU
  let eV := LinearEquiv.ofBijective rV.pull1 hbV
  apply (TensorProduct.congr eU eV).injective
  rw [map_sum, map_zero]
  exact e

end GlobalTheory.Kunneth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LTensorLiftBaseChangeGlobalOneFormsAffinePreimag
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_bijective_of_isBaseChange {R R' B B' W W' Ω Ω' : Type} [CommRing R]
    [CommRing R'] [Algebra R R'] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B']
    [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R' W']
    [AddCommGroup Ω] [Module R Ω] [Module B Ω] [IsScalarTower R B Ω]
    [AddCommGroup Ω'] [Module R' Ω'] [Module B' Ω'] [IsScalarTower R' B' Ω']
    (α : B →+* B') (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h1 : Function.Surjective (liftSemi f))
    (m : Ω →ₛₗ[algebraMap R R'] Ω') (hm : ∀ (b : B) (ω : Ω), m (b • ω) = α b • m ω)
    (h2 : Function.Bijective (liftSemi m))
    (e : W →ₗ[R] Ω) (he : IsBaseChange B e) (e' : W' →ₗ[R'] Ω') (he' : IsBaseChange B' e')
    (p : W →ₛₗ[algebraMap R R'] W') (hp : ∀ w, e' (p w) = m (e w)) :
    Function.Bijective (LinearMap.lTensor B' (liftSemi p)) := by
  letI : Module R (B' ⊗[R'] (R' ⊗[R] W)) := Module.compHom _ (algebraMap R R')
  have hsm : ∀ (c : R) (z : B' ⊗[R'] (R' ⊗[R] W)), c • z = algebraMap R R' c • z := fun _ _ ↦ rfl
  have hR : ∀ (c : R) (x : R' ⊗[R] B), c • x = algebraMap R R' c • x := fun c x ↦
    (algebraMap_smul R' c x).symm
  have hW : ∀ (c : R) (w : W), (1 : R') ⊗ₜ[R] (c • w) = algebraMap R R' c • ((1 : R') ⊗ₜ[R] w) := by
    intro c w
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
      Algebra.algebraMap_eq_smul_one]

  let bil : R' ⊗[R] B →ₗ[R] W →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    LinearMap.mk₂ R (fun x w ↦ liftSemi f x ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] w))
      (fun x y w ↦ by rw [map_add, TensorProduct.add_tmul])
      (fun c x w ↦ by rw [hR, map_smul, hsm, TensorProduct.smul_tmul'])
      (fun x w w' ↦ by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
      (fun c x w ↦ by rw [hW, TensorProduct.tmul_smul, hsm])
  let Ψ : R' ⊗[R] (B ⊗[R] W) →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    TensorProduct.lift bil ∘ₗ (TensorProduct.assoc R R' B W).symm.toLinearMap
  have hΨ : Function.Surjective Ψ := by
    suffices hall : ∀ z, z ∈ LinearMap.range Ψ from
      LinearMap.range_eq_top.1 (eq_top_iff.2 fun z _ ↦ hall z)
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
      | tmul r w =>
        obtain ⟨x, hx⟩ := h1 (r • b)
        refine ⟨TensorProduct.assoc R R' B W (x ⊗ₜ w), ?_⟩
        have e1 : r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          TensorProduct.lift.tmul, bil, LinearMap.mk₂_apply, hx, e1, ← TensorProduct.smul_tmul]
  let Θ : R' ⊗[R] (B ⊗[R] W) ≃ₗ[R] R' ⊗[R] Ω := (he.equiv.restrictScalars R).lTensor R'
  have hΘ : Function.Bijective (fun z ↦ liftSemi m (Θ z)) := h2.comp Θ.bijective
  have key : ∀ z, he'.equiv (LinearMap.lTensor B' (liftSemi p) (Ψ z)) = liftSemi m (Θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]
    | tmul r t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add, map_add]
      | tmul b w =>
        simp only [Ψ, Θ, bil, LinearMap.comp_apply, LinearEquiv.coe_coe,
          TensorProduct.assoc_symm_tmul, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
          liftSemi_tmul, LinearMap.lTensor_tmul, LinearEquiv.lTensor_tmul,
          LinearEquiv.restrictScalars_apply, IsBaseChange.equiv_tmul, one_smul, hf, hp, hm,
          map_smul, smul_assoc]
  refine ⟨fun x y hxy ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨x0, rfl⟩ := hΨ x
    obtain ⟨y0, rfl⟩ := hΨ y
    have := hΘ.1 (show liftSemi m (Θ x0) = liftSemi m (Θ y0) by rw [← key, ← key, hxy])
    rw [this]
  · obtain ⟨z, hz⟩ := hΘ.2 (he'.equiv q)
    refine ⟨Ψ z, he'.equiv.injective ?_⟩
    rw [key]; exact hz

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_pullForm_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → ∀ U : X.affineOpens, IsAffineOpen (φ ⁻¹ᵁ U.1) → Function.Bijective (LinearMap.lTensor (Sec s' (φ ⁻¹ᵁ U.1)) (liftSemi (pullForm h.w))) := by
  intro R R' _ _ _ X X' s s' φ h hF hH hF' hH' U hU
  let U' : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, hU⟩
  let pr : Pair φ := ⟨(U', U), le_rfl⟩
  have hsemi : SemiHom (algebraMap R R') (GlobalTheory.CechDR.secPull s s' pr) := GlobalTheory.CechDR.semiHom_secPull h.w pr
  let f : Sec s U.1 →ₛₗ[algebraMap R R'] Sec s' (φ ⁻¹ᵁ U.1) :=
    { toFun := GlobalTheory.CechDR.secPull s s' pr, map_add' := map_add _, map_smul' := hsemi }
  have h1 : Function.Bijective (liftSemi f) :=
    GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h pr rfl f (fun _ ↦ rfl)
  have h2 : Function.Bijective (liftSemi hsemi.m1) :=
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (GlobalTheory.CechDR.secPull s s' pr) hsemi f (fun _ ↦ rfl) h1
  let e : GlobForm s →ₗ[R] Ω[Sec s U.1⁄R] :=
    { toFun := fun w ↦ w.1 (Opposite.op U), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he : IsBaseChange (Sec s U.1) e :=
    isBaseChange_glob1 R (AffOp X) (OAff s) hF hH (Opposite.op U) e (fun _ ↦ rfl)
  let e' : GlobForm s' →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'] :=
    { toFun := fun w ↦ w.1 (Opposite.op U'), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he' : IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) e' :=
    isBaseChange_glob1 R' (AffOp X') (OAff s') hF' hH' (Opposite.op U') e' (fun _ ↦ rfl)
  exact lTensor_liftSemi_bijective_of_isBaseChange (GlobalTheory.CechDR.secPull s s' pr) f (fun _ ↦ rfl) h1.2 hsemi.m1
    (fun b ω ↦ hsemi.oneFormMap_smul_semilinear b ω) h2 e he e' he' (pullForm h.w)
    (fun w ↦ ((isPullForm_iff.1 (isPullForm_pullForm h.w w)) pr).symm)

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMapGivesHomomorphism
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolUnifHom

open GlobalTheory.SS GlobalTheory.EighthPowerFactor CechPic in

theorem exists_polAV_retract_dim (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g : ℕ)
    (hB : IsAbelianScheme B) (hd : SmoothOfRelativeDimension g B.hom) (M : LB B.left) (hM : M.IsLB)
    (ha : Out.RelAmple B M) (hK : Out.KTriv B M) :
    ∃ (Q : Out.PolAV (Sp k)) (i : B ⟶ Q.A) (r : Q.A ⟶ B),
      Q.g = 8 * g ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 B := by
  have := hB.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase k 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns hB hM g).Principal :=
    ⟨relAmple_diag_lam hB hM (exists_gen_theta_of_isAbelianScheme k B hB M hM) ha,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam hM hK x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, -⟩, -, -, -⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g _ W _ a w w' bas hW hb
    hw hw' hs 1 k b _ (𝟙 _) (siegOne L₁.globalFns hB hM g) (one_pow _) odd_one hc hd
  obtain ⟨i, hi, -⟩ := hu B fun _ => 𝟙 B
  refine ⟨t.pol, i, pr 0, rfl, isMonHom_of_coord hpr hu fun u => ?_, hpr 0, hi 0⟩
  rw [hi u]
  exact inferInstanceAs (IsMonHom (𝟙 B))

end GlobalTheory.HolUnifHom

namespace GlobalTheory.HolUnifHom

open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel GlobalTheory.HolUnifEnd in

theorem exists_linear_factor (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hgA : SmoothOfRelativeDimension g A.hom) (L : LB A.left) (u : HolUnif A L g) :
    ∃ (Q : Out.PolAV (Sp ℂ)) (v : HolUnif Q.A Q.L (8 * g)) (i : A ⟶ Q.A) (r : Q.A ⟶ A)
      (J : (Fin g → ℂ) →ₗ[ℂ] (Fin (8 * g) → ℂ)) (R : (Fin (8 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (m : ℕ),
      Q.g = 8 * g ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ (∀ z, v.ex (J z) = u.ex z ≫ i) ∧
      (∀ z, u.ex (R z) = v.ex z ≫ r) ∧ (∀ x ∈ u.Λ, J x ∈ v.Λ) ∧ (∀ x ∈ v.Λ, R x ∈ u.Λ) ∧
      ∀ z, R (J z) = m • z := by
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', hQg, hi', hr', hir'⟩ := exists_polAV_retract_dim ℂ B g hB hgB MB hMB hamp hK
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  suffices key : ∀ n, Q.g = n → ∃ (v : HolUnif Q.A Q.L n) (J : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ))
      (R : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, v.ex (J z) = u.ex z ≫ (i ≫ i')) ∧
      (∀ z, u.ex (R z) = v.ex z ≫ (r' ≫ r)) ∧ (∀ x ∈ u.Λ, J x ∈ v.Λ) ∧ (∀ x ∈ v.Λ, R x ∈ u.Λ) ∧
      ∀ z, R (J z) = m • z by
    obtain ⟨v, J, R, hJ, hR, hJΛ, hRΛ, hRJ⟩ := key (8 * g) hQg
    exact ⟨Q, v, i ≫ i', r' ≫ r, J, R, m, hQg, inferInstance, inferInstance, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩
  rintro n rfl
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -, -, -, -, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
  obtain ⟨J, hJ, hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v
    hv1 hv2 (i ≫ i') inferInstance
  obtain ⟨R, hR, hRΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u
    hu.1 hu.2 (r' ≫ r) inferInstance
  have hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  have hsB := (abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2
  have : Surjective (r.left ≫ i.left) := by rw [← Over.comp_left, hri]; exact hsB
  have : Surjective i.left := Surjective.of_comp r.left i.left
  obtain ⟨n, hn, hkill⟩ := exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i
  have hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m := by
    intro x
    simp only [Category.assoc]
    rw [reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow,
      Category.comp_id, MonObj.pow_comp, Category.assoc]
  have hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ := by
    intro a b h
    rw [← v.ker]
    have e := v.ex_add (a - b) b
    rw [sub_add_cancel, h] at e
    have e2 := congrArg (· * (v.ex b)⁻¹) e
    simpa using e2.symm
  have hRJ : ∀ z, R (J z) = m • z := by
    intro z
    have hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ := by
      intro t
      have h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z)) := by
        rw [hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]
        simp only [Category.assoc]
      have h2 := hsubv _ _ h1
      have h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z) := by
        rw [map_smul, map_smul, smul_sub, smul_comm t m z]
      rw [h3, map_sub, map_nsmul]
      exact h2
    have hJy0 : J (R (J z) - m • z) = 0 :=
      LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t
    have hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1 := by
      intro t
      have h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1 := by
        rw [← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]
      calc u.ex (t • (R (J z) - m • z)) ≫ i = u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' ≫ r' := by
            rw [hir', Category.comp_id]
        _ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]
        _ = 1 := by rw [h2, MonObj.one_comp]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hy0 : R (J z) - m • z = 0 := LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by
      rw [← u.ker]
      have e := hkill _ (hker ((n : ℂ)⁻¹ * t))
      rw [← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc,
        mul_inv_cancel₀ hn0, _root_.one_mul] at e
      exact e
    exact sub_eq_zero.1 hy0
  exact ⟨v, J, R, hJ, hR, hJΛ, hRΛ, hRJ⟩

end GlobalTheory.HolUnifHom

namespace GlobalTheory.HolUnifHom

open GlobalTheory.HolUnifEnd in

theorem exists_isMonHom_of_map_lattice :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g : ℕ), IsAbelianScheme A → IsAbelianScheme A' →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom →
    ∀ (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g) (u' : HolUnif A' L' g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u'.Λ) → ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  intro A A' _ _ g hA hA' hgA hgA' L L' u u' M hM
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := _root_.GlobalTheory.exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q Q' (8 * g) v v'
    (J' ∘ₗ M ∘ₗ R) hQ hQ' (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

end GlobalTheory.HolUnifHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfEventualPolynomialGrowth
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem le_of_frequently_mul_pow_le_mul_add_pow :
    ∀ (d D a f : ℕ), (∀ N : ℕ, ∃ s, N ≤ s ∧ d * s ^ f ≤ D * (s + a) ^ f) → d ≤ D := by
  intro d D a f h
  by_contra hlt
  push_neg at hlt
  have hq : Filter.Tendsto (fun s : ℕ => ((s:ℝ) + a) / s) Filter.atTop (nhds 1) := by
    have h2 : Filter.Tendsto (fun s : ℕ => 1 + (a:ℝ) / s) Filter.atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (a:ℝ))
    rw [add_zero] at h2
    apply h2.congr'
    filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    have hs' : (s:ℝ) ≠ 0 := by positivity
    rw [add_div, div_self hs']
  have h1 : Filter.Tendsto (fun s : ℕ => (D:ℝ) * (((s:ℝ) + a) / s) ^ f) Filter.atTop
      (nhds ((D:ℝ) * 1 ^ f)) := tendsto_const_nhds.mul (hq.pow f)
  rw [one_pow, _root_.mul_one] at h1
  have hd : (D:ℝ) < d := by exact_mod_cast hlt
  have hev : ∀ᶠ s : ℕ in Filter.atTop, (D:ℝ) * (((s:ℝ) + a) / s) ^ f < d :=
    h1.eventually (gt_mem_nhds hd)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨s, hs, hle⟩ := h (N + 1)
  have hlt2 := hN s (by omega)
  have hspos : (0:ℝ) < s := by
    have : 0 < s := by omega
    exact_mod_cast this
  rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)] at hlt2
  have hc : ((d * s ^ f : ℕ) : ℝ) ≤ ((D * (s + a) ^ f : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at hc
  linarith

example : ∀ (d D a f : ℕ), (∀ N : ℕ, ∃ s, N ≤ s ∧ d * s ^ f ≤ D * (s + a) ^ f) → d ≤ D := le_of_frequently_mul_pow_le_mul_add_pow

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFiniteProjectiveRankStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_finite_projective_rank : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)),
    Module.Finite R X.Lie ∧ Module.Projective R X.Lie ∧ ∀ p, Module.rankAtStalk (R := R) X.Lie p = Module.finrank ℚ F := by
  first | exact @GlobalTheory.LieProj.lie_finite_projective_rank | exact GlobalTheory.LieProj.lie_finite_projective_rank | (intros; apply GlobalTheory.LieProj.lie_finite_projective_rank <;> assumption)
end

