import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0144
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0210
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0212
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0216
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0214

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyOfBaseZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

section Kunneth

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem mp_box_left {T T' : C} (ψ : T ⟶ T') (b : C) (u : F.obj T ⊗[R] F.obj b) :
    mp (box F) (show ((T, b) : C × C) ⟶ (T', b) from (ψ, 𝟙 b)) u = (mp F ψ).toLinearMap.rTensor _ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change mp F ψ x ⊗ₜ[R] mp F (𝟙 b) y = mp F ψ x ⊗ₜ[R] y
    rw [mp_id]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem mp_box_right (a : C) {T T' : C} (ψ : T ⟶ T') (u : F.obj a ⊗[R] F.obj T) :
    mp (box F) (show ((a, T) : C × C) ⟶ (a, T') from (𝟙 a, ψ)) u = (mp F ψ).toLinearMap.lTensor _ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change mp F (𝟙 a) x ⊗ₜ[R] mp F ψ y = x ⊗ₜ[R] mp F ψ y
    rw [mp_id]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {F}

theorem box_square (f : Z1 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    (mp F ψ).toLinearMap.lTensor _ (f.1 (a, b) (a', b) (φ, 𝟙 b)) + f.1 (a', b) (a', b') (𝟙 a', ψ) =
      (mp F φ).toLinearMap.rTensor _ (f.1 (a, b) (a, b') (𝟙 a, ψ)) + f.1 (a, b') (a', b') (φ, 𝟙 b') := by
  have e1 := Z1.comp f (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', ψ))
  have e2 := Z1.comp f (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b'))
  rw [mp_box_right] at e1
  rw [mp_box_left] at e2
  rw [← e1, ← e2]
  congr 1
  simp

end Kunneth

theorem kunneth (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (hf : ∀ T, Module.Flat R (F.obj T)) (hU : USt F) (c : H1 (box F)) :
    ∃ x y : H1 F, c = (boxL F).pull1 x + (boxR F).pull1 y := by
  classical
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hz : ∀ b : C, ∃ t : Z1 F ⊗[R] F.obj b, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor _ t = f.1 (T, b) (T', b) (φ, 𝟙 b) := fun b ↦ by
    haveI := hf b
    let f₀ : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] F.obj b := fun T T' φ ↦ f.1 (T, b) (T', b) (φ, 𝟙 b)
    refine GlobalTheory.T.flat_cocycle_tensor_representation R C F (F.obj b) f₀ ?_
    intro T T' T'' φ ψ
    have e := Z1.comp f (show ((T, b) : C × C) ⟶ (T', b) from (φ, 𝟙 b)) (show ((T', b) : C × C) ⟶ (T'', b) from (ψ, 𝟙 b))
    rw [mp_box_left] at e
    rw [← e]
    congr 1
    simp
    rfl
  choose t ht using hz
  have hcomp : ∀ (b b' : C) (ψ : b ⟶ b'), (H1.mk F).rTensor _ (t b') =
      (mp F ψ).toLinearMap.lTensor (H1 F) ((H1.mk F).rTensor _ (t b)) := fun b b' ψ ↦ by
    haveI := hf b'
    have k := GlobalTheory.T.cocycle_tensor_coboundary_class_zero R C F (F.obj b') (t b' - (mp F ψ).toLinearMap.lTensor (Z1 F) (t b))
      (fun a ↦ f.1 (a, b) (a, b') (𝟙 a, ψ)) (fun T T' φ ↦ by
        have e : (evZ F φ).rTensor _ ((mp F ψ).toLinearMap.lTensor (Z1 F) (t b)) =
            (mp F ψ).toLinearMap.lTensor _ ((evZ F φ).rTensor _ (t b)) := by
          rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
            LinearMap.lTensor_comp_rTensor]
        have s := box_square f φ ψ
        rw [map_sub, e, ht, ht]
        exact sub_eq_sub_iff_add_eq_add.2 (by rw [add_comm, ← s, add_comm]))
    have e : (H1.mk F).rTensor _ ((mp F ψ).toLinearMap.lTensor (Z1 F) (t b)) =
        (mp F ψ).toLinearMap.lTensor _ ((H1.mk F).rTensor _ (t b)) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [map_sub, e, sub_eq_zero] at k
    exact k
  obtain ⟨x, hx, -⟩ := hU (H1 F) (fun b ↦ (H1.mk F).rTensor _ (t b)) hcomp
  obtain ⟨z, rfl⟩ := H1.mk_surjective F x
  have hg : ∀ b : C, ∃ g : ∀ T : C, F.obj T ⊗[R] F.obj b, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor _ (z ⊗ₜ[R] (1 : F.obj b) - t b) = g T' - (mp F φ).toLinearMap.rTensor _ (g T) := fun b ↦
    GlobalTheory.T.class_zero_cocycle_tensor_coboundary R C F (F.obj b) _ (by
      rw [map_sub, LinearMap.rTensor_tmul, hx b, sub_self])
  choose g hg using hg
  let G : C0 (box F) := fun T ↦ g T.2 T.1
  let f' : Z1 (box F) := f - (boxL F).pullbackOneCocycle z + (d0 (box F)).codRestrict (Z1 (box F)) (commAlgFunctorCoboundaryZero_mem_cocyclesOne _) G
  have hv : ∀ (a a' b : C) (φ : a ⟶ a'), f'.1 (a, b) (a', b) (φ, 𝟙 b) = 0 := fun a a' b φ ↦ by
    have e := hg b a a' φ
    rw [map_sub, LinearMap.rTensor_tmul, ht] at e
    have e2 : mp (box F) (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) (G (a, b)) =
        (mp F φ).toLinearMap.rTensor _ (g b a) := mp_box_left F φ b _
    have e3 : f'.1 (a, b) (a', b) (φ, 𝟙 b) = f.1 (a, b) (a', b) (φ, 𝟙 b) - (z.1 a a' φ) ⊗ₜ[R] (1 : F.obj b) +
        (g b a' - mp (box F) (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) (G (a, b))) := rfl
    rw [e3, e2, ← e]
    change _ - z.1 a a' φ ⊗ₜ[R] (1 : F.obj b) + (z.1 a a' φ ⊗ₜ[R] (1 : F.obj b) - _) = 0
    abel
  obtain ⟨y, hy⟩ := GlobalTheory.T.cocycle_on_product_from_second_factor R C F hU f' hv
  refine ⟨H1.mk F z, H1.mk F y, ?_⟩
  rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, ← map_add, H1.mk_eq_mk]
  refine ⟨-G, ?_⟩
  rw [hy, map_neg]
  have : (f' : C1 (box F)) = f.1 - ((boxL F).pullbackOneCocycle z).1 + d0 (box F) G := rfl
  change -d0 (box F) G = f.1 - (((boxL F).pullbackOneCocycle z).1 + f'.1)
  rw [this]
  abel

theorem first_cohomology_of_base_zero (R : Type) [CommRing R] (c : HO1 (𝟙_ (Over (Sp R))).hom) : c = 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))
  exact H1.eq_zero_of_isInitial _ (T₀ := op ⟨⊤, isAffineOpen_top _⟩)
    (Limits.IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top _⟩ from
        le_top (a := U.unop.1))).op) fun _ _ ↦ rfl) c

theorem isPullO_id (R : Type) [CommRing R] (X : Over (Sp R)) (a : HO1 X.hom) : IsPullO (wOver (𝟙 X)) a a :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull (wOver (𝟙 X))) (pairRes _ X.hom) (pairIdTrans X.left) (fun _ _ ↦ rfl) a

theorem ust_abelian : DescentSt → LowSt → SysBCSt → SteinSt → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (P : Type) [SemilatticeInf P] (S : Sys A.left P), USt (OSys A.hom S) := by
  intro hD hL hB hS R _ A _ g hA hg P _ S M _ _ z hz
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingEquiv.toOpposite R).symm.toRingHom)
  haveI : IsCentralScalar R M := ⟨fun r m ↦ rfl⟩
  obtain ⟨A', _, φ, hA', hg', hpb⟩ := GlobalTheory.T.abelian_scheme_base_change_exists R (TrivSqZeroExt R M) A g hA hg
  have := hA.proper
  have := hA'.proper
  obtain ⟨S', m, -⟩ := hB R (TrivSqZeroExt R M) A.left A'.left A.hom A'.hom φ hpb inferInstance P S
  have hSt : Stein (OSys A'.hom S') :=
    ((hL _ _ _ _ _ (resSys A'.hom S') (hD _ _ A'.hom inferInstance P S')).2.2).1 (hS _ A' g hA' hg')
  exact GlobalTheory.T.exists_unique_constant_of_compatible_family R Pᵒᵖ (OSys A.hom S) M _ m hSt z hz

theorem isPullO_comp (R : Type) [CommRing R] {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom) (h1 : IsPullO (wOver g) a b) (h2 : IsPullO (wOver f) b c) :
    IsPullO (wOver (f ≫ g)) a c :=
  GlobalTheory.T.isPullO_comp_block_decomposition R X Y Z f g a b c h1 h2

theorem isPullO_add {R : Type} [CommRing R] {X Y : Over (Sp R)} (f : X ⟶ Y) {a a' : HO1 Y.hom} {b b' : HO1 X.hom}
    (h : IsPullO (wOver f) a b) (h' : IsPullO (wOver f) a' b') : IsPullO (wOver f) (a + a') (b + b') := by
  unfold IsPullO at *; rw [map_add, map_add, h, h']

theorem isPullO_unique {R : Type} [CommRing R] {X Y : Over (Sp R)} (f : X ⟶ Y) {a : HO1 Y.hom} {b b' : HO1 X.hom}
    (h : IsPullO (wOver f) a b) (h' : IsPullO (wOver f) a b') : b = b' :=
  (existsUnique_isPullO (wOver f) a).unique h h'

theorem isPullO_through_unit {R : Type} [CommRing R] {X Y : Over (Sp R)} (t : X ⟶ 𝟙_ (Over (Sp R)))
    (u : 𝟙_ (Over (Sp R)) ⟶ Y) (a : HO1 Y.hom) (b : HO1 X.hom) (h : IsPullO (wOver (t ≫ u)) a b) : b = 0 := by
  have h1 := isPullO_pullHO1 (wOver u) a
  rw [first_cohomology_of_base_zero R (pullHO1 (wOver u) a)] at h1
  have h2 := isPullO_comp R t u a 0 0 h1 ((map_zero _).trans (map_zero _).symm)
  exact isPullO_unique _ h h2

theorem axOSt : DescentSt → LowSt → SysBCSt → SteinSt → AxOSt := by
  intro hD hL hB hS R _ A _ g hA hg c h1 h2
  have hA2 := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hA.proper
  have := hA2.proper
  have := hA.smooth
  obtain ⟨P, _, _, ⟨S⟩⟩ := GlobalTheory.T.exists_finite_semilattice_system R A.left A.hom inferInstance inferInstance
  obtain ⟨Q, _, S', m, hm, hfst, hsnd⟩ := GlobalTheory.T.product_first_cohomology_comparison R A P S
  have hU := ust_abelian hD hL hB hS R A g hA hg P S
  have hb := (hL _ _ _ _ _ (resSys A.hom S) (hD R _ A.hom inferInstance P S)).1
  have hb' := (hL _ _ _ _ _ (resSys (A ⊗ A).hom S') (hD R _ (A ⊗ A).hom inferInstance Q S')).1
  haveI : Finite Pᵒᵖ := Finite.of_injective Opposite.unop Opposite.unop_injective
  obtain ⟨w, hw⟩ := hm ((resSys (A ⊗ A).hom S').pull1 c)
  obtain ⟨x, y, rfl⟩ := kunneth R Pᵒᵖ (OSys A.hom S) (fun T ↦ GlobalTheory.T.smooth_sections_affine_flat R _ A.hom inferInstance _) hU w
  obtain ⟨x₀, rfl⟩ := hb.2 x
  obtain ⟨y₀, rfl⟩ := hb.2 y
  have e1 := isPullO_pullHO1 (wOver (fst A A)) x₀
  have e2 := isPullO_pullHO1 (wOver (snd A A)) y₀
  have hc : c = pullHO1 (wOver (fst A A)) x₀ + pullHO1 (wOver (snd A A)) y₀ := by
    apply hb'.1
    rw [map_add, hfst _ _ e1, hsnd _ _ e2, ← hw, map_add]
  set c₁ := pullHO1 (wOver (fst A A)) x₀ with hc₁
  set c₂ := pullHO1 (wOver (snd A A)) y₀ with hc₂

  have a1 := isPullO_pullHO1 (wOver (lift (𝟙 A) (1 : A ⟶ A))) c₁
  have a2 := isPullO_pullHO1 (wOver (lift (𝟙 A) (1 : A ⟶ A))) c₂
  have b1 := isPullO_pullHO1 (wOver (lift (1 : A ⟶ A) (𝟙 A))) c₁
  have b2 := isPullO_pullHO1 (wOver (lift (1 : A ⟶ A) (𝟙 A))) c₂
  have k1 := isPullO_comp R _ _ _ _ _ e1 a1
  have k2 := isPullO_comp R _ _ _ _ _ e2 a2
  have l1 := isPullO_comp R _ _ _ _ _ e1 b1
  have l2 := isPullO_comp R _ _ _ _ _ e2 b2
  rw [lift_fst] at k1
  rw [lift_snd, Hom.one_def] at k2
  rw [lift_fst, Hom.one_def] at l1
  rw [lift_snd] at l2
  have z2 := isPullO_through_unit _ _ _ _ k2
  have z3 := isPullO_through_unit _ _ _ _ l1
  have u1 := isPullO_unique _ k1 (isPullO_id R A x₀)
  have u2 := isPullO_unique _ l2 (isPullO_id R A y₀)
  rw [hc] at h1 h2
  have v1 := isPullO_unique _ h1 (isPullO_add _ a1 a2)
  have v2 := isPullO_unique _ h2 (isPullO_add _ b1 b2)
  rw [z2, add_zero, u1] at v1
  rw [z3, zero_add, u2] at v2
  rw [hc, hc₁, hc₂, ← v1, ← v2, map_zero, map_zero, add_zero]

end GlobalTheory.CompanionTheory.Axis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorAdjoint
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Ibp

variable {n : ℕ}

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_of_cpt (hL : LgFacts) {φ : Mat n → ℂ} (hφ : ContinuousOn φ (GLs n)) (cφ : Cpt φ) :
    Integrable (fun y : G n => φ y.val) μ := by
  obtain ⟨R, hR⟩ := cφ
  have hc : Continuous (fun y : G n => φ y.val) :=
    hφ.comp_continuous Units.continuous_val val_mem
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_)
  intro y hy
  exact hR _ (val_mem y) (not_le.1 hy)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem sm_inner {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => ⟪f y, h y⟫_ℂ) (GLs n) :=
  hf.inner ℂ hh

theorem Cpt_inner {f h : Mat n → V} (cf : Cpt f) : Cpt (fun y => ⟪f y, h y⟫_ℂ) := by
  obtain ⟨R, hR⟩ := cf
  exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩

theorem Cpt_inner' {f h : Mat n → V} (ch : Cpt h) : Cpt (fun y => ⟪f y, h y⟫_ℂ) := by
  obtain ⟨R, hR⟩ := ch
  exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩

theorem int_inner (hL : LgFacts) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (sm_inner hf hh).continuousOn (Cpt_inner cf)

theorem int_inner' (hL : LgFacts) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (ch : Cpt h) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (sm_inner hf hh).continuousOn (Cpt_inner' ch)

theorem ibp_Rd (hL : LgFacts) (hR : RCalc) (X : Mat n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Rd X f y.val, h y.val⟫_ℂ ∂μ = -∫ y : G n, ⟪f y.val, Rd X h y.val⟫_ℂ ∂μ := by
  have h0 := (hR n).2.2 μ ℂ (fun y => ⟪f y, h y⟫_ℂ) (sm_inner hf hh) (Cpt_inner cf) X
  have e : ∀ y : G n, Rd X (fun y => ⟪f y, h y⟫_ℂ) y.val =
      ⟪f y.val, Rd X h y.val⟫_ℂ + ⟪Rd X f y.val, h y.val⟫_ℂ := by
    intro y
    exact fderiv_inner_apply ℂ (diffAt hf (val_mem y)) (diffAt hh (val_mem y)) _
  simp_rw [e] at h0
  rw [integral_add (int_inner' μ hL hf (sm_Rd hR X hh) (Cpt_Rd hL X ch))
    (int_inner μ hL (sm_Rd hR X hf) hh (Cpt_Rd hL X cf))] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem ibp_Eu (hL : LgFacts) (hR : RCalc) (s : Bool) (a b : Fin n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Eu s a b f y.val, h y.val⟫_ℂ ∂μ = -∫ y : G n, ⟪f y.val, Eu (!s) a b h y.val⟫_ℂ ∂μ := by
  set X : Mat n := Matrix.single a b 1
  set Y : Mat n := Matrix.single a b Complex.I
  set c : ℂ := if !s then -Complex.I else Complex.I with hc
  have hc' : conj (if s then -Complex.I else Complex.I) = c := by
    cases s <;> simp [hc]
  have e1 : ∀ y : G n, ⟪Eu s a b f y.val, h y.val⟫_ℂ =
      (1 / 2 : ℂ) * (⟪Rd X f y.val, h y.val⟫_ℂ + c * ⟪Rd Y f y.val, h y.val⟫_ℂ) := by
    intro y
    have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    simp only [Eu, Pi.smul_apply, Pi.add_apply, inner_smul_left, inner_add_left, hc', h2]
    rfl
  have e2 : ∀ y : G n, ⟪f y.val, Eu (!s) a b h y.val⟫_ℂ =
      (1 / 2 : ℂ) * (⟪f y.val, Rd X h y.val⟫_ℂ + c * ⟪f y.val, Rd Y h y.val⟫_ℂ) := by
    intro y
    simp only [Eu, Pi.smul_apply, Pi.add_apply, inner_smul_right, inner_add_right]
    simp [X, Y, hc]
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul,
    integral_add (int_inner μ hL (sm_Rd hR X hf) hh (Cpt_Rd hL X cf))
      ((int_inner μ hL (sm_Rd hR Y hf) hh (Cpt_Rd hL Y cf)).const_mul c),
    integral_add (int_inner' μ hL hf (sm_Rd hR X hh) (Cpt_Rd hL X ch))
      ((int_inner' μ hL hf (sm_Rd hR Y hh) (Cpt_Rd hL Y ch)).const_mul c),
    integral_const_mul, integral_const_mul, ibp_Rd μ hL hR X hf hh cf ch, ibp_Rd μ hL hR Y hf hh cf ch]
  ring

theorem ibp_Epow (hL : LgFacts) (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Epow s m a b f y.val, h y.val⟫_ℂ ∂μ =
      (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, EpowT (!s) m b a h y.val⟫_ℂ ∂μ := by
  induction m generalizing a h with
  | zero =>
    by_cases hab : a = b
    · subst hab
      simp [Epow, EpowT]
    · simp [Epow, EpowT, hab, Ne.symm hab]
  | succ m ih =>
    have e1 : ∀ y : G n, ⟪Epow s (m + 1) a b f y.val, h y.val⟫_ℂ =
        ∑ c, ⟪Eu s a c (Epow s m c b f) y.val, h y.val⟫_ℂ := by
      intro y
      simp only [Epow, Finset.sum_apply, sum_inner]
    have e2 : ∀ y : G n, ⟪f y.val, EpowT (!s) (m + 1) b a h y.val⟫_ℂ =
        ∑ c, ⟪f y.val, EpowT (!s) m b c (Eu (!s) a c h) y.val⟫_ℂ := by
      intro y
      rw [EpowT_succ' hR (!s) m a b hh (val_mem y), Finset.sum_apply, inner_sum]
    simp_rw [e1, e2]
    rw [integral_finset_sum _ fun c _ => int_inner μ hL (sm_Eu hR s a c (sm_Epow hR s m c b hf)) hh
        (Cpt_Eu hL s a c (Cpt_Epow hL s m c b cf)),
      integral_finset_sum _ fun c _ => int_inner μ hL hf
        (sm_EpowT hR (!s) m b c (sm_Eu hR (!s) a c hh)) cf,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ibp_Eu μ hL hR s a c (sm_Epow hR s m c b hf) hh (Cpt_Epow hL s m c b cf) ch,
      ih c (sm_Eu hR (!s) a c hh) (Cpt_Eu hL (!s) a c ch), pow_succ]
    ring

end Int

theorem ibp_gel : LgFacts → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)]
    (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (s : Bool) (m : ℕ) (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h →
    ∫ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ ∂μ =
      (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ ∂μ := by
  intro hL hR n _ _ μ _ V _ _ _ s m f h hf hh cf ch
  have e1 : ∀ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ = ∑ a, ⟪Epow s m a a f y.val, h y.val⟫_ℂ := by
    intro y
    simp only [gel, Finset.sum_apply, sum_inner]
  have e2 : ∀ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ =
      ∑ a, ⟪f y.val, EpowT (!s) m a a h y.val⟫_ℂ := by
    intro y
    simp only [gelT, Finset.sum_apply, inner_sum]
  simp_rw [e1, e2]
  rw [integral_finset_sum _ fun a _ => int_inner μ hL (sm_Epow hR s m a a hf) hh
      (Cpt_Epow hL s m a a cf),
    integral_finset_sum _ fun a _ => int_inner μ hL hf (sm_EpowT hR (!s) m a a hh) cf,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => ibp_Epow μ hL hR s m a a hf hh cf ch

end GlobalTheory.CompanionTheory.WaveMult.Ibp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

section U

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

def IsPermW (w : GU σ n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ a c : Fin n, ((w : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a c = if c = π a then 1 else 0

theorem isPermW_one : IsPermW (1 : GU σ n) 1 := fun a c => by
  simp [Matrix.one_apply, eq_comm]

variable [Valued L (WithZero (Multiplicative ℤ))]

def permWt (t : GU σ n) (π : Equiv.Perm (Fin n)) : ℤ :=
  ∑ a : Fin n, ((a.val : ℤ) + 1) * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a))

end U

def aOp {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) : G → ℂ :=
  fun g => ∑ r ∈ R, φ (g * r * t)

end GlobalTheory.CompanionTheory.SatPow

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointRegularStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_adjoint_regular : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg | exact GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierLinearStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_multiplier_linear : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι ι' : Type} [Fintype ι] [Fintype ι'] (c : ι → ℂ) (c' : ι' → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (ks' : ι' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)), (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) → ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels | exact GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
section
noncomputable section

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

def Lap {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) : Mat n → V :=
  fun g => -∑ p, Rd (bs p) (Rd (bs p) f) g

end GlobalTheory.CompanionTheory.FcSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivativeStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_translate_right_derivative : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | exact GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | (intros; apply GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevelStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_continuous_proper_sublevel : ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | exact GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | (intros; apply GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompactStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_function_compact : PositivityTheory.RgBcC.VC.LgCpt := by
  first | exact @GlobalTheory.CompanionTheory.LgBound.lgCpt | exact GlobalTheory.CompanionTheory.LgBound.lgCpt | (intros; apply GlobalTheory.CompanionTheory.LgBound.lgCpt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzExistsRealMajorantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_exists_real_majorant : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ), ∃ F : SchwartzMap E ℂ, ∀ x, (F x).im = 0 ∧ ‖f x‖ ≤ (F x).re := by
  first | exact @GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant | exact GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant | (intros; apply GlobalTheory.CompanionTheory.SchwartzMaj.exists_nonneg_schwartz_majorant <;> assumption)
end

