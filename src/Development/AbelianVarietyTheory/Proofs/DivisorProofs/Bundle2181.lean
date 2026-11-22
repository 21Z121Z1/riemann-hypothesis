import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionConstantOnFibresDescends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Semi MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolAdjoint

section Chern

open GlobalTheory.Cris.ChernExists

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X Y : Scheme.{0}} {s : X ⟶ Sp R}
  {s' : Y ⟶ Sp R}

def expU (T : Thick κ s) : T.J →+ Additive T.Bˣ :=
  AddMonoidHom.mk' (fun a ↦ Additive.ofMul ⟨dpExp T.δ a.1, dpExp T.δ (-a.1),
      by rw [← exp_add T a.2 (T.J.neg_mem a.2), add_neg_cancel, dpExp_zero],
      by rw [← exp_add T (T.J.neg_mem a.2) a.2, neg_add_cancel, dpExp_zero]⟩)
    fun a b ↦ congrArg Additive.ofMul (Units.ext (exp_add T a.2 b.2))

theorem exp_sum (T : Thick κ s) {K : Type} [Fintype K] (ε : K → ℤ) (a : K → T.B) (ha : ∀ k, a k ∈ T.J)
    (p q : K → T.Bˣ) (h : ∀ k, dpExp T.δ (a k) * (p k).val = (q k).val) :
    dpExp T.δ (∑ k, ε k • a k) * (∏ k, p k ^ ε k).val = (∏ k, q k ^ ε k).val := by
  have e1 : ∀ k, q k = Additive.toMul (expU T ⟨a k, ha k⟩) * p k := fun k ↦ Units.ext (h k).symm
  have e2 : dpExp T.δ (∑ k, ε k • a k) =
      (Additive.toMul (expU T (∑ k, ε k • (⟨a k, ha k⟩ : T.J)))).val := by
    change _ = dpExp T.δ (Subtype.val _)
    congr 1
    simp
  rw [e2, map_sum, toMul_sum, ← Units.val_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [e1, mul_zpow, map_zsmul, toMul_zsmul]

theorem isChern_linComb {L : LB X} {z : Cris.H2 κ s} (hz : IsChern κ s L z) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : ∀ k, IsMor κ s κ s' (RingHom.id R) (φ k)) :
    IsChern κ s' (LB.LinComb L φ ε) (∑ k, ε k • (m k).pull2 z) := by
  obtain ⟨i, hi, u, ℓ, h1, h2, h3⟩ := hz
  let G : K → (IsSmall κ s' (LB.LinComb L φ ε).U).FullSubcategory ⥤ (IsSmall κ s L.U).FullSubcategory :=
    fun k ↦ ObjectProperty.lift _ ((IsSmall κ s' (LB.LinComb L φ ε).U).ι ⋙ (m k).functor) fun T ↦
      T.property.elim fun j hj ↦ ⟨j k, fun p _ ↦ LB.wchart_le L φ j k (hj (Set.mem_univ p))⟩
  let n : K → CoefMap (RingHom.id R) ((IsSmall κ s L.U).ι ⋙ O κ s)
      ((IsSmall κ s' (LB.LinComb L φ ε).U).ι ⋙ O κ s') := fun k ↦
    { G := G k
      α := fun T ↦ RingHom.id T.obj.B
      naturality := fun _ _ ↦ rfl
      smul := fun T r b ↦ (m k).coef.smul T.obj r b }
  have hu : ∀ k T T' (ψ : T ⟶ T'), IsUnit (M := T'.obj.B) (u _ _ ((G k).map ψ)) := fun k T T' ψ ↦
    isUnit_of_π T'.obj ((h1 _ _ ((G k).map ψ)).symm ▸ (Units.isUnit _).map _)
  choose U hU using hu
  have hi' : ∀ T : (IsSmall κ s' (LB.LinComb L φ ε).U).FullSubcategory,
      ⊤ ≤ T.obj.x ⁻¹ᵁ (LB.LinComb L φ ε).U (fun k ↦ i ((G k).obj T)) :=
    fun T p _ ↦ Set.mem_iInter.2 fun k ↦ hi ((G k).obj T) (Set.mem_univ p)
  refine ⟨fun T k ↦ i ((G k).obj T), hi', fun T T' ψ ↦ (∏ k, U k T T' ψ ^ ε k).val,
    ∑ k, ε k • (n k).pullbackTwoCocycle ℓ, fun T T' ψ ↦ ?_, fun T T' T'' ψ χ ↦ ?_, ?_⟩
  · refine congrArg Units.val (show Units.map (T'.obj.π : T'.obj.B →* T'.obj.B₀) (∏ k, U k T T' ψ ^ ε k) =
      evU T'.obj.x ((LB.LinComb L φ ε).U (fun k ↦ i ((G k).obj T')) ⊓ (LB.LinComb L φ ε).U (fun k ↦ i ((G k).obj T)))
        (le_inf (hi' T') (ψ.hom.le_preimage (hi' T))) ((LB.LinComb L φ ε).g _ _) from ?_)
    refine (map_prod _ _ _).trans (Eq.trans (Finset.prod_congr rfl fun k _ ↦ ?_) (map_prod _ _ _).symm)
    refine (map_zpow _ _ _).trans (Eq.trans (congrArg (· ^ ε k) ?_) (map_zpow _ _ _).symm)
    refine Units.ext ?_
    refine ((congrArg T'.obj.π (hU k T T' ψ)).trans (h1 _ _ ((G k).map ψ))).trans ?_
    exact evalAt_pull (φ k) T'.obj.x _ _ _ _
  · have e : ((∑ k, ε k • (n k).pullbackTwoCocycle ℓ).1 T T' T'' ψ χ : T''.obj.B) =
        ∑ k, ε k • (show T''.obj.B from ℓ.1 _ _ _ ((G k).map ψ) ((G k).map χ)) := by
      rw [Submodule.coe_sum]
      simp only [Finset.sum_apply]
      rfl
    have hm : ∀ k, (show T''.obj.B from ℓ.1 _ _ _ ((G k).map ψ) ((G k).map χ)) ∈ T''.obj.J :=
      fun k ↦ (h2 _ _ _ ((G k).map ψ) ((G k).map χ)).1
    rw [e]
    refine ⟨Submodule.sum_mem _ fun k _ ↦ zsmul_mem (hm k) _, ?_⟩
    refine (exp_sum T''.obj ε _ hm _
      (fun k ↦ Units.map (χ.hom.φ : T'.obj.B →* T''.obj.B) (U k T T' ψ) * U k T' T'' χ) fun k ↦ ?_).trans ?_
    · rw [hU, Units.val_mul, hU, Units.coe_map, hU]
      exact (h2 _ _ _ ((G k).map ψ) ((G k).map χ)).2
    · refine Eq.trans ?_ (Units.val_mul (Units.map (χ.hom.φ : T'.obj.B →* T''.obj.B) (∏ k, U k T T' ψ ^ ε k)) _)
      rw [map_prod, ← Finset.prod_mul_distrib]
      simp only [mul_zpow, map_zpow]
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_zsmul, map_zsmul, ← (n k).pullCohomologyTwo_class, ← h3]
    obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective _ z
    rfl

end Chern

section Cube

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem pullOver_one {T : Over S} (c : prim κ t A) : pullOver κ t (1 : T ⟶ A) c.1 = 0 := by
  have h := c.2 T 1 1
  rw [_root_.mul_one] at h
  exact left_eq_add.1 h

theorem pullOver_psum {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) (J : Finset (Fin n)) (c : prim κ t A) :
    pullOver κ t (psum A x J) c.1 = ∑ i ∈ J, pullOver κ t (x i) c.1 := by
  have key : ∀ l : List (Fin n), pullOver κ t (l.foldr (fun k acc ↦ padd A (x k) acc) (pzero A T)) c.1 =
      (l.map fun i ↦ pullOver κ t (x i) c.1).sum := fun l ↦ by
    induction l with
    | nil => exact pullOver_one c
    | cons k l ih => exact (c.2 T (x k) _).trans (by rw [ih, List.map_cons, List.sum_cons])
  rw [psum, key, ← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

theorem isMor_psum {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) (J : ULift.{0} (Finset (Fin n))) :
    IsMor κ (A.hom ≫ t) κ (T.hom ≫ t) (RingHom.id R) (psum A x J.down).left :=
  IsMor.of_over κ (by rw [← Category.assoc, Over.w])

theorem isChern_cube {L : LB A.left} {n : ℕ} {a b : Fin n → prim κ t A}
    (h : IsChern κ (A.hom ≫ t) L (∑ k, cup _ (a k).1 (b k).1)) {T : Over S} (u v : T ⟶ A) :
    IsChern κ (T.hom ≫ t) (cubeLB A ![u, v] L)
      (∑ k, (cup _ (pullOver κ t u (a k).1) (pullOver κ t v (b k).1) +
        cup _ (pullOver κ t v (a k).1) (pullOver κ t u (b k).1))) := by
  have H := isChern_linComb h _ (fun J : ULift.{0} (Finset (Fin 2)) ↦ (-1 : ℤ) ^ (2 - J.down.card))
    (isMor_psum ![u, v])
  have e : ∀ J : ULift.{0} (Finset (Fin 2)), (isMor_psum ![u, v] J).pull2 (∑ k, cup _ (a k).1 (b k).1) =
      ∑ k, cup _ (∑ i ∈ J.down, pullOver κ t (![u, v] i) (a k).1)
        (∑ i ∈ J.down, pullOver κ t (![u, v] i) (b k).1) := fun J ↦ by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [IsMor.pullCohomologyTwo_cup, ← pullOver_psum, ← pullOver_psum]
    rfl
  simp only [e, Finset.smul_sum] at H
  rw [Finset.sum_comm] at H
  refine (congrArg (IsChern κ (T.hom ≫ t) (cubeLB A ![u, v] L)) ?_).mpr H
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Equiv.ulift.symm.sum_comp,
    show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp only [Equiv.ulift_symm_down, Finset.sum_empty, Finset.sum_singleton,
    Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide), Finset.card_pair (show (0 : Fin 2) ≠ 1 by decide),
    Finset.card_singleton, map_zero, smul_zero, map_add, LinearMap.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num
  abel

end Cube

theorem lbIso_cube {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A]
    [IsCommMonObj A] {f : S' ⟶ S} {π : A.left ⟶ G.left} (h : IsGrpPullback A G f π) (L : LB G.left)
    {α β : G ⟶ G} {α' β' : A ⟶ A} (hα : α'.left ≫ π = π ≫ α.left) (hβ : β'.left ≫ π = π ≫ β.left)
    (H : LBIso (cubeLB G ![fst G G ≫ α, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ β] L)) :
    LBIso (cubeLB A ![fst A A ≫ α', snd A A] (L.pull π)) (cubeLB A ![fst A A, snd A A ≫ β'] (L.pull π)) := by
  let U : Over.mk ((A ⊗ A).hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have e : ∀ {ρ : G ⟶ G} {ρ' : A ⟶ A}, ρ'.left ≫ π = π ≫ ρ.left → ∀ p : A ⊗ A ⟶ A,
      pushPt h.1.w (p ≫ ρ') = pushPt h.1.w p ≫ ρ := fun hρ p ↦ Over.OverMorphism.ext (by
    change (p.left ≫ _) ≫ π = (p.left ≫ π) ≫ _
    rw [Category.assoc, Category.assoc, hρ])
  refine LBIso.chartPull (chartPullLinComb L π _ _ _ U.left fun J ↦ psum_push h _ _ U (fun i ↦ ?_) _)
    (chartPullLinComb L π _ _ _ U.left fun J ↦ psum_push h _ _ U (fun i ↦ ?_) _) H
  · fin_cases i
    · exact (e hα _).trans (lift_fst_assoc _ _ _).symm
    · exact (lift_snd _ _).symm
  · fin_cases i
    · exact (lift_fst _ _).symm
    · exact (e hβ _).trans (lift_snd_assoc _ _ _).symm

theorem exists_wedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (X Y : M →ₗ[R] R) :
    ∃ Λ : ⋀[R]^2 M →ₗ[R] R, ∀ c d, Λ (exteriorPower.ιMulti R 2 ![c, d]) = X c * Y d - X d * Y c := by
  refine ⟨exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating.compLinearMap (LinearMap.pi ![X, Y])), fun c d ↦ ?_⟩
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change Matrix.det (Matrix.of fun i j ↦ (![X, Y] j) (![c, d] i)) = _
  rw [Matrix.det_fin_two]
  simp [mul_comm]

theorem exists_wedge_functional (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)}
    [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (X Y : FirstDeRham (A.hom ≫ 𝟙 _) →ₗ[R] R) :
    ∃ Λ : SecondDeRham (A.hom ≫ 𝟙 _) →ₗ[R] R, ∀ c d, Λ (cup _ c d) = X c * Y d - X d * Y c := by
  obtain ⟨-, -, -, -, e, he⟩ := P R A g hA hg
  obtain ⟨Λ, hΛ⟩ := exists_wedge X Y
  exact ⟨Λ ∘ₗ e.symm.toLinearMap, fun c d ↦ by
    rw [← he, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, hΛ]⟩

theorem isAbelianScheme_sq {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) :
    IsAbelianScheme (A ⊗ A) := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    exact GeometricallyConnected.comp _ _

theorem adjoint_of_lbIso (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)}
    [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left}
    (hL : L.IsLB) {ψ : LinearMap.BilinForm R (HdR A)} (hψ : IsPolForm (dp0 R) (𝟙 _) A L ψ)
    (α β : A ⟶ A) [IsMonHom α] [IsMonHom β]
    (H : LBIso (cubeLB A ![fst A A ≫ α, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ β] L)) (x y : HdR A) :
    ψ (push (dp0 R) (𝟙 _) α x) y = ψ x (push (dp0 R) (𝟙 _) β y) := by
  obtain ⟨n, a, b, hc, rfl⟩ := hψ
  have h0 := (P R A g hA hg).1
  have hg2 : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom A.hom).flip hg
    rw [Over.tensorObj_hom]
    exact smoothOfRelativeDimension_comp g g _ _
  let E : primDR A ≃ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) := LinearEquiv.ofTop _ h0
  obtain ⟨Λ, hΛ⟩ := exists_wedge_functional P (isAbelianScheme_sq hA) hg2
    (x ∘ₗ E.symm.toLinearMap ∘ₗ pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1))
    (y ∘ₗ E.symm.toLinearMap ∘ₗ pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)))
  have C := isChern_existsUnique_and_iso R _ (dp0 R) _ ((A ⊗ A).hom ≫ 𝟙 _)
  have l₁ : (cubeLB A ![fst A A ≫ α, snd A A] L).IsLB := DVR.linComb_isLB _ hL _ _
  have l₂ : (cubeLB A ![fst A A, snd A A ≫ β] L).IsLB := DVR.linComb_isLB _ hL _ _
  have e := congrArg Λ ((C.1 _ l₂).unique (C.2 _ _ l₁ l₂ H _ (isChern_cube hc _ _)) (isChern_cube hc _ _))
  have v : ∀ (ρ : A ⟶ A) [IsMonHom ρ] (c : primDR A),
      E.symm (pullOver (dp0 R) (𝟙 _) ρ c.1) = primPull (dp0 R) (𝟙 _) ρ c := fun _ _ _ ↦ Subtype.ext rfl
  have v₁ : ∀ c : primDR A, primPull (dp0 R) (𝟙 _) (𝟙 A) c = c := fun c ↦
    Subtype.ext (IsMor.pullCohomologyOne_id _ _)
  simp only [map_sum, map_add, hΛ, LinearMap.comp_apply, LinearEquiv.coe_coe, pullOver_pullOver,
    lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, Category.id_comp, MonObj.one_comp, pullOver_one,
    map_zero, v, v₁, mul_zero, zero_mul, sub_zero, zero_sub] at e
  simp only [wedgeForm_apply, push_apply, sub_eq_add_neg]
  exact e

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm K (HdR A)}, IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  intro P E _ _ _ H Dw l Xo K _ x A _ π hπ a ha ψ hψ z u v
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have := hA.comm
  have := a.hom
  exact adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z) (a.act (H.bar z))
    (lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v

end GlobalTheory.PolAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtPlacesFromComparison
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.TraceClassRank

local instance runAlgRank {D : D7} {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] (r : RunData J) :
    Algebra r.full.J.Q.c.F D.what₂.LL := inst

section General

open scoped TensorProduct

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem goodOp_rho_comm {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (j : Fin D.R.m) (g : G) (x : Fin (R.nW j) → D.what₂.LL) :
    OntoChain.goodOp R j ((R.FW j).ρ g x) = (R.FW j).ρ g (OntoChain.goodOp R j x) := by
  have h := LinearMap.congr_fun (goodOp_comm (R := R) hX j g) x
  simp only [LinearMap.comp_apply, twRep_apply, map_smul] at h
  have h' := congrArg (fun y => (((R.FW j).chi g : D.what₂.LLˣ) : D.what₂.LL) • y) h
  simp only [smul_smul, Units.mul_inv, one_smul] at h'
  exact h'

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem tie_e_comm_rho (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (g : P) : O.e i ∘ₗ O.ρ i g = O.ρ i g ∘ₗ O.e i := by
  refine LinearMap.ext fun x => (toForms_bijective h fw ι z).1 ?_
  simp only [LinearMap.comp_apply]
  rw [t.e_eOp, t.rho_eq_of_actionPin ha, t.rho_eq_of_actionPin ha, t.e_eOp]
  exact goodOp_rho_comm hX ι (inc g) _

theorem tie_thetaJ (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (ha : ActionPin h fw ι ℓ)
    (hi : Function.Injective inc) (hU : U ≤ inc.range) (hd : FormsDetermined R ι) (hM : SpanOverClasses R ι U ψ ph v p)
    (hty : ∀ x ∈ thetaBase R ι U ψ ph v p, ∀ u : U, (R.FW ι).ρ u x = ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • x)
    {n : ℕ} (hp : RunPin R ι n v p) (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) :
    (O.ThJ v i).FG ∧ O.ThJ v i ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ i) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v i) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v i) := by
  have hb := toForms_bijective h fw ι z
  refine ⟨?_, fun x hx => ?_, trace_lattice_le_theta_lattice_at_place t hi hU hp hA⟩
  · refine Submodule.fg_of_fg_map_injective ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.1 ?_
    rw [t.ThJ_eq, Submodule.map_comap_eq_of_surjective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) hb.2]
    exact thetaBase_fg hd hM
  · rw [t.ThJ_eq] at hx
    have hx' : toForms h fw ι z x ∈ thetaBase R ι U ψ ph v p := hx
    change x ∈ Formalism.EigenvalueLevelCeiling.eig _ _ _
    unfold Formalism.EigenvalueLevelCeiling.eig
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro u
    have hU' : ∀ g : P, g ∈ O.U → inc g ∈ U := fun g hg => by
      rw [t.U_eq] at hg
      exact hg
    have hu : inc u ∈ U := hU' u u.2
    apply hb.1
    rw [t.rho_eq_of_actionPin ha, hty _ hx' ⟨inc u, hu⟩, map_smul, t.ψ_eq u hu]

end General

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}

theorem conjPl_mem_twPl (hC : (R2 p).Char (F2 p)) {w : HeightOneSpectrum (𝓞 D.what₂.LL)} (hw : w ∈ p.R.twPl) :
    Formalism.DivisionValues.conjPl w ∈ p.R.twPl := by
  by_contra h
  exact hC.tup.mu_ne w hw ((hC.tup.mu_conj w).symm.trans (hC.tup.mu_off _ h))

theorem rankAtPlaces_rec (hR : p.Rows) (hm : More p) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hrec : RecAt p Tp r O)
    (hMax : ∀ v ∈ p.R.twPl, ∀ j,
      GlobalTheory.TraceClassRank.SpanOverClasses (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt D v))
    (hSp : LeafSpan O) (hD : LeafData O)
    (hCmp : ∀ v ∈ p.R.twPl, ∀ j,
      letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
      GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (hrec.1.ok.laws v).p (fw2 p) j (r.lev j)
        (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt D v)) :
    GlobalTheory.TraceClassRank.RankAtPlaces O := by
  obtain ⟨hC, hOk, hLU, -⟩ := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hR hm.1
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.1.tied
  have hX := hOk.irr
  have h1 := hC.grp.levels
  have hU : (F2 p).P0 ≤ (mirIncl (R2 p)).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩
  have hProj : LeafProj O := (level_of_tied ⟨z, act, y, ht⟩ hX h1).2.2
  have hd : ∀ j, FormsDetermined (R2 p) j := fun j =>
    formsDetermined_of (GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj.of_char GlobalTheory.LowTypeRestriction.resInj _ _ hC) hC.models.HW hLU
  have hComm : ∀ j (g : Mir (R2 p)), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j := fun j g => by
    obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
    exact tie_e_comm_rho (ht v₁ j).1 (ht v₁ j).2 hOk.irr g
  have key : ∀ v ∈ p.R.twPl, ∀ j, (O.ThJ v j).FG ∧
      O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := fun v hv j => by
    have hv' : v ∈ (R2 p).twPl := hv
    have hdel : ∀ x, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range := fun x => by
      obtain ⟨a, ha⟩ := Formalism.L2.Pj.FO_le _ (hm.2.1.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) x)
      exact ⟨a, ha⟩
    have hty := GlobalTheory.T.baseTupleThetaSpan_hasType _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j hLU (hd j) v hv'
      hC.tup.mu_on hdel (fun u => chi_eq_one h1 hC.grp.chiW j u.2)
    exact tie_thetaJ (ht v j).1 (ht v j).2 (mirIncl_injective _) hU (hd j) (hMax v hv j) hty (hrec.1.ok.run v hv' j)
      (hCmp v hv j)
  exact GlobalTheory.T.eigenlattice_local_containment_at_pairs _ _ _ _ _ _ O hSp hD hProj hComm fun w hw =>
    ⟨fun j => key w hw j, fun j => key _ (conjPl_mem_twPl hC hw) j⟩

end Point

end GlobalTheory.BigOn

theorem GlobalTheory.BigOn.rankLocSt_of : MaxSt → GeoSt → (AtRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) → (AtRec fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) := by
  intro hM hG hC
  refine ((hM.and hG).and hC).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨x1, H1⟩, ⟨c0, H2⟩⟩, ⟨x3, H3⟩⟩ := H
  refine ⟨c0, fun c hc hb => ?_⟩
  obtain ⟨x2, H2'⟩ := H2 c hc hb
  refine ⟨max x1 (max x2 x3), fun x hx hle i p hR hm r O hrec => ?_⟩
  have hle1 : x1 ≤ x := (le_max_left _ _).trans hle
  have hle2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have hle3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hg := H2' x hx hle2 i p hR hm r O hrec
  exact rankAtPlaces_rec hR hm hrec (H1 x hx hle1 i p hR hm) hg.2.1 hg.2.2.2.1 (H3 x hx hle3 i p hR hm r hrec.1.ok hrec.2)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

def ratField {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (S : Set (H0 p B O))
    (y : Y) (hy : y ∈ O) : Subfield (Y.residueField y) :=
  Subfield.closure {r | ∃ (i : B.ι) (hi : y ∈ B.U i) (s s' : H0 p B O), s ∈ S ∧ s' ∈ S ∧
    r = (Y.residue y).hom (germ i y hy hi s) / (Y.residue y).hom (germ i y hy hi s')}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def RatGen {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) : Prop :=
  ∃ (η : Y₀ X Z) (hη : η ∈ U₀ X Z), IsGenericPoint η Set.univ ∧
    ratField (Set.range (cuspSec X Z U la)) η hη = ⊤

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLawsStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (N : Type) [Finite N] (χ : N → Formalism.L2.Host.HChar D.host.E) (xi : N → (AE D)ˣ →* Circle) (Q : N → Finset (Pl D.host.E))
      (xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      (∀ n, GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ n) (xi n) (Q n) (xiR n)) → Function.Injective χ → (∀ n t, χ n ≠ R.xiH t) →
      (∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
        (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) →
      ∃ (T0' : Type) (A' : FamIn D.what₂.LL G Pl0 T0' D.R.m) (R' : RealDat D A' T.Q.c.F) (F' : Face D A')
        (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)),
        GlobalTheory.BigOn.Exp.TwConj.Laws T R' F' κ v₀' O' ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R' v₀' O' ∧
          ∀ n, ∃ t', R'.xi t' = xi n ∧ R'.Q t' = Q n := by
  first | exact @GlobalTheory.TupExt.extend_tuples | exact GlobalTheory.TupExt.extend_tuples | (intros; apply GlobalTheory.TupExt.extend_tuples <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleRootOfPrintStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaleRoot_of_cuspRapidDecay_of_reciprocity_of_rayClassField : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → GlobalTheory.BigOn.Exp.ScaleRoot := by
  first | exact @GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis | exact GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis | (intros; apply GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionConstantOnFibresDescendsStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_constant_on_fibres_descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, FibConst d g → ∃ f ∈ sec Xo c a n, Pull d f g := by
  first | exact @GlobalTheory.CoverDesc.section_descends | exact GlobalTheory.CoverDesc.section_descends | (intros; apply GlobalTheory.CoverDesc.section_descends <;> assumption)
end

