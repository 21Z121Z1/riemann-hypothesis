import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0279

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitTorusExtensionTorsion
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext

section General
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def pre {Y Y' A : C} [MonObj A] (ρ : Y' ⟶ Y) : (Y ⟶ A) →* (Y' ⟶ A) where
  toFun x := ρ ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

def post {Y A A' : C} [MonObj A] [MonObj A'] (φ : A ⟶ A') [IsMonHom φ] : (Y ⟶ A) →* (Y ⟶ A') where
  toFun x := x ≫ φ
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

theorem pre_pow {Y Y' A : C} [MonObj A] (ρ : Y' ⟶ Y) (x : Y ⟶ A) (n : ℕ) : ρ ≫ (x ^ n) = (ρ ≫ x) ^ n :=
  map_pow (pre ρ) x n

theorem post_pow {Y A A' : C} [MonObj A] [MonObj A'] (φ : A ⟶ A') [IsMonHom φ] (x : Y ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n :=
  map_pow (post φ) x n

theorem post_inv {Y A A' : C} [GrpObj A] [GrpObj A'] (φ : A ⟶ A') [IsMonHom φ] (x : Y ⟶ A) :
    x⁻¹ ≫ φ = (x ≫ φ)⁻¹ :=
  map_inv (post φ) x

theorem pre_inv {Y Y' A : C} [GrpObj A] (ρ : Y' ⟶ Y) (x : Y ⟶ A) : ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  map_inv (pre ρ) x

theorem isPullback_of_lift {Z P G B : C} {f : Z ⟶ P} {g : Z ⟶ G} {h : P ⟶ B} {k : G ⟶ B}
    (w : f ≫ h = g ≫ k) (hm : ∀ {Y : C} {a b : Y ⟶ Z}, a ≫ f = b ≫ f → a ≫ g = b ≫ g → a = b)
    (hl : ∀ {Y : C} (x : Y ⟶ P) (y : Y ⟶ G), x ≫ h = y ≫ k → ∃ l : Y ⟶ Z, l ≫ f = x ∧ l ≫ g = y) :
    IsPullback f g h k :=
  ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (hl s.fst s.snd s.condition).choose)
    (fun s => (hl s.fst s.snd s.condition).choose_spec.1)
    (fun s => (hl s.fst s.snd s.condition).choose_spec.2)
    (fun s m h1 h2 => hm (h1.trans (hl s.fst s.snd s.condition).choose_spec.1.symm)
      (h2.trans (hl s.fst s.snd s.condition).choose_spec.2.symm))⟩⟩

end General

theorem mulN_eq_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [pow_succ, ← ih]; rfl

section Main
variable {S : Scheme.{0}} {T Gt B : Over S} [GrpObj T] [IsCommMonObj T] [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B]
  [IsCommMonObj B] {u : T ⟶ Gt} {q : Gt ⟶ B} [IsMonHom u] [IsMonHom q] {N : ℕ}
  {TN GN BN : Over S} {jT : TN ⟶ T} {jG : GN ⟶ Gt} {jB : BN ⟶ B} {eB : 𝟙_ _ ⟶ BN}

theorem mono_of_ext (hu : IsPullback u (toUnit _) q η[B]) : Mono u :=
  ⟨fun _ _ h => hu.hom_ext h (toUnit_unique _ _)⟩

theorem lift_of_ext (hu : IsPullback u (toUnit _) q η[B]) {Y : Over S} (y : Y ⟶ Gt) (hy : y ≫ q = 1) :
    ∃ z : Y ⟶ T, z ≫ u = y :=
  ⟨hu.lift y (toUnit Y) (by rw [hy, Hom.one_def]), hu.lift_fst _ _ _⟩

theorem comp_ext (hu : IsPullback u (toUnit _) q η[B]) {Y : Over S} (z : Y ⟶ T) : (z ≫ u) ≫ q = 1 := by
  rw [Category.assoc, hu.w, Hom.one_def, ← Category.assoc, toUnit_unique (z ≫ toUnit T) (toUnit Y)]

theorem isPullback_kernel (hu : IsPullback u (toUnit _) q η[B])
    (hT : IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[T]) (hG : IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt])
    (hB : IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B]) (he : eB ≫ jB = η[B])
    {a : TN ⟶ GN} {b : GN ⟶ BN} (ha : a ≫ jG = jT ≫ u) (hb : b ≫ jB = jG ≫ q) :
    IsPullback a (toUnit TN) b eB := by
  have := mono_of_ext hu
  have := mono_of_pullback hT
  have := mono_of_pullback hG
  have := mono_of_pullback hB
  refine GlobalTheory.Diag.isPullback_toUnit_of_lift S ?_ (fun {Y} x y h => ?_) (fun {Y} t ht => ?_)
  · rw [← cancel_mono jB, Category.assoc, hb, reassoc_of% ha, Category.assoc, he]
    have := comp_ext hu jT
    rw [Category.assoc] at this
    rw [this, Hom.one_def]
  · rw [← cancel_mono jG, Category.assoc, Category.assoc, ha] at h
    rw [← cancel_mono (jT ≫ u)]
    simpa using h
  · have h1 : (t ≫ jG) ≫ q = 1 := by
      have : t ≫ b ≫ jB = t ≫ jG ≫ q := by rw [hb]
      rw [Category.assoc, ← this, ← Category.assoc, ht, Category.assoc, he, Hom.one_def]
    obtain ⟨v, hv⟩ := lift_of_ext hu _ h1
    have h2 : v ^ N = 1 := by
      rw [← cancel_mono u, post_pow, hv, torsion_of_comp hG, MonObj.one_comp]
    obtain ⟨w, hw⟩ := lift_of_torsion hT v h2
    refine ⟨w, ?_⟩
    rw [← cancel_mono jG, Category.assoc, ha, reassoc_of% hw, hv]

theorem exists_isPullback_cover (hu : IsPullback u (toUnit _) q η[B])
    (hG : IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt]) (hB : IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B])
    {b : GN ⟶ BN} (hb : b ≫ jB = jG ≫ q) {P : Over S} {pG : P ⟶ Gt} {pB : P ⟶ BN} (hP : pG ≫ q = pB ≫ jB) :
    ∃ (φ : P ⟶ T) (c : pullback φ ((𝟙 T) ^ N) ⟶ GN), IsPullback (pullback.fst _ _) c pB b := by
  have := mono_of_ext hu
  have := mono_of_pullback hG
  have := mono_of_pullback hB
  have h0 : (pG ^ N)⁻¹ ≫ q = 1 := by
    rw [post_inv, post_pow, hP, torsion_of_comp hB, inv_one]
  obtain ⟨φ, hφ⟩ := lift_of_ext hu _ h0
  have key : ∀ {Y : Over S} (y : Y ⟶ P), (y ≫ φ) ≫ u = ((y ≫ pG) ^ N)⁻¹ := fun y => by
    rw [Category.assoc, hφ, pre_inv, pre_pow]
  have hz : ∀ {Y : Over S} (z : Y ⟶ T), z ≫ ((𝟙 T) ^ N) = z ^ N := fun z => by
    rw [pre_pow, Category.comp_id]
  have tor : ((pullback.snd φ ((𝟙 T) ^ N) ≫ u) * (pullback.fst φ ((𝟙 T) ^ N) ≫ pG)) ^ N = 1 := by
    rw [mul_pow, ← post_pow u, ← hz (pullback.snd φ ((𝟙 T) ^ N)), ← pullback.condition, key, inv_mul_cancel]
  obtain ⟨c, hc⟩ := lift_of_torsion hG _ tor
  refine ⟨φ, c, isPullback_of_lift ?_ (fun {Y} a a' h1 h2 => ?_) (fun {Y} x k hxk => ?_)⟩
  · rw [← cancel_mono jB, Category.assoc, Category.assoc, hb, ← hP, reassoc_of% hc, MonObj.mul_comp,
      comp_ext hu, _root_.one_mul, Category.assoc]
  · refine pullback.hom_ext h1 ?_
    have h3 : a ≫ c ≫ jG = a' ≫ c ≫ jG := by rw [reassoc_of% h2]
    rw [hc, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc a (pullback.fst _ _) pG,
      ← Category.assoc a' (pullback.fst _ _) pG, h1, mul_left_inj] at h3
    rw [← cancel_mono u, Category.assoc, Category.assoc]
    exact h3
  · have e : (k ≫ jG) ≫ q = (x ≫ pG) ≫ q := by
      rw [Category.assoc, Category.assoc, ← hb, hP, reassoc_of% hxk]
    have hw : ((k ≫ jG) * (x ≫ pG)⁻¹) ≫ q = 1 := by
      rw [MonObj.mul_comp, post_inv, e, mul_inv_cancel]
    obtain ⟨s, hs⟩ := lift_of_ext hu _ hw
    have hsN : x ≫ φ = s ≫ ((𝟙 T) ^ N) := by
      rw [← cancel_mono u, key x, hz, post_pow, hs, mul_pow, torsion_of_comp hG, _root_.one_mul, inv_pow]
    refine ⟨pullback.lift x s hsN, pullback.lift_fst _ _ _, ?_⟩
    rw [← cancel_mono jG, Category.assoc, hc, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
      pullback.lift_fst, pullback.lift_snd, hs, inv_mul_cancel_right]

end Main

theorem torsion_exact : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Gt B : Over S) [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B] [IsCommMonObj B] (u : splitTorus S X ⟶ Gt) (q : Gt ⟶ B) [IsMonHom u] [IsMonHom q], Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback u (toUnit _) q η[B] → ∀ (N : ℕ), 1 ≤ N → ∀ (TN GN BN : Over S) (jT : TN ⟶ splitTorus S X) (jG : GN ⟶ Gt) (jB : BN ⟶ B) (eB : 𝟙_ _ ⟶ BN), IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[splitTorus S X] → IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt] → IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B] → eB ≫ jB = η[B] → ∀ (a : TN ⟶ GN) (b : GN ⟶ BN), a ≫ jG = jT ≫ u → b ≫ jB = jG ≫ q → Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit TN) b eB := by
  intro S X _ _ _ Gt B _ _ _ _ u q _ _ hfl hsu hqc hu N hN TN GN BN jT jG jB eB hT hG hB he a b ha hb
  have hN' : N ≠ 0 := by omega
  have hP := IsPullback.of_hasPullback q jB
  obtain ⟨φ, c, sq⟩ := exists_isPullback_cover hu hG hB hb hP.w
  have sql : IsPullback (pullback.fst φ ((𝟙 _) ^ N)).left c.left (pullback.snd q jB).left b.left :=
    sq.map (Over.forget S)
  have hPl : IsPullback (pullback.fst q jB).left (pullback.snd q jB).left q.left jB.left :=
    hP.map (Over.forget S)
  have hZl : IsPullback (pullback.snd φ ((𝟙 _) ^ N)).left (pullback.fst φ ((𝟙 _) ^ N)).left
      ((𝟙 (splitTorus S X)) ^ N).left φ.left :=
    (IsPullback.of_hasPullback φ ((𝟙 _) ^ N)).flip.map (Over.forget S)
  have f1 : Flat ((𝟙 (splitTorus S X)) ^ N).left := by
    rw [← mulN_eq_pow]; exact GlobalTheory.Diag.flat_mulN S X hN'
  have s1 : Surjective ((𝟙 (splitTorus S X)) ^ N).left := by
    rw [← mulN_eq_pow]; exact GlobalTheory.Diag.surjective_mulN S X hN'
  have f2 : Flat (pullback.fst φ ((𝟙 _) ^ N)).left := MorphismProperty.of_isPullback hZl f1
  have s2 : Surjective (pullback.fst φ ((𝟙 _) ^ N)).left := MorphismProperty.of_isPullback hZl s1
  have f3 : Flat (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hfl
  have s3 : Surjective (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hsu
  have c3 : QuasiCompact (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hqc
  refine ⟨?_, ?_, isPullback_kernel hu hT hG hB he ha hb⟩
  · haveI := GlobalTheory.flat_descendsAlong_fpqc
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sql ⟨⟨s3, f3⟩, c3⟩ f2
  · have : Surjective (c.left ≫ b.left) := by
      rw [← sql.w]; infer_instance
    exact Surjective.of_comp c.left b.left

end GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SurjectiveLeftOfFibre
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.FinFlat

theorem bijective_of_lTensor (R M N : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] (f : M →ₗ[R] N)
    (h : Function.Bijective (f.lTensor (IsLocalRing.ResidueField R))) : Function.Bijective f := by
  have hsurj : Function.Surjective f := by
    have hQ : Subsingleton (IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f)) := by
      have key : ∀ z : IsLocalRing.ResidueField R ⊗[R] (N ⧸ LinearMap.range f), z = 0 := fun z => by
        obtain ⟨w, rfl⟩ := LinearMap.lTensor_surjective (IsLocalRing.ResidueField R)
          (Submodule.mkQ_surjective (LinearMap.range f)) z
        obtain ⟨v, rfl⟩ := h.2 w
        have h0 : (LinearMap.range f).mkQ ∘ₗ f = 0 := by
          ext x
          simp
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero]
        rfl
      exact ⟨fun x y => by rw [key x, key y]⟩
    have h1 : Subsingleton (N ⧸ LinearMap.range f) := IsLocalRing.subsingleton_tensorProduct.1 hQ
    exact fun y => (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).1 (Subsingleton.elim _ _)
  have hfree : Module.Free R N := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hsurj
  have hs' : ∀ y, f (s y) = y := fun y => LinearMap.congr_fun hs y
  let π : M →ₗ[R] LinearMap.ker f := (LinearMap.id - s ∘ₗ f).codRestrict (LinearMap.ker f) (fun x => by
    simp [hs'])
  have hπ : π ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    simp [π, LinearMap.mem_ker.1 x.2]
  have hK : Subsingleton (IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f) := by
    have key : ∀ z : IsLocalRing.ResidueField R ⊗[R] LinearMap.ker f, z = 0 := fun z => by
      have h0 : f ∘ₗ (LinearMap.ker f).subtype = 0 := by
        ext x
        simp
      have h1 : (LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z = 0 := by
        apply h.1
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero, map_zero]
        rfl
      have h2 : π.lTensor (IsLocalRing.ResidueField R) ((LinearMap.ker f).subtype.lTensor (IsLocalRing.ResidueField R) z) = z := by
        rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπ, LinearMap.lTensor_id]
        rfl
      rw [← h2, h1, map_zero]
    exact ⟨fun x y => by rw [key x, key y]⟩
  have hK' : Subsingleton (LinearMap.ker f) := IsLocalRing.subsingleton_tensorProduct.1 hK
  refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, hsurj⟩
  have h3 : (⟨x, hx⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h3

theorem flat_left_of_fibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Over (Spec (CommRingCat.of R))) [IsFinite A.hom] [IsFinite B.hom] [Flat A.hom] (b : A ⟶ B)
    (h : Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) : Flat b.left := by
  obtain ⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩ := GlobalTheory.T.finite_scheme_map_from_special_fibre R A B b
  have := h3 inferInstance
  have h' : Flat (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) =
        i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ j₀.hom := by
      rw [e2]; simp
    rw [this]; infer_instance
  rw [Flat.SpecMap_iff] at h'
  have h'' : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    rw [Flat.SpecMap_iff]
    exact GlobalTheory.T.flat_of_flat_special_fibre R Q P φ h'
  rw [e1]; infer_instance

theorem isIso_of_fibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C K : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite K.hom] [Flat C.hom] (u : C ⟶ K)
    (h : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)) : IsIso u := by
  obtain ⟨P, Q, _, _, _, _, φ, i, j, i₀, j₀, h1, h2, h3, e1, e2⟩ := GlobalTheory.T.finite_scheme_map_from_special_fibre R C K u
  have := h3 inferInstance
  have h0 : IsIso ((Over.forget _).map ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u)) := inferInstance
  have h0' : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left := h0
  have h' : IsIso (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) =
        i₀.inv ≫ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u).left ≫ j₀.hom := by
      rw [e2]; simp
    rw [this]; infer_instance
  have h2' : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ) :=
    isIso_SpecMap_iff.1 h'
  have hco : ⇑(φ.toLinearMap.lTensor (IsLocalRing.ResidueField R)) =
      ⇑(Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hφ : Function.Bijective φ :=
    bijective_of_lTensor R Q P φ.toLinearMap (by rw [hco]; exact h2')
  have hS : IsIso (Spec.map (CommRingCat.ofHom φ.toRingHom)) := isIso_SpecMap_iff.2 hφ
  have hl : IsIso u.left := by rw [e1]; infer_instance
  haveI : IsIso ((Over.forget _).map u) := hl
  exact isIso_of_reflects_iso u (Over.forget _)

theorem surjective_left_of_fibre (R : Type) [CommRing R] [IsLocalRing R] (A B : Over (Spec (CommRingCat.of R))) [IsFinite B.hom] (b : A ⟶ B) [Flat b.left]
    (h : Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) : Surjective b.left := by
  constructor
  intro x
  have hsp : SpecializingMap B.hom := B.hom.isClosedMap.specializingMap
  obtain ⟨y, hxy, hy⟩ := hsp (IsLocalRing.specializes_closedPoint (B.hom x))
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) := by
    rw [Ideal.Quotient.nontrivial_iff]; simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)))) := inferInstance
  have ht : thick R (IsLocalRing.maximalIdeal R) 0 t = IsLocalRing.closedPoint R := by
    have hle : IsLocalRing.maximalIdeal R ≤ (thick R (IsLocalRing.maximalIdeal R) 0 t).asIdeal := fun x hx => by
      show Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1)) x ∈ t.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hx)]
      exact zero_mem _
    exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (thick R (IsLocalRing.maximalIdeal R) 0 t).isPrime.ne_top) hle)
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback y t (hy.trans ht.symm)
  obtain ⟨z₀, hz₀⟩ := h.surj y₀
  have hcomp : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left ≫ pullback.fst B.hom (thick R (IsLocalRing.maximalIdeal R) 0) =
      pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) ≫ b.left := pullback.lift_fst _ _ _
  have hz : b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) = y := by
    rw [← hy₀, ← hz₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]
  obtain ⟨w, -, hw⟩ := Flat.generalizingMap b.left (show x ⤳ b.left (pullback.fst A.hom (thick R (IsLocalRing.maximalIdeal R) 0) z₀) by rwa [hz])
  exact ⟨w, hw⟩

theorem main (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C A B : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite A.hom] [IsFinite B.hom] [Flat C.hom] [Flat A.hom] [Flat B.hom] (a : C ⟶ A) (b : A ⟶ B) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (hab : a ≫ b = toUnit C ≫ e)
  (h₀ : IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map (toUnit C)) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map e))
  (hf : Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left)
  (hs : Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left) :
  IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit C) b e := by
  have hb : Flat b.left := flat_left_of_fibre R A B b hf
  have hK : IsPullback (pullback.fst b e) (toUnit (pullback b e)) b e := by
    have h := IsPullback.of_hasPullback b e
    rwa [toUnit_unique (pullback.snd _ _) (toUnit _)] at h
  have hKl := hK.map (Over.forget _)
  have hKl' : IsPullback (pullback.fst b e).left (pullback b e).hom b.left e.left := by
    have hA : (toUnit (pullback b e)).left = (pullback b e).hom := by simpa using Over.w (toUnit (pullback b e))
    rw [← hA]; exact hKl
  have hbfin : IsFinite b.left := by
    have : IsFinite (b.left ≫ B.hom) := by rw [Over.w b]; infer_instance
    exact IsFinite.of_comp b.left B.hom
  have hKfin : IsFinite (pullback b e).hom := by
    have h1 : IsFinite (pullback b e).hom := MorphismProperty.of_isPullback hKl' ‹_›
    exact h1
  have hclosed : IsClosedImmersion (pullback.fst b e).left := by
    have he : IsClosedImmersion e.left := by
      have : IsClosedImmersion (e.left ≫ B.hom) := by
        have : e.left ≫ B.hom = 𝟙 _ := by simpa using Over.w e
        rw [this]; infer_instance
      exact IsClosedImmersion.of_comp _ B.hom
    exact MorphismProperty.of_isPullback hKl'.flip he
  let u : C ⟶ pullback b e := hK.lift a (toUnit C) hab
  have hu1 : u ≫ pullback.fst b e = a := hK.lift_fst _ _ _
  have hu0 : IsIso ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u) := by
    have hK0 := hK.map (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0))
    have : (Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map u = (h₀.isoIsPullback _ _ hK0).hom := by
      apply hK0.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp, hu1]
      · rw [IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp, toUnit_unique (u ≫ toUnit _) (toUnit C)]
    rw [this]; infer_instance
  have hu : IsIso u := isIso_of_fibre R C _ u hu0
  refine ⟨?_, hb, surjective_left_of_fibre R A B b hs, ?_⟩
  · have : IsIso u.left := inferInstanceAs (IsIso ((Over.forget _).map u))
    rw [← hu1, Over.comp_left]; infer_instance
  · exact IsPullback.of_iso hK (asIso u).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [hu1]) (by simp) (by simp) (by simp)

theorem exact_of_closedFibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (C A B : Over (Spec (CommRingCat.of R))) [IsFinite C.hom] [IsFinite A.hom] [IsFinite B.hom] [Flat C.hom] [Flat A.hom] [Flat B.hom] (a : C ⟶ A) (b : A ⟶ B) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B), a ≫ b = toUnit C ≫ e → IsPullback ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map (toUnit C)) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map e) → Flat ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left → Surjective ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b).left → IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit C) b e := by
  intro R _ _ _ C A B _ _ _ _ _ _ a b e hab h₀ hf hs
  exact main R C A B a b e hab h₀ hf hs

end GlobalTheory.CompanionTheory.Ar.BT.FinFlat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_periodQuot_transport {V P : Type} [AddCommGroup V] [Module ℂ V] [CommGroup P] (E : V → P)
    (hadd : ∀ z w, E (z + w) = E z * E w) (hsurj : Function.Surjective E) (Γ₀ : Submodule ℤ V)
    (hΓ : (Γ₀ : Set V) = {z | E z = 1}) (N : ℕ) (hN : 0 < N) (T₀ : Set P) (hT₀ : ∀ τ ∈ T₀, τ ^ N = 1) :
    ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))),
      Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) = Nat.card {p : P // p ^ N = 1} ∧
      Nat.card T = Nat.card T₀ ∧
      (∀ x : Γ₀, Submodule.Quotient.mk x ∈ T → E ((N : ℂ)⁻¹ • (x : V)) ∈ T₀) ∧
      ∀ x : Γ₀, E ((N : ℂ)⁻¹ • (x : V)) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hmem : ∀ z : V, z ∈ Γ₀ ↔ E z = 1 := fun z => by
    have := Set.ext_iff.1 hΓ z
    simpa using this
  have h0 : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hpow : ∀ (k : ℕ) (z : V), E ((k : ℂ) • z) = E z ^ k := by
    intro k z
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have hdiv : ∀ z : V, (N : ℂ) • (N : ℂ)⁻¹ • z = z := fun z => by rw [smul_smul, mul_inv_cancel₀ hNc, one_smul]
  let Eh : V →+ Additive P := AddMonoidHom.mk' (fun z => Additive.ofMul (E z)) (fun a b => by
    rw [hadd]; rfl)
  let d : Γ₀ →+ V := (((N : ℂ)⁻¹ • (LinearMap.id : V →ₗ[ℂ] V)).toAddMonoidHom).comp Γ₀.subtype.toAddMonoidHom
  let f : Γ₀ →ₗ[ℤ] Additive P := (Eh.comp d).toIntLinearMap
  have hf : ∀ x : Γ₀, f x = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hle : LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ≤ LinearMap.ker f := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, hf]
    have : (N : ℂ)⁻¹ • (((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀)) : V) = y := by
      have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) y : Γ₀) : V) = (N : ℂ) • (y : V) := by
        simp [Nat.cast_smul_eq_nsmul]
      rw [this, smul_smul, inv_mul_cancel₀ hNc, one_smul]
    rw [this, (hmem _).1 y.2]
    rfl
  let φ := Submodule.liftQ _ f hle
  have hφ : ∀ x : Γ₀, φ (Submodule.Quotient.mk x) = Additive.ofMul (E ((N : ℂ)⁻¹ • (x : V))) := fun x => rfl
  have hφN : ∀ q, (Additive.toMul (φ q)) ^ N = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ, toMul_ofMul, ← hpow, hdiv]
    exact (hmem _).1 x.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ] at hq
    have h1 : E ((N : ℂ)⁻¹ • (x : V)) = 1 := hq
    have h2 : (N : ℂ)⁻¹ • (x : V) ∈ Γ₀ := (hmem _).2 h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨_, h2⟩, Subtype.ext ?_⟩
    have : ((((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀)) ⟨_, h2⟩ : Γ₀) : V) = (N : ℂ) • (N : ℂ)⁻¹ • (x : V) := by
      simp [Nat.cast_smul_eq_nsmul]
    rw [this, hdiv]
  have hrange : ∀ p : P, p ^ N = 1 → ∃ q, Additive.toMul (φ q) = p := by
    intro p hp
    obtain ⟨z, rfl⟩ := hsurj p
    have h1 : (N : ℂ) • z ∈ Γ₀ := (hmem _).2 (by rw [hpow, hp])
    refine ⟨Submodule.Quotient.mk ⟨_, h1⟩, ?_⟩
    rw [hφ, toMul_ofMul]
    congr 1
    change (N : ℂ)⁻¹ • (N : ℂ) • z = z
    rw [smul_smul, inv_mul_cancel₀ hNc, one_smul]
  let ψ : (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) → P := fun q => Additive.toMul (φ q)
  have hψ : Function.Injective ψ := fun a b h => hinj (Additive.toMul.injective h)
  refine ⟨ψ ⁻¹' T₀, ?_, ?_, ?_, fun x => hφN (Submodule.Quotient.mk x)⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q, hφN q⟩) ⟨?_, ?_⟩)
    · exact fun a b h => hψ (congrArg Subtype.val h)
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p hp
      exact ⟨q, Subtype.ext hq⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨ψ q.1, q.2⟩) ⟨?_, ?_⟩)
    · exact fun a b h => Subtype.ext (hψ (congrArg Subtype.val h))
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := hrange p (hT₀ p hp)
      refine ⟨⟨q, ?_⟩, Subtype.ext hq⟩
      change ψ q ∈ T₀
      rw [show ψ q = p from hq]
      exact hp
  · intro x hx
    exact hx

theorem toric_torsion_radical_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp t.G M B ψ), SmoothOfRelativeDimension g t.G.hom → ∀ b₀ ∈ B, ∀ Γ₀ : Submodule ℤ (Fin g → ℂ), (Γ₀ : Set (Fin g → ℂ)) = e.per b₀ → ∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → GlobalTheory.UU.CubWeil t.cub N (e.ex b₀ ((N : ℂ)⁻¹ • (x : Fin g → ℂ))) (e.ex b₀ ((N : ℂ)⁻¹ • (y : Fin g → ℂ))) 1 := by
  intro E _ _ _ H R _ t g n M B ψ e dG b₀ hb₀ Γ₀ hΓ N hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨T₀, hT₁, hT₂, hT₃⟩ := GlobalTheory.exists_toric_torsion_cubWeil_one GlobalTheory.firstFiveLaws.2.2.1 (Sp R) t.G t.semi t.PP t.cub g N ℂ
    (spMap (ψ b₀)) dG hNc
  have hsurj := GlobalTheory.T.exponential_surjective_semiabelian R t.G g n M B ψ e t.semi b₀ hb₀
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := exists_periodQuot_transport (e.ex b₀) (e.add b₀ hb₀) hsurj Γ₀ hΓ N hN T₀ hT₁
  refine ⟨T, by rw [h₁, h₂, hT₃], fun x y hx => ?_⟩
  exact hT₂ _ (h₃ x hx) _ (h₄ y)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

