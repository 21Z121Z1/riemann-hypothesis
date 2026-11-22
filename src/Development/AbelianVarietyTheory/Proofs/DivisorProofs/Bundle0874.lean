import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroup
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieCoordR

open ReciprocityTheory.ChartRestriction.G.Chart (sp fB sp_hom_fB)

section Iso

variable {W : Type} [CommRing W] {R' : Type} [CommRing R'] [Algebra W R']

theorem epsHom_w : 𝟙 (Spec (CommRingCat.of (DualNumber R'))) ≫ (sp (R₀ := W) (DualNumber R')).hom =
    (epsPtR (spMap (algebraMap W R'))).hom := by
  rw [Category.id_comp]
  exact (sp_hom_fB (R := W) (R' := R') (P := DualNumber R')).symm

theorem epsInv_w : 𝟙 (Spec (CommRingCat.of (DualNumber R'))) ≫ (epsPtR (spMap (algebraMap W R'))).hom =
    (sp (R₀ := W) (DualNumber R')).hom := by
  rw [Category.id_comp]
  exact sp_hom_fB (R := W) (R' := R') (P := DualNumber R')

def epsHom : epsPtR (spMap (algebraMap W R')) ⟶ sp (R₀ := W) (DualNumber R') :=
  Over.homMk (𝟙 (Spec (CommRingCat.of (DualNumber R')))) epsHom_w

def epsInv : sp (R₀ := W) (DualNumber R') ⟶ epsPtR (spMap (algebraMap W R')) :=
  Over.homMk (𝟙 (Spec (CommRingCat.of (DualNumber R')))) epsInv_w

end Iso

section Main
open GlobalTheory.SqZero
variable {W : Type} [CommRing W] {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR W ⟶ G)} {R' : Type} [CommRing R'] [Algebra W R']

theorem epsHom_epsInv : epsHom (W := W) (R' := R') ≫ epsInv = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp (𝟙 (Spec (CommRingCat.of (DualNumber R')))))

theorem epsInv_epsHom : epsInv (W := W) (R' := R') ≫ epsHom = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp (𝟙 (Spec (CommRingCat.of (DualNumber R')))))

theorem fst_left : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (fstS W R')).left =
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom := rfl

theorem isTanOver_epsInv (w : epsPtR (spMap (algebraMap W R')) ⟶ G)
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left =
        (1 : Over.mk (spMap (algebraMap W R')) ⟶ G).left) : IsTanOver (epsInv ≫ w) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, fst_left]
  exact (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·)
    (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) w.left)).trans hw

variable (v) in

def coordPt (c : Fin n → R') : epsPtR (spMap (algebraMap W R')) ⟶ G :=
  epsHom ≫ tanExp v c

theorem coordPt_injective [Smooth G.hom] (hv : IsLieBasis v) :
    Function.Injective (coordPt (R' := R') v) := by
  intro c c' h
  have h' := congrArg (epsInv ≫ ·) h
  simp only [coordPt] at h'
  rw [← Category.assoc, ← Category.assoc, epsInv_epsHom, Category.id_comp, Category.id_comp] at h'
  exact (LieTwo.isLieBasisOver_of_expBij (expBij (DualNumber R') hv)).1 c c' h'

theorem coordPt_range [Smooth G.hom] (hv : IsLieBasis v) (w : epsPtR (spMap (algebraMap W R')) ⟶ G) :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left =
        (1 : Over.mk (spMap (algebraMap W R')) ⟶ G).left ↔ w ∈ Set.range (coordPt v) := by
  constructor
  · intro hw
    obtain ⟨s, hs⟩ := (LieTwo.isLieBasisOver_of_expBij (expBij (DualNumber R') hv)).2 _
      (isTanOver_epsInv w hw)
    exact ⟨s, by rw [coordPt, ← hs, ← Category.assoc, epsHom_epsInv, Category.id_comp]⟩
  · rintro ⟨s, rfl⟩
    have := congrArg (fun f => Over.Hom.left f) (isTanOver_tanExp (S := R') hv.1 s)
    rw [Over.comp_left, fst_left] at this
    rw [coordPt, Over.comp_left]
    exact (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·)
      (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) (tanExp v s).left)).trans this

theorem coordPt_add (hv : IsLieBasis v) (c c' : Fin n → R') :
    coordPt v (c + c') = coordPt v c * coordPt v c' := by
  rw [coordPt, coordPt, coordPt, LieTwo.tanExp_add hv.1, MonObj.comp_mul]

theorem dualScale_eq (s : R') : (dualScale W s).toRingHom = ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR])
    (by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mul_comm])

theorem coordPt_smul (s : R') (c : Fin n → R') :
    (coordPt v (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (coordPt v c).left := by
  have h1 : s • c = fun i => c i * s := funext fun i => by simp [mul_comm]
  rw [coordPt, coordPt, Over.comp_left, Over.comp_left, h1, ← scl_tanExp, scl, Over.comp_left,
    ReciprocityTheory.ChartRestriction.G.Chart.spMap_left, dualScale_eq]
  exact (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) _).trans
    (congrArg (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ ·)
      (Category.id_comp (X := Spec (CommRingCat.of (DualNumber R'))) (tanExp v c).left)).symm

variable (v) in

def lieMat (hv : IsLieBasis v) (u : G ⟶ G) : Matrix (Fin n) (Fin n) W := by
  classical
  exact if h : ∀ i, IsTangent (v i ≫ u) then
    Matrix.transpose (Matrix.of fun i => (hv.2 _ (h i)).exists.choose) else 0

theorem isTangent_comp (hv : ∀ i, IsTangent (v i)) (u : G ⟶ G) [IsMonHom u] (i : Fin n) :
    IsTangent (v i ≫ u) := by
  unfold IsTangent at *
  rw [Over.comp_left, ← Category.assoc, hv i, ← Over.comp_left, IsMonHom.one_hom]

theorem comp_eq_tanExp (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (i : Fin n) :
    v i ≫ u = tanExp v (fun j => lieMat v hv u j i) := by
  have h := isTangent_comp hv.1 u
  have hc := (hv.2 _ (h i)).exists.choose_spec
  rw [isLieComb_iff_lieExp] at hc
  rw [hc]
  simp only [lieMat, dif_pos h, Matrix.transpose_apply, Matrix.of_apply]

theorem coordPt_comp (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (c : Fin n → R') :
    coordPt v c ≫ u = coordPt v (((lieMat v hv u).map (algebraMap W R')).mulVec c) := by
  have h1 : tanExp v c ≫ u = tanExp (fun i => v i ≫ u) c := by
    simp only [tanExp, lieExp]
    exact (map_prod (IsMonHom.monoidHom u (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := W) (DualNumber R'))) _ _).trans
      (Finset.prod_congr rfl fun i _ => by
        show (_ ≫ v i) ≫ u = _
        exact Category.assoc _ _ _)
  have hM : ∀ i, res (Algebra.ofId W R') (v i ≫ u) =
      tanExp v (Matrix.of (fun i j => algebraMap W R' (lieMat v hv u j i)) i) := by
    intro i
    rw [comp_eq_tanExp hv u i, res_tanExp]
    rfl
  have key : Matrix.vecMul c (Matrix.of (fun i j => algebraMap W R' (lieMat v hv u j i))) =
      ((lieMat v hv u).map (algebraMap W R')).mulVec c := by
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [coordPt, coordPt, Category.assoc, h1, LieTwo.tanExp_eq_vecMul hv.1 hM, key]

end Main

theorem exists_coords_baseChange : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∃ T : (Fin n → R') → (epsPtR (spMap β) ⟶ G), Function.Injective T ∧ (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c) := by
  intro W _ _ G _ _ hsm
  haveI := hsm
  obtain ⟨n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G hsm
  refine ⟨n, lieMat v hv, fun R' _ β => ?_⟩
  letI := β.toAlgebra
  exact ⟨coordPt v, coordPt_injective hv, coordPt_range hv, coordPt_add hv, coordPt_smul,
    fun u hu c => by haveI := hu; exact coordPt_comp hv u c⟩

end GlobalTheory.LieCoordR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTransitionUnitsCocycleThinBasis
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBTrans

variable {X : Scheme.{0}}

theorem res_comp {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {U : X.Opens} (a b : Γ(X, U)ˣ)
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ res hW a = res hW b) : a = b := by
  let J := {W : X.Opens // ∃ hW : W ≤ U, res hW a = res hW b}
  have hc : U ≤ ⨆ j : J, j.1 := fun x hx => by
    obtain ⟨W, hW, hx', e⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, e⟩, hx'⟩
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun j : J => j.1) U (fun j => homOfLE j.2.1) hc _ _ (fun j => ?_)
  exact congrArg Units.val j.2.2

theorem glue_units {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val) (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(X, V) from s) * (show Γ(X, V) from s') = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    show (X.presheaf.map (homOfLE (hW i)).op).hom _ = (X.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  exact ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => Units.ext (hs i)⟩

variable {C : Type} [Category.{0} C] {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
  {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ}

theorem res_quot (hu : IsCoc V hV u) {T₁ T₂ T T'' : C} (a : T₁ ⟶ T) (b : T₂ ⟶ T) (c : T ⟶ T'') :
    res (hV c) (u T₂ T b * (u T₁ T a)⁻¹) = u T₂ T'' (b ≫ c) * (u T₁ T'' (a ≫ c))⁻¹ := by
  rw [hu b c, hu a c, map_mul, map_inv, mul_inv_rev, _root_.mul_assoc, mul_inv_cancel_left]

theorem transition_units (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [thin : Quiver.IsThin C]
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) :
    IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ,
      ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  intro hB hu T₁ T₂
  have sub : ∀ {T T' : C} (f f' : T ⟶ T'), f = f' := fun f f' => @Subsingleton.elim _ (thin _ _) f f'
  let J := {T : C // Nonempty (T₁ ⟶ T) ∧ Nonempty (T₂ ⟶ T)}
  let W : J → X.Opens := fun j => V j.1
  have hW : ∀ j : J, W j ≤ V T₁ ⊓ V T₂ := fun j => le_inf (hV j.2.1.some) (hV j.2.2.some)
  let w : ∀ j : J, Γ(X, W j)ˣ := fun j => u T₂ j.1 j.2.2.some * (u T₁ j.1 j.2.1.some)⁻¹
  have hw : ∀ (j : J) (a : T₁ ⟶ j.1) (b : T₂ ⟶ j.1), w j = u T₂ j.1 b * (u T₁ j.1 a)⁻¹ :=
    fun j a b => by simp only [w]; rw [sub j.2.2.some b, sub j.2.1.some a]
  have hc : V T₁ ⊓ V T₂ ≤ iSup W := fun x hx => by
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨T, ⟨a⟩, ⟨b⟩⟩, hxT⟩
  have hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (w i) = res inf_le_right (w j) := by
    intro i j
    apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨c⟩, ⟨d⟩, hxT, hle⟩ := hB.2 i.1 j.1 x (W i ⊓ W j) hx hx.1 hx.2
    refine ⟨V T, hle, hxT, ?_⟩
    rw [res_comp, res_comp]
    have e1 := res_quot hu i.2.1.some i.2.2.some c
    have e2 := res_quot hu j.2.1.some j.2.2.some d
    change res (hV c) (w i) = res (hV d) (w j)
    simp only [w]
    rw [e1, e2, sub (i.2.1.some ≫ c) (j.2.1.some ≫ d), sub (i.2.2.some ≫ c) (j.2.2.some ≫ d)]
  obtain ⟨s, hs⟩ := glue_units (V T₁ ⊓ V T₂) W hW hc w hh
  have key : ∀ (g : Γ(X, V T₁ ⊓ V T₂)ˣ) (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T),
      res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b ↔
        res (le_inf (hV a) (hV b)) g = u T₂ T b * (u T₁ T a)⁻¹ :=
    fun g T a b => (eq_mul_inv_iff_mul_eq).symm
  refine ⟨s, fun T a b => (key s T a b).2 ?_, fun g hg => ?_⟩
  · have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this
  · apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    refine ⟨V T, le_inf (hV a) (hV b), hxT, ?_⟩
    rw [(key g T a b).1 (hg T a b)]
    have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this.symm

end GlobalTheory.LBTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueUnitRatioGeneratorsIsomorphicLineBun
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenRatio

variable {X : Scheme.{0}}

theorem comm_identity {M : Type} [CommGroup M] (B G G' Q Q' : M) :
    G' * G⁻¹ * B * (G * Q) * (G' * Q')⁻¹ = B * Q * Q'⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem gm_isGenOn {L : LB X} {W : X.Opens} {τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ} (hτ : IsGenOn L W τ)
    {x : X} {m n : L.ι} (hx : x ∈ W) (hm : x ∈ L.U m) (hn : x ∈ L.U n) :
    gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m n) * gm (𝟙 X) x _ (τ n) := by
  have hmem : x ∈ W ⊓ L.U m ⊓ L.U n := ⟨⟨hx, hm⟩, hn⟩
  have := congrArg (gm (𝟙 X) x _) (hτ m n)
  rwa [map_mul, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem] at this

def isoAt {L L' : LB X} (w : LB.Iso L L') (m' : L'.ι) (m : L.ι) : Γ(X, L'.U m' ⊓ L.U m)ˣ := w.s (m', m)

theorem isoAt_compat {L L' : LB X} {w : LB.Iso L L'} (hw : w.IsGen) (m n : L.ι) (m' n' : L'.ι) :
    res (inf_le_left : L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U m' ⊓ L'.U n') (L'.g m' n') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L.U m ⊓ L.U n) (L.g m n))⁻¹ *
      res (inf_le_right : L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) ≤ L'.U n' ⊓ L.U n) (isoAt w n' n) :=
  hw (m', m) (n', n)

theorem gm_iso {L L' : LB X} {w : LB.Iso L L'} (hw : w.IsGen) {x : X} {m n : L.ι} {m' n' : L'.ι}
    (hm : x ∈ L.U m) (hn : x ∈ L.U n) (hm' : x ∈ L'.U m') (hn' : x ∈ L'.U n') :
    gm (𝟙 X) x _ (isoAt w m' m) =
      gm (𝟙 X) x _ (L'.g m' n') * (gm (𝟙 X) x _ (L.g m n))⁻¹ * gm (𝟙 X) x _ (isoAt w n' n) := by
  have hmem : x ∈ L'.U m' ⊓ L.U m ⊓ (L'.U n' ⊓ L.U n) := ⟨⟨hm', hm⟩, ⟨hn', hn⟩⟩
  have := congrArg (gm (𝟙 X) x _) (isoAt_compat hw m n m' n')
  rwa [map_mul, map_mul, map_inv, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem,
    gm_res _ x _ hmem] at this

def ratioLoc (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ)
    (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ) (m' : L'.ι) (m : L.ι) : Γ(X, W ⊓ (L'.U m' ⊓ L.U m))ˣ :=
  res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) *
    res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) *
    (res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m'))⁻¹

theorem gm_ratioLoc (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ)
    (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ) (m : L.ι) (m' : L'.ι) {x : X} (hx : x ∈ W ⊓ (L'.U m' ⊓ L.U m)) :
    gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' m' m) =
      gm (𝟙 X) x _ (isoAt w m' m) * gm (𝟙 X) x _ (τ m) * (gm (𝟙 X) x _ (τ' m'))⁻¹ := by
  rw [ratioLoc, map_mul, map_mul, map_inv, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]

theorem exists_unique_ratio : ∀ (X : Scheme.{0}) (L L' : LB X) (W : X.Opens) (w : LB.Iso L L') (τ : ∀ m : L.ι, Γ(X, W ⊓ L.U m)ˣ) (τ' : ∀ m : L'.ι, Γ(X, W ⊓ L'.U m)ˣ), L.IsLB → L'.IsLB → w.IsGen → IsGenOn L W τ → IsGenOn L' W τ' → ∃! t : Γ(X, W)ˣ, ∀ (m : L.ι) (m' : L'.ι), res (inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W) t * res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m') = res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (w.s (m', m)) * res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) := by
  intro X L L' W w τ τ' hL hL' hw hτ hτ'
  have hc : W ≤ ⨆ p : L'.ι × L.ι, W ⊓ (L'.U p.1 ⊓ L.U p.2) := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨i', hi'⟩ := exists_chart hL' x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i', i), hx, hi', hi⟩
  have hagree : ∀ (p q : L'.ι × L.ι), ∀ x ∈ (W ⊓ (L'.U p.1 ⊓ L.U p.2)) ⊓ (W ⊓ (L'.U q.1 ⊓ L.U q.2)),
      gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' p.1 p.2) = gm (𝟙 X) x _ (ratioLoc L L' W w τ τ' q.1 q.2) := by
    rintro ⟨m', m⟩ ⟨n', n⟩ x ⟨⟨hx, hm', hm⟩, ⟨-, hn', hn⟩⟩
    rw [gm_ratioLoc L L' W w τ τ' m m' ⟨hx, hm', hm⟩, gm_ratioLoc L L' W w τ τ' n n' ⟨hx, hn', hn⟩,
      gm_iso hw hm hn hm' hn', gm_isGenOn hτ hx hm hn, gm_isGenOn hτ' hx hm' hn']
    exact comm_identity _ _ _ _ _
  obtain ⟨t, ht⟩ := glue_unit W (fun p : L'.ι × L.ι ↦ W ⊓ (L'.U p.1 ⊓ L.U p.2)) (fun p ↦ inf_le_left) hc
    (fun p ↦ ratioLoc L L' W w τ τ' p.1 p.2) hagree
  refine ⟨t, fun m m' ↦ ?_, fun t' ht' ↦ ?_⟩
  · rw [ht (m', m)]
    exact inv_mul_cancel_right _ _
  · apply unit_ext
    intro x hx
    obtain ⟨m, hm⟩ := exists_chart hL x
    obtain ⟨m', hm'⟩ := exists_chart hL' x
    have hmem : x ∈ W ⊓ (L'.U m' ⊓ L.U m) := ⟨hx, hm', hm⟩
    have e0 : res (inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W) t' *
        res (inf_le_inf_left W inf_le_left : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L'.U m') (τ' m') =
        res (inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ L'.U m' ⊓ L.U m) (isoAt w m' m) *
        res (inf_le_inf_left W inf_le_right : W ⊓ (L'.U m' ⊓ L.U m) ≤ W ⊓ L.U m) (τ m) := ht' m m'
    have e1 := congrArg (gm (𝟙 X) x _) e0
    rw [map_mul, map_mul, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem, gm_res _ x _ hmem] at e1
    have e2 := congrArg (gm (𝟙 X) x _) (ht (m', m))
    dsimp only at e2
    rw [gm_res _ x _ hmem, gm_ratioLoc L L' W w τ τ' m m' hmem] at e2
    rw [e2]
    exact eq_mul_inv_of_mul_eq e1

end GlobalTheory.GenRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

section Res

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def resI (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : Formalism.L2.Herm.intAf F E →+* 𝓞 E ⧸ I :=
  ((RingEquiv.ofBijective (cmpS F I) (cmpS_bij (F := F) I hI)).symm : _ →+* 𝓞 E ⧸ I).comp
    (Ideal.Quotient.mk (idS F I))

variable {F}

theorem resI_oToS (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (a : 𝓞 E) :
    resI F I hI (oToS F E a) = Ideal.Quotient.mk I a := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem resI_eq_zero_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    resI F I hI s = 0 ↔ s ∈ idS F I := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _ ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem exists_sub_mem (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    ∃ a : 𝓞 E, s - oToS F E a ∈ idS F I := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (resI F I hI s)
  exact ⟨a, (resI_eq_zero_iff I hI _).1 (by rw [map_sub, resI_oToS, ha, sub_self])⟩

theorem resI_eq_mk_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) (a : 𝓞 E) :
    resI F I hI s = Ideal.Quotient.mk I a ↔ s - oToS F E a ∈ idS F I := by
  rw [← resI_eq_zero_iff I hI, map_sub, resI_oToS, sub_eq_zero]

theorem resS_eq_resI (w : Pl E) : resS F w = resI F w.asIdeal w.ne_bot := rfl

theorem factor_resI {I J : Ideal (𝓞 E)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : I ≤ J) (s : Formalism.L2.Herm.intAf F E) :
    Ideal.Quotient.factor h (resI F I hI s) = resI F J hJ s := by
  obtain ⟨a, ha⟩ := exists_sub_mem I hI s
  rw [(resI_eq_mk_iff I hI s a).2 ha, (resI_eq_mk_iff J hJ s a).2 (Ideal.map_mono h ha)]
  rfl

theorem factor_resI_eq_resS {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (w : Pl E) (h : I ≤ w.asIdeal)
    (s : Formalism.L2.Herm.intAf F E) : Ideal.Quotient.factor h (resI F I hI s) = resS F w s :=
  factor_resI hI w.ne_bot h s

end Res

section CRT

variable {E : Type} [Field E] [NumberField E] {I : Ideal (𝓞 E)} {Pg : Finset (Pl E)}

def crtHom (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) : 𝓞 E ⧸ I →+* ∀ w : ↥Pg, kP w.1 :=
  RingHom.pi fun w => Ideal.Quotient.factor (hle w)

theorem crtHom_bijective (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) :
    Function.Bijective (crtHom hle) := by
  classical
  have hc : Pairwise (fun v w : ↥Pg => IsCoprime v.1.asIdeal w.1.asIdeal) := fun v w h =>
    HeightOneSpectrum.isCoprime_of_ne _ _ (fun e => h (Subtype.ext e))
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, hP, ← Finset.prod_coe_sort Pg,
      Ideal.prod_eq_iInf_of_pairwise_isCoprime (fun v _ w _ h => hc h)]
    simp only [Finset.mem_univ, iInf_pos, Ideal.mem_iInf]
    intro w
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hx w)
  · intro x
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hc x
    exact ⟨Ideal.Quotient.mk I a, funext fun w => ha w⟩

def crt (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) : (𝓞 E ⧸ I) ≃+* ∀ w : ↥Pg, kP w.1 :=
  RingEquiv.ofBijective (crtHom hle) (crtHom_bijective hP hle)

theorem crt_apply (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) (x : 𝓞 E ⧸ I) (w : ↥Pg) :
    crt hP hle x w = Ideal.Quotient.factor (hle w) x := rfl

def chiProd {K : Type} [Field K] (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) (χ : ∀ w : ↥Pg, (kP w.1)ˣ →* Kˣ) :
    (𝓞 E ⧸ I)ˣ →* Kˣ :=
  ∏ w : ↥Pg, (χ w).comp (Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom)

theorem chiProd_apply {K : Type} [Field K] (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal) (χ : ∀ w : ↥Pg, (kP w.1)ˣ →* Kˣ)
    (u : (𝓞 E ⧸ I)ˣ) : chiProd hle χ u = ∏ w : ↥Pg, χ w (Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom u) := by
  simp [chiProd]

theorem exists_chiProd_eq {K : Type} [Field K] (hP : I = ∏ w ∈ Pg, w.asIdeal) (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal)
    (χ' : (𝓞 E ⧸ I)ˣ →* Kˣ) : ∃ χ, chiProd hle χ = χ' := by
  classical
  let e : (𝓞 E ⧸ I)ˣ ≃* ∀ w : ↥Pg, (kP w.1)ˣ := (Units.mapEquiv (crt hP hle).toMulEquiv).trans MulEquiv.piUnits
  refine ⟨fun w => (χ'.comp e.symm.toMonoidHom).comp (MonoidHom.mulSingle (fun w : ↥Pg => (kP w.1)ˣ) w), ?_⟩
  ext1 u
  rw [chiProd_apply]
  have h : ∀ w, Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom u = e u w := fun w => Units.ext rfl
  simp only [h, MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
  rw [← map_prod, ← map_prod, Finset.univ_prod_mulSingle]
  simp

end CRT

end GlobalTheory.GeoActCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyOneTwoDualResolutionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_homology_one_two_dualResolution : ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g → ∀ (f : Fin g → O), Ideal.span (Set.range f) ≠ ⊤ → IsArtinianRing (O ⧸ Ideal.span (Set.range f)) → ∀ (C : CochainComplex (ModuleCat.{0} O) ℕ), (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] (O ⧸ Ideal.span (Set.range f))) → ∀ (K : Type) [Field K] (φ : O →+* K), RingHom.ker φ = IsLocalRing.maximalIdeal O → Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1) = g ∧ Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2) ≤ g.choose 2 := by
  first | exact @GlobalTheory.finrank_homology_one_two_of_dual_resolution | exact GlobalTheory.finrank_homology_one_two_of_dual_resolution | (intros; apply GlobalTheory.finrank_homology_one_two_of_dual_resolution <;> assumption)
end

