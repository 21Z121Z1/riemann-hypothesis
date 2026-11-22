import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

namespace GlobalTheory

namespace TopForm

open LB

section Ring

variable {k k' A B : Type} [CommRing k] [CommRing k'] [CommRing A] [CommRing B]
  {α : k →+* A} {β : k' →+* B}

def formMapSq (D : ℕ) (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ) :
    Forms α D →ₛₗ[ρ] Forms β D :=
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  { toFun := exteriorPowerMapOver B D (KaehlerDifferential.map k k' A B)
    map_add' := map_add _
    map_smul' := fun a x => by
      rw [map_smul, ← algebraMap_smul B]
      rfl }

variable {D : ℕ}

theorem formMapSq_dForm (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ) (f : Fin D → A) :
    formMapSq D σ ρ h (dForm α f) = dForm β fun i => ρ (f i) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  change exteriorPowerMapOver B D (KaehlerDifferential.map k k' A B)
    (exteriorPower.ιMulti A D _) = _
  rw [exteriorPowerMapOver_ιMulti, dForm_eq]
  simp only [KaehlerDifferential.map_D]
  rfl

theorem IsFreeGen.formMapSq (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ)
    (H : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom β)) {ω : Forms α D} (hω : IsFreeGen A ω) :
    IsFreeGen B (formMapSq D σ ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  haveI : Algebra.IsPushout k k' A B := (CommRingCat.isPushout_iff_isPushout.1 H).symm
  refine hω.of_isBaseChange (isBaseChange_exteriorPower
    (IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv k k' A B) fun x => ?_) D)
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) :=
    (KaehlerDifferential.span_range_derivation k A).ge Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul B, map_smul, hx, map_smul, algebraMap_smul]

end Ring

variable {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {Y Y' : Scheme.{0}}
  {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {φ : Y' ⟶ Y} {D : ℕ}

theorem appLE_comp_algX (w : φ ≫ p = p' ≫ spMap σ) {V : Y.Opens} {W : Y'.Opens}
    (h : W ≤ φ ⁻¹ᵁ V) : (φ.appLE V W h).hom.comp (algX p V) = (algX p' W).comp σ := by
  have e₁ : p.appLE ⊤ V le_top ≫ φ.appLE V W h =
      (spMap σ).appLE ⊤ ⊤ le_top ≫ p'.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE φ p ⊤ V W le_top h).trans (Eq.trans ?_
      (Scheme.Hom.appLE_comp_appLE p' (spMap σ) ⊤ ⊤ W le_top le_top).symm)
    simp only [w]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at e₂
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V le_top ≫ φ.appLE V W h =
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (CommRingCat.of k')).inv ≫ p'.appLE ⊤ W le_top := by
    rw [e₁, ← Category.assoc, ← Category.assoc, e₂]
    rfl
  exact congrArg CommRingCat.Hom.hom e₃

def pullForm (w : φ ≫ p = p' ≫ spMap σ) {V : Y.Opens} {W : Y'.Opens} (h : W ≤ φ ⁻¹ᵁ V) :
    FormsOn p D V →ₛₗ[(φ.appLE V W h).hom] FormsOn p' D W :=
  formMapSq D σ (φ.appLE V W h).hom (appLE_comp_algX w h)

variable (w : φ ≫ p = p' ≫ spMap σ) {U V : Y.Opens} {U' W W' : Y'.Opens}

theorem pullForm_dOn (h : W ≤ φ ⁻¹ᵁ V) (f : Fin D → Γ(Y, V)) :
    pullForm w h (dOn p f) = dOn p' fun a => (φ.appLE V W h).hom (f a) :=
  formMapSq_dForm _ _ _ f

theorem resForm_pullForm (h : W ≤ φ ⁻¹ᵁ V) (e : W' ≤ W) (η : FormsOn p D V) :
    resForm e (pullForm w h η) = pullForm w (e.trans h) η := by
  haveI : RingHomCompTriple (φ.appLE V W h).hom (resG Y' e) (φ.appLE V W' (e.trans h)).hom :=
    ⟨RingHom.ext (resG_appLE φ h e)⟩
  refine LinearMap.congr_fun (forms_ext (φ := (resForm e).comp (pullForm w h))
    (ψ := pullForm w (e.trans h)) fun f => ?_) η
  rw [LinearMap.comp_apply, pullForm_dOn, pullForm_dOn, resForm_dOn]
  simp only [resG_appLE]

theorem pullForm_resForm (e : V ≤ U) (h : W ≤ φ ⁻¹ᵁ V) (η : FormsOn p D U) :
    pullForm w h (resForm e η) = pullForm w (h.trans (φ.preimage_mono e)) η := by
  haveI : RingHomCompTriple (resG Y e) (φ.appLE V W h).hom
      (φ.appLE U W (h.trans (φ.preimage_mono e))).hom :=
    ⟨RingHom.ext (appLE_resG φ e h)⟩
  refine LinearMap.congr_fun (forms_ext (φ := (pullForm w h).comp (resForm e))
    (ψ := pullForm w (h.trans (φ.preimage_mono e))) fun f => ?_) η
  rw [LinearMap.comp_apply, resForm_dOn, pullForm_dOn, pullForm_dOn]
  simp only [appLE_resG]

theorem IsFrame.coeff_pullForm {ω : FormsOn p D U} (hω : IsFrame ω) (hU : U' ≤ φ ⁻¹ᵁ U)
    (hω' : IsFrame (pullForm w hU ω)) (e : V ≤ U) (e' : W ≤ U') (h : W ≤ φ ⁻¹ᵁ V)
    (η : FormsOn p D V) :
    hω'.coeff e' (pullForm w h η) = (φ.appLE V W h).hom (hω.coeff e η) := by
  refine fun_ext_of_cover (fun T : {T : Y.Opens // IsAffineOpen T ∧ T ≤ V} => W ⊓ φ ⁻¹ᵁ T.1)
    (fun _ => inf_le_left) (fun x hx => ?_) fun T => ?_
  · obtain ⟨T, hT⟩ := Opens.mem_iSup.1 (le_iSup_affine V (h hx))
    exact Opens.mem_iSup.2 ⟨T, hx, hT⟩
  · have h₁ := congrArg (pullForm w (inf_le_right : W ⊓ φ ⁻¹ᵁ T.1 ≤ _))
      (hω.resForm_eq_coeff_smul e η T.2.1 T.2.2)
    rw [map_smulₛₗ, pullForm_resForm, pullForm_resForm, appLE_resG] at h₁
    rw [IsFrame.resG_coeff, resForm_pullForm, resG_appLE]
    exact hω'.coeff_eq_of_eq_smul _ (h₁.trans (by rw [resForm_pullForm]))

theorem isAffineOpen_preimage_of_isPullback (H : IsPullback φ p' p (spMap σ))
    (hU : IsAffineOpen U) : IsAffineOpen (φ ⁻¹ᵁ U) :=
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  hU.preimage φ

theorem IsFrame.pullForm (H : IsPullback φ p' p (spMap σ)) {ω : FormsOn p D U} (hω : IsFrame ω)
    (hW : IsAffineOpen W) (h : W ≤ φ ⁻¹ᵁ U) : IsFrame (pullForm H.w h ω) := by
  letI := σ.toAlgebra
  have h₁ : IsFrame (TopForm.pullForm H.w (inf_le_left : φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _) ω) := by
    refine ⟨?_, hω.gen.formMapSq σ _ _ (isPushout_sections p p' φ H U hω.affine)⟩
    rw [show φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ = φ ⁻¹ᵁ U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H hω.affine
  have h₂ := h₁.res hW (le_inf h le_top)
  rwa [resForm_pullForm] at h₂

end TopForm

namespace CanonLB

open TopForm LB

variable {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {Y Y' : Scheme.{0}}
  {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {φ : Y' ⟶ Y} {D : ℕ}
  [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

theorem isFrame_pull (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D)
    (i : (K.bundle.pull φ).ι) : IsFrame (pullForm H.w (pull_U_le φ i) (K.om (i PUnit.unit))) :=
  (K.isFrame _).pullForm H
    (by rw [pull_U]; exact isAffineOpen_preimage_of_isPullback H (K.affine _)) _

def baseChange (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D) : CanonLB p' D where
  bundle := K.bundle.pull φ
  isLB := Semi.LB.isLB_linComb K.isLB _ _
  affine i := (K.isFrame_pull H i).affine
  om i := pullForm H.w (pull_U_le φ i) (K.om (i PUnit.unit))
  gen i := (K.isFrame_pull H i).gen
  trans i j W hW hi hj := by
    have h : W ≤ φ ⁻¹ᵁ (K.bundle.U (i PUnit.unit) ⊓ K.bundle.U (j PUnit.unit)) :=
      le_inf (hi.trans (pull_U_le φ i)) (hj.trans (pull_U_le φ j))
    have h₁ := (K.isFrame _).coeff_pullForm H.w _ (K.isFrame_pull H i) inf_le_left hi h
      (resForm inf_le_right (K.om (j PUnit.unit)))
    rw [pullForm_resForm] at h₁
    rw [resG_pull_g, g_eq_ratio, resForm_pullForm]
    exact ((K.isFrame_pull H i).coeff_smul_resForm hW hi _).symm.trans (congrArg (· • _) h₁)

theorem jacobian_baseChange (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D)
    (i : (K.bundle.pull φ).ι) {V : Y.Opens} (hV : V ≤ K.bundle.U (i PUnit.unit)) {W : Y'.Opens}
    (hW : W ≤ (K.bundle.pull φ).U i) (h : W ≤ φ ⁻¹ᵁ V) (f : Fin D → Γ(Y, V)) :
    (K.baseChange H).jacobian i hW (fun a => (φ.appLE V W h).hom (f a)) =
      (φ.appLE V W h).hom (K.jacobian (i PUnit.unit) hV f) := by
  have h₁ := (K.isFrame _).coeff_pullForm H.w _ (K.isFrame_pull H i) hV hW h (dOn p f)
  rw [pullForm_dOn] at h₁
  exact h₁

end CanonLB

theorem canonLB_baseChange (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (Y Y' : Scheme.{0}) (p : Y ⟶ Sp k) (p' : Y' ⟶ Sp k') (φ : Y' ⟶ Y) (D : ℕ)
    [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']
    (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D) (K' : CanonLB p' D) :
    ∃ w : LB.Iso K'.bundle (K.bundle.pull φ), w.IsGen ∧
      ∀ (i : (K.bundle.pull φ).ι) (j : K'.bundle.ι) (V : Y.Opens)
        (hV : V ≤ K.bundle.U (i PUnit.unit)) (W : Y'.Opens) (hW : W ≤ K'.bundle.U j)
        (h : W ≤ φ ⁻¹ᵁ V) (hw : W ≤ (LB.div (K.bundle.pull φ) K'.bundle).U (i, j))
        (f : Fin D → Γ(Y, V)),
        (φ.appLE V W h).hom (K.jacobian (i PUnit.unit) hV f) =
          resG Y' hw (w.s (i, j)).val * K'.jacobian j hW (fun a => (φ.appLE V W h).hom (f a)) :=
  ⟨K'.iso (K.baseChange H), K'.iso_isGen (K.baseChange H), fun i j _ hV _ hW h hw f =>
    (K.jacobian_baseChange H i hV (hw.trans inf_le_left) h f).symm.trans
      (K'.coeff_eq_iso_mul (K.baseChange H) i j _ hW _)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv.CondGen

theorem gs_appLE_self {X Y : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (z : Y)
    (hz : z ∈ W) (f : Γ(X, U)) : gs (𝟙 Y) z W ((q.appLE U W e).hom f) = gs q z U f := by
  have h1 := gs_res (𝟙 Y) z e hz ((q.app U).hom f)
  have h2 := gs_pull (𝟙 Y) q z U (e hz) f
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_fsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

end GlobalTheory.HomFixUniv.CondGen

open GlobalTheory.HomFixUniv.CondGen in

theorem GlobalTheory.HomFixUniv.isGen_of_matRel : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  intro Rg _ A B _ _ L M k mA mB bA bB R _ A' B' Φ' ψA ψB c u hG hR p p'
  apply unit_ext
  intro z hz
  have hzp : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := hz.1
  have hzp' : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p' := hz.2
  have hmB : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hzp.1
  have hmB' : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p'.1 hzp'.1
  have hmA : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hzp.2
  have hmA' : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p'.2 hzp'.2
  have key : ∀ (q : (Fin 1 → M.ι) × (Fin 1 → L.ι)), z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U q → ∀ j : Fin mB,
      gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) q.1) ((bB j).f q.1) =
        (gm (𝟙 _) z _ (u q)).val * GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z q.2 j := by
    intro q hq j
    have e := congrArg (gs (𝟙 A'.left) z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U q)) (hR j q)
    refine (gs_appLE_self _ _ _ _ z hq _).symm.trans (e.trans ?_)
    rw [gs_mul _ z _ hq, gs_unit _ z _ hq, gs_fsum _ z _ hq]
    unfold GlobalTheory.HomFixUniv.comb
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ z _ hq]
    exact congrArg₂ (· * ·) (gs_appLE_self _ _ _ _ z hq _) (gs_appLE_self _ _ _ _ z hq _)
  have tB : ∀ j : Fin mB, gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) =
      (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val *
        gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1) ((bB j).f p'.1) :=
    fun j => sec_trans (bB j) (Φ'.left ≫ ψB) z hmB hmB'
  have tA : ∀ i : Fin mA, gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) ((bA i).f p.2) =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2) ((bA i).f p'.2) :=
    fun i => sec_trans (bA i) ψA z hmA hmA'
  have tC : ∀ j : Fin mB, GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p.2 j =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j := by
    intro j
    unfold GlobalTheory.HomFixUniv.comb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (congrArg (_ * ·) (tA i)).trans (mul_left_comm _ _ _)
  have hg : gm (𝟙 A'.left) z _ ((isoLB (L := L) (M := M) k Φ' ψA ψB).g p p') =
      trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1 *
        (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹ := by
    show gm (𝟙 A'.left) z _ (res _ _ * (res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ hz _).trans ?_)
      ((map_inv _ _).trans (congrArg _ ((gm_res _ z _ hz _).trans ?_))))
    · exact (gm_linComb M _ _ (𝟙 A'.left) z p.1 p'.1 hzp.1 hzp'.1).trans (by simp only [trF, Category.id_comp])
    · exact (gm_linComb L _ _ (𝟙 A'.left) z p.2 p'.2 hzp.2 hzp'.2).trans (by simp only [trF, Category.id_comp])
  obtain ⟨j, hj⟩ := hG z p.2 hmA
  refine (gm_res _ z _ hz _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  rw [hg, gm_res _ z _ hz]
  apply Units.ext
  apply hj.mul_right_cancel
  have e1 := key p hzp j
  have e2 := key p' hzp' j
  have e3 := tB j
  have e4 := tC j
  have hinv := Units.inv_mul (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)
  rw [e1, e2, e4] at e3
  simp only [Units.val_mul]
  rw [e4]
  set TM := (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val
  set TL := (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val
  set TLi := ((trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹).val
  set U' := (gm (𝟙 A'.left) z _ (u p')).val
  set C' := GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j
  linear_combination e3 - (TM * U' * C') * hinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabelsStatement
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrrRep_harishChandra_distinct_cuspidal_labels : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∀ (C : LabelConv K) (O : LabelMap K C), Function.Injective (fun c => labO O (lam c)) → IsIrrRep (hcRep K b lam) := by
  first | exact @GlobalTheory.HcIrr.isIrrRep_hcRep | exact GlobalTheory.HcIrr.isIrrRep_hcRep | (intros; apply GlobalTheory.HcIrr.isIrrRep_hcRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfIsNilDP
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.TaylorCore

open GlobalTheory.PeriodFamily GlobalTheory.CatCoh

theorem isNilpotent_of_isNilDP {D : Type} [CommRing D] {J : Ideal D} {κ : DividedPowers J} (h : IsNilDP κ) : IsNilpotent J := by
  obtain ⟨N, hN⟩ := h
  have key : ∀ (n : ℕ) (l : List D), (∀ x ∈ l, x ∈ J) → N ≤ l.length + n → ∀ y ∈ J ^ n, l.prod * y = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl hn y _
      have := hN (l.map fun x => (1, x)) (by simpa using hl) (by simpa [Function.comp_def] using hn)
      rw [List.map_map, List.map_congr_left (f := (fun p : ℕ × D ↦ κ.dpow p.1 p.2) ∘ fun x ↦ (1, x)) (g := id)
        fun x hx => κ.dpow_one (hl x hx), List.map_id] at this
      rw [this, zero_mul]
    | succ n ih =>
      intro l hl hn y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) fun a b ha hb => by rw [mul_add, ha, hb, add_zero]
      have := ih (a :: l) (by simpa [ha] using hl) (by simp; omega) b hb
      rw [List.prod_cons] at this
      linear_combination this
  exact ⟨N, eq_bot_iff.2 fun y hy => by simpa using key N [] (by simp) (by simp) y hy⟩

def tayHom {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) : Hol V →+* D where
  toFun f := PeriodFamily.taylor N t f.fn
  map_one' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 1) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_one]),
      (taylor_formal_properties N t).2.2.1, map_one]
  map_zero' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 0) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_zero]),
      (taylor_formal_properties N t).2.2.1, map_zero]
  map_mul' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z * f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_mul _ _ hz),
      taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic _ h0) (f'.analytic _ h0)]
  map_add' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z + f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_add _ _ hz),
      (taylor_formal_properties N t).1 _ _ (f.analytic _ h0) (f'.analytic _ h0)]

theorem ev_red {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {D : Type} [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (p : E) (hp : p ∈ W) (x : D ⊗[ℂ] Hol W) :
    Hol.ev p hp (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol W)).comp π) (AlgHom.id ℂ (Hol W))
      (fun _ _ ↦ Commute.all _ _) x) =
    π (Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul d c =>
    simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply, AlgHom.id_apply, Algebra.ofId_apply,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem main : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B _ X X₀ s s₀ σ e e₀ hX hX₀ h0 hV₀ hτ φ₀ hφ₀ D _ _ π κ hκ hπ N t ht htN j hj s' hs' n φ hφ k c per hper
    m d cs p ps hps hcs hdec l
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  obtain ⟨D', _, _, io, π', nn, hio, hpio, hnil, hn0, hn2, hnt⟩ := SquareZeroSum.exists_sum_sq_zero N D πa t
    (isNilpotent_of_isNilDP hκ) ht htN
  obtain ⟨M, hM⟩ := id hnil
  have hJ : ∀ s : Fin (N + M + 1) → D', (∀ a, s a ∈ RingHom.ker π') → ∏ a, s a = 0 := fun s hs => by
    have h1 : ∏ a, s a ∈ ∏ _a : Fin (N + M + 1), RingHom.ker π' := Ideal.prod_mem_prod fun a _ => hs a
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Ideal.pow_le_pow_right (show M ≤ N + M + 1 by omega) h1
    rwa [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  have ht0 : ∀ i, π' (io (t i)) = 0 := fun i => (hpio _).trans (ht i)
  have ht' : ∀ s : Fin (N + M + 1) → I, ∏ a, io (t (s a)) = 0 := fun s => hJ _ fun a => ht0 _
  have hT : ∀ f, PeriodFamily.taylor (N + M) (fun i => io (t i)) f = io (PeriodFamily.taylor N t f) := fun f => by
    rw [← (taylor_formal_properties (N + M) t).2.2.2.2.1 D' io f, taylor_eq_of_le N t htN _ (Nat.le_add_right _ _)]
  have hred : ∀ f, π' (PeriodFamily.taylor (N + M) (fun i => io (t i)) f) = f 0 := fun f => by
    have h1 : PeriodFamily.taylor (N + M) (fun i => io (t i)) f - algebraMap ℂ D' (f 0) ∈ RingHom.ker π' :=
      (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ht0 i)) ((taylor_formal_properties (N + M) _).2.2.2.2.2 f)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.commutes] at h1
    exact h1
  obtain ⟨K₀, K, ν, hrich, hK₀, hK, hW, hν⟩ := ChartPair.exists_pair e₀ e (fun _ => 0) analyticOnNhd_const (fun _ _ => h0)
    LinearMap.id (AddMonoidHom.id Λ) fun l z _ => (hτ l z).symm
  obtain ⟨r₀, hr₀, -⟩ := exists_real_isFor e₀ hX₀ K₀ hK₀
  obtain ⟨r, hr, -⟩ := exists_real_isFor e hX K hK
  choose Ta hTa hTd using fun k => TaylorHom.exists_taylor_algHom (N + M) (fun i => io (t i)) ht' (K.W (ν k)) (K₀.W k) (hW k)
  let τV : Hol F.V →+* D' := tayHom (N + M) (fun i => io (t i)) ht' h0
  have hfam := TenFam.main π' r₀ rfl κ hs' (io : D →+* D') hpio hnil K r ν hν Ta τV
    (fun k f => tensor_hol_ext_of_values _ _ _ _ fun q hq => by
      rw [hTa k _ q hq, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      refine (taylor_formal_properties _ _).2.2.2.1 _ _ ?_
      have hc : Continuous fun z : I → ℂ => ((z, q.2) : Tot I g) := by fun_prop
      filter_upwards [hc.continuousAt.preimage_mem_nhds ((K.W (ν k)).isOpen.mem_nhds (hW k q hq))] with z hz
      exact K.fn_cst _ f hz)
    hTd (fun l k' k h₀ => close_paramTaylor_shift F F₀ h0 hτ _ (N + M) hJ _ N nn hn0 hn2 hnt K K₀ l _ _ k k' (hν l k' k h₀) h₀
      (hW k') (Ta k) (Ta k') (hTa k) (hTa k')) φ₀
    (fun k => point_hol_ext_of_isSeparated _ hX _ _ fun q hq => by
      rw [← Category.assoc, ← Category.assoc, hr₀ k q hq, hφ₀ q (K₀.base k q hq), ← hr (ν k) (0, q.2) (hW k q hq),
        ← Cris.spMap_comp]
      refine congrArg (fun ψ => spMap ψ ≫ r.x (ν k)) (RingHom.ext fun h => ?_)
      refine (ev_red π' q hq (Ta k h)).trans ?_
      rw [hTa k h q hq, hred]
      exact (Hol.ev_apply _ _ _).symm)
    j n (fun b => (congrArg io (hj b)).trans (hT _).symm) c per (τV.toAddMonoidHom.comp per) (fun _ => rfl) (hper K r hr)
  obtain ⟨z₀, hz₀⟩ := hV₀
  let q : Fin m → Λ →+ D' := fun i => ((algebraMap ℂ D').comp (Hol.ev z₀ hz₀).toRingHom).toAddMonoidHom.comp (ps i)
  have hq : ∀ i l, q i l = algebraMap ℂ D' (p i l) := fun i l =>
    congrArg (algebraMap ℂ D') ((congrArg (Hol.ev z₀ hz₀) (hps i l)).trans ((Hol.ev z₀ hz₀).commutes _))
  have hfib := fun i => TenFib.ten_fib π' r₀ rfl κ hs' (io : D →+* D') hpio hnil (algebraMap ℂ D) φ hφ k io.commutes (cs i) (p i)
    (ps i) (q i) (hps i) (hq i) (hcs i K₀ r₀ hr₀)
  rw [hdec, map_sum] at hfam
  simp only [LinearMap.map_smulₛₗ, hfib] at hfam
  have hz : K₀.tenZ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) =
      ∑ i, io (d i) • K₀.tenZ (q i) - K₀.tenZ (τV.toAddMonoidHom.comp per) := by
    let Z : (Λ →+ D') →ₗ[D'] Z1 (K₀.Ten D') :=
      { toFun := K₀.tenZ
        map_add' := fun a b => Subtype.ext (by funext T T' f; exact map_add (algebraMap D' (T'.ten D')) _ _)
        map_smul' := fun a b => Subtype.ext (by
          funext T T' f
          exact (map_mul (algebraMap D' (T'.ten D')) _ _).trans (Algebra.smul_def _ _).symm) }
    change Z _ = ∑ i, io (d i) • Z _ - Z _
    simp only [map_sub, map_sum, map_smul]
  have := Charts.tenZ_eq_zero K₀ hrich ⟨z₀, hz₀⟩ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) (by
    rw [hz, map_sub, ← hfam, map_sum]
    simp only [map_smul]
    exact sub_self _)
  have h1 := DFunLike.congr_fun (sub_eq_zero.1 this) l
  refine hio ?_
  rw [← hT, map_sum]
  refine Eq.trans ?_ h1
  rw [AddMonoidHom.finset_sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, io.commutes, AddMonoidHom.smul_apply, hq, smul_eq_mul]

end GlobalTheory.AnPer.TaylorCore
end
end

