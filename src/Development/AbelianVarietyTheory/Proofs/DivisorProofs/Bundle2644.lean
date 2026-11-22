import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2523
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoExponentDivisorPullbackFlagCover
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlagLL

open GlobalTheory.FlagMod (FlagCover Frames ev)
open GlobalTheory.ShFam (EigFrame FlagCpt stalkPt genericPt constF)
open GlobalTheory.VarFlag GlobalTheory.VarFlagSpec
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

theorem spMap_alg_stalkPt {F : Type} [Field F] (Yv : GlobalTheory.ProjVar.Var F) (y : Yv.X) :
    spMap (algebraMap (Yv.X.presheaf.stalk y) Yv.X.functionField) ≫ stalkPt Yv y = genericPt Yv :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Yv.X).specializes trivial)

theorem mem_of_top_le {Xs Ys : Scheme.{0}} (x : Xs) (f : Xs ⟶ Ys) {V : Ys.Opens}
    (h : ⊤ ≤ (Xs.fromSpecStalk x ≫ f) ⁻¹ᵁ V) : f x ∈ V := by
  have h1 : f (Xs.fromSpecStalk x (IsLocalRing.closedPoint (Xs.presheaf.stalk x))) ∈ V := h trivial
  rwa [Scheme.fromSpecStalk_closedPoint] at h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Frames

variable {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_cast {R : Type} [CommRing R] {φ φ' : c.F →+* R} {x x' : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (hφ : φ' = φ) (hx : x' = x) : ∃ f' : EigFrame Z φ' x', ∀ τ i, f'.v τ i = f.v τ i := by
  subst hφ hx
  exact ⟨f, fun _ _ => rfl⟩

theorem tri_cast {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' φ'' : c.F →+* R'} {x : Sp R ⟶ Z.X}
    {x' x'' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {g : EigFrame Z φ' x'} {g' : EigFrame Z φ'' x''}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ} (h : f.Tri ψ g t) (hφ : φ'' = φ') (hx : x'' = x')
    (hv : ∀ τ i, g'.v τ i = g.v τ i) : f.Tri ψ g' t := by
  subst hφ hx
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun τ i => by rw [hv]; exact h3 τ i⟩

end Frames

variable {Y : Model Xo c (RingHom.id c.F)}

theorem co_chart {Zs : Scheme.{0}} {π : Zs ⟶ Y.X} (F : Frames Y π) {R : Type} [CommRing R] {φ : c.F →+* R}
    {x : Sp R ⟶ Y.X} (z z₁ z₂ : Sp R ⟶ Zs) (hx : x = z ≫ π) (h₁ : z₁ = z) (h₂ : z₂ = z) (k k' : F.J)
    (hk : ⊤ ≤ z₁ ⁻¹ᵁ F.U k) (hk' : ⊤ ≤ z₂ ⁻¹ᵁ F.U k') (hh : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) {g g' : EigFrame Y φ x}
    (hg : ∀ σ i, g.v σ i = (tv (F.vecAt k z₁ hk rfl σ i)).left)
    (hg' : ∀ σ i, g'.v σ i = (tv (F.vecAt k' z₂ hk' rfl σ i)).left) (τ : E →+* ℂ) :
    g.co g' τ = (F.B k k' τ).map (ev z _ hh) := by
  subst hx
  subst h₁
  subst h₂
  exact EigFrame.co_eq fun i => by
    rw [funext (hg τ), hg' τ i, GlobalTheory.LieMet.isComb_iff]
    exact F.vecAt_eq_sum k k' _ hk hk' hh rfl τ i

theorem gen_frame (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) (g : C.Y.X ⟶ X.YY)
    (hg : g ≫ X.π = C.π ≫ GlobalTheory.Toroidal.genι Y) (hrel : Rel X.F C (genericPt C.Y ≫ g) (genericPt C.Y)) :
    ∃ (k₀ : X.F.J) (hk₀ : ⊤ ≤ (genericPt C.Y ≫ g) ⁻¹ᵁ X.F.U k₀)
      (G₀ : EigFrame Y (constF (RingEquiv.refl c.F) C.Y) (genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y))
      (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
      (∀ σ i, G₀.v σ i = (tv (X.F.vecAt k₀ _ hk₀ rfl σ i)).left) ∧
      ∀ τ, (G₀.co C.f0 τ).BlockTriangular id ∧ ∀ i, G₀.co C.f0 τ i i = t₀ τ i := by
  obtain ⟨φ₀, k₀, hz₀, g₀, -, hfr, hcar⟩ := hrel
  have hx : (genericPt C.Y ≫ g) ≫ X.π = genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y := by
    rw [Category.assoc, hg]
  obtain ⟨g₁, hg₁⟩ := exists_cast g₀ (φ' := φ₀) rfl hx.symm
  have hcar₁ : C.Carries (genericPt C.Y) g₁ := by
    obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hcar
    exact ⟨y, ψ, φ₁, f, t, t', h1, h2, tri_cast h3 rfl hx.symm hg₁⟩
  have hcf : C.Carries (genericPt C.Y) C.f0 := by
    obtain ⟨φy, fy, ty, hT, -⟩ := C.gr_spec (genericPoint C.Y.X)
    exact ⟨_, _, φy, fy, ty, ty, (spMap_alg_stalkPt C.Y _).symm, hT, hT⟩
  obtain ⟨t₀, ht₀⟩ := tri_of_carries C hcar₁ hcf
  obtain ⟨G₀, hG₀⟩ := g₁.exists_isMap (RingHom.id _) ht₀.2.1 ht₀.1
  refine ⟨k₀, hz₀, G₀, t₀, fun σ i => ?_, fun τ => ?_⟩
  · rw [hG₀ σ i, spMap_dualMap_id, Category.id_comp, hg₁ σ i]
    exact hfr σ i
  · obtain ⟨h1, h2⟩ := ht₀.co τ hG₀
    exact ⟨fun a i h => h1 a i h, h2⟩

theorem isEqn_chart (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) (g : C.Y.X ⟶ X.YY)
    (hg : g ≫ X.π = C.π ≫ GlobalTheory.Toroidal.genι Y) (hFE : FramesExist X) {k₀ : X.F.J}
    {hk₀ : ⊤ ≤ (genericPt C.Y ≫ g) ⁻¹ᵁ X.F.U k₀}
    {G₀ : EigFrame Y (constF (RingEquiv.refl c.F) C.Y) (genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y)}
    {t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hG₀v : ∀ σ i, G₀.v σ i = (tv (X.F.vecAt k₀ _ hk₀ rfl σ i)).left)
    (hG₀ : ∀ τ, (G₀.co C.f0 τ).BlockTriangular id ∧ ∀ i, G₀.co C.f0 τ i i = t₀ τ i) (k : X.F.J) (y : C.Y.X)
    (hy : g y ∈ X.F.U k) (hh : ⊤ ≤ (genericPt C.Y ≫ g) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k₀)) (τ : E →+* ℂ)
    (i : Fin (Dw.mult τ)) :
    (C.gr τ i).IsEqn y (X.F.TAt k k₀ (genericPt C.Y ≫ g) hh (some ⟨τ, i⟩) * t₀ τ i) := by
  classical
  set α := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField with hα_def
  have hα : Function.Injective α := IsFractionRing.injective _ _
  have hzy : ⊤ ≤ (stalkPt C.Y y ≫ g) ⁻¹ᵁ X.F.U k := GlobalTheory.ShFam.top_le_stalk_preimage y g hy
  obtain ⟨φy, fy, ty, hT, hE⟩ := C.gr_spec y
  have hgs : g ≫ X.π ≫ Y.s = C.π ≫ GlobalTheory.Toroidal.genι Y ≫ Y.s := by rw [← Category.assoc, hg, Category.assoc]
  have hs : (stalkPt C.Y y ≫ g) ≫ X.π ≫ Y.s = spMap φy := by
    rw [Category.assoc, hgs]
    exact flagSpaceComponent_stalkPoint_over_coefficientField C y hT
  obtain ⟨gy, hgy⟩ := hFE _ φy _ k hzy hs
  have hzα : spMap α ≫ (stalkPt C.Y y ≫ g) = genericPt C.Y ≫ g := by
    rw [← Category.assoc, spMap_alg_stalkPt]
  have hxy : stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y = (stalkPt C.Y y ≫ g) ≫ X.π := by
    rw [Category.assoc, hg]
  have hx0 : genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y = spMap α ≫ ((stalkPt C.Y y ≫ g) ≫ X.π) := by
    rw [← hxy]
    exact hT.1
  obtain ⟨gF, hgF⟩ := gy.exists_isMap α hT.2.1 hx0
  obtain ⟨gF₂, hgF₂⟩ := gy.exists_isMap α (x' := (spMap α ≫ (stalkPt C.Y y ≫ g)) ≫ X.π) hT.2.1
    (Category.assoc _ _ _)
  have hF₂ := isFrameAt_map X.F hgy α hgF₂
  have hgFv : ∀ σ j, gF.v σ j = (tv (X.F.vecAt k (spMap α ≫ (stalkPt C.Y y ≫ g))
      (GlobalTheory.FlagMod.le_preimage_comp _ hzy) rfl σ j)).left := fun σ j => by
    rw [hgF σ j, ← hgF₂ σ j]
    exact hF₂ σ j
  have hB : gF.co G₀ τ = (X.F.B k k₀ τ).map (ev (genericPt C.Y ≫ g) _ hh) :=
    co_chart X.F (genericPt C.Y ≫ g) _ _ (by rw [Category.assoc, hg]) hzα rfl k k₀ _ hk₀ hh hgFv hG₀v τ
  obtain ⟨fF, hfF⟩ := fy.exists_isMap α hT.2.1 hT.1
  have hTf := hT.co τ hfF
  obtain ⟨gy', hgy'⟩ := exists_cast gy (φ' := φy) rfl hxy
  have hMap : gy'.IsMap α gF := fun σ j => by rw [hgF σ j, hgy' σ j]
  have hco : gF.co fF τ = (gy'.co fy τ).map α := hMap.co τ hfF hT.1
  set A := gF.co C.f0 τ with hA_def
  set T := fF.co C.f0 τ with hT_def
  set M := gy'.co fy τ with hM_def
  have hA : A = (X.F.B k k₀ τ).map (ev _ _ hh) * G₀.co C.f0 τ := by rw [← hB, EigFrame.co_mul]
  have hAt : A.BlockTriangular id := hA ▸ (X.F.B_map_tri k k₀ τ _).mul (hG₀ τ).1
  have hAd : A i i = ev _ _ hh (X.F.B k k₀ τ i i) * t₀ τ i := by
    rw [hA, GlobalTheory.FlagMod.tri_mul_diag (X.F.B_map_tri k k₀ τ _) (hG₀ τ).1, Matrix.map_apply, (hG₀ τ).2]
  have hTt : T.BlockTriangular id := fun a b h => hTf.1 a b h
  have hTT : T * C.f0.co fF τ = 1 := by rw [hT_def, EigFrame.co_mul, EigFrame.co_self]
  letI : Invertible T := Matrix.invertibleOfIsUnitDet T (Matrix.isUnit_det_of_right_inverse hTT)
  have hinv : C.f0.co fF τ = T⁻¹ := (Matrix.inv_eq_right_inv hTT).symm
  have hTi : (T⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hTt
  have hM' : M.map α = A * T⁻¹ := by rw [hM_def, ← hco, ← hinv, hA_def, EigFrame.co_mul]
  have hMt : M.BlockTriangular id := fun a b h => by
    have h1 := (hAt.mul hTi) h
    rw [← hM', Matrix.map_apply] at h1
    exact hα (h1.trans (map_zero α).symm)
  have hMu : IsUnit (M i i) := by
    have hdet := gy'.isUnit_det_co fy τ
    rw [← hM_def, Matrix.det_of_upperTriangular hMt] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => M j j) (Finset.mem_univ i)) hdet
  have hTd : T i i * T⁻¹ i i = 1 := by
    rw [← GlobalTheory.FlagMod.tri_mul_diag hTt hTi, Matrix.mul_inv_of_invertible, Matrix.one_apply_eq]
  have hMd : α (M i i) = A i i * ((ty τ i : C.Y.Fnˣ) : C.Y.Fn)⁻¹ := by
    have e1 : α (M i i) = (A * T⁻¹) i i := by rw [← hM', Matrix.map_apply]
    rw [e1, GlobalTheory.FlagMod.tri_mul_diag hAt hTi]
    congr 1
    rw [← hTf.2 i]
    exact eq_inv_of_mul_eq_one_right hTd
  refine (hE τ i).iff_unitAt.2 ⟨M i i, hMu, ?_⟩
  rw [hMd, hAd, Units.val_mul, div_eq_mul_inv]
  rfl

theorem fnOf_pull_g {Xs Ys : Scheme.{0}} [IsIntegral Xs] (M : LB Ys) (f : Xs ⟶ Ys) (J J' : (M.pull f).ι)
    (hgen : genericPoint Xs ∈ (M.pull f).U J ⊓ (M.pull f).U J')
    (hh : ⊤ ≤ (Xs.fromSpecStalk (genericPoint Xs) ≫ f) ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit))) :
    GlobalTheory.Cartier.fnOf _ hgen ((M.pull f).g J J' : Γ(Xs, _)) =
      ev (Xs.fromSpecStalk (genericPoint Xs) ≫ f) _ hh (M.g (J PUnit.unit) (J' PUnit.unit)).val := by
  show GlobalTheory.Cartier.fnOf _ hgen (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, GlobalTheory.Cartier.fnOf_resG]
  have hg' : genericPoint Xs ∈ f ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hgen.1, mem_pull.1 hgen.2⟩
  exact GlobalTheory.ShFam.fnOf_app_eq_ev f hg' hh _

end GlobalTheory.VarFlagLL

open GlobalTheory.VarFlagLL GlobalTheory.ShFam GlobalTheory.VarFlag in

theorem GlobalTheory.VarFlag.lbIso_LL_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (g : C.Y.X ⟶ X.YY), g ≫ X.π = C.π ≫ GlobalTheory.Toroidal.genι Y → (∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C (p ≫ g) p) → ∀ ex : Ix Dw → ℤ, ex none = 0 → LBIso (C.Y.lb (C.LEx ex)) ((X.LL ex).pull g) := by
  intro E _ _ _ H Dw l Xo c Y X C g hg hrel ex hex
  classical
  obtain ⟨k₀, hk₀, G₀, t₀, hG₀v, hG₀⟩ := gen_frame X C g hg (hrel _ (genericPt C.Y))
  have hFE := framesExist_flagCover X
  have hL : ((X.LL ex).pull g).IsLB := pull_isLB (X.F.isLB_LL ex) g
  let J₀ : ((X.LL ex).pull g).ι := fun _ => k₀
  have h₀ : genericPoint C.Y.X ∈ ((X.LL ex).pull g).U J₀ := mem_pull.2 (mem_of_top_le _ g hk₀)
  let cst : C.Y.Fnˣ := ∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t₀ x.1 x.2 ^ (-ex (some x))
  let r : ((X.LL ex).pull g).ι → C.Y.X.functionFieldˣ := fun J => GlobalTheory.Cartier.frameRat _ J₀ h₀ J * cst
  have hr : GlobalTheory.Cartier.IsRatSec ((X.LL ex).pull g) r := fun J J' h => by
    simp only [r, Units.val_mul]
    rw [GlobalTheory.Cartier.isRatSec_frameRat hL J₀ h₀ J J' h, mul_assoc]
  have heq : ∀ J, ∀ y ∈ ((X.LL ex).pull g).U J, (C.LEx ex).IsEqn y (r J) := by
    intro J y hy
    have hyk : g y ∈ X.F.U (J PUnit.unit) := mem_pull.1 hy
    have hgen : genericPoint C.Y.X ∈ ((X.LL ex).pull g).U J := GlobalTheory.Cartier.gen_mem hy
    have hh : ⊤ ≤ (genericPt C.Y ≫ g) ⁻¹ᵁ (X.F.U (J PUnit.unit) ⊓ X.F.U k₀) :=
      GlobalTheory.ShFam.top_le_stalk_preimage _ g ⟨mem_pull.1 hgen, mem_pull.1 h₀⟩
    have hx := fun x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
      isEqn_chart X C g hg hFE hG₀v hG₀ (J PUnit.unit) y hyk hh x.1 x.2
    have h1 := (GlobalTheory.ShFam.isEqn_finset_sum Finset.univ
      (fun x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => ex (some x) • C.gr x.1 x.2) y _
      fun x => (hx x).zsmul (ex (some x))).neg
    have hval : r J = (∏ x ∈ Finset.univ, (X.F.TAt (J PUnit.unit) k₀ (genericPt C.Y ≫ g) hh (some x) *
        t₀ x.1 x.2) ^ ex (some x))⁻¹ := by
      apply Units.ext
      have e1 : (r J : C.Y.X.functionField) = (GlobalTheory.Cartier.frameRat _ J₀ h₀ J : C.Y.X.functionField) * cst :=
        Units.val_mul _ _
      rw [e1, GlobalTheory.Cartier.val_frameRat J₀ h₀ J hgen, fnOf_pull_g _ g J J₀ _ hh]
      erw [GlobalTheory.FlagMod.Frames.ev_LL_g]
      have hu : (∏ ix : Ix Dw, X.F.TAt (J PUnit.unit) k₀ (genericPt C.Y ≫ g) hh ix ^ (-ex ix)) * cst =
          (∏ x ∈ Finset.univ, (X.F.TAt (J PUnit.unit) k₀ (genericPt C.Y ≫ g) hh (some x) *
            t₀ x.1 x.2) ^ ex (some x))⁻¹ := by
        rw [Fintype.prod_option, hex, neg_zero, zpow_zero, one_mul, ← Finset.prod_mul_distrib,
          ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun x _ => ?_
        rw [zpow_neg, zpow_neg, ← mul_inv, ← mul_zpow]
      exact (Units.val_mul _ _).symm.trans (congrArg Units.val hu)
    rw [hval]
    exact h1
  exact (GlobalTheory.Cartier.presents_toLB _).lbIso ⟨hL, hr, heq⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairOfLambdaBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pullback_pair_of_lambdaBundle_iso : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (M : LB A.left), P.IsLB → M.IsLB → LBIso P (cubeLB A ![fst A A, snd A A] M) → ∀ (T : Over (Sp ℂ)) (a b : T ⟶ A), LBIso (P.pull (lift a b).left) (cubeLB A ![a, b] M) := by
  first | exact @GlobalTheory.LamPull.lbIso_pull_lift | exact GlobalTheory.LamPull.lbIso_pull_lift | (intros; apply GlobalTheory.LamPull.lbIso_pull_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionPairPullback
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

theorem obAt_pairPull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (D : Type) [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ), ObAt S α L (K ⋙ pairSnd f₀) ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) → ObAt S' α (L.pull f₀) (K ⋙ pairFst f₀) ((extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c)) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L c D _ K hob
  obtain ⟨u, hfr, hu⟩ := hob
  let n : CoefMap (RingHom.id R₀) ((K ⋙ pairSnd f₀) ⋙ OAff s₀) ((K ⋙ pairFst f₀) ⋙ OAff t₀) :=
    { G := 𝟭 D
      α := fun T ↦ (pairPull h).α (K.obj T)
      naturality := fun a b ↦ (pairPull h).naturality (K.map a) b
      smul := fun T r b ↦ (pairPull h).smul (K.obj T) r b }
  have hH : ∀ T : D, opOf (K ⋙ pairFst f₀) T ≤ f₀ ⁻¹ᵁ opOf (K ⋙ pairSnd f₀) ((𝟭 D).obj T) :=
    fun T ↦ (K.obj T).unop.2
  refine ⟨_, isFrame_pull X₀ D _ (opOf_le (K ⋙ pairSnd f₀)) L u Z₀ f₀ D _ (opOf_le (K ⋙ pairFst f₀)) (𝟭 D) hH hfr, ?_⟩
  have key : (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c) =
      (extMap R₁ n).pull2 ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) := by
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    have hy : ∀ (T : D) (y : R₁ ⊗[R₀] (OAff s₀).obj ((pairSnd f₀).obj (K.obj T))),
        (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).α T ((extMap R₁ (pairPull h)).α (K.obj T) y) =
          (extMap R₁ n).α T ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).α T y) := by
      intro T y
      induction y using TensorProduct.induction_on with
      | zero => repeat erw [map_zero]
      | tmul x y => rfl
      | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]
    rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
    congr 1
    apply Subtype.ext
    funext T T' T'' a b
    simp only [CoefMap.pullCocycleTwo_apply]
    exact hy T'' _
  rw [key]
  refine isObU_pull R R₀ I hI π hπ hk R₁ α D _ ((ofSys S).restrict (K ⋙ pairSnd f₀)) D _
    ((ofSys S').restrict (K ⋙ pairFst f₀)) n (fun T ↦ l (K.obj T)) u _ _
    (fun T b ↦ hl (K.obj T) b) (fun T T' a b ↦ hn (K.map a) b) ?_ hu
  intro T T' a
  change (Z₀.presheaf.map _).hom ((f₀.app _).hom _) = (f₀.appLE _ _ _).hom _
  rfl

end GlobalTheory.LBObs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLocalSectionFamilyUnitAtFinitePointsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLocalSectionFamily_unit_at_finite_points : ∀ (X : Scheme.{0}) (L : LB X) (W : X.Opens) (J : Type) (D : J → X.Opens), (∀ j, D j ≤ W) → ∀ (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (F : Set X), F.Finite → ∀ (a : X → Γ(X, W)), (∀ x ∈ F, x ∈ X.basicOpen (a x)) → (∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x)) → ∀ (E : X → ∀ j, Γ(X, D j)), (∀ x ∈ F, GlobalTheory.Pinch.IsSecFam L D k hD (E x)) → (∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (E x j))) → ∃ e : ∀ j, Γ(X, D j), GlobalTheory.Pinch.IsSecFam L D k hD e ∧ ∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) := by
  first | exact @GlobalTheory.Pinch.secFam_unit_at_finite | exact GlobalTheory.Pinch.secFam_unit_at_finite | (intros; apply GlobalTheory.Pinch.secFam_unit_at_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSection_baseMul_cancel_flat_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  first | exact @GlobalTheory.Mum.secIsMul_cancel | exact GlobalTheory.Mum.secIsMul_cancel | (intros; apply GlobalTheory.Mum.secIsMul_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetricOfSymmetricGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGenericExt

theorem symm_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (jK R))).pull (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L := by
  intro R _ _ _ _ _ G _ hG L hL h
  have e := GlobalTheory.SymBaseChange.inv_left_fst _ _ G (jK R)
  have h1 := GenSpread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R))
    (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : G ⟶ G).left) (pullback.fst G.hom (jK R)) e
  refine GlobalTheory.GenericDec.lbIso_of_generic G hG (pull_isLB hL _) hL ?_
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h2)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h1 h)

end GlobalTheory.SymGenericExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineCStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_extends_normal_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → GlobalTheory.IsNormalScheme M.Z → ∀ (R₀ : Type) [CommRing R₀] (P : PolAV (Sp R₀)) (P' : PolAV (Sp (M.ringOn U))) (P₀ : PolAV (Sp Ω)) (f : R₀ →+* Ω) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap f) a → IsGrpPullback P₀.A P'.A (spMap (M.ringOn U).val.toRingHom) a' → LBIso P₀.L (P.L.pull a) → LBIso P₀.L (P'.L.pull a') → HypS P.A P.L → HypS P'.A P'.L := by
  first | exact @GlobalTheory.Poinc.hypS_of_generic_ringOn | exact GlobalTheory.Poinc.hypS_of_generic_ringOn | (intros; apply GlobalTheory.Poinc.hypS_of_generic_ringOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUnifor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UTraitHyp

theorem hypS_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif I t), (letI := P.A.isAb.comm; GlobalTheory.ZH.HypS P.A.A P.A.L) := by
  intro V _ _ I E _ _ _ H t P
  letI := P.A.isAb.comm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ t.G P.A.A (jK V) _ t.PP.L P.A.L t.PP.isLB P.A.isLB h1 h2
    ⟨t.act.act H.w0, t.act.act (H.bar H.w0), t.act.hom _, t.act.hom _,
      by rw [← t.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t.act.one], t.prim, t.adj _⟩

end GlobalTheory.UTraitHyp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_of_polAV_pullback : ∀ {S S' : Scheme.{0}} (P : PolAV S) (P' : PolAV S') (f : S' ⟶ S) (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f ψ → LBIso P'.L (P.L.pull ψ) → HypS P.A P.L → HypS P'.A P'.L := by
  first | exact @GlobalTheory.Poinc.hypS_polAV_pullback | exact GlobalTheory.Poinc.hypS_polAV_pullback | (intros; apply GlobalTheory.Poinc.hypS_polAV_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfInvariantPullbackGeneratorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_trivial_of_invariant_pullback_generator : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y), Flat p → Surjective p → IsAffineHom p → ∀ (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → (∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ X), y₁ ≫ p = y₂ ≫ p → ∀ (k : M.ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ (p ⁻¹ᵁ M.U k)), res h₁ (pullU y₁ _ (e k)) = res h₂ (pullU y₂ _ (e k))) → Triv M := by
  first | exact @GlobalTheory.CharKer.triv_of_isPullGen_of_invariant | exact GlobalTheory.CharKer.triv_of_isPullGen_of_invariant | (intros; apply GlobalTheory.CharKer.triv_of_isPullGen_of_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentCotangentOfIsTopFormFrameOfVaniStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (y : Y) (hy : y ∈ U) (J : Finset (Fin n)) (hz : ∀ j : J, Y.presheaf.germ U y hy (z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : J => Y.presheaf.germ U y hy (z j)) j, hz j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  first | exact @GlobalTheory.CotIndep.linearIndependent_cotangent_of_isFrame | exact GlobalTheory.CotIndep.linearIndependent_cotangent_of_isFrame | (intros; apply GlobalTheory.CotIndep.linearIndependent_cotangent_of_isFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointFunctionFieldOfFlatBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearlyDisjoint_functionField_of_flat_baseChange : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D), a.Flat → ∀ (H : Over (Sp T)) [IsIntegral H.left] (H' : Over (Sp D)) [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  first | exact @GlobalTheory.Desc.FlatLin.linDisj_of_flat | exact GlobalTheory.Desc.FlatLin.linDisj_of_flat | (intros; apply GlobalTheory.Desc.FlatLin.linDisj_of_flat <;> assumption)
end

