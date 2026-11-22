import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldOfTangentVectorOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3421
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOnOpenCuspIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.Sandwich

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {TF : TorFlag Xo c} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {P : WtPar Dw} (R : Choice TF.X Z U P)

theorem restr_mulPole (j : ℕ) (f : H0 R.str (R.adj j) ⊤) :
    H0.restr le_top (R.mulPole j ⊤ f) = R.mulPole j R.off (H0.restr le_top f) :=
  (ProdChart.restr_mul _ _ _ _).trans (by rw [H0.restr_ofSec]; rfl)

theorem mulPole_injective (h₁ : FreeOnOpen TF.X Z U P.u₁) (j : ℕ) : Function.Injective (R.mulPole j R.off) :=
  ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).injective

theorem nowhereZero_pow_zero : NowhereZero (H0.ofSec R.str ⊤ (R.Δ₁.pow 0)) := nowhereZero_of_exists fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart R.Δ₁.isLB y
  exact ⟨fun _ => i, mem_zpow_U.2 hi, by rw [R.Δ₁.germ_pow R.str 0 i y hy hi, pow_zero]; exact isUnit_one⟩

end GlobalTheory.HSApp.Sandwich

open GlobalTheory.HSApp.Sandwich in

theorem GlobalTheory.HSApp.sandwich : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P)
    (ω : CanId R.toModif), FnAlgClosed Xo c → ∀ h₁ : FreeOnOpen TF.X Z U P.u₁,
    (∀ j, CuspIso TF.X Z U (P.wt j) → adjGlobal R j ≤ LinearMap.range (adjSec R ω h₁ j)) ∧
    (CuspIso TF.X Z U (P.wt 0) → LinearMap.range (adjSec R ω h₁ 0) ≤ adjGlobal R 0) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U P R ω hF h₁
  have key := fun (j : ℕ) m => GlobalTheory.T.canonical_ideal_weight_section hP hG E H Dw l Xo c TF Z hF R.toModif ω _ _ (P.kap_add j) m
  refine ⟨fun j hj => ?_, fun hj => ?_⟩
  · rintro _ ⟨f, rfl⟩
    let e := R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)
    obtain ⟨m, hm⟩ := (R.bijective_pullOff (isLB_L₀ TF.X Z (P.wt j))).2 (e.symm (H0.restr le_top f))
    have hmul : H0.restr le_top (R.mulPole j ⊤ f) =
        (((common₀ TF.X Z).pull R.σ).canChart R.K.isLB (P.kap_add j)).mul ω.ω (R.pullOff m) := by
      rw [restr_mulPole, hm]
      have := R.mulPole_adjEquiv ω.ω ω.unit h₁ j (P.kap_add j) (e.symm (H0.restr le_top f))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
    obtain ⟨g, hg, hgm⟩ := (key j m).2 ⟨R.mulPole j ⊤ f, hmul⟩
    obtain ⟨c', hc'⟩ := hj.2 hg
    refine ⟨c', ?_⟩
    show e (R.pullOff (cuspSec TF.X Z U _ c')) = _
    rw [hc', hgm, hm, LinearEquiv.apply_symm_apply]
  · rintro _ ⟨c', rfl⟩
    obtain ⟨s, hs, hsr⟩ := hj.1 c'
    obtain ⟨g, hg⟩ := (key 0 _).1 ⟨s, hs, hsr⟩
    obtain ⟨f, hf⟩ := ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (nowhereZero_pow_zero R)).surjective g
    refine ⟨f, mulPole_injective R h₁ 0 ?_⟩
    rw [← restr_mulPole, mulPole_adjSec]
    exact (congrArg (H0.restr le_top) hf).trans hg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreInvariantVectorFieldsAtGenericPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFields

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem dualMapR_eq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : Chart.dualMapR f = dualMap f :=
  RingHom.ext fun z => by ext <;> simp [dualMap, Chart.dualMapR]

theorem one_left {S : Scheme.{0}} (X G : Over S) [GrpObj G] : (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  rw [Hom.one_def]; rfl

theorem red_of_isTr {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]
    {φ : R →+* S} {g : Sp S ⟶ G.left} {v : TanM (𝟙 (Sp R)) G} {w : Sp (DualNumber S) ⟶ G.left}
    (hg : g ≫ G.hom = spMap φ) (h : IsTr G φ g v w) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := h
  have e0 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [sp_comp]
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact Spec.map_id _
  let red : Over.mk (g ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom = g ≫ G.hom
      rw [← Category.assoc, e0, Category.id_comp])
  have ef : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    exact RingHom.ext fun z => by simp [dualMap]
  have hv : red ≫ v' = 1 := by
    apply Over.OverMorphism.ext
    have hr := congrArg (fun q => q.left) (GlobalTheory.InvFieldBase.redPt_tv G v)
    simp only [Over.comp_left] at hr
    rw [Over.comp_left, one_left, h₂, ← Category.assoc]
    change (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ _ = _
    rw [sp_comp, ef, ← sp_comp, Category.assoc]
    change spMap φ ≫ ((GlobalTheory.InvFieldBase.redPt R).left ≫ (tv v).left) = _
    rw [hr, one_left]
    change spMap φ ≫ 𝟙 _ ≫ _ = (g ≫ G.hom) ≫ _
    rw [Category.id_comp, hg]
  have k := congrArg (fun q => q.left) (MonObj.comp_mul red g' v')
  simp only [hv, _root_.mul_one, Over.comp_left] at k
  change red.left ≫ _ = g
  rw [k, h₁, ← Category.assoc]
  change (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S))) ≫ g = g
  rw [e0, Category.id_comp]

theorem isTr_push {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left)
    (hm : IsGrpPullback A G (spMap x₀) m) (w₀ : TanM (𝟙 (Sp R)) G) (v : TanM (𝟙 (Sp K)) A)
    (hv : (tv v).left ≫ m = spMap (dualMap x₀) ≫ (tv w₀).left) {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (y : Sp (DualNumber B) ⟶ A.left) (hy : IsTr A φ x v y) :
    IsTr G (φ.comp x₀) (x ≫ m) w₀ (y ≫ m) := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := hy
  obtain ⟨p, q, hp, hq, hpq⟩ := GlobalTheory.CechKS.exists_mul_of_isGrpPullback hm (tEpsG (x ≫ A.hom)) g' v'
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ G.hom) (by
      change _ = (spMap (algebraMap B (DualNumber B)) ≫ x ≫ A.hom) ≫ spMap x₀
      rw [Category.assoc x m, hm.1.w]
      simp only [Category.assoc])
  refine ⟨p, q, ?_, ?_, hpq⟩
  · simp only [hp, h₁, Category.assoc]
  · rw [hq, h₂, Category.assoc (spMap (dualMap φ)), hv, ← Category.assoc, sp_comp, dualMap_comp]

def epsOf {L : Type} [CommRing L] (D : L → L) (h1 : D 1 = 0) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = x * D y + y * D x) : L →+* DualNumber L where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (D s)
  map_one' := by ext <;> simp [h1]
  map_zero' := by
    have h0 : D 0 = 0 := by have := ha 0 0; simp at this; exact this
    ext <;> simp [h0]
  map_add' a b := by ext <;> simp [ha]
  map_mul' a b := by ext <;> simp [hm]; ring

theorem eq_of_isTr {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {v : TanM (𝟙 (Sp R)) G} {dd : Fld G.left} (hd : IsInv G v dd) {L : Type} [CommRing L] (φ : R →+* L)
    (y : Sp L ⟶ G.left) (hy : y ≫ G.hom = spMap φ) (D : L → L) (h1 : D 1 = 0) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = x * D y + y * D x) (U : G.left.Opens) (hU : IsAffineOpen U)
    (hyU : ⊤ ≤ y ⁻¹ᵁ U) (hD : ∀ f, valR y U (dd U f) = D (valR y U f)) {w : Sp (DualNumber L) ⟶ G.left}
    (hw : IsTr G φ y v w) : w = spMap (epsOf D h1 ha hm) ≫ y := by
  have r1 := red_of_isTr hy hw
  have e1 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ spMap (epsOf D h1 ha hm) = 𝟙 _ := by
    rw [sp_comp]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (epsOf D h1 ha hm) = RingHom.id L := by
      ext r; simp [epsOf]
    rw [this]; exact Spec.map_id _
  have r2 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ (spMap (epsOf D h1 ha hm) ≫ y) = y := by
    rw [← Category.assoc, e1, Category.id_comp]
  have hwU := GlobalTheory.CechKS.le_preimage_of_red r1 hyU
  refine GlobalTheory.Points.ext_of_valR hU hwU (GlobalTheory.CechKS.le_preimage_of_red r2 hyU) fun f => ?_
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hyU]
  have h0 := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom L L L).toRingHom w U hwU f
  rw [r1] at h0
  ext
  · rw [h0]; simp [epsOf]
  · rw [hd.2 L φ y w U f hy hyU hw, hD]; simp [epsOf]

theorem exists_affine {Ω : Type} [CommRing Ω] [IsLocalRing Ω] {X : Scheme.{0}} (x : Sp Ω ⟶ X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show x.base (IsLocalRing.closedPoint Ω) ∈ (⊤ : X.Opens) from trivial)
  refine ⟨U, hU, fun p _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint (R := Ω) p).map x.base.hom.continuous).mem_open U.isOpen hx

theorem exists_basis_bc {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left)
    (hm : IsGrpPullback A G (spMap x₀) m) (hs : Smooth G.hom) {n : ℕ}
    (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) :
    ∃ v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) A),
      ∀ a, (tv (v a)).left ≫ m = spMap (dualMap x₀) ≫ (tv (v' a)).left := by
  obtain ⟨u', hu', hu'l⟩ := GlobalTheory.Heat.CoeffWt.exists_isLieBasis v'
  obtain ⟨u, hu, hul⟩ := GlobalTheory.exists_isLieBasis_baseChange R K x₀ G A m hm hs n u' hu'
  have h := GlobalTheory.Heat.CoeffWt.isGrpPullback_self A
  let b : Fin n → TanM (𝟙 (Sp K)) A := fun j =>
    PullbackSections.mkT (pushHom h (epsR K) (u j)) ((PullbackSections.isTangent_iff h _).1 (hu.1 j))
  have ts : ∀ f : Fin n → TanM (𝟙 (Sp K)) A, tv (∑ i, f i) = ∏ i, tv (f i) := fun f => by
    simp only [tv, toMul_sum, Subgroup.val_finset_prod]
  have hcomb : ∀ (c : Fin n → K) (w : epsR K ⟶ A), IsLieComb c u w ↔
      pushHom h (epsR K) w = tv (∑ i, c i • b i) := fun c w => by
    rw [PullbackSections.isLieComb_iff h, ts]
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination K b) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact PullbackSections.tv_mem W)
    refine (existsUnique_congr fun c => ?_).1 (hu.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (PullbackSections.tanM_ext e).symm, fun e => by rw [e]⟩
  refine ⟨(Pi.basisFun K (Fin n)).map (LinearEquiv.ofBijective _ hbij), fun a => ?_⟩
  have e : (Pi.basisFun K (Fin n)).map (LinearEquiv.ofBijective _ hbij) a = b a := by
    simp [Module.Basis.map_apply, Fintype.linearCombination_apply_single]
  rw [e]
  change ((u a).left ≫ 𝟙 _) ≫ m = _
  rw [Category.comp_id, hul a, hu'l a, dualMapR_eq]

theorem der_frac {R : Type} [CommRing R] [IsDomain R] {L : Type} [Field L] (ψ : FractionRing R →+* L)
    (D : L → L) (hl : ∀ x y, D (x * y) = x * D y + y * D x) (h : ∀ r, D (ψ (algebraMap R (FractionRing R) r)) = 0)
    (k : FractionRing R) :
    D (ψ k) = 0 := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hy0 : algebraMap R (FractionRing R) y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hψ0 : ψ (algebraMap R (FractionRing R) y) ≠ 0 := (map_ne_zero ψ).2 hy0
  have e : ψ (algebraMap R (FractionRing R) x / algebraMap R (FractionRing R) y) * ψ (algebraMap R (FractionRing R) y) =
      ψ (algebraMap R (FractionRing R) x) := by rw [← map_mul, div_mul_cancel₀ _ hy0]
  have k2 := congrArg D e
  rw [hl, h, h, mul_zero, zero_add] at k2
  exact (mul_eq_zero.1 k2).resolve_left hψ0

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (v : Module.Basis (Fin n) (FractionRing R) (TanM (𝟙 (Sp (FractionRing R))) P.A.A)) (dd : Fin n → Fld P.A.A.left), (∀ a, IsInv P.A.A (v a) (dd a)) ∧ ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL a (valR ξ O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx' hinv hδ hval _ g _ δL hδL ψ ξ
    hψ hξA hξ _
  have hm : IsGrpPullback P.A.A t.G (spMap (algebraMap R (FractionRing R)))
      (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  obtain ⟨v, hv⟩ := exists_basis_bc (algebraMap R (FractionRing R)) t.G P.A.A _ hm t.semi.smooth v'
  choose dd hdd using fun a => GlobalTheory.InvFieldBase.exists_isInv (FractionRing R) P.A.A (v a)
  refine ⟨v, dd, hdd, fun a O f hO => ?_⟩
  obtain ⟨U, hU, hxU⟩ := exists_affine x'
  have hyU : ⊤ ≤ (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ⁻¹ᵁ U := by
    rw [hξ]
    exact fun p _ => hxU (Set.mem_univ ((spMap (algebraMap Ω (FractionRing Ω))).base p))
  have hyG : (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ≫ t.G.hom =
      spMap (ψ.comp (algebraMap R (FractionRing R))) := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hξA, sp_comp]
  have hl : ∀ x y, δL a (x * y) = x * δL a y + y * δL a x := fun x y => by
    rw [(δL a).leibniz, smul_eq_mul, smul_eq_mul]
  have hDy : ∀ f, valR (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) U (dd' a U f) =
      δL a (valR (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) U f) := by
    intro f
    rw [hξ, GlobalTheory.Points.valR_spMap_comp _ _ _ hxU, GlobalTheory.Points.valR_spMap_comp _ _ _ hxU, hval a U _ hxU, hδL]
  have hc : ∀ k, δL a (ψ k) = 0 := der_frac ψ (δL a) hl fun r => by rw [hψ, hδL, hδ, map_zero]
  have hdual : (dualMap ψ).comp (algebraMap (FractionRing R) (DualNumber (FractionRing R))) =
      (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))).comp ψ := by
    ext k <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let g' : tEpsG (ξ ≫ P.A.A.hom) ⟶ P.A.A :=
    Over.homMk (spMap (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))) ≫ ξ) (Category.assoc _ _ _)
  let w' : tEpsG (ξ ≫ P.A.A.hom) ⟶ P.A.A :=
    Over.homMk (spMap (dualMap ψ) ≫ (tv (v a)).left) (by
      rw [Category.assoc, Over.w (tv (v a)), hξA]
      change spMap (dualMap ψ) ≫ spMap (algebraMap _ _) ≫ 𝟙 _ = spMap _ ≫ spMap ψ
      rw [Category.comp_id, sp_comp, sp_comp, hdual])
  have htr : IsTr P.A.A ψ ξ (v a) (g' * w').left := ⟨g', w', rfl, rfl, rfl⟩
  have key : (g' * w').left = spMap (epsOf (δL a) (δL a).map_one_eq_zero (map_add _) hl) ≫ ξ := by
    refine hm.1.hom_ext ?_ ?_
    · rw [eq_of_isTr (hinv a) _ _ hyG (δL a) (δL a).map_one_eq_zero (map_add _) hl U hU hyU hDy
        (isTr_push _ _ hm (v' a) (v a) (hv a) ψ ξ _ htr), Category.assoc]
    · rw [Over.w (g' * w')]
      change spMap (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))) ≫ ξ ≫ P.A.A.hom =
        (spMap _ ≫ ξ) ≫ P.A.A.hom
      rw [Category.assoc, hξA, sp_comp, sp_comp]
      congr 1
      ext k
      · simp [epsOf, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [epsOf, TrivSqZeroExt.algebraMap_eq_inl, hc]
  rw [← (hdd a).2 (FractionRing Ω) ψ ξ _ O f hξA hO htr, key, GlobalTheory.Points.valR_spMap_comp _ _ _ hO]
  simp [epsOf]

end GlobalTheory.GenFields
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreNormalProjectiveAmpleCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.GenFibNormal

theorem genFibre_of_fieldChange (hd2 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0}) (g : Y ⟶ Sp F), GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme (pullback g (spMap c))) : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) := by
  intro o K _ _ _ _ b hb Z z L hP hN hL hA
  haveI hsa : IsAffineHom (spMap b) := inferInstance
  haveI : IsAffineHom (pullback.fst z (spMap b)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback z (spMap b)).flip hsa
  refine ⟨ProjSpace.isProjOver_pullback_snd b hP, ?_, LB.isLB_pull hL _, IsAmpleLB.pull_of_isAffineHom hA _⟩
  haveI : CharZero o := ⟨fun m n h => by
    have := congrArg b h; simp only [map_natCast] at this; exact_mod_cast this⟩
  let F := FractionRing o
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective o F)
  let b' : F →+* K := IsFractionRing.lift hb
  have hbb : b'.comp (algebraMap o F) = b := RingHom.ext fun x => IsFractionRing.lift_algebraMap hb x
  have hZF : GlobalTheory.IsNormalScheme (pullback z (spMap (algebraMap o F))) :=
    IsNormalScheme.of_pred (FlagCls.isNormalScheme_of_isPullback_fractionField o F Z _ z
      (pullback.fst z (spMap (algebraMap o F))) (pullback.snd z (spMap (algebraMap o F)))
      (IsPullback.of_hasPullback _ _) ((isNormalScheme_iff_pred Z).mp hN))
  have h1 := hd2 F K b' _ (pullback.snd z (spMap (algebraMap o F))) hZF
  have e := pullbackLeftPullbackSndIso z (spMap (algebraMap o F)) (spMap b')
  have hc : spMap b' ≫ spMap (algebraMap o F) = spMap b := by
    rw [← hbb]
    simp only [spMap, ← Spec.map_comp]
    rfl
  exact (IsNormalScheme.iff_of_iso (e ≪≫ pullback.congrHom rfl hc)).mp h1

theorem genericFibre_normal_projective_ample : ∀ (o K : Type) [CommRing o] [IsDomain o] [Field K] [CharZero K] (b : o →+* K), Function.Injective b → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp o) (L : LB Z), IsProjOver z → GlobalTheory.IsNormalScheme Z → L.IsLB → IsAmpleLB L → IsProjOver (pullback.snd z (spMap b)) ∧ GlobalTheory.IsNormalScheme (pullback z (spMap b)) ∧ (L.pull (pullback.fst z (spMap b))).IsLB ∧ IsAmpleLB (L.pull (pullback.fst z (spMap b))) :=
  genFibre_of_fieldChange (GlobalTheory.T.isNormalScheme_pullback_spMap_of_isNormalScheme (GlobalTheory.T.isDomain_and_isIntegrallyClosed_atPrime_tensor_field_alt GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero GlobalTheory.T.isDomain_isIntegrallyClosed_atPrime_of_finset_subrings))

end GlobalTheory.GenFibNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedHeatOperatorsPreserveSectionsUpToConstant
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatVExt
open GlobalTheory.KS

theorem cst_resV {Y : Scheme.{0}} {R : Type} [CommRing R] (π : Y ⟶ Sp R) (c : R) {O : Y.Opens}
    (h : O ≤ π ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1) (r : R) :
    GlobalTheory.HeatV.cst π _ h (GlobalTheory.HeatV.resV R c r) = rsT (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) O := by
  rw [rsT_of_le le_top]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.Hom.map_appLE π (U := (GlobalTheory.HeatV.bo R c).1) (U' := ⊤) (V := O) h (homOfLE le_top).op)

theorem rsT_cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O O' : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O)
    (a : Γ(X, V)) : rsT (GlobalTheory.HeatV.cst π V h a) O' = GlobalTheory.HeatV.cst π V (h'.trans h) a := by
  rw [rsT_of_le h']
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_map π h (homOfLE h').op)

theorem rsT_natCast {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (m : ℕ) : rsT (m : Γ(Y, O₀)) O = m := by
  rw [rsT_of_le h, map_natCast]

theorem rsT_two {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) : rsT (2 : Γ(Y, O₀)) O = 2 := by
  rw [rsT_of_le h, map_ofNat]

theorem opV_rsT : ∀ {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → GlobalTheory.Heat.Fld Y), (∀ a, IsField ⊤ (dd a)) → ∀ (Θ : Matrix (Fin n) (Fin n) Γ(X, V)) (u : Fin n → Γ(X, V)) (d : GlobalTheory.Heat.Fld Y) {W : Y.Opens}, IsField W d → ∀ (p p' : Γ(Y, W)) (k : ℕ) {O O' : Y.Opens} (hOW : O ≤ W) (h : O ≤ π ⁻¹ᵁ V) (h' : O' ≤ O) (f : Γ(Y, O)), rsT (GlobalTheory.HeatV.opV π V dd Θ u d p p' k O h f) O' = GlobalTheory.HeatV.opV π V dd Θ u d p p' k O' (h'.trans h) (rsT f O') := by
  intro Y X π V n dd hdd Θ u d W hd p p' k O O' hOW h h' f
  have hd' : ∀ g, resG Y h' (d O g) = d O' (resG Y h' g) :=
    fun g => ((hd.2.2 O O' h' hOW g)).symm
  have hdd' : ∀ a g, resG Y h' (dd a O g) = dd a O' (resG Y h' g) :=
    fun a g => ((hdd a).2.2 O O' h' le_top g).symm
  have hc : ∀ r, resG Y h' (GlobalTheory.HeatV.cst π V h r) = GlobalTheory.HeatV.cst π V (h'.trans h) r :=
    fun r => (rsT_of_le h' _).symm.trans (rsT_cst π V h h' r)
  have hp : ∀ q : Γ(Y, W), resG Y h' (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h', rsT_rsT hOW h']
  rw [rsT_of_le h', rsT_of_le h']
  simp only [GlobalTheory.HeatV.opV, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem heat_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (dd' : Fin n → Fld t.G.left), (∀ a, IsField ⊤ (dd' a)) → ∀ (D : Derivation ℤ R R) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∀ (k : ℕ) (σ : SecM (𝟙 t.G.left) t.PP.L k) (a : R), ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k), r ≠ 0 ∧ ∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t c hc n dd' hdd' D Θ₁ DV hDV J W j d u pf pf' hW hcov hWL hd hdc hglue k σ a
  set π := t.G.hom
  set M := LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)) with hMdef
  have hM : M.IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.PP.isLB _ _
  set f : Γ(t.G.left, ⊤) := π.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) with hfdef
  have hb : π ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 = t.G.left.basicOpen f := Scheme.preimage_basicOpen_top π _
  have hWc : ∀ i, W i ≤ M.U (fun _ => j i) := fun i => GlobalTheory.Heat.Glue.le_wchart _ (hWL i)
  let F : ∀ i, Γ(t.G.left, W i) := fun i =>
    GlobalTheory.HeatV.cst π _ (hW i) (GlobalTheory.HeatV.resV R c a) *
                 GlobalTheory.HeatV.opV π _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) -
      2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst π _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) *
        rsT (σ.f fun _ => j i) (W i)
  have hF : ∀ i i', rsT (F i) (W i ⊓ W i') =
      rsT (M.g (fun _ => j i) (fun _ => j i')).val (W i ⊓ W i') * rsT (F i') (W i ⊓ W i') := by
    intro i i'
    have hII : W i ⊓ W i' ≤ M.U (fun _ => j i) ⊓ M.U (fun _ => j i') := inf_le_inf (hWc i) (hWc i')
    have hs := GlobalTheory.Heat.Glue.sec_rel (𝟙 t.G.left) k σ (fun _ => j i) (fun _ => j i') hII
    have hgl := hglue k i i' (W i ⊓ W i') le_rfl (rsT (σ.f fun _ => j i') (W i ⊓ W i'))
    rw [GlobalTheory.Heat.Glue.linComb_g (𝟙 t.G.left) k _ _ hII]
    simp only [F, rsT_sub, rsT_mul, rsT_cst _ _ _ inf_le_left, rsT_cst _ _ _ inf_le_right,
      rsT_natCast inf_le_left, rsT_natCast inf_le_right, rsT_two inf_le_left, rsT_two inf_le_right]
    rw [opV_rsT π _ dd' hdd' Θ₁ u (d i) (hd i) (pf i) (pf' i) k le_rfl (hW i) inf_le_left,
      opV_rsT π _ dd' hdd' Θ₁ u (d i') (hd i') (pf i') (pf' i') k le_rfl (hW i') inf_le_right,
      rsT_rsT (hWc i) inf_le_left, rsT_rsT (hWc i') inf_le_right, hs, hgl]
    ring
  haveI := t.semi.quasiCompact
  haveI := t.semi.separated
  haveI : CompactSpace t.G.left := QuasiCompact.compactSpace_of_compactSpace t.G.hom
  haveI : QuasiSeparatedSpace t.G.left := quasiSeparatedSpace_of_quasiSeparated t.G.hom
  obtain ⟨tt, htt, htF⟩ := GlobalTheory.T.exists_glued_lineBundleSection_cover M hM (t.G.left.basicOpen f) W (fun i _ => j i) F (by rw [hcov, hb]) hWc hF
  obtain ⟨N, s, hs⟩ := GlobalTheory.T.exists_lineBundleSection_extend_basicOpen t.G.left M hM f tt htt
  refine ⟨c ^ N, s, pow_ne_zero N hc, fun i => ?_⟩
  have hWi : W i ≤ M.U (fun _ => j i) ⊓ t.G.left.basicOpen f := le_inf (hWc i) (hb ▸ hW i)
  refine (rsT_rsT inf_le_left hWi _).symm.trans ?_
  refine (congrArg (fun x => rsT x (W i)) (hs (fun _ => j i))).trans ?_
  rw [rsT_mul, GlobalTheory.Heat.Glue.rsT_pow' hWi, rsT_rsT le_top hWi,
    htF i, map_pow, map_pow, cst_resV]

end GlobalTheory.HeatVExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodWeightAntitoneGapStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_weight_antitone_gap : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (wtOf _ la 0) ∧ ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ la 0) := by
  first | exact @GlobalTheory.CovTop.GoodDom.goodAt_dom | exact GlobalTheory.CovTop.GoodDom.goodAt_dom | (intros; apply GlobalTheory.CovTop.GoodDom.goodAt_dom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGoodReduction_of_many_rational_torsion_points : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], GlobalTheory.SS.SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} = m ^ (2 * g)}.Infinite → HasGoodReduction R K A := by
  first | exact @GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion | exact GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion | (intros; apply GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjectiveStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_isogeny_omega_and_dual_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → Function.Surjective (omegaMap G H q) → Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  first | exact @GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | exact GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | (intros; apply GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective <;> assumption)
end

