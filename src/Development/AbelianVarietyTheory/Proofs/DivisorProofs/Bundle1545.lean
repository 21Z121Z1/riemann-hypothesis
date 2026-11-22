import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueFactor
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.GenericCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_residue_factor {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (ξ : X) (q : Sp k) (h : x q = ξ) :
    ∃ ι : X.residueField ξ →+* k, spMap ι ≫ X.fromSpecResidueField ξ = x := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  have hp : p = ξ := by
    rw [← h, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  subst hp
  exact ⟨φ.hom, rfl⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in

theorem isCombAtG_map {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (a i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · have h := map_list_prod (Formalism.L2.Pj.preHom (G := t.G) δ) (List.ofFn u)
    rw [List.map_ofFn] at h
    exact congrArg (fun g => g.left) h.symm

attribute [local instance] Over.cartesianMonoidalCategory in

theorem exists_comb {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) (a : Fin m → S) :
    ∃ w, IsCombAtG t x v a w ∧ IsTanAtG t x w :=
  ⟨_, (isCombAtG_iff t x (fun j => ovT (hv j)) a _).2 rfl,
    isTanAtG_of _ (combT_tan _ _ (fun j => smT_zero_ovT (hv j)) a)⟩

attribute [local instance] Over.cartesianMonoidalCategory in

theorem comb_unique {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) (h' : IsCombAtG t x v a w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hv j)) a _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hv j)) a _).1 h')

theorem exists_frac_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (φ : A →+* B)
    (h : Function.Injective φ) : ∃ φF : FractionRing A →+* FractionRing B,
      φF.comp (algebraMap A (FractionRing A)) = (algebraMap B (FractionRing B)).comp φ := by
  have hi : Function.Injective ((algebraMap B (FractionRing B)).comp φ) := (IsFractionRing.injective B _).comp h
  refine ⟨IsFractionRing.lift (K := FractionRing A) hi, RingHom.ext fun r => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_centre (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c β) (hB : PointsOfFlagModel.BaseAt la β) (Z : Comp Xo c) :
    ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e) (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c)
      (ξ : Y.X) (ι : Y.X.residueField ξ →+* ResidueField T.V),
      z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt ∧ z ≫ pullback.snd _ _ = spMap io ∧
      (∀ q, z q ∈ (Z : Set (Xo.XF c))) ∧ spMap ι ≫ Y.X.fromSpecResidueField ξ = spMap (residue T.V) ≫ yt ∧
      TrdegGe (Y.X.residueField ξ) Dw.dim ∧
      ∃ s : ℕ → ResidueField T.V, letI := ι.toAlgebra; AlgebraicIndependent (Y.X.residueField ξ) s := by
  obtain ⟨_, _, hfr, hover⟩ := GlobalTheory.T.ramification_bound_over_dvr c.F la O β hB.1 hB.2
  letI : Algebra O c.F := β.toAlgebra
  have : CharZero O := RingHom.charZero β
  have : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  let g : Sp (kap Z) ⟶ Xo.XF c := genSp Z
  have : IsPreimmersion g := by unfold g genSp; infer_instance
  have hg : g ≫ pullback.snd _ _ = spMap (algebraMap c.F (kap Z)) := (Spec.map_preimage _).symm
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  let a : O →+* kap Z := (algebraMap c.F (kap Z)).comp β
  have htr : letI := a.toAlgebra; ((Dw.dim : ℕ) : Cardinal) ≤ Algebra.trdeg O (kap Z) := by
    letI := a.toAlgebra
    have : IsScalarTower O c.F (kap Z) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    rw [← trdeg_add_eq O c.F (A := kap Z), kapTrdeg_pf Xo c Z]
    exact le_add_self
  have hga : (g ≫ Y.j) ≫ Y.s = spMap a := by
    rw [Category.assoc, hjs, ← Category.assoc, hg, spMap_comp' β]
  obtain ⟨T₀, yt₀, ψ, b, hb, hs, hgen, hd⟩ := GlobalTheory.T.complete_dvr_point_lifting O Y.X Y.s (kap Z) (g ≫ Y.j) a
    ((algebraMap c.F (kap Z)).injective.comp hB.1) hga Dw.dim htr
  obtain ⟨T, φ, hφ, hinj, s, hs'⟩ := GlobalTheory.T.complete_dvr_residue_transcendence T₀
  obtain ⟨φF, hφF⟩ := exists_frac_map φ hinj
  have hba : (algebraMap T₀.V T₀.Fr).comp b = ψ.comp a := by
    apply spMap_inj
    rw [← spMap_comp' b, ← hs, ← Category.assoc, hgen, Category.assoc, hga, spMap_comp' a]
  obtain ⟨e, he⟩ := hover T ((φF.comp ψ).comp (algebraMap c.F (kap Z))) (φ.comp b) inferInstance (by
    rw [← RingHom.comp_assoc, ← hφF, RingHom.comp_assoc, hba]; rfl)
  obtain ⟨ι₀, hι₀⟩ := exists_residue_factor (spMap (residue T₀.V) ≫ yt₀) (yt₀ (closedPoint T₀.V))
    (closedPoint (ResidueField T₀.V))
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg yt₀ (comap_closedPoint (residue T₀.V))))
  refine ⟨T, _, e, he, spMap φ ≫ yt₀, spMap (φF.comp ψ) ≫ g, _, (ResidueField.map φ).comp ι₀, ?_, ?_, fun q => ?_, ?_,
    hd, s, ?_⟩
  · rw [← spMap_comp', Category.assoc, Category.assoc, ← hgen, ← Category.assoc, ← Category.assoc, spMap_comp',
      spMap_comp', hφF]
  · rw [Category.assoc, hg, spMap_comp']
  · have h1 : (spMap (φF.comp ψ) ≫ g) q = genPt Z :=
      (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
    rw [h1]
    exact ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)).mem
  · rw [← spMap_comp', Category.assoc, hι₀, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp',
      ResidueField.map_comp_residue]
  · letI := ι₀.toAlgebra
    letI := (ResidueField.map φ).toAlgebra
    letI := ((ResidueField.map φ).comp ι₀).toAlgebra
    have : IsScalarTower (Y.X.residueField (yt₀ (closedPoint T₀.V))) (ResidueField T₀.V) (ResidueField T.V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact AlgebraicIndependent.restrictScalars ι₀.injective hs'

end GlobalTheory.GenericCentre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRiemannDataPull
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

noncomputable section

namespace GlobalTheory.HodgePull

open GlobalTheory.Points GlobalTheory.HermFrame

theorem sqMap_comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''}
    {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : A'.left ⟶ A.left} {φ' : A''.left ⟶ A'.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) (w' : φ' ≫ A'.hom = A''.hom ≫ g)
    (w'' : (φ' ≫ φ) ≫ A.hom = A''.hom ≫ (g ≫ f)) :
    sqMap w' ≫ sqMap w = sqMap w'' := by
  unfold sqMap
  exact Limits.pullback.map_comp ..

theorem exists_dChart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (P : PPAS X) (y : CxPts p σ) :
    ∃ (c : Chart (LieVB.omega P.A) P.g) (W : P.A.left.Opens)
      (hW : c.U ≤ LieVB.unitSec P.A ⁻¹ᵁ W) (f : Fin P.g → Γ(P.A.left, W)),
      y ∈ ptsIn p σ c.U ∧ ∀ a, c.e a = LieVB.dUnit P.A hW (f a) := by
  obtain ⟨U, W, hx, hle, c⟩ := Conormal.exists_isChart (LieVB.sec_hom (MonObj.one (X := P.A)))
    (mem_ptsIn.1 (P.isVB_omega.mem_pick y))
  choose f hf using fun a => c.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A)))
    (GlobalTheory.Twist.resM (LieVB.omega P.A) hle ((P.isVB_omega.pick y).e a))
  exact ⟨⟨U, fun a => GlobalTheory.Twist.resM _ hle ((P.isVB_omega.pick y).e a),
    (P.isVB_omega.pick y).isFrame.res hle⟩, W, c.le, f, mem_ptsIn.2 hx, fun a => (hf a).symm⟩

theorem exists_riemannData_pull {X Y : Scheme.{0}} {π : Y ⟶ X} {P : PPAS X} {P' : PPAS Y}
    {φ : P'.A.left ⟶ P.A.left} (hφ : IsGrpPullback P'.A P.A π φ) (hg : P'.g = P.g)
    (hc : P'.c = CechPic.pull (sqMap hφ.1.w) P.c) {z : Sp ℂ ⟶ Y} (d' : P'.RiemannData z) (t : ℂ) :
    ∃ d : P.RiemannData (z ≫ π), ∀ (W : P.A.left.Opens) (f f' : Γ(P.A.left, W)),
      form (dualGram (t • d.H)) (d.cov W f) (d.cov W f') =
        form (dualGram (t • d'.H)) (d'.cov (φ ⁻¹ᵁ W) (φ.app W f))
          (d'.cov (φ ⁻¹ᵁ W) (φ.app W f')) := by
  obtain ⟨A', isAb', g', sd', c', pol'⟩ := P'
  change g' = P.g at hg
  subst hg
  have hp := d'.isPull.comp hφ
  refine ⟨⟨d'.B, d'.φ ≫ φ, hp, d'.L, d'.isLB, ?_, d'.u, d'.H, d'.χ, d'.isAH⟩, fun W f f' => ?_⟩
  · rw [← sqMap_comp hφ.1.w d'.isPull.1.w hp.1.w, CechPic.pull_comp]
    change (CechPic.pull (sqMap d'.isPull.1.w)) (CechPic.pull (sqMap hφ.1.w) P.c) = _
    rw [← hc]
    exact d'.pol
  · have e (f : Γ(P.A.left, W)) (w : Fin P.g → ℂ) :
        valR ((d'.u.ex w).left ≫ d'.φ ≫ φ) W f =
          valR ((d'.u.ex w).left ≫ d'.φ) (φ ⁻¹ᵁ W) (φ.app W f) := by
      rw [← Category.assoc]
      exact valR_comp _ _ _ _
    exact congrArg₂ (form (dualGram (t • d'.H)))
      (funext fun a => congrArg (fun F => fderiv ℂ F 0 (Pi.single a 1)) (funext (e f)))
      (funext fun a => congrArg (fun F => fderiv ℂ F 0 (Pi.single a 1)) (funext (e f')))

theorem form_eq_of_frames {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {σ : k →+* ℂ} {π : Y ⟶ X} (hπ : π ≫ p = q) {E : X.Modules} {E' : Y.Modules} {r r' : ℕ}
    (hr : r' = r) (h : Met p σ E r) (h' : Met q σ E' r')
    (α : (Scheme.Modules.pullback π).obj E ⟶ E') [IsIso α]
    (H : ∀ z : CxPts q σ, ∃ c : Chart E r, PtsOver.map π hπ _ z ∈ ptsIn p σ c.U ∧ ∀ a b,
      h'.form (α.app _ (QCoh.pullbackSections π E (le_refl (π ⁻¹ᵁ c.U)) (c.e a)))
        (α.app _ (QCoh.pullbackSections π E (le_refl (π ⁻¹ᵁ c.U)) (c.e b))) z =
        h.form (c.e a) (c.e b) (PtsOver.map π hπ _ z))
    {U : Y.Opens} (s s' : Γ((Scheme.Modules.pullback π).obj E, U)) {z : CxPts q σ}
    (hz : z ∈ ptsIn q σ U) :
    h'.form (α.app U s) (α.app U s') z = (h.pull π hπ).form s s' z := by
  subst hr
  have key : h' = (h.pull π hπ).map (asIso α) := Met.ext_of_exists fun z => by
    obtain ⟨c, hy, e⟩ := H z
    have hz' : z ∈ ptsIn q σ ((c.pull h.isVB π).map (asIso α)).U := hy
    refine ⟨_, hz', Matrix.ext fun a b => ?_⟩
    have e₁ := ((h.pull π hπ).map_G (asIso α) (c.pull h.isVB π) hz').trans (h.pull_G π hπ c hy)
    exact ((h'.form_frame _ hz' a b).symm.trans (e a b)).trans
      ((h.form_frame c hy a b).trans (congrFun₂ e₁ a b).symm)
  rw [key]
  exact Met.form_map _ (asIso α) s s' hz

theorem form_omegaBase : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Y : Scheme.{0}) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (P : PPAS X) (P' : PPAS Y) (φ : P'.A.left ⟶ P.A.left) (hφ : IsGrpPullback P'.A P.A π φ), P'.g = P.g → P'.IsPull P π φ → ∀ (t : ℝ) (h : VMetric p (LieVB.omega P.A) P.g) (h' : VMetric q (LieVB.omega P'.A) P'.g), P.IsDualRiemann t h → P'.IsDualRiemann t h' → ∀ (σ : k →+* ℂ) (U : Y.Opens) (s s' : Γ((Scheme.Modules.pullback π).obj (LieVB.omega P.A), U)), ∀ z ∈ ptsIn q σ U, (h'.met σ).form ((LieVB.omegaBase hφ).app U s) ((LieVB.omegaBase hφ).app U s') z = ((h.pull π hπ).met σ).form s s' z := by
  intro k _ X p Y q π hπ P P' φ hφ hg hpull t h h' H H' σ U s s' z hz
  obtain ⟨_, hc⟩ := hpull
  refine form_eq_of_frames hπ hg (h.met σ) (h'.met σ) (LieVB.omegaBase hφ) (fun z => ?_) s s' hz
  obtain ⟨c, W, hW, f, hy, hf⟩ := exists_dChart (σ := σ) P (PtsOver.map π hπ _ z)
  refine ⟨c, hy, fun a b => ?_⟩
  have hz' : z ∈ ptsIn q σ (π ⁻¹ᵁ c.U) := hy
  have hW' := Conormal.le_of_sq (LieVB.unitSec_comp hφ) hW (le_refl (π ⁻¹ᵁ c.U))
  obtain ⟨d'⟩ := (H' σ z).1
  obtain ⟨d, hd⟩ := exists_riemannData_pull hφ hg hc d' (t : ℂ)
  rw [hf a, hf b, LieVB.omegaBase_dUnit hφ hW le_rfl hW' le_rfl,
    LieVB.omegaBase_dUnit hφ hW le_rfl hW' le_rfl, Scheme.Hom.appLE_eq_app]
  exact ((H' σ z).2 d' _ _ hW' _ _ hz').trans
    ((hd W _ _).symm.trans ((H σ (PtsOver.map π hπ _ z)).2 d c.U W hW (f a) (f b) hy).symm)

end GlobalTheory.HodgePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SchRing

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem subsingleton_primeSpectrum_trivSqZeroExt (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
    Subsingleton (PrimeSpectrum (TrivSqZeroExt k M)) := by
  have key : ∀ (P : PrimeSpectrum (TrivSqZeroExt k M)) (a : TrivSqZeroExt k M), a ∈ P.asIdeal ↔ a.fst = 0 := by
    intro P a
    constructor
    · intro ha
      by_contra h
      have hu : IsUnit a := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    · intro h
      have ha : a = TrivSqZeroExt.inr a.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      apply P.isPrime.mem_of_pow_mem 2
      rw [ha, pow_two, TrivSqZeroExt.inr_mul_inr]
      exact P.asIdeal.zero_mem
  exact ⟨fun P Q => PrimeSpectrum.ext (Ideal.ext fun a => (key P a).trans (key Q a).symm)⟩

theorem range_subset_of_fst {X : Scheme.{0}} (k : Type) [Field k] (M : Type) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
    (x : Sp k ⟶ X) (u : Sp (TrivSqZeroExt k M) ⟶ X)
    (h : spMap (TrivSqZeroExt.fstHom k k M).toRingHom ≫ u = x) : Set.range u.base ⊆ Set.range x.base := by
  rintro _ ⟨y, rfl⟩
  haveI := subsingleton_primeSpectrum_trivSqZeroExt k M
  let z : PrimeSpectrum k := ⟨⊥, Ideal.bot_prime⟩
  refine ⟨z, ?_⟩
  have hy : (spMap (TrivSqZeroExt.fstHom k k M).toRingHom).base z = y := Subsingleton.elim (α := PrimeSpectrum (TrivSqZeroExt k M)) _ _
  rw [← h, ← hy]
  rfl

theorem exists_ringHom_of_range {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (D : Type) [CommRing D]
    (g : Sp D ⟶ X) (hg : Set.range g.base ⊆ (V : Set X)) : ∃ r : Γ(X, V) →+* D, g = spMap r ≫ hV.fromSpec := by
  have h' : Set.range g ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hg
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom, ?_⟩
  have e1 : spMap (Spec.preimage (IsOpenImmersion.lift hV.fromSpec g h')).hom = IsOpenImmersion.lift hV.fromSpec g h' := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [e1, IsOpenImmersion.lift_fac]

theorem spMap_cancel {R D : Type} [CommRing R] [CommRing D] {Y : Scheme.{0}} (G : Sp R ⟶ Y) [Mono G]
    {a b : R →+* D} (h : spMap a ≫ G = spMap b ≫ G) : a = b :=
  spMap_inj (cancel_mono G |>.mp h)

end GlobalTheory.SchRing

namespace GlobalTheory.SchRing

theorem deformation_on_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  intro B _ X s U V hU hV e d k _ x hx hyp
  obtain ⟨u, hux, hus, huniq⟩ := hyp
  obtain ⟨φ, hφ⟩ := exists_ringHom_of_range hV k x hx
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_range hV _ u ((range_subset_of_fst k _ x u hux).trans hx)
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have hs : ∀ (D : Type) [CommRing D] (r : Γ(X, V) →+* D),
      spMap r ≫ hV.fromSpec ≫ s = spMap (r.comp (s.appLE U V e).hom) ≫ hU.fromSpec := by
    intro D _ r
    rw [← key, spMap_comp']
    rfl
  have hbase : ∀ (D : Type) [CommRing D] (alg : k →+* D) (r : Γ(X, V) →+* D),
      (spMap r ≫ hV.fromSpec) ≫ s = spMap alg ≫ x ≫ s ↔
        r.comp (s.appLE U V e).hom = alg.comp (φ.comp (s.appLE U V e).hom) := by
    intro D _ alg r
    rw [hφ]
    simp only [Category.assoc]
    rw [hs, ← Category.assoc (spMap alg) (spMap φ), ← spMap_comp', hs]
    constructor
    · intro h; exact spMap_inj ((cancel_mono hU.fromSpec).mp h)
    · intro h; rw [h]
  have hfst : ∀ (D : Type) [CommRing D] (f : D →+* k) (r : Γ(X, V) →+* D),
      spMap f ≫ spMap r ≫ hV.fromSpec = x ↔ f.comp r = φ := by
    intro D _ f r
    rw [hφ, ← Category.assoc, ← spMap_comp']
    constructor
    · intro h; exact spMap_cancel hV.fromSpec h
    · intro h; rw [h]
  refine ⟨φ, ψ, ?_, ?_, ?_⟩
  · rw [hψ] at hux; exact (hfst _ _ _).mp hux
  · rw [hψ] at hus; exact (hbase _ _ _).mp hus
  · intro v hv1 hv2
    have h1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (spMap v ≫ hV.fromSpec) = x := (hfst _ _ _).mpr hv1
    have h2 := (hbase _ _ _).mpr hv2
    obtain ⟨c, hc, hcu⟩ := huniq _ h1 h2
    refine ⟨c, ?_, ?_⟩
    · rw [hψ, ← Category.assoc, ← spMap_comp'] at hc
      exact spMap_cancel hV.fromSpec hc
    · intro c' hc'
      apply hcu
      rw [hψ, ← Category.assoc, ← spMap_comp', ← hc']

end GlobalTheory.SchRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.VMetric

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E E' : X.Modules} {r : ℕ}
  {h : VMetric p E r} {h' : VMetric p E' r} {φ : E ≅ E'}

theorem stepMet_ofIso (hφ : h.IsIsometry h' φ) (fl : Vert.Flag E r) (i : Fin r) :
    h'.stepMet (fl.ofIso φ) i = h.stepMet fl i := by
  refine VMetric.ext (funext fun σ => Met.ext_form fun V s t y hy => ?_)
  exact (Met.form_restrict (h'.met σ) ((fl.ofIso φ).isSubbundle i.succ) ((fl.ofIso φ).isVB i.succ)
    s t hy).trans ((hφ σ V _ _ y hy).trans
      (Met.form_restrict (h.met σ) (fl.isSubbundle i.succ) (fl.isVB i.succ) s t hy).symm)

theorem flagBc_ofIso (hφ : h.IsIsometry h' φ) (fl : Vert.Flag E r) :
    h'.flagBc (fl.ofIso φ) = h.flagBc fl :=
  Finset.sum_congr rfl fun i _ => congrArg (fun g : VMetric p (stepSeq fl i).X₂ (i + 1) =>
    g.bcInt (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)) (stepMet_ofIso hφ fl i)

theorem flagBcFinite_ofIso (hφ : h.IsIsometry h' φ) (fl : Vert.Flag E r) :
    h'.FlagBcFinite (fl.ofIso φ) ↔ h.FlagBcFinite fl :=
  forall_congr' fun i => iff_of_eq (congrArg (fun g : VMetric p (stepSeq fl i).X₂ (i + 1) =>
    g.BcFinite (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)) (stepMet_ofIso hφ fl i))

theorem grLB_ofIso (hφ : h.IsIsometry h' φ) (H : h.IsCInf) (H' : h'.IsCInf) (fl : Vert.Flag E r)
    (i : Fin r) : grLB (fl.ofIso φ) i H' = grLB fl i H := by
  have e : h'.grMet (fl.ofIso φ) i = h.grMet fl i :=
    congrArg (fun g : VMetric p (stepSeq fl i).X₂ (i + 1) =>
      g.quot (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)) (stepMet_ofIso hφ fl i)
  change det (H'.grMet (fl.ofIso φ) i) = det (H.grMet fl i)
  generalize H'.grMet (fl.ofIso φ) i = A
  generalize H.grMet fl i = B
  revert A B
  rw [e]
  intro A B
  rfl

end GlobalTheory.VMetric

theorem GlobalTheory.VMetric.isFlagCh2_ofIso : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r)
    (φ : E ≅ E') (H : h.IsCInf) (H' : h'.IsCInf) (fl : Vert.Flag E r) (a : ℝ),
    h.IsIsometry h' φ → (VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 H' (fl.ofIso φ) a) := by
  intro k _ X p _ E E' r h h' φ H H' fl a hφ
  unfold IsFlagCh2
  rw [flagBcFinite_ofIso hφ, flagBc_ofIso hφ]
  simp only [grLB_ofIso hφ H H']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagExtensionOfSubbundle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.Vert.Flag

theorem isSubbundle_ι_comp {X : Scheme.{0}} {E K : X.Modules} {i : K ⟶ E} {r : ℕ}
    (hi : IsSubbundle i) (fl : Vert.Flag K r) (j : Fin (r + 1)) : IsSubbundle (fl.ι j ≫ i) := by
  have := hi.mono
  obtain ⟨s, hs⟩ := hi.isVB_cokernel
  obtain ⟨h, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp (fl.ι j) i) (fl.isVB_cokernel j) hs
  exact ⟨inferInstance, _, h⟩

theorem nonempty_extend : ∀ (X : Scheme.{0}) (E K : X.Modules) (i : K ⟶ E) (r : ℕ),
    IsSubbundle i → IsVB E (r + 1) → Vert.Flag K r → Nonempty (Vert.Flag E (r + 1)) := by
  intro X E K i r hi hE fl

  let G : Fin (r + 2) → Σ A : X.Modules, (A ⟶ E) :=
    fun j => Fin.lastCases (motive := fun _ => Σ A : X.Modules, (A ⟶ E)) ⟨E, 𝟙 E⟩
      (fun k => ⟨fl.F k, fl.ι k ≫ i⟩) j
  have hlast : G (Fin.last (r + 1)) = ⟨E, 𝟙 E⟩ := Fin.lastCases_last ..
  have hcast (k : Fin (r + 1)) : G k.castSucc = ⟨fl.F k, fl.ι k ≫ i⟩ :=
    Fin.lastCases_castSucc ..
  have hsub (j : Fin (r + 2)) : IsSubbundle (G j).2 := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact VB.isSubbundle_of_isIso _
    | cast k => rw [hcast]; exact isSubbundle_ι_comp hi fl k
  have hvb (j : Fin (r + 2)) : IsVB (G j).1 j := by
    induction j using Fin.lastCases with
    | last => rw [hlast]; exact hE
    | cast k => rw [hcast]; exact fl.isVB k
  have hstep (k : Fin (r + 1)) :
      ∃ f : (G k.castSucc).1 ⟶ (G k.succ).1, f ≫ (G k.succ).2 = (G k.castSucc).2 := by
    induction k using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, hlast, hcast]
      exact ⟨fl.ι _ ≫ i, Category.comp_id _⟩
    | cast k =>
      rw [← Fin.castSucc_succ, hcast, hcast]
      exact ⟨fl.step k, fl.step_ι_assoc k i⟩
  choose step step_ι using hstep
  have hiso : IsIso (G (Fin.last (r + 1))).2 := by
    rw [hlast]; exact IsIso.id E
  exact ⟨{ F := fun j => (G j).1
           ι := fun j => (G j).2
           isSubbundle := hsub
           isVB := hvb
           step := step
           step_ι := step_ι
           isIso_last := hiso }⟩

end GlobalTheory.Vert.Flag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
section
noncomputable section

namespace GlobalTheory.LevModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def Moved (X₂ X : Data E r) (δ : GL (Fin r) E) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) : Prop :=
  ∀ (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ),
    mat x' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩

open Classical in

def genScal {S : Type} [CommRing S] (t : Sˣ) : Ix Dw → Sˣ := fun i => if i = none then t else 1

def Over (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) (U : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r)
    (U₂ : Unf d.Xo₂ d.c₂ σ₂ r) (k₂ : U₂.Comp) (k : U.Comp) (δ : GL (Fin r) E) : Prop :=
  ∀ (x : Frame (U₂.X k₂).Ψ r) (hx : x ∈ (U₂.X k₂).dom) (x' : Frame (U.X k).Ψ r), Moved (U₂.X k₂) (U.X k) δ x x' →
    ∃ hx' : x' ∈ (U.X k).dom, ∃ t : ℂˣ, ((∀ τ i, ‖dmin (U₂.X k₂).Gm x τ i‖ = 1) → ‖(t : ℂ)‖ = 1) ∧
      letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
      ∃ y : FrPt Xo c (CAt σ₂),
        FrBor (S := CAt σ₂) (genScal (Dw := Dw) (S := CAt σ₂) t) (U.un k ⟨x', hx'⟩) y ∧
        FrOver d (U₂.un k₂ ⟨x, hx⟩) y

end GlobalTheory.LevModel
end
end

