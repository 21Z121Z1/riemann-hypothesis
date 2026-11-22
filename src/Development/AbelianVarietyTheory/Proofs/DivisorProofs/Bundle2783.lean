import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem intElem_pow_mul_of_away {R S Rt St : Type} [CommRing R] [CommRing S] [CommRing Rt] [CommRing St]
    (f : R →+* S) (t : R) [Algebra R Rt] [Algebra S St] [IsLocalization.Away t Rt]
    [IsLocalization.Away (f t) St] (ft : Rt →+* St)
    (hc : ft.comp (algebraMap R Rt) = (algebraMap S St).comp f) (x : S)
    (hx : ft.IsIntegralElem (algebraMap S St x)) : ∃ n : ℕ, f.IsIntegralElem (f t ^ n * x) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra Rt St := ft.toAlgebra
  letI : Algebra R St := ((algebraMap S St).comp f).toAlgebra
  haveI : IsScalarTower R Rt St := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : IsScalarTower R S St := IsScalarTower.of_algebraMap_eq' rfl
  have hx' : IsIntegral Rt (algebraMap S St x) := hx
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := hx'.exists_multiple_integral_of_isLocalization (Submonoid.powers t)
  have e : (⟨t ^ a, a, rfl⟩ : Submonoid.powers t) • algebraMap S St x =
      algebraMap S St (f t ^ a * x) := by
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S St, ← map_mul]
    simp [RingHom.algebraMap_toAlgebra]
  rw [e] at ha
  have hr : IsIntegral R (f t) := f.isIntegralElem_map
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (R := R) (Sₘ := St) hr ha
  exact ⟨n + a, by rw [pow_add, _root_.mul_assoc]; exact hn⟩

theorem isIntegralElem_of_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) {y : C} (h : (g.comp f).IsIntegralElem y) : g.IsIntegralElem y := by
  obtain ⟨p, hp, h⟩ := h
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact h⟩

theorem res_res_sections {Y : Scheme.{0}} {U V V' : Y.Opens} (h1 : V ≤ U) (h2 : V' ≤ V) (z : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom z) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chartVal_isIntegral_of_intAt : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k)
    (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) →
    (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  intro X Y L α k s j W hW hWa hYa hint
  letI : Algebra Γ(X, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  set F := chartVal L α s j W hW with hF
  have loc : ∀ x ∈ W, ∃ d : Γ(X, W), x ∈ X.basicOpen d ∧
      ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F) := by
    intro x hx
    obtain ⟨j', W', hW', hxW', hW'a, hint'⟩ := hint x hx
    obtain ⟨d, hdle, hxd⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨x, ⟨hx, hxW'⟩⟩ hx
    refine ⟨d, hxd, ?_⟩
    set r : Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom d with hr
    have hED : Y.basicOpen r ≤ α ⁻¹ᵁ X.basicOpen d := (Scheme.preimage_basicOpen α d).ge
    haveI := hWa.isLocalization_basicOpen d
    haveI := hYa.isLocalization_basicOpen r
    have hDW : X.basicOpen d ≤ W := X.basicOpen_le d
    have hDW' : X.basicOpen d ≤ W' := hdle.trans inf_le_right
    have hEW : Y.basicOpen r ≤ α ⁻¹ᵁ W := Y.basicOpen_le r
    have hEW' : Y.basicOpen r ≤ α ⁻¹ᵁ W' := hED.trans (fun y hy => hDW' hy)
    have hDjj : X.basicOpen d ≤ L.U j ⊓ L.U j' := le_inf (hDW.trans hW) (hDW'.trans hW')
    let LC := LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))
    have hEJ : Y.basicOpen r ≤ LC.U (fun _ => j) ⊓ LC.U (fun _ => j') :=
      le_inf (hEW.trans (locInt_le_chart L α j W hW)) (hEW'.trans (locInt_le_chart L α j' W' hW'))
    refine intElem_pow_mul_of_away (α.app W).hom d (Rt := Γ(X, X.basicOpen d))
      (St := Γ(Y, Y.basicOpen r)) (α.appLE _ _ hED).hom ?_ F ?_
    · show (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW).op).hom =
        (Y.presheaf.map (homOfLE hEW).op).hom.comp (α.app W).hom
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
    · have hc0 := congrArg (Y.presheaf.map (homOfLE hEJ).op).hom (s.compat (fun _ => j) (fun _ => j'))
      rw [map_mul] at hc0
      show (α.appLE _ _ hED).hom.IsIntegralElem ((Y.presheaf.map (homOfLE hEW).op).hom F)
      have eF : (Y.presheaf.map (homOfLE hEW).op).hom F = (Y.presheaf.map (homOfLE hEJ).op).hom
          ((Y.presheaf.map (homOfLE (inf_le_left : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ LC.U (fun _ => j))).op).hom
            (s.f (fun _ => j))) :=
        (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
      rw [eF, hc0]
      refine RingHom.IsIntegralElem.mul _ ?_ ?_
      · have h'' : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ α ⁻¹ᵁ (L.U j ⊓ L.U j') :=
          le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
        have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
            Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) ^ k := by
          change ((∏ _i : Fin 1, (ReciprocityTheory.ChartRestriction.G.Semi.res h''
            (ReciprocityTheory.ChartRestriction.G.Semi.pullU α (L.U j ⊓ L.U j') (L.g j j'))) ^ (k : ℤ) :
              Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = _
          rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
          rfl
        have hz : (Y.presheaf.map (homOfLE hEJ).op).hom ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) =
            (α.appLE _ _ hED).hom ((X.presheaf.map (homOfLE hDjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) := by
          refine (res_res_sections _ _ _).trans ?_
          have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (L.g j j' : Γ(X, L.U j ⊓ L.U j')))
            (Scheme.Hom.map_appLE (f := α) hED (homOfLE hDjj).op)
          exact this.symm
        rw [hg, map_pow, hz, ← map_pow]
        exact RingHom.isIntegralElem_map _
      · have h1 := hint'.map (Y.presheaf.map (homOfLE hEW').op).hom
        have e1 : (Y.presheaf.map (homOfLE hEW').op).hom.comp (α.app W').hom =
            (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW').op).hom := by
          rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
        rw [e1] at h1
        have h2 := isIntegralElem_of_comp _ _ h1
        convert h2 using 1
        exact (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
  change F ∈ (integralClosure Γ(X, W) Γ(Y, α ⁻¹ᵁ W)).toSubmodule
  let S0 : Set Γ(X, W) := {d | ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F)}
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ S0 ?_ F ?_
  · rw [← hWa.iSup_basicOpen_eq_self_iff]
    apply le_antisymm
    · exact iSup_le fun d => X.basicOpen_le _
    · intro x hx
      obtain ⟨d, hxd, hd⟩ := loc x hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨d, hd⟩, hxd⟩
  · rintro ⟨d, n, hn⟩
    refine ⟨n, ?_⟩
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow]
    exact hn

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemRangeOfAgreeTraitExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem gs_eq_germ_top {Z X : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs f z U a = (Z.presheaf.germ ⊤ z trivial).hom ((f.appLE U ⊤ h).hom a) := by
  rw [gs_eq f z U (h trivial)]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z trivial _).symm

theorem specMap_appLE_top {R Ω : Type} [CommRing R] [CommRing Ω] (f : R →+* Ω) (V : (Sp R).Opens) (hV : ⊤ ≤ V)
    (h : ⊤ ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ V) (a : Γ(Sp R, V)) :
    ((Spec.map (CommRingCat.ofHom f)).appLE V ⊤ h).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (((Sp R).presheaf.map (homOfLE hV).op).hom a))) := by
  have e1 := Scheme.Hom.map_appLE (Spec.map (CommRingCat.ofHom f)) (U := ⊤) (U' := V) (V := ⊤) (fun _ _ => trivial) (homOfLE hV).op
  have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  rw [← e1]
  have e3 : (Spec.map (CommRingCat.ofHom f)).appLE ⊤ ⊤ (fun _ _ => trivial) = (Spec.map (CommRingCat.ofHom f)).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have e4 : ∀ x, ((Spec.map (CommRingCat.ofHom f)).appTop).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x)) := fun x => by
    have := congrArg (fun t => t.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← this, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [CommRingCat.hom_comp, RingHom.comp_apply, e3, e4]

theorem fromSpec_appLE_self {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem ΓSpecIso_hom_inv_apply (R : CommRingCat.{0}) (a : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom a) = a := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_specMap_comp {R Ω : Type} [CommRing R] [CommRing Ω] {X : Scheme.{0}} (f : R →+* Ω) (g : Sp R ⟶ X)
    (z : Sp Ω) (U : X.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs (Spec.map (CommRingCat.ofHom f) ≫ g) z U a = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((g.appLE U ⊤ hg).hom a)))) := by
  have h : ⊤ ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ (g ⁻¹ᵁ U) := fun x _ => hg trivial
  rw [← gs_pull (Spec.map (CommRingCat.ofHom f)) g z U (hg trivial) a, gs_eq_germ_top _ z _ h,
    specMap_appLE_top f _ hg h]
  rfl

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartVal_mem_range_of_agree : ∀ (X S Y : Scheme.{0}) (gX : X ⟶ S) (L : LB X), L.IsLB → ∀ (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) (hWa : IsAffineOpen W), IsAffineOpen (α ⁻¹ᵁ W) → ∀ (T : Type) [CommRing T] (lam : Γ(X, W) →+* T) (W' : Type) [CommRing W'] (io : T →+* W') (σ : SecK L (pullback.fst gX (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX)) k), Agree L σ s → ∀ (Ω : Type) [Field Ω] (ψ : Γ(Y, α ⁻¹ᵁ W) →+* Ω) (e : W' →+* Ω), (∀ c, ψ ((α.app W).hom c) = e (io (lam c))) → ∃ w : W', ψ (chartVal L α s j W hW) = e w := by
  intro X S Y gX L hL α k s j W hW hWa hαW T _ lam W' _ io σ hσ Ω _ ψ e hψ
  have hq : (Spec.map (CommRingCat.ofHom (io.comp lam)) ≫ hWa.fromSpec) ≫ gX =
      𝟙 (Sp W') ≫ (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.id_comp]
    simp only [spMap, Category.assoc]
  let q'' := pullback.lift (Spec.map (CommRingCat.ofHom (io.comp lam)) ≫ hWa.fromSpec) (𝟙 (Sp W')) hq
  let P : Sp Ω ⟶ _ := Spec.map (CommRingCat.ofHom e) ≫ q''
  let pY : Sp Ω ⟶ Y := Spec.map (CommRingCat.ofHom ψ) ≫ hαW.fromSpec
  have hring : α.appLE W (α ⁻¹ᵁ W) le_rfl ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (e.comp (io.comp lam)) := by
    ext c
    rw [Scheme.Hom.appLE_eq_app]
    exact hψ c
  have hA : P ≫ pullback.fst _ _ = pY ≫ α := by
    simp only [P, pY, q'', Category.assoc, pullback.lift_fst]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec α hWa hαW le_rfl, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      hring, ← CommRingCat.ofHom_comp]
  have hαmem : ∀ x, hαW.fromSpec x ∈ α ⁻¹ᵁ W := fun x => by
    show _ ∈ ((α ⁻¹ᵁ W : Y.Opens) : Set Y)
    rw [← hαW.range_fromSpec]
    exact ⟨x, rfl⟩
  have hWmem : ∀ x, hWa.fromSpec x ∈ W := fun x => by
    show _ ∈ ((W : X.Opens) : Set X)
    rw [← hWa.range_fromSpec]
    exact ⟨x, rfl⟩
  obtain ⟨z⟩ : Nonempty (Sp Ω) := ⟨IsLocalRing.closedPoint Ω⟩
  have hz : (pY ≫ α) z ∈ L.U j := hW (hαmem _)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := Unit) (fun _ => pY ≫ α) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hz)
  have hag := hσ (Sp Ω) P pY hA z J hJ
  have hl : sval s pY z J = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (ψ (chartVal L α s j W hW))) := by
    rw [sval_of s pY z J (fun _ => j) (fun _ => hJj ()),
      ← gs_res pY z (locInt_le_chart L α j W hW) (hαmem _) (s.f (fun _ => j))]
    rw [gs_specMap_comp ψ hαW.fromSpec z (α ⁻¹ᵁ W) hαW.fromSpec_preimage_self.ge]
    rw [fromSpec_appLE_self hαW]
    exact congrArg (fun t => ((Sp Ω).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (ψ t)))
      (ΓSpecIso_hom_inv_apply _ _)
  have hq'' : ⊤ ≤ q'' ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => pullback.fst _ _) (fun _ => j) := fun x _ =>
    Set.mem_iInter.2 fun _ => hW (by
      show (q'' ≫ pullback.fst _ _) x ∈ W
      rw [pullback.lift_fst]
      exact hWmem _)
  have hr : sval σ P z J = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (e ((Scheme.ΓSpecIso (CommRingCat.of W')).hom.hom
        ((q''.appLE _ ⊤ hq'').hom (σ.f (fun _ => j)))))) := by
    rw [sval_of σ P z J (fun _ => j) (fun _ => by rw [hA]; exact hJj ())]
    exact gs_specMap_comp e q'' z _ hq'' _
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W')).hom.hom ((q''.appLE _ ⊤ hq'').hom (σ.f (fun _ => j))),
    ((((Sp Ω).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).injective) ?_⟩
  simp only [RingHom.comp_apply]
  rw [← hl, ← hr, hag]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZeroStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPart_over_properClosed_eq_zero : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∀ (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ (σ : k →+* ℂ) {B : LB X} (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = 0 := by
  first | exact @GlobalTheory.ChernNull.chernPart_over_closed | exact GlobalTheory.ChernNull.chernPart_over_closed | (intros; apply GlobalTheory.ChernNull.chernPart_over_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCoveringStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ (n : ℕ), (∀ y ∈ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w)) → ∀ (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ U → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ)  ⁻¹' S) = n * φ.chernPart D ε S := by
  first | exact @GlobalTheory.CoverChern.chernPart_preimage_of_cover | exact GlobalTheory.CoverChern.chernPart_preimage_of_cover | (intros; apply GlobalTheory.CoverChern.chernPart_preimage_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointNormPsiCoordinateExpNegQuadratic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TestAtPt

theorem norm_psi_coord : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-l.q (ε α)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G _ _ gm D A U p _ y₀ ev u ε hBC l α s hs
  obtain ⟨ev₀, _, hD, bc, -, -, hx, hev, -⟩ := hBC
  have hs' : PsiCoord D.toPre (hD.xe (ε α)) s := by rw [hx]; exact hs
  obtain ⟨w, hw⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (ε α) s hs'
  obtain ⟨j, hj, hv⟩ := GlobalTheory.Poinc.valF_psi_of_psiCoord u.V u.D.toPre (ε α) _ hw
  have hq := l.q_eq (ε α) j hj
  rw [hv] at hq
  have unit_norm : ∀ v : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V))‖ = 1 := by
    intro v
    have h1 := (u.norm_le _).2 ⟨(v : u.V), rfl⟩
    have h2 := (u.norm_le _).2 ⟨((v⁻¹ : u.Vˣ) : u.V), rfl⟩
    have hm : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V)) *
        algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ((v⁻¹ : u.Vˣ) : u.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V))),
      norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ((v⁻¹ : u.Vˣ) : u.V)))]
  rw [map_mul, map_mul, norm_mul, unit_norm w, _root_.one_mul, hev] at hq
  exact hq

end GlobalTheory.Poinc.TestAtPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordinateIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem specMap_contravariant_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem Near.closed_product_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s s' : Sp Ω ⟶ M.S) (a b c c' : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (x' y' : Over.mk s' ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → s' ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → N.Pt s' a x'.left → N.Pt s' b y'.left → N.Pt s' c' (x' * y').left → c = c' := by
  intro R _ _ _ M G' _ E N fU l hl1 hl2 hsurj Ω _ κ s s' a b c c' x y x' y' hs hs' ha hb hc ha' hb' hc'
  obtain ⟨Ω₁, _, io₁, ca, cb, hca, hcb, hcc⟩ := GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s a b c x y hs ha hb hc
  obtain ⟨Ω₂, _, io₂, ca', cb', hca', hcb', hcc'⟩ :=
    GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s' a b c' x' y' hs' ha' hb' hc'
  obtain ⟨Ω₃, _, j₁, j₂, hj⟩ := GlobalTheory.T.exists_common_field_extension' Ω Ω₁ Ω₂ io₁ io₂
  have : Mono E.j := by haveI := E.imm; infer_instance

  let g₁ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₁.comp κ)) :=
    Over.homMk (spMap j₁) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom])
  let g₂ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₂.comp κ)) :=
    Over.homMk (spMap j₂) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom, hj])
  have hg₁ : g₁.left = spMap j₁ := rfl
  have hg₂ : g₂.left = spMap j₂ := rfl
  have e₁ : spMap j₁ ≫ spMap io₁ = spMap (j₁.comp io₁) := specMap_contravariant_comp_ringHom _ _
  have e₂ : spMap j₂ ≫ spMap io₂ = spMap (j₁.comp io₁) := by rw [specMap_contravariant_comp_ringHom, hj]
  have hA : g₁ ≫ ca = g₂ ≫ ca' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hca, hca']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hB : g₁ ≫ cb = g₂ ≫ cb' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcb, hcb']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hC : g₁ ≫ (ca * cb) = g₂ ≫ (ca' * cb') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, hA, hB]
  have hfU : spMap (j₁.comp io₁) ≫ c ≫ fU = spMap (j₁.comp io₁) ≫ c' ≫ fU := by
    have := congrArg (fun g => g.left ≫ E.j) hC
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcc, hcc'] at this
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂] at this
    exact this

  have hlies : ∀ (t : Sp Ω ⟶ M.S) (d : Sp Ω ⟶ N.U.left) (z : Sp Ω ⟶ G'.left), t ≫ M.π = spMap (κ.comp (residue R)) →
      N.Pt t d z → d ≫ N.U.hom = spMap (κ.comp (residue R)) := by
    rintro t d z ht ⟨x₀, h₁, h₂, -⟩
    rw [← h₁, Category.assoc, pullback.condition, ← Category.assoc, h₂, ht]
  have hco : ∀ d : Sp Ω ⟶ N.U.left, d ≫ N.U.hom = spMap (κ.comp (residue R)) →
      (spMap (j₁.comp io₁) ≫ d) ≫ N.U.hom = spMap (((j₁.comp io₁).comp κ).comp (residue R)) := by
    intro d hd
    rw [Category.assoc, hd, specMap_contravariant_comp_ringHom]
  have key := GlobalTheory.T.closedFibre_fieldPoints_injective_projective_map R M G' E N fU l hl1 hl2 hsurj Ω₃ ((j₁.comp io₁).comp κ) (spMap (j₁.comp io₁) ≫ c)
    (spMap (j₁.comp io₁) ≫ c') (hco c (hlies s c _ hs hc)) (hco c' (hlies s' c' _ hs' hc'))
    (by simpa only [Category.assoc] using hfU)
  exact GlobalTheory.T.spMap_field_ext_cancel Ω Ω₃ (j₁.comp io₁) N.U.left c c' key

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTermStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  first | exact @GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | exact GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | (intros; apply GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueCharStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_completion_positive_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  first | exact @GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar | exact GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar | (intros; apply GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImageStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_range_eq_fixedGroup_image : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (E : Emb π G'), (∀ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R → ∃ y : E.Y.left, E.f g = E.j y) ∧ (Surjective π → ∀ y : E.Y.left, ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g = E.j y) := by
  first | exact @GlobalTheory.Mum.Emb.range_closed | exact GlobalTheory.Mum.Emb.range_closed | (intros; apply GlobalTheory.Mum.Emb.range_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

noncomputable section

namespace GlobalTheory.MixDensNull

theorem part_over_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (D : ℕ), IsArithVar p D → ∀ (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ (σ : k →+* ℂ) (ρ : AlgChart p σ D → CxPts p σ → ℝ), part ρ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = 0 := by
  intro k _ X p _ D h Z hZ hgen σ ρ
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    have : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} =
        (ptsIn p σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl
  exact GlueCoverNull.glueMeas_null _ _ hA fun c => GlobalTheory.ChernNull.chart_null h hZ hgen σ c

end GlobalTheory.MixDensNull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeExistsMultipleIntegralPrimeToLStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_exists_multiple_integral_prime_to_l : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime → OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  first | exact @GlobalTheory.HilbFam.LatticeUp.exists_mul_integral | exact GlobalTheory.HilbFam.LatticeUp.exists_mul_integral | (intros; apply GlobalTheory.HilbFam.LatticeUp.exists_mul_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLinearHomCoordinateLatticeFgStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLinearHomCoordinateLattice_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  first | exact @GlobalTheory.FlatCM.HomLat.lat_fg | exact GlobalTheory.FlatCM.HomLat.lat_fg | (intros; apply GlobalTheory.FlatCM.HomLat.lat_fg <;> assumption)
end

