import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModuliOfSignatureEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3477

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegIdSameCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.DivIso

theorem exists_isPullDeg_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (Q' : DegPre V) [Module (𝓞 E) Q'.X] (oQ' : letI := H.starRing; Q'.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (e' : Q'.X ≃ₗ[𝓞 E] L.D.X), (∀ k, s k ≠ 0) → DivFrom L Q oQ iw s ε e → DivFrom L Q' oQ' iw s ε e' → ∃ hD : IsPullDeg (RingHom.id V) Q Q', (∀ y, e (hD.xe y) = e' y) ∧ (letI := H.starRing; ∀ x, oQ'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (oQ.onB.act x)) := by
  intro E _ _ _ H D' l c L V _ _ _ Q _ oQ Q' _ oQ' iw I _ s ε e e' hs ⟨g, p, hg, hx, ha⟩ ⟨g', p', hg', hx', ha'⟩
  letI := H.starRing
  obtain ⟨q, q₁, q₂⟩ := GlobalTheory.PullDegTop.main.2.2.2 (RingHom.id_comp iw) p p' (fun y => L.gen (l.M' • y))
  have he : ∀ y : Q'.X, e (q.xe y) = e' y := fun y => (hx _).symm.trans ((q₂ y).trans (hx' y))
  obtain ⟨r, r₁, r₂⟩ := GlobalTheory.PullDegResc.main.2.1 g g' q s hs (fun y k => (l.M' : ℤ) * ε k (e y) (H.w0 • e y)) hg
    (fun x => (hg' x).trans (Finset.prod_congr rfl fun k _ => by rw [← he x]; rfl))
  refine ⟨r, fun y => (congrArg e (r₂ y)).trans (he y), fun x => (GlobalTheory.PullDegTop.main.2.1 r _ _).2 ?_⟩
  have r' : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫
      p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) = p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) :=
    (congrArg (· ≫ _) r₁).trans q₁
  have pb : IsPullback (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) Q.P.A.hom L.D.P.A.hom (spMap iw) :=
    (pull_grp p).1
  have w : (r.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf (RingHom.id V))) ≫ Q.P.A.hom =
      Q'.P.A.hom ≫ spMap (RingHom.id V) := (pull_grp r).1.w
  have b : (oQ.onB.act x).left ≫ p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha x).trans (Category.assoc _ _ _).symm
  have b' : (oQ'.onB.act x).left ≫ p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      (p'.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) ≫ (L.oa.onB.act x).left :=
    (ha' x).trans (Category.assoc _ _ _).symm
  refine pb.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) r').trans (b'.trans (Eq.symm ?_)))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) b).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) r')))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (oQ'.onB.act x))).trans (Eq.symm ?_))))
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w (oQ.onB.act x))).trans w)

end GlobalTheory.UCanon.DivIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegRescaleBothSides
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleBoth

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.RescaleLift
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_fnOn_of_le {R : Type} [CommRing R] {W : (Sp R).Opens} (r : R) (h : W ≤ (Sp R).basicOpen (fnSp R r)) :
    IsUnit (fnOn W r) := isUnit_of_basicOpen_top _ (by
  have e := Scheme.preimage_basicOpen W.ι (fnSp R r)
  refine Eq.trans e.symm (top_le_iff.1 fun x _ => h x.2))

theorem mem_basicOpen_of_ne {R F : Type} [CommRing R] [Field F] (α : R →+* F) {r : R} (h : α r ≠ 0) {Z : Scheme.{0}}
    (s : Z ⟶ Sp F) (z : Z) : (s ≫ spMap α) z ∈ (Sp R).basicOpen (fnSp R r) := by
  have hpre : (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) = ⊤ := by
    rw [Scheme.preimage_basicOpen]
    refine Scheme.basicOpen_of_isUnit _ ?_
    refine (congrArg IsUnit (appTop_comp_spMap α s r)).mpr ?_
    exact ((IsUnit.mk0 _ h).map (fnSp _)).map s.appTop.hom
  exact (show z ∈ (s ≫ spMap α) ⁻¹ᵁ (Sp R).basicOpen (fnSp R r) from hpre.ge trivial)

theorem val_psiOn_rescale {R F : Type} [CommRing R] [IsDomain R] [Field F] (Q : DegPre R) (g : Q.X → (FractionRing R)ˣ)
    {W W₀ : (Sp R).Opens} (ψ : PsiOn Q W) (ψ₀ : PsiOn (GlobalTheory.PolDeg.rescale Q g) W₀) (y : Q.X) (a b : R)
    (hab : (g y : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a)
    (α : R →+* F) (hb : α b ≠ 0) (v : Fˣ) (hv : (v : F) * α b = α a) {Z : Scheme.{0}} (r : Z ⟶ W.toScheme)
    (r₀ : Z ⟶ W₀.toScheme) (s : Z ⟶ Sp F) (hr : r ≫ W.ι = s ≫ spMap α) (hr₀ : r₀ ≫ W₀.ι = s ≫ spMap α)
    (z : Z) (J) (hJ : Good Q.P.L z J) :
    val (ψ₀.psi y) r₀ z J = gm s z ⊤ (unitOn v) * val (ψ.psi y) r z J := by
  have ha : α a ≠ 0 := hv ▸ mul_ne_zero v.ne_zero hb
  have ha' : algebraMap R (FractionRing R) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => ha (by rw [h, map_zero])
  have hb' : algebraMap R (FractionRing R) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 fun h => hb (by rw [h, map_zero])
  obtain ⟨W', l, l₀, la, lb, hm⟩ : ∃ W' : (Sp R).Opens, W' ≤ W ∧ W' ≤ W₀ ∧ W' ≤ (Sp R).basicOpen (fnSp R a) ∧
      W' ≤ (Sp R).basicOpen (fnSp R b) ∧ ∀ x, (s ≫ spMap α) x ∈ W' :=
    ⟨(W ⊓ W₀) ⊓ ((Sp R).basicOpen (fnSp R a) ⊓ (Sp R).basicOpen (fnSp R b)), inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right, inf_le_right.trans inf_le_left, inf_le_right.trans inf_le_right, fun x =>
      ⟨⟨(congrArg (fun q => q x ∈ W) hr).mp (r x).2, (congrArg (fun q => q x ∈ W₀) hr₀).mp (r₀ x).2⟩,
        mem_basicOpen_of_ne α ha s x, mem_basicOpen_of_ne α hb s x⟩⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Z ⟶ W'.toScheme, ρ ≫ W'.ι = s ≫ spMap α :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hm x), IsOpenImmersion.lift_fac _ _ _⟩
  let m : W'.toScheme ⟶ W.toScheme := (Sp R).homOfLE l
  let m₀ : W'.toScheme ⟶ W₀.toScheme := (Sp R).homOfLE l₀
  have f : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have f₀ : m₀ ≫ W₀.ι = W'.ι := Scheme.homOfLE_ι _ _
  have ua := isUnit_fnOn_of_le a la
  have ub := isUnit_fnOn_of_le b lb
  have hφ : m ≫ (toUnit (TW W) ≫ Q.c y).left = m₀ ≫ (toUnit (TW W₀) ≫ Q.c y).left := by
    show m ≫ W.ι ≫ (Q.c y).left = m₀ ≫ W₀.ι ≫ (Q.c y).left
    rw [← Category.assoc, f, ← Category.assoc, f₀]
  have key := GlobalTheory.PsiEvenPull.val_eq_of_app_injective Q.P.isLB
    (u := GlobalTheory.UU.scaleGen ub.unit (LB.pullGen Q.P.L _ _ (ψ₀.psi y) m₀))
    (u' := GlobalTheory.UU.scaleGen ua.unit (LB.pullGen Q.P.L _ _ (ψ.psi y) m))
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) hφ)
    (jK R ∣_ W') (GlobalTheory.PsiEvenPull.app_injective_generic W')
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ₀.psi_gen y) m₀))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m)) (fun x I hI => by
      have e : (jK R ∣_ W') ≫ W'.ι = (jK R ⁻¹ᵁ W').ι ≫ jK R := morphismRestrict_ι _ _
      have p := GlobalTheory.ArcSpecialise.psiOn_generic ψ y ((jK R ∣_ W') ≫ m) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f, e]) hI
      have p₀ := GlobalTheory.ArcSpecialise.psiOn_generic ψ₀ y ((jK R ∣_ W') ≫ m₀) (jK R ⁻¹ᵁ W').ι
        (by rw [Category.assoc, f₀, e]) hI
      have q : val ((GlobalTheory.PolDeg.rescale Q g).psi y) (jK R ⁻¹ᵁ W').ι x I =
          gm (jK R ⁻¹ᵁ W').ι x ⊤ (unitOn (g y)) * val (Q.psi y) (jK R ⁻¹ᵁ W').ι x I :=
        GlobalTheory.UU.val_scaleGen (unitOn (g y)) (Q.psi y) _ hI
      have ga := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e a ua.unit (Units.mk0 _ ha') ua.unit_spec rfl x
      have gb := gm_fnOn W' (algebraMap R (FractionRing R)) _ _ e b ub.unit (Units.mk0 _ hb') ub.unit_spec rfl x
      have w : unitOn (Units.mk0 _ ha') = unitOn (Units.mk0 _ hb') * unitOn (g y) :=
        (congrArg unitOn (Units.ext (hab.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
      refine (GlobalTheory.UU.val_scaleGen _ _ _ hI).trans (Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hI).symm)
      refine (congrArg₂ (· * ·) gb ((val_pull hI _ _ _).trans (p₀.trans q))).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) ga ((val_pull hI _ _ _).trans p)).symm)
      rw [w, map_mul, _root_.mul_assoc]) Z ρ z J hJ
  have ga := gm_fnOn W' α _ _ hρ a ua.unit (Units.mk0 _ ha) ua.unit_spec rfl z
  have gb := gm_fnOn W' α _ _ hρ b ub.unit (Units.mk0 _ hb) ub.unit_spec rfl z
  have w : unitOn (Units.mk0 _ ha) = unitOn (Units.mk0 _ hb) * unitOn v :=
    (congrArg unitOn (Units.ext (hv.symm.trans (_root_.mul_comm _ _)))).trans (map_mul _ _ _)
  have c : ρ ≫ m = r := by rw [← cancel_mono W.ι, Category.assoc, f, hρ, hr]
  have c₀ : ρ ≫ m₀ = r₀ := by rw [← cancel_mono W₀.ι, Category.assoc, f₀, hρ, hr₀]
  have k₂ := (congrArg₂ (· * ·) gb (val_pull hJ _ _ _)).symm.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm.trans
    (key.trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) ga (val_pull hJ _ _ _)))))
  rw [w, map_mul, _root_.mul_assoc, c, c₀] at k₂
  exact mul_left_cancel k₂

theorem exists_isPullDeg_rescale : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {Q : DegPre R} {Q' : DegPre V} (hD : IsPullDeg θ Q Q') (g : Q.X → (FractionRing R)ˣ) (g' : Q'.X → (FractionRing V)ˣ), Nonempty (PsiOn (GlobalTheory.PolDeg.rescale Q g) ⊤) → (∀ y, ∃ a b : R, θ b ≠ 0 ∧ (g (hD.xe y) : FractionRing R) * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a ∧ (g' y : FractionRing V) * algebraMap V (FractionRing V) (θ b) = algebraMap V (FractionRing V) (θ a)) → ∃ h : IsPullDeg θ (GlobalTheory.PolDeg.rescale Q g) (GlobalTheory.PolDeg.rescale Q' g'), h.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) = hD.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf θ) ∧ ∀ y, h.xe y = hD.xe y := by
  intro R V _ _ _ _ θ Q Q' h g g' ⟨ψ₀⟩ H
  have hsq : jK V ≫ specOf θ = 𝟙 (TK V).left ≫ spMap ((algebraMap V (FractionRing V)).comp θ) := by
    rw [Category.id_comp]
    exact (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  obtain ⟨t, ht⟩ : ∃ t : (TK V).left ⟶ (TW (⊤ : (Sp R).Opens)).left, t ≫ (⊤ : (Sp R).Opens).ι = jK V ≫ specOf θ :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp R).Opens).ι (jK V ≫ specOf θ) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have gp : IsGrpPullback Q'.P.A Q.P.A (spMap θ) (proj h) := pull_grp h
  have hr : PMaps (K := PUnit) h.w (fun _ => eSec Q'.P.A) (fun _ => eSec Q.P.A) (fun _ => 1) Q'.rig Q.rig (spMap θ) :=
    GlobalTheory.FieldPull.pmaps_rig h
  have hc : ∀ x : Q'.X, (Q'.c x).left ≫ proj h = spMap θ ≫ (Q.c (h.xe x)).left := h.c_pr
  have hv : ∀ (x : Q'.X) (z : (TK V).left) J J', Good Q.P.L z J → Good Q'.P.L z J' →
      val (ψ₀.psi (h.xe x)) t z J =
        (om h.w z J J' (Q'.xK x))⁻¹ * val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    obtain ⟨a, b, hb, hab, hab'⟩ := H x
    have e0 := val_psiOn_rescale Q g h.psiW ψ₀ (h.xe x) a b hab ((algebraMap V (FractionRing V)).comp θ)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hb) (g' x) hab' h.g t (𝟙 _)
      (h.g_comm.trans hsq) (ht.trans hsq) z J hJ
    have e1 := GlobalTheory.PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
    rw [Category.id_comp] at e1
    have e2 : val ((GlobalTheory.PolDeg.rescale Q' g').psi x) (𝟙 _) z J' =
        gm (𝟙 (TK V).left) z ⊤ (unitOn (g' x)) * val (Q'.psi x) (𝟙 _) z J' :=
      GlobalTheory.UU.val_scaleGen (unitOn (g' x)) (Q'.psi x) (𝟙 _) hJ'
    refine e0.trans ?_
    rw [e1, e2, mul_left_comm]
    simp only [om, Category.id_comp]
  obtain ⟨hD, h₁, h₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW (GlobalTheory.PolDeg.rescale Q g)
    (GlobalTheory.PolDeg.rescale Q' g') ψ₀ t ht gp h.w ((isGen_iff h.w).1 h.w_gen) hr h.xe hc hv
  exact ⟨hD, h₁, h₂⟩

end GlobalTheory.RescaleBoth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegWholeSpectrum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullDegWhole

theorem exists_isPullDeg_top : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  intro R R' _ _ _ _ i D D' p ⟨ψ⟩
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme,
      g ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι = jK R' ≫ specOf i :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨{ p with W := ⊤, psiW := ψ, g := g, g_comm := hg, psi_pr := fun x => ?_ }, rfl, rfl, fun _ => rfl⟩
  obtain ⟨b, hb, hc⟩ := p.psi_pr x
  refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc _).trans ?_⟩
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  exact GlobalTheory.ArcSpecialise.psiOn_agree p.psiW ψ _ _ _
    (by rw [Category.assoc, Category.assoc]; exact congrArg _ (p.g_comm.trans hg.symm)) hJ

end GlobalTheory.PullDegWhole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShear
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem IsOpp.exists_isometry_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ)
    (hN : 0 < N) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (t : Z →ₗ[𝓞 E] D.La)
    (ht : ∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) (hiso : ∀ z z' : Z, D.EF (t z) (t z') = 0) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ z : Z, g z = t z := by
  set q := h.symm.proj with hq
  have hr : ∀ a, a - (q a : D.La) ∈ perp D Z' := fun a => h.symm.sub_proj_mem a
  have hδ : ∀ z : Z, t z - (z : D.La) ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hz⟩ := ht z
    rw [hz, add_sub_cancel_left]
    exact nsmul_mem he N
  choose c hc hu using fun a : D.La => h.2.2.1 (AddMonoidHom.mk' (fun z : Z => D.EF (t z - z) (a - q a))
    fun z z' => by simp only [map_add, map_sub, Submodule.coe_add, LinearMap.add_apply, LinearMap.sub_apply]; abel)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  let α : D.La →ₗ[𝓞 E] Z' :=
    { toFun := c
      map_add' := fun a a' => (hu _ _ fun z => by
        simp only [Submodule.coe_add, map_add, hc, map_sub, LinearMap.sub_apply, map_add]
        abel).symm
      map_smul' := fun x a => (hu _ _ fun z => by
        have key : ∀ u w : D.La, D.EF u (x • w) = D.EF (H.bar x • u) w := fun u w => by rw [D.adj, bar_bar]
        simp only [RingHom.id_apply, Submodule.coe_smul, map_smul, ← smul_sub]
        rw [key, key, ← Submodule.coe_smul, hc, Submodule.coe_smul, map_smul, smul_sub]).symm }
  have hα : ∀ a, α a = c a := fun _ => rfl
  let g : D.La →ₗ[𝓞 E] D.La := LinearMap.id + (t - Z.subtype) ∘ₗ q - Z'.subtype ∘ₗ α
  have hg : ∀ a, g a = a + (t (q a) - q a) - c a := fun _ => rfl
  refine ⟨g, fun a a' => ?_, fun a => ?_, fun z => ?_⟩
  · have hZ : ∀ (x y : Z), D.EF x y = 0 := fun x y => h.1 x.2 _ y.2
    have hZ' : ∀ (x y : Z'), D.EF x y = 0 := fun x y => h.2.1 x.2 _ y.2
    have f1 := hZ' (c a) (c a')
    have f2 : D.EF (t (q a) - q a) (c a') = 0 := hδ (q a) _ (c a').2
    have f3 : D.EF (c a) (t (q a') - q a') = 0 := by
      rw [ef_swap, hδ (q a') _ (c a).2, neg_zero]
    have f4 := hiso (q a) (q a')
    have f5 := hZ (q a) (q a')
    have f7 : D.EF a (c a') = D.EF (t (q a) - q a) (a' - q a') := by
      have := hr a _ (c a').2
      rw [← hc a' (q a)]
      simp only [map_sub, LinearMap.sub_apply] at this
      linear_combination this
    have f8 : D.EF (c a) a' = D.EF (a - q a) (t (q a') - q a') := by
      have := hr a' _ (c a).2
      have h2 := hc a (q a')
      rw [ef_swap D (c a) a', ef_swap D (a - q a)]
      simp only [map_sub, LinearMap.sub_apply] at this h2 ⊢
      linear_combination -this - h2
    rw [hg, hg]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at f2 f3 f7 f8 ⊢
    linear_combination f1 - f2 - f3 + f4 - f5 - f7 - f8
  · obtain ⟨e, -, he⟩ := ht (q a)
    obtain ⟨e', he'⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hN (c a : D.La) fun b => by
      obtain ⟨e₁, -, he₁⟩ := ht (q b)
      have h1 : D.EF (c a) (b - q b) = 0 := by rw [ef_swap, hr b _ (c a).2, neg_zero]
      have h2 := hc a (q b)
      rw [he₁, add_sub_cancel_left, map_nsmul, LinearMap.smul_apply] at h2
      refine ⟨-D.EF e₁ (a - q a), ?_⟩
      have h3 : D.EF (c a) b = D.EF (c a) (q b) := by
        rw [map_sub] at h1; linear_combination h1
      rw [h3, ef_swap, h2, nsmul_eq_mul]
      ring
    refine ⟨e - e', ?_⟩
    rw [hg, he, he', smul_sub]
    abel
  · have hqz : q z = z := Subtype.ext (h.symm.proj_of_mem z.2)
    have hcz : c z = 0 := (hu z 0 fun z' => by simp [hqz]).symm
    rw [hg, hqz, hcz]
    simp

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedSubmoduleOfFinrankLeStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropicSaturatedSubmodule_of_finrank_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (r : ℕ), r ≤ min D.p D.q →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = r := by
  first | exact @GlobalTheory.LowFilt.exists_isIsoSat_finrank | exact GlobalTheory.LowFilt.exists_isIsoSat_finrank | (intros; apply GlobalTheory.LowFilt.exists_isIsoSat_finrank <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicShearOfAdjoint
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_eq_nsmul_of_forall_ef_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) : ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

theorem exists_shear_of_adjoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    ∀ σ w : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') → (∀ b ∈ Z', σ b = b) → (∀ a, ∃ e, y (σ a) = y a + n • e) →
    (∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e) → (∀ a b, D.EF (w a) b = D.EF a (σ b)) →
    (∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e) →
    ∃ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) ∧ (∀ z z' : Z, D.EF (t z) (t z') = 0) ∧
      ∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a := by
  intro E _ _ _ H D X _ _ y n N hn hNn hC Z Z' hO σ w hσZ hσb hσy hσN hw hsat
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  obtain ⟨k, hk⟩ := hNn
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'

  have ha : ∀ z ∈ Z, ∃ e ∈ perp D Z', w z = z + N • e := by
    intro z hz
    obtain ⟨e, he⟩ := exists_eq_nsmul_of_forall_ef_dvd D hN (w z - z) fun b => by
      obtain ⟨b', hb', e, he⟩ := hσN b
      have h0 : D.EF z b' = 0 := by rw [ef_swap, hb' z hz, neg_zero]
      refine ⟨D.EF z e, ?_⟩
      simp only [map_sub, LinearMap.sub_apply, hw, he, map_add, map_nsmul, h0, nsmul_eq_mul]
      ring
    refine ⟨e, mem_perp.2 fun b hb => ?_, (sub_eq_iff_eq_add'.1 he)⟩
    have h1 : D.EF (w z - z) b = 0 := by rw [map_sub, LinearMap.sub_apply, hw, hσb b hb, sub_self]
    rw [he, map_nsmul, LinearMap.smul_apply, smul_eq_zero] at h1
    exact h1.resolve_left hN.ne'

  have hb : ∀ z a : D.La, (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (w z) a := by
    rintro z a ⟨e, he⟩
    obtain ⟨e₁, he₁⟩ := hσy a
    obtain ⟨e', -, he'⟩ := hsat (σ a) (hσZ a) ⟨e + e₁, by rw [he₁, he, smul_add]⟩
    refine ⟨D.EF z e', ?_⟩
    rw [hw, he', map_nsmul, nsmul_eq_mul]
  have hwy : ∀ z, ∃ e, y (w z) = n • e := fun z => hC.2 (w z) fun b hb' => hb z b hb'
  have hww : ∀ z z', (n : ℤ) ∣ D.EF (w z) (w z') := fun z z' => hb z (w z') (hwy z')
  obtain ⟨f, hf⟩ : ∃ f : Z → Z → ℤ, ∀ z z', (n : ℤ) * f z z' = D.EF (w z) (w z') :=
    ⟨fun z z' => D.EF (w z) (w z') / n, fun z z' => Int.mul_ediv_cancel' (hww _ _)⟩
  obtain ⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm ℤ Z, ∀ a b, β a b = f a b :=
    ⟨LinearMap.mk₂ ℤ f
      (fun z₁ z₂ z' => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp))
      (fun z z₁ z₂ => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp)),
      fun _ _ => rfl⟩
  have hskew : ∀ a b, β a b = -β b a := fun a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [mul_neg, hf, hf, ef_swap])
  have hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b) := fun c a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [hf, hf, Submodule.coe_smul, Submodule.coe_smul, w.map_smul, w.map_smul, D.adj])
  obtain ⟨c, hc⟩ := exists_skew_solve hO.2.2.1 β hskew hadj
  have ht : ∀ z : Z, (w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c)) z = w z - n • (c z : D.La) := fun z => rfl
  refine ⟨w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c), fun z => ?_, fun z z' => ?_, fun z a ha' => ?_⟩
  · obtain ⟨e₁, he₁, hwz⟩ := ha z z.2
    refine ⟨e₁ - k • (c z : D.La), sub_mem he₁ (nsmul_mem (hO.2.1 (c z).2) k), ?_⟩
    rw [ht, hwz, hk, smul_sub, mul_smul]
    abel
  · have e1 : D.EF (w z) (c z') = D.EF z (c z') := by rw [hw, hσb _ (c z').2]
    have e2 : D.EF (c z) (w z') = D.EF (c z) z' := by rw [ef_swap, hw, hσb _ (c z).2, ← ef_swap]
    have e3 : D.EF (c z) (c z') = 0 := hO.2.1 (c z).2 _ (c z').2
    have e4 : (n : ℤ) * β z z' = D.EF (w z) (w z') := by rw [hβ, hf]
    have e5 := hc z z'
    rw [ht, ht]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul, e1, e2, e3]
    linear_combination (-1 : ℤ) * e4 - (n : ℤ) * e5
  · rw [ht, map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_sub (hb z a ha') (dvd_mul_right _ _)

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryExtensionAlgClosedStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelIsometry_extension_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (I₀ : letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD (AlgebraicClosure (FractionRing R))),
    GlobalTheory.LowDat.XFLevel C tK m1 m2 (AlgebraicClosure (FractionRing R)) I₀ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧
      ∀ n a, (I.ev n a).y = (I₀.ev n a).y := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel_ext | exact GlobalTheory.LowDat.exists_xfLevel_ext | (intros; apply GlobalTheory.LowDat.exists_xfLevel_ext <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryGenericFibreBoundaryChartStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelIsometry_genericFibre_boundaryChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  first | exact @GlobalTheory.LowDat.exists_xfLevel | exact GlobalTheory.LowDat.exists_xfLevel | (intros; apply GlobalTheory.LowDat.exists_xfLevel <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionAtBoundaryPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_extension_at_boundaryPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ x : S, x ∉ Set.range j → ∃ N : LB (pullback G.hom (S.fromSpecStalk x)), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ pullback G.hom (S.fromSpecStalk x)) (b : T ⟶ tF.G.left), a ≫ pullback.fst G.hom (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (tF.PP.L.pull b) := by
  first | exact @GlobalTheory.BdStalkExt.exists_extension_at_boundary | exact GlobalTheory.BdStalkExt.exists_extension_at_boundary | (intros; apply GlobalTheory.BdStalkExt.exists_extension_at_boundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGeneratorStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearForm_factor_through_traceGenerator : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (Z' : Submodule (𝓞 E) D.La) (θ : 𝓞 E →+ ℤ) (s : 𝓞 E) (hs : s ≠ 0)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) (w : D.La),
    ∃ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, ∀ x : Z', θ (ℓ x) = D.EF x (H.bar s • w) := by
  first | exact @GlobalTheory.LowFilt.exists_linear_theta_factor | exact GlobalTheory.LowFilt.exists_linear_theta_factor | (intros; apply GlobalTheory.LowFilt.exists_linear_theta_factor <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneModMaximalMemOtherMaximalsOverNatStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_one_mod_maximal_mem_other_maximals_over_nat : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  first | exact @GlobalTheory.sep_one_mod_maximal_mem_others | exact GlobalTheory.sep_one_mod_maximal_mem_others | (intros; apply GlobalTheory.sep_one_mod_maximal_mem_others <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeIsotropicPairStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oppositeIsotropicPair : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (Z : Submodule (𝓞 E) D.La), IsIsoSat D Z → ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' := by
  first | exact @GlobalTheory.LowFilt.Opp.exists_opp | exact GlobalTheory.LowFilt.Opp.exists_opp | (intros; apply GlobalTheory.LowFilt.Opp.exists_opp <;> assumption)
end
end

