import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3478
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0131
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0040
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3476
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3480

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRechartingThetaSystemAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.UPoinc.exists_rechart_wit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w₀ ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ ∧ ∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (ρ'.pt x).left := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi w₀ hw₀
  obtain ⟨⟨hL, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratHull_lift E H Dw hpq l Xo cf C X w₀ hw₀
  obtain ⟨U₁, h₁, P₁, hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.USetup.exists_polAV_ringOn_near E H Dw hpq l Xo cf C X w₀ hw₀ U₀ u₀ hU₀a hwU₀ hu₀
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w₀ hU₁a hwU₁ P₁ X.S.N hN
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf := spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hu' : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hUO : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat (X.M.ringOn U))).2 ?_
    have h2 := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e1 : (Subalgebra.inclusion (ratHull_mono h)).toRingHom.comp (toRat (X.M.ringOn U₁)) =
        (toRat (X.M.ringOn U)).comp (Subalgebra.inclusion h).toRingHom := RingHom.ext fun _ => rfl
    have e2 : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    rw [e1, e2] at h2
    exact h2
  obtain ⟨G, _, α, β, hα, hβ, hLG⟩ := hUO
  have wβ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [wi.hβ.1.w, ← hu']
    simp only [Category.assoc]
  let m : wi.G.left ⟶ G.left := hβ.1.lift wi.β (wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom) wβ
  have hm₁ : m ≫ β = wi.β := hβ.1.lift_fst _ _ _
  have hm₂ : m ≫ G.hom = wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom := hβ.1.lift_snd _ _ _
  have hm : IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m :=
    hβ.cancel (wi.hβ.congr (by rw [← hu']; simp only [Category.assoc]) hm₁.symm) hm₂
  have hmα : IsGrpPullback wi.G P'.A (spMap (X.M.ringOn U).val.toRingHom) (m ≫ α) :=
    (hm.comp hα).congr (spMap_val_toRat (X.M.ringOn U)) rfl
  have hLU := Xo.univ.t.PP.isLB
  have hLρ := X.ρ.P.isLB
  have hLP := P'.isLB
  have hLw : LBIso (X.ρ.P.L.pull wi.α) (P'.L.pull (m ≫ α)) :=
    LBIso.trans (pull_isLB hLρ _) (pull_isLB hLU _) (pull_isLB hLP _) wi.hL
      (LBIso.trans (pull_isLB hLU _) (pull_isLB (pull_isLB hLU _) _) (pull_isLB hLP _)
        (GenSpread.lbIso_pull_pull hLU m hm₁.symm)
        (LBIso.trans (pull_isLB (pull_isLB hLU _) _) (pull_isLB (pull_isLB hLP _) _) (pull_isLB hLP _)
          (GenSpread.lbIso_pullback hLG.symm m) (GenSpread.lbIso_pull_pull hLP m rfl).symm))
  obtain ⟨P₀, a, a', e, he, hea, hea', ha, ha', hl, hl'⟩ :=
    GlobalTheory.UPoinc.exists_polAV_common_pullback X.Ω₁ (Sp X.S.R) (Sp (X.M.ringOn U)) X.ρ.P P' (spMap X.S.R.val.toRingHom) (spMap (X.M.ringOn U).val.toRingHom) wi.G wi.α (m ≫ α)
      wi.hα hmα hLw
  have hne : ((U : Set X.M.Z)).Nonempty := ⟨w₀, hwU⟩
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ a a' ha ha' hl hl' X.ρ.hypS
  have hg : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ a' ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ a ha).trans X.ρ.g_eq)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  have frac : ∀ x : X.Ω₁, ∃ a ∈ (X.M.ringOn U), ∃ b ∈ (X.M.ringOn U), x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI : IsIntegrallyClosed (X.M.ringOn U) :=
    TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : (X.M.ringOn U)) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hL X.S.R.val.toRingHom X.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U) (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  let Q : (P : PolAV (Sp (X.M.ringOn U))) → (X.S.Gam → (baseOver (Sp (X.M.ringOn U)) ⟶ P.A)) → Prop := fun P pt =>
    (∃ (P₀ : PolAV (Sp X.Ω₁)) (a : P₀.A.left ⟶ X.ρ.P.A.left) (a' : P₀.A.left ⟶ P.A.left),
      IsGrpPullback P₀.A X.ρ.P.A (spMap ((RingHom.id _).comp X.S.R.val.toRingHom)) a ∧
      IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a' ∧ LBIso P₀.L (X.ρ.P.L.pull a) ∧ LBIso P₀.L (P.L.pull a') ∧
      ∀ x, ∃ w : Sp X.Ω₁ ⟶ P₀.A.left, w ≫ a = spMap ((RingHom.id _).comp X.S.R.val.toRingHom) ≫ (X.ρ.pt x).left ∧
        w ≫ a' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) ∧
    (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧
      LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧
        ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left)
  have hQ : Q P' pt' := by
    refine ⟨⟨P₀, a, a', ha, ha', hl, hl', hw0⟩, G, inferInstance, α, β, hα, hβ, hLG, m, hm, hm₁, fun x => ?_⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    refine ⟨w0 ≫ inv e, ?_, ?_⟩
    · rw [← hea, Category.assoc, IsIso.inv_hom_id_assoc, h₁]
    · rw [← hea', Category.assoc, IsIso.inv_hom_id_assoc]
      exact h₂
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hS₁, G', _, α', β', hα', hβ', hL', m', hm', hm₁', hpt'⟩, hi₀⟩ :=
    GlobalTheory.ThetaExtend.exists_real_rechart hL X.S X.ρ (X.M.ringOn U) fg frac P' P₀ a a' pt' th b ha ha' hl hl' hg hyp hadd hbij hweil
      hw0 hth hb Q hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, hS₁, hi₀, hu', G', inferInstance, α', β', hα', hβ', hL', m',
    hm', hm₁', hpt'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDegGeneratingEverywhere
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PreLiftData

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PreLift

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_rescale_isPullDeg_data {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left) :
    ∃ (κ : D'.X → (FractionRing R')ˣ) (hD : IsPullDeg i D (GlobalTheory.PolDeg.rescale D' κ)),
      (∀ y, hD.xe y = xe y) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = Φ ∧ hD.W = W := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  choose u hu using GlobalTheory.FieldPull.exists_psi_ratio D' psi hpsi
  refine ⟨fun x => (u x)⁻¹, ?_⟩
  have eψ : ∀ x, psi x = (GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi x := fun x =>
    GlobalTheory.TorusExt.gen_ext_val D'.P.isLB (hpsi x) ((GlobalTheory.PolDeg.rescale D' fun x => (u x)⁻¹).psi_gen x)
      fun y J' hJ' => by
        refine Eq.trans ?_ (GlobalTheory.UU.val_scaleGen _ _ _ hJ').symm
        have h1 : unitOn (u x)⁻¹ * unitOn (u x) = 1 := (map_mul _ _ _).symm.trans
          ((congrArg unitOn (inv_mul_cancel (u x))).trans (map_one _))
        rw [hu x y J' hJ', GlobalTheory.TauTwist.unitAt_apply, ← _root_.mul_assoc, ← map_mul]
        erw [h1]
        rw [map_one, _root_.one_mul]
  have key : ∀ x, GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit)
      (fun _ => e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) w (D'.xK x) (-1) (psi x) (b x) := fun x jN jL => by
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, eψ x ▸ key x,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, fun _ => rfl, rfl, rfl⟩
  exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
    (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr

theorem exists_rescale_isPullDeg_top : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  intro _ _ _ _ _ _ θ₀ D₀ Q e β hU gp hL hc
  obtain ⟨ψW⟩ := GlobalTheory.ArcPull.nonempty_psiOn_top D₀ hU
  let gg : (TK _).left ⟶ (TW (⊤ : (Sp _).Opens)).left := (jK _ ≫ specOf θ₀) ≫ (Sp _).topIso.inv
  have hg : gg ≫ (⊤ : (Sp _).Opens).ι = jK _ ≫ specOf θ₀ := by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨w₀, hw₀⟩ := hL
  have he : eSec Q.P.A ≫ β = spMap θ₀ ≫ eSec D₀.P.A := (cubeMapOf gp).e_comm
  have hσ : eSec Q.P.A ≫ Q.P.A.hom = 𝟙 _ := Over.w η[Q.P.A]
  obtain ⟨w, hw, hr⟩ := GlobalTheory.UnifPreCompare.exists_rigidified D₀.P.isLB Q.P.isLB Q.P.A.hom (eSec Q.P.A) hσ w₀ hw₀
    Q.rig Q.rig_gen (φ := eSec D₀.P.A) D₀.rig D₀.rig_gen (spMap θ₀) he
  exact exists_rescale_isPullDeg_data (i := θ₀) D₀ Q ψW gg hg gp w ((isGen_iff w).1 hw) hr e hc

end GlobalTheory.PreLiftData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedLineBundleExtensionOfLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidifiedLineBundle_extension_of_local : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S] [GlobalTheory.IsNormalScheme S] (f : Y ⟶ S) [Smooth f] [GeometricallyConnected f] (j : U ⟶ S) [IsOpenImmersion j], Dense (Set.range j) → ∀ (e : YU ⟶ Y) (fU : YU ⟶ U), IsPullback e fU f j → ∀ (σ : S ⟶ Y) (σU : U ⟶ YU), σ ≫ f = 𝟙 S → σU ≫ e = j ≫ σ → ∀ (L : LB YU), L.IsLB → ∀ (r : LB.Gen (L.pull σU)), r.IsGen → (∀ x : S, x ∉ Set.range j → ∃ W : S.Opens, x ∈ W ∧ ∃ N : LB ↑(f ⁻¹ᵁ W), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ ↑(f ⁻¹ᵁ W)) (b : T ⟶ YU), a ≫ (f ⁻¹ᵁ W).ι = b ≫ e → LBIso (N.pull a) (L.pull b)) → ∃ M : LB Y, M.IsLB ∧ LBIso (M.pull e) L := by
  first | exact @GlobalTheory.RigLBDense.exists_extension_of_local_ext | exact GlobalTheory.RigLBDense.exists_extension_of_local_ext | (intros; apply GlobalTheory.RigLBDense.exists_extension_of_local_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtendDescendedSemiAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringAction_extend_descended_semiAbelian : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∃ act : OAct (𝓞 E) G, ∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left := by
  first | exact @GlobalTheory.DescAct.exists_oAct_extend_toSemiAbelian_normBl | exact GlobalTheory.DescAct.exists_oAct_extend_toSemiAbelian_normBl | (intros; apply GlobalTheory.DescAct.exists_oAct_extend_toSemiAbelian_normBl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivPowerSeriesPrescribedParameters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

theorem sum_residue_smul_toCotangent {R : Type} [CommRing R] [IsLocalRing R] {Idx : Type} [Fintype Idx]
    (a : Idx → R) (y : Idx → R) (hy : ∀ i, y i ∈ maximalIdeal R) :
    ∑ i, residue R (a i) • (maximalIdeal R).toCotangent ⟨y i, hy i⟩ =
      (maximalIdeal R).toCotangent ⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ := by
  have h : (⟨∑ i, a i * y i, sum_mem fun i _ => Ideal.mul_mem_left _ _ (hy i)⟩ : maximalIdeal R) =
      ∑ i, a i • (⟨y i, hy i⟩ : maximalIdeal R) := by
    ext; simp [smul_eq_mul]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]

end GlobalTheory.CohenChart

namespace GlobalTheory.CohenChart

open IsLocalRing MvPowerSeries

theorem exists_ringEquiv_chartRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
    IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R),
    (∀ i, t i ∈ maximalIdeal R) →
    (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) →
    ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  intro R _ _ hc hQ m t ht hind
  classical
  obtain ⟨q⟩ := hQ
  letI : Algebra ℚ (ResidueField R) := ((IsLocalRing.residue R).comp q).toAlgebra
  haveI : CharZero (ResidueField R) := algebraRat.charZero _
  haveI := hc
  obtain ⟨Λ, hF, hΛ⟩ := GlobalTheory.CohenRegular.exists_coefficientField_of_charZero R
  letI := hF.toField

  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨t i, ht i⟩
  have hv : LinearIndependent (ResidueField R) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (R := R) (g j)
    have h1 : ∑ j, residue R (a j) • v j = 0 := by simpa [ha] using hg
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq_zero] at h1
    rw [← ha i, residue_eq_zero_iff]
    exact hind a h1 i
  set d := Module.finrank (ResidueField R) (CotangentSpace R) with hd
  have hmd : m ≤ d := by simpa using hv.fintype_card_le_finrank
  set W := Submodule.span (ResidueField R) (Set.range v) with hW
  have hWd : Module.finrank (ResidueField R) (CotangentSpace R ⧸ W) = d - m := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank (ResidueField R) W = m := by rw [finrank_span_eq_card hv]; simp
    omega
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R ⧸ W) hWd
  choose w hw using fun j => W.mkQ_surjective (b j)
  choose s hs using fun j => (maximalIdeal R).toCotangent_surjective (w j)
  let x : Fin m ⊕ Fin (d - m) → R := Sum.elim t (fun j => (s j : R))
  have hx : ∀ j, x j ∈ maximalIdeal R := by
    rintro (j | j)
    exacts [ht j, (s j).2]
  let g : Fin m ⊕ Fin (d - m) → CotangentSpace R := fun j => (maximalIdeal R).toCotangent ⟨x j, hx j⟩
  set U := Submodule.span (ResidueField R) (Set.range g) with hU
  have hUtop : ∀ y : CotangentSpace R, y ∈ U := by
    intro y
    have hWU : W ≤ U := Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
    have hwU : ∀ j, w j ∈ U := fun j => Submodule.subset_span ⟨Sum.inr j, by simp [g, x, hs]⟩
    have h1 : W.mkQ (y - ∑ j, b.repr (W.mkQ y) j • w j) = 0 := by
      simp only [map_sub, map_sum, map_smul, hw, b.sum_repr, sub_self]
    have h2 : y - ∑ j, b.repr (W.mkQ y) j • w j ∈ W := by
      rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at h1
    have h3 : ∑ j, b.repr (W.mkQ y) j • w j ∈ U := U.sum_mem fun j _ => U.smul_mem _ (hwU j)
    have := U.add_mem (hWU h2) h3
    simpa using this

  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  haveI : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  let f : ChartRing Λ m (d - m) →ₐ[Λ] R := GlobalTheory.mvEvalAdic Λ (maximalIdeal R) x hx
  have hfX : ∀ j, f (X j) = x j := fun j => GlobalTheory.mvEvalAdic_X (A := Λ) (maximalIdeal R) x hx j
  have hfC : ∀ a : Λ, f (C a) = a := fun a => GlobalTheory.mvEvalAdic_C (A := Λ) (maximalIdeal R) x hx a
  have hle : ∀ g ∈ maximalIdeal (ChartRing Λ m (d - m)), f g ∈ maximalIdeal R := by
    intro g hg
    have h4 := GlobalTheory.algHom_sub_constantCoeff_mem f (K := maximalIdeal R) (fun j => by rw [hfX]; exact hx j) g
    have h5 := GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hXm : ∀ j, (X j : ChartRing Λ m (d - m)) ∈ maximalIdeal (ChartRing Λ m (d - m)) := fun j =>
    GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp)
  have hloc : IsLocalHom (f : ChartRing Λ m (d - m) →+* R) := ⟨fun g hg => by
    by_contra hn
    exact (hle g hn) hg⟩
  have hres : ∀ z : R, ∃ r, z - (f : ChartRing Λ m (d - m) →+* R) r ∈ maximalIdeal R := by
    intro z
    obtain ⟨a, ha, h⟩ := hΛ z
    exact ⟨C ⟨a, ha⟩, by simpa [hfC] using h⟩
  have hcot : maximalIdeal R ≤ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) ⊔
      maximalIdeal R ^ 2 := by
    intro z hz
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField R)).1
      (hUtop ((maximalIdeal R).toCotangent ⟨z, hz⟩))
    choose a ha using fun j => residue_surjective (R := R) (c j)
    have h1 : ∑ j, residue R (a j) • g j = (maximalIdeal R).toCotangent ⟨z, hz⟩ := by simpa [ha] using hc'
    rw [sum_residue_smul_toCotangent, Ideal.toCotangent_eq] at h1
    have h2 : ∑ j, a j * x j ∈ (maximalIdeal (ChartRing Λ m (d - m))).map (f : ChartRing Λ m (d - m) →+* R) :=
      sum_mem fun j _ => Ideal.mul_mem_left _ _ (by rw [← hfX]; exact Ideal.mem_map_of_mem _ (hXm j))
    have h3 : z = ∑ j, a j * x j + (z - ∑ j, a j * x j) := by ring
    rw [h3]
    refine Submodule.add_mem_sup h2 ?_
    have : (z - ∑ j, a j * x j) = -((∑ j, a j * x j) - z) := by ring
    rw [this]
    exact neg_mem h1
  have hcA : IsAdicComplete (maximalIdeal (ChartRing Λ m (d - m))) (ChartRing Λ m (d - m)) :=
    GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv
      (MvPowerSeries.renameEquiv Λ finSumFinEquiv.symm).toRingEquiv
      (h := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries Λ (m + (d - m)))
  have hsurj : Function.Surjective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.LocalSurj.surjective_of_residue_of_cotangent _ R _ hcA hloc hres hcot
  letI : Algebra (ChartRing Λ m (d - m)) R := (f : ChartRing Λ m (d - m) →+* R).toAlgebra
  haveI : Module.Finite (ChartRing Λ m (d - m)) R :=
    Module.Finite.of_surjective (Algebra.linearMap (ChartRing Λ m (d - m)) R) hsurj
  have hdA : ringKrullDim (ChartRing Λ m (d - m)) = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF, Nat.card_sum,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin, zero_add]
  have hdR : ringKrullDim R = ((m + (d - m) : ℕ) : WithBot ℕ∞) := by
    rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance, ← hd]
    have hmd' : m + (d - m) = d := by omega
    rw [hmd']
  have hinj : Function.Injective (f : ChartRing Λ m (d - m) →+* R) :=
    GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq hdA hdR
  let φ := RingEquiv.ofBijective (f : ChartRing Λ m (d - m) →+* R) ⟨hinj, hsurj⟩
  refine ⟨Λ, inferInstance, d - m, φ.symm, fun i => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  show t i = f (X (Sum.inl i))
  rw [hfX]
  rfl

end GlobalTheory.CohenChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.TriplePull

theorem exists_sabMap_of_isProper : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (π : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f π → (∀ a, (t'.act.act a).left ≫ π = π ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull π) → ∃ m : SABMap t' t f, m.φ = π := by
  intro E _ _ _ H S S' t' t f π hp gp hact h
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) gp.1 hp
  exact GlobalTheory.CartTriple.exists_tripleMap GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 E H S S' f t' t π
    ⟨t'.semi.comm, t'.semi.smooth, hp', t'.semi.geomConnected⟩ gp hact h

end GlobalTheory.UCanon.TriplePull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupRegularOverModuliPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.SetupAt

theorem exists_generic_specializes {X : Scheme.{0}} (x : X) : ∃ η ∈ genericPoints X, η ⤳ x := by
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  refine ⟨hirr.genericPoint, ?_, ?_⟩
  · show closure {hirr.genericPoint} ∈ irreducibleComponents X
    rw [hirr.isGenericPoint_genericPoint_closure.def, hcl.closure_eq]
    exact irreducibleComponent_mem_irreducibleComponents x
  · rw [specializes_iff_mem_closure, hirr.isGenericPoint_genericPoint_closure.def, hcl.closure_eq]
    exact mem_irreducibleComponent

theorem exists_uSetup_regular_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c), ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w :=
  GlobalTheory.UPoinc.exists_uSetup_regular_at

end GlobalTheory.UPoinc.SetupAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantLiftDerivationRaynaudStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusInvariant_lift_derivation_raynaud : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ d : Fld Y.H.left, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V.1) d ∧ ∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V.1 → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f) := by
  first | exact @GlobalTheory.Heat.HxLift.exists_invLift | exact GlobalTheory.Heat.HxLift.exists_invLift | (intros; apply GlobalTheory.Heat.HxLift.exists_invLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUTraitOfStalkDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.UPoinc.exists_uTrait_of_stalk_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ Xo.XF c) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : UTrait Xo c) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  intro E _ _ _ H Dw l Xo c o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ
  haveI : CharZero (M.Z.presheaf.stalk x) := (M.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB inferInstance (spMap γ₀ ≫ y₀)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e,
      ← Formalism.L2.Pj.spMap_comp', Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds
section
theorem GlobalTheory.PeriodFamily.periodComparison_holds : GlobalTheory.Published.PeriodComparison :=
  GlobalTheory.PeriodFamily.periodComparison_of_gaussManinPeriods GlobalTheory.PeriodFamily.gaussManinPeriods_holds
end

