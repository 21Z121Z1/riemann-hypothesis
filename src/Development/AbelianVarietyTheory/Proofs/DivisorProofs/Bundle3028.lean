import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianActionEqUniversalAtFieldPointsOfTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ActField

theorem exists_factor_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y : RatModel o Ω) (K : Type) [Field K]
    (s : Sp K ⟶ Y.Z), ∃ (z : Y.Z) (j : Sp (Y.O z) ⟶ Y.Z) (s' : Sp K ⟶ Sp (Y.O z)),
      spMap (algebraMap (Y.O z) Ω) ≫ j = Y.pt ∧ s' ≫ j = s ∧ j (IsLocalRing.closedPoint (Y.O z)) = z ∧ ∀ w, s w = z := by
  intro o Ω _ _ _ Y K _ s
  have hsz : ∀ w, s w = s (IsLocalRing.closedPoint K) := fun w => by
    rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
  let z := s (IsLocalRing.closedPoint K)
  let e := Y.stalkEquiv z
  let E : Y.Z.presheaf.stalk z ⟶ CommRingCat.of (Y.O z) := CommRingCat.ofHom e.toRingHom
  let E' : CommRingCat.of (Y.O z) ⟶ Y.Z.presheaf.stalk z := CommRingCat.ofHom e.symm.toRingHom
  have hEE : E ≫ E' = 𝟙 _ := by ext a; exact e.symm_apply_apply a
  refine ⟨z, Spec.map E ≫ Y.Z.fromSpecStalk z, Spec.map (E' ≫ Scheme.stalkClosedPointTo s), ?_, ?_, ?_, hsz⟩
  · have h1 : E ≫ CommRingCat.ofHom (algebraMap (Y.O z) Ω) =
        Y.Z.presheaf.stalkSpecializes (Y.pt_specializes (IsLocalRing.closedPoint Ω) z) ≫
          Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Y.pt := by
      ext a; rfl
    show Spec.map _ ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, hEE, Category.id_comp,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · haveI : IsLocalHom E.hom := ⟨fun a ha => by
      have h := ha.map e.symm.toRingHom
      have h' : e.symm.toRingHom (E.hom a) = a := e.symm_apply_apply a
      rwa [h'] at h⟩
    change Y.Z.fromSpecStalk z ((Spec.map E) (IsLocalRing.closedPoint (CommRingCat.of (Y.O z)))) = z
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem exists_factor_i : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (O : Type) [CommRing O] [IsLocalRing O] (g : Sp O ⟶ C.Z),
      g (IsLocalRing.closedPoint O) ∈ Set.range C.i → ∃ v : Sp O ⟶ Xo.XF c, g = v ≫ C.i := by
  intro E _ _ _ H Dw l Xo c C O _ _ g hg
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  obtain ⟨x, hx⟩ := hg
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ C.z)
  have hpt : (Spec.map φ) (IsLocalRing.closedPoint O) =
      (spMap C.b) ((pullback.snd C.z (spMap C.b)) (C.iF x)) := by
    rw [hφ]
    change C.z (g _) = _
    rw [← hx]
    change ((C.iF ≫ pullback.fst C.z (spMap C.b)) ≫ C.z) x = ((C.iF ≫ pullback.snd C.z (spMap C.b)) ≫ spMap C.b) x
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hbot : Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) = ⊥ := by
    have hc := congrArg PrimeSpectrum.asIdeal hpt
    change Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) = Ideal.comap C.b _ at hc
    haveI := ((pullback.snd C.z (spMap C.b)) (C.iF x)).isPrime
    rw [hc, Ideal.eq_bot_of_prime ((pullback.snd C.z (spMap C.b)) (C.iF x)).asIdeal]
    exact Ideal.comap_bot_of_injective _ C.inj
  have hunit : ∀ y : nonZeroDivisors C.o, IsUnit (φ.hom y) := fun y => by
    by_contra hy
    have hm : (y : C.o) ∈ Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) := (IsLocalRing.mem_maximalIdeal _).2 hy
    rw [hbot, Ideal.mem_bot] at hm
    exact nonZeroDivisors.ne_zero y.2 hm
  let ψF : c.F →+* O := IsLocalization.lift (M := nonZeroDivisors C.o) (S := c.F) hunit
  have hψF : ψF.comp C.b = φ.hom := IsLocalization.lift_comp hunit
  have w : g ≫ C.z = Spec.map (CommRingCat.ofHom ψF) ≫ spMap C.b := by
    rw [← hφ]
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (RingHom.congr_fun hψF a).symm
  let g' : Sp O ⟶ pullback C.z (spMap C.b) := pullback.lift g _ w
  have hg'1 : g' ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) := (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  have hcl : g' (IsLocalRing.closedPoint O) ∈ Set.range C.iF := ⟨x, hinj (by
    change (C.iF ≫ pullback.fst _ _) x = (g' ≫ pullback.fst _ _) _
    rw [hg'1]; exact hx)⟩
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    haveI := C.iF_open
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map g'.continuous).mem_open C.iF.isOpenEmbedding.isOpen_range hcl
  haveI := C.iF_open
  refine ⟨IsOpenImmersion.lift C.iF g' hrange, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hg'1]

theorem isNoetherianRing_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (Y : RatModel o Ω)
    (z : Y.Z), IsNoetherianRing (Y.O z) := by
  intro o Ω _ _ _ _ Y z
  haveI := Y.lft
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  exact isNoetherianRing_of_ringEquiv _ (Y.stalkEquiv z)

set_option maxHeartbeats 4000000 in

theorem exists_action_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ wi : UWit X₁, ∃ (f : 𝓞 E → (out.G ⟶ out.G)) (ψ : wi.G.left ⟶ out.G.left), (∀ a, IsMonHom (f a)) ∧ IsGrpPullback wi.G out.G Y.pt ψ ∧ (∀ (T : Scheme.{0}) (w : T ⟶ wi.G.left), ∃ x' : T ⟶ pullback X₁.ρ.P.A.hom out.u₀, x' ≫ out.φ = w ≫ ψ ∧ x' ≫ pullback.fst _ _ = w ≫ wi.α) ∧ (∀ (a : 𝓞 E) (e : wi.G ⟶ wi.G), e.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e.left ≫ ψ = ψ ≫ (f a).left) ∧ ∀ (K : Type) [Field K] (s : Sp K ⟶ Y.Z) (y : Sp K ⟶ Xo.XF c), s ≫ r = y ≫ C.i → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G s γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hr wi

  have hrange : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hO.ne (x := w) trivial
  let xU : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hrange
  have hxU : xU ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hu₀ : xU ≫ out.u₀ = spMap X₁.S.R.val.toRingHom := out.u₀_gen xU hxU
  have wℓ : wi.α ≫ X₁.ρ.P.A.hom = (wi.G.hom ≫ xU) ≫ out.u₀ := by
    rw [Category.assoc, hu₀]; exact wi.hα.1.w
  let ℓ : wi.G.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift wi.α (wi.G.hom ≫ xU) wℓ
  have hℓα : ℓ ≫ pullback.fst _ _ = wi.α := pullback.lift_fst _ _ _
  have hℓ : IsGrpPullback wi.G ((Over.pullback out.u₀).obj X₁.ρ.P.A) xU ℓ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (wi.hα.congr hu₀.symm hℓα.symm)
      (pullback.lift_snd _ _ _)
  let ψ : wi.G.left ⟶ out.G.left := ℓ ≫ out.φ
  have hψ : IsGrpPullback wi.G out.G Y.pt ψ := (hℓ.comp out.cart).congr hxU rfl

  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c (Sp X₁.Ω₁) X₁.uΩ wi.G wi.β wi.hβ
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hψ (isGrpPullback_pullback out.G Y.pt)
  haveI := he
  have hf' : ∀ a, IsMonHom (e.inv ≫ f₀ a ≫ e.hom) := fun a => by
    haveI := (hf₀ a).1
    infer_instance
  have hF : ∀ a, ∃ F : out.G ⟶ out.G, IsMonHom F ∧ (Over.pullback Y.pt).map F = e.inv ≫ f₀ a ≫ e.hom :=
    fun a => (out.endo _ (hf' a)).exists
  choose F hFm hFe using hF
  have hmap : ∀ {S' : Scheme.{0}} (q : S' ⟶ Y.Z) (a : 𝓞 E),
      ((Over.pullback q).map (F a)).left ≫ pullback.fst out.G.hom q = pullback.fst out.G.hom q ≫ (F a).left :=
    fun q a => pullback.lift_fst _ _ _
  have hei : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have gen₀ : ∀ a, (f₀ a).left ≫ ψ = ψ ≫ (F a).left := fun a => by
    have key : e.hom.left ≫ ((Over.pullback Y.pt).map (F a)).left = (f₀ a).left ≫ e.hom.left := by
      rw [hFe a, Over.comp_left, Over.comp_left, ← Category.assoc, hei, Category.id_comp]
    calc (f₀ a).left ≫ ψ = ((f₀ a).left ≫ e.hom.left) ≫ pullback.fst _ _ := by rw [← heψ, Category.assoc]
      _ = (e.hom.left ≫ ((Over.pullback Y.pt).map (F a)).left) ≫ pullback.fst _ _ := by rw [key]
      _ = ψ ≫ (F a).left := by rw [Category.assoc, hmap, ← Category.assoc, heψ]
  have uniq : ∀ (a : 𝓞 E) (e' : wi.G ⟶ wi.G), e'.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e' = f₀ a :=
    fun a e' h => Over.OverMorphism.ext (wi.hβ.1.hom_ext (h.trans (hf₀ a).2.symm) (by rw [Over.w, Over.w]))
  refine ⟨F, ψ, hFm, hψ, fun T w => ⟨w ≫ ℓ, Category.assoc _ _ _, by rw [Category.assoc, hℓα]⟩,
    fun a e' h => (uniq a e' h) ▸ gen₀ a, ?_⟩

  intro K _ s y hsy tK ⟨mm⟩
  haveI : IsNoetherianRing X₁.o₁ := by haveI := X₁.ar.ded; infer_instance
  obtain ⟨z₀, j, s', hj, hs', hjz, hsz⟩ := exists_factor_localRing _ _ Y K s
  haveI := isNoetherianRing_O _ _ Y z₀
  haveI := RatModel.isIntegrallyClosed_O hO.normal z₀
  have hpt : (j ≫ r) (IsLocalRing.closedPoint (Y.O z₀)) = C.i (y (IsLocalRing.closedPoint K)) := by
    change r (j (IsLocalRing.closedPoint (Y.O z₀))) = _
    rw [hjz, ← hsz (IsLocalRing.closedPoint K)]
    change (s ≫ r) _ = (y ≫ C.i) _
    rw [hsy]
  obtain ⟨v, hv⟩ := exists_factor_i E H Dw l Xo c C (Y.O z₀) (j ≫ r) ⟨_, hpt.symm⟩
  haveI := C.isPreimmersion_i
  have hsv : s' ≫ v = y := (cancel_mono C.i).1 (by rw [Category.assoc, ← hv, ← Category.assoc, hs', hsy])
  have hgv : spMap (algebraMap (Y.O z₀) X₁.Ω₁) ≫ v = X₁.uΩ :=
    (cancel_mono C.i).1 (by rw [Category.assoc, ← hv, ← Category.assoc, hj, hr])
  haveI : IsCommMonObj ((Over.pullback j).obj out.G) := Functor.isCommMonObj_obj
  have hAb : IsAbelianScheme ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G) :=
    PolPull.isAbelianScheme_of_isGrpPullback (Obj.toPolAV Xo.univ).isAb (isGrpPullback_pullback _ _)
  have hSe := IsSemiAbelian.pullback j out.G out.semi
  have wa : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (algebraMap (Y.O z₀) X₁.Ω₁)) ≫ v ≫ pullback.fst _ _ := by
    rw [wi.hβ.1.w, ← hgv]; simp only [Category.assoc]
  let aa := pullback.lift _ _ wa
  have haa : aa ≫ pullback.fst _ _ = wi.β := pullback.lift_fst _ _ _
  have ha : IsGrpPullback wi.G ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G)
      (spMap (algebraMap (Y.O z₀) X₁.Ω₁)) aa :=
    (isGrpPullback_pullback Xo.univ.t.G _).cancel (wi.hβ.congr (by rw [← hgv, Category.assoc]) haa.symm)
      (pullback.lift_snd _ _ _)
  have wg : ψ ≫ out.G.hom = (wi.G.hom ≫ spMap (algebraMap (Y.O z₀) X₁.Ω₁)) ≫ j := by
    rw [hψ.1.w, Category.assoc, hj]
  let gg := pullback.lift _ _ wg
  have hgg : gg ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hg : IsGrpPullback wi.G ((Over.pullback j).obj out.G) (spMap (algebraMap (Y.O z₀) X₁.Ω₁)) gg :=
    (isGrpPullback_pullback out.G j).cancel (hψ.congr hj.symm hgg.symm) (pullback.lift_snd _ _ _)
  obtain ⟨i, hi, hai, hLi, hEi⟩ := GlobalTheory.T.iso_abelianScheme_semiAbelian_of_common_genericFibre (Y.O z₀) _ ((Over.pullback j).obj out.G) hAb hSe X₁.Ω₁ wi.G aa gg ha hg
  haveI := hi
  obtain ⟨f₁, hf₁, hT⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c (Sp (Y.O z₀)) v ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G) (pullback.fst _ _)
    (isGrpPullback_pullback Xo.univ.t.G (v ≫ pullback.fst _ _))
  have mm' : SABMap tK Xo.univ.t ((s' ≫ v) ≫ pullback.fst _ _) := hsv ▸ mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hactγ⟩ := hT (Sp K) s' tK mm'
  refine ⟨γ₀ ≫ i.hom.left ≫ pullback.fst out.G.hom j, ?_, ?_, ?_⟩
  · exact (hγ₀.comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback out.G j))).congr
      (by rw [Category.id_comp, hs']) rfl
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hOL := out.L.isLB
    have sA : LBIso (X₁.ρ.P.L.pull wi.α) (out.L.L.pull ψ) :=
      GenSpread.lbIso_pull_comp ℓ hℓα.symm rfl (LBIso.symm ⟨out.w, out.w_gen⟩)
    have sB : LBIso (Xo.univ.t.PP.L.pull wi.β) (out.L.L.pull ψ) :=
      LBIso.trans (pull_isLB hU _) (pull_isLB hP _) (pull_isLB hOL _) wi.hL.symm sA
    have sC : LBIso ((Xo.univ.t.PP.L.pull (pullback.fst _ _)).pull aa)
        ((out.L.L.pull (pullback.fst out.G.hom j)).pull gg) :=
      LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB (pull_isLB hOL _) _)
        (GenSpread.lbIso_pull_pull hU aa haa.symm).symm
        (LBIso.trans (pull_isLB hU _) (pull_isLB hOL _) (pull_isLB (pull_isLB hOL _) _) sB
          (GenSpread.lbIso_pull_pull hOL gg hgg.symm))
    have sD := hLi _ _ (pull_isLB hU _) (pull_isLB hOL _) sC
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hOL _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB (pull_isLB hOL _) _) _) (pull_isLB hOL _)
        (GenSpread.lbIso_pullback sD γ₀)
        (LBIso.trans (pull_isLB (pull_isLB (pull_isLB hOL _) _) _) (pull_isLB (pull_isLB hOL _) _) (pull_isLB hOL _)
          (GenSpread.lbIso_pull_pull (pull_isLB hOL _) γ₀ rfl).symm
          (GenSpread.lbIso_pull_pull hOL (γ₀ ≫ i.hom.left) (Category.assoc _ _ _).symm).symm))
  · intro a
    have h1 : (f₀ a).left ≫ aa = aa ≫ (f₁ a).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, haa, Category.assoc, (hf₁ a).2, ← Category.assoc, haa, (hf₀ a).2]
      · have w1 := Over.w (f₁ a)
        have w0 := Over.w (f₀ a)
        erw [Category.assoc, pullback.lift_snd, Category.assoc, w1, pullback.lift_snd, ← Category.assoc, w0]
    have h2 : (f₀ a).left ≫ gg = gg ≫ ((Over.pullback j).map (F a)).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hmap, hgg, ← Category.assoc gg, hgg, gen₀]
      · have w1 := Over.w ((Over.pullback j).map (F a))
        have w0 := Over.w (f₀ a)
        erw [Category.assoc, pullback.lift_snd, Category.assoc, w1, pullback.lift_snd, ← Category.assoc, w0]
    have h3 := congrArg Over.Hom.left (hEi (f₁ a) ((Over.pullback j).map (F a)) (f₀ a) h1 h2)
    rw [Over.comp_left, Over.comp_left] at h3
    rw [← Category.assoc, hactγ a]
    simp only [Category.assoc]
    rw [← Category.assoc (f₁ a).left, h3, Category.assoc, hmap]

end GlobalTheory.UPoinc.ActField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPositivePullbackGenericallyEtale
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.SemiPosUp

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem levi_pull_nonneg {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {D D' : ℕ} {B : LB X}
    (φ : Weight p σ B) (hC : φ.IsCInf) (hSP : φ.SemiPosReg D) (i : (B.pull π).ι)
    (c : AlgChart q σ D') {y : CxPts q σ} (hy : y ∈ c.e.source ∩ ptsIn q σ ((B.pull π).U i))
    (c0 : AlgChart p σ D) (h0 : PtsOver.map π hπ (spMap σ) y ∈ c0.e.source) (ξ : Fin D' → ℂ) :
    0 ≤ (leviV D' (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re := by
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U :=
    GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

theorem semiPos_pull_of_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  intro k _ X Y _ _ p q D hp hq π hπ V hV he L hL
  have := hq.isDomain
  have := hq.finite
  obtain ⟨T, hT, hηT, hch⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k X p D hp
  let U : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨v, hv⟩ := hV
  obtain ⟨v', -, hv'⟩ := Flat.generalizingMap (V.ι ≫ π)
    (genericPoint_specializes ((V.ι ≫ π) ⟨v, hv⟩))
  have hW : ((π ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
    refine ⟨V.ι v', ?_⟩
    show π (V.ι v') ∈ Tᶜ
    rw [← Scheme.Hom.comp_apply, hv']
    exact hηT
  intro σ
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  intro i
  refine GlobalTheory.SemiPosBir.PosOn.of_inter hσ (isOpen_ptsIn _) ((L.cInf σ).pull π hπ i) hW ?_
  rintro c y ⟨hyc, hyS, hyW⟩ ξ
  obtain ⟨c0, h0⟩ := hch σ (PtsOver.map π hπ (spMap σ) y) (mem_ptsIn.1 hyW)
  exact levi_pull_nonneg π hπ (L.φ σ) (L.cInf σ) (hL σ) i c ⟨hyc, hyS⟩ c0 h0 ξ

end GlobalTheory.SemiPosUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortGeneratorSectionsSmallShiftedFubiniStudy
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem smallSec_shift_of_isShortGen : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → ∀ (j : Fin n) (hj : w j ∈ W), s ⟨w j, hj⟩ ∈ (L.shift (fun _ => t) (fun _ => rfl)).smallSec := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev n w abelian₂ t hw ht j hj τ y
  obtain ⟨N, n', b, g, A, c, gw, hF, hgw, hb, hφ⟩ := hM.fs
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ :=
    ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp τ⟩
  refine (le_of_eq (GlobalTheory.HermLB.nsq_shift L (fun _ => t) (fun _ => rfl)
    (GlobalTheory.CxPts.secVal p _ (s ⟨w j, hj⟩)) y)).trans ?_
  set i := GlobalTheory.CxPts.pick ((L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB) y with hi_def
  have hi := GlobalTheory.CxPts.mem_pick ((L.φ (σ.comp (algebraMap (𝓞 K) K))).isLB) y
  rw [GlobalTheory.Weight.nsq_eq _ (GlobalTheory.CxPts.secVal_mem _) hi, GlobalTheory.CxPts.secVal_apply, hφ σ i y]
  set ℓ : W → ℂ := fun x => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR y.1 (L.B.U i) ((s x).f i) with hℓ
  have hlin : ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) →
      ℓ x = ∑ k, σ (β k : K) * ℓ (u k) := fun m β u x hx =>
    GlobalTheory.T.valR_imageModelSection_semilinear K V Ω Nm W ev D X p L ψ s hM hev _ i y hi m β u x hx
  have hbd := GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq K V Nm W N n' b g A c gw σ ℓ hF hgw hb hlin ⟨w j, hj⟩
  set S := ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * ℓ (gw k)‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hev' : GlobalTheory.CxPts.ev p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i) ((s ⟨w j, hj⟩).f i) y = ℓ ⟨w j, hj⟩ := rfl
  rw [hev']
  have hNm0 : 0 ≤ Nm σ (w j) := by
    rw [← hF.norm σ (w j)]; exact Real.sqrt_nonneg _
  have hNm : Nm σ (w j) ≤ abelian₂ := hw.le j σ
  have hLam0 : 0 < abelian₂ := lt_of_lt_of_le one_pos hw.one_le
  have hLt : abelian₂ ≤ Real.exp t := (Real.log_le_iff_le_exp hLam0).1 ht
  have hLam2 : abelian₂ ^ 2 * Real.exp (-(2 * t)) ≤ 1 := by
    have h1 : abelian₂ ^ 2 ≤ Real.exp t ^ 2 := pow_le_pow_left₀ hLam0.le hLt 2
    have h2 : Real.exp t ^ 2 * Real.exp (-(2 * t)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
    calc abelian₂ ^ 2 * Real.exp (-(2 * t)) ≤ Real.exp t ^ 2 * Real.exp (-(2 * t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := h2
  rcases hS0.eq_or_lt with h0 | hpos
  · have : ‖ℓ ⟨w j, hj⟩‖ ^ 2 ≤ 0 := by simpa [← h0] using hbd
    have hz : ‖ℓ ⟨w j, hj⟩‖ ^ 2 = 0 := le_antisymm this (sq_nonneg _)
    rw [hz]; simp
  · rw [Real.exp_neg, Real.exp_log hpos]
    have h3 : ‖ℓ ⟨w j, hj⟩‖ ^ 2 * S⁻¹ ≤ abelian₂ ^ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      calc ‖ℓ ⟨w j, hj⟩‖ ^ 2 ≤ Nm σ (w j) ^ 2 * S := hbd
        _ ≤ abelian₂ ^ 2 * S := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNm0 hNm 2) hS0
    calc ‖ℓ ⟨w j, hj⟩‖ ^ 2 * S⁻¹ * Real.exp (-(2 * t)) ≤ abelian₂ ^ 2 * Real.exp (-(2 * t)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ ≤ 1 := hLam2

end GlobalTheory.ImageModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelClassifiedAtPrimeSpreadsBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegSpread

theorem spread_point : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := GlobalTheory.T.exists_away_spread_point_localization_atPrime

theorem spread_iso : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := GlobalTheory.T.exists_spread_of_pullbacks_alt

theorem spMap_comp_eq {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (a : A →+* C) (b : C →+* D) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem classified_basicOpen : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)) (𝔭 : Ideal R) [𝔭.IsPrime], c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) → ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧ SiegPB c' F.univ f) → ∃ r ∉ 𝔭, ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.Away r)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.Away r))) → ∃ f : Sp (Localization.Away r) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ SiegPB c' F.univ f := by
  intro g n hg hn hodd F R _ _ β c 𝔭 _ hc H
  obtain ⟨c₀, hc₀⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _)
    (Sp R) (Sp (Localization.AtPrime 𝔭)) (spMap β) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))
    (spMap (algebraMap R (Localization.AtPrime 𝔭))) rfl (by rw [spMap_comp_eq, spMap_comp_eq, RingHom.comp_id])).1 c
  obtain ⟨f₀, hf₀s, hf₀⟩ := H c₀ hc₀
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : LocallyOfFinitePresentation F.s := inferInstance
  obtain ⟨r₀, hr₀, ι₀, f₁, hι₀, hf₁s, hf₁⟩ := spread_point (cycAway n) F.X F.s R β 𝔭 f₀ hf₀s
  obtain ⟨r, hr, κ, d', hκ, hd'c, hd'u⟩ := spread_iso g n (cycAway n) (zetaAway n) R β 𝔭 c F.X F.s F.univ r₀ ι₀ f₁ c₀
    hr₀ hι₀ hf₁s hc₀ (hf₁ ▸ hf₀)
  refine ⟨r, hr, fun c' hc' => ⟨spMap κ ≫ f₁, ?_, ?_⟩⟩
  · rw [Category.assoc, hf₁s, spMap_comp_eq, ← RingHom.comp_assoc, hκ]
  · have h₁ : SiegPB c' c (𝟙 _ ≫ spMap (algebraMap R (Localization.Away r))) := by rwa [Category.id_comp]
    have h₂ := GlobalTheory.SiegelPullComp.pb_cancel hd'c h₁
    have h₃ := GlobalTheory.SiegelPullComp.pb_comp hd'u h₂
    rwa [Category.id_comp] at h₃

end GlobalTheory.SiegSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliIntegralNormalLocallyNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), IsIntegral F.X ∧ Geo.Tor.IsNormalScheme F.X ∧ IsLocallyNoetherian F.X := by
  first | exact @GlobalTheory.SiegelIntegral.integral_normal_noetherian | exact GlobalTheory.SiegelIntegral.integral_normal_noetherian | (intros; apply GlobalTheory.SiegelIntegral.integral_normal_noetherian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleTransportedWeilDatumDoubledTargetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelRule_transported_weilDatum_doubledTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS : (AE D)ˣ →* Circle), IsHeckeChar D χS → ResEta D χS S.rank →
      ∀ (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ωd omp →
            GlobalTheory.WeilM.SiegelRule (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JB)
              (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) χS
              ((GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id)
              (omp.comp (MonoidHom.inl _ _)) := by
  first | exact @GlobalTheory.DblTargetSiegel.siegelRule_dblTarget | exact GlobalTheory.DblTargetSiegel.siegelRule_dblTarget | (intros; apply GlobalTheory.DblTargetSiegel.siegelRule_dblTarget <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickening
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smooth_lifts_over_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hsm
  obtain ⟨C₀, _, _, i, r, hstd, hri⟩ := GlobalTheory.T.exists_standardSmooth_retract_of_smooth R₀ B₀ hsm
  obtain ⟨C, _, _, p', hs', hp', hker', hC⟩ := GlobalTheory.T.standardSmooth_lift_over_sqZero_thickening R R₀ I hI π hπ hk C₀ hstd
  exact GlobalTheory.T.exists_smoothLift_of_retract_squareZero R R₀ I hI π hπ hk C C₀ p' hs' hp' hker' B₀ i r hri

end GlobalTheory
end

