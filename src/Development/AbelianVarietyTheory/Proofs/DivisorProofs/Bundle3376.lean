import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3366
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastTer
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gens

theorem res_ι_app {X : Scheme.{0}} (U : X.Opens) (V : U.toScheme.Opens) (x : Γ(X, U.ι ''ᵁ V))
    (hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V)) :
    (U.toScheme.presheaf.map (homOfLE hle).op).hom ((U.ι.app (U.ι ''ᵁ V)).hom x) = x := by
  have h1 := Scheme.Hom.appIso_hom U.ι V
  rw [Scheme.Opens.ι_appIso] at h1
  have h3 := congrArg (fun f => f.hom x) h1
  simp only [Iso.refl_hom, CommRingCat.hom_comp, RingHom.comp_apply] at h3
  exact (congrArg (fun f => (U.toScheme.presheaf.map f).hom ((U.ι.app (U.ι ''ᵁ V)).hom x))
    (Subsingleton.elim (homOfLE hle).op _)).trans h3.symm

theorem gs_ι {X : Scheme.{0}} (U : X.Opens) (j : X ⟶ U.toScheme) (hj : j ≫ U.ι = 𝟙 X) (V : U.toScheme.Opens)
    (x : Γ(X, U.ι ''ᵁ V)) (y : X) (hy : j y ∈ V) : gs j y V x = gs (𝟙 X) y (U.ι ''ᵁ V) x := by
  have hle : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V) := (Scheme.Hom.preimage_image_eq U.ι V).ge
  have e := gs_res j y hle hy ((U.ι.app (U.ι ''ᵁ V)).hom x)
  rw [res_ι_app] at e
  rw [e, gs_pull j U.ι y _ (hle hy), hj]

theorem gens : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R), ∃ N : ℕ, 1 ≤ N ∧ ∃ (Ix : Type) (U : Ix → Q.P.A.left.Opens) (M : Ix → Type) (r : ∀ i, M i → Γ(Q.P.A.left, U i)), (⨆ i, U i = ⊤) ∧ (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE ⊤ (U i) (fun _ _ => trivial)).hom (r i))) ∧ ∀ i j, ∃ σ σ' : Q.SecB N 0, ∀ z ∈ U i, ∀ J, Good Q.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z (U i) (r i j) * sval σ' (𝟙 _) z J := by
  intro R _ _ Q
  obtain ⟨N, hN, M, s, hcov, hs⟩ := Q.P.ample ⊤ (isAffineOpen_top _)
  choose haff r hr hsurj using hs
  let ιU := (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).ι
  let j : Q.P.A.left ⟶ (Q.P.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)).toScheme := Q.P.A.left.topIso.inv
  have hj : j ≫ ιU = 𝟙 _ := by
    show Q.P.A.left.topIso.inv ≫ (⊤ : Q.P.A.left.Opens).ι = _
    rw [← Scheme.topIso_hom, Iso.inv_hom_id]
  have hιj : ιU ≫ j = 𝟙 _ := by
    show (⊤ : Q.P.A.left.Opens).ι ≫ Q.P.A.left.topIso.inv = _
    rw [← Scheme.topIso_hom, Iso.hom_inv_id]; rfl
  have hjι : ∀ w, j (ιU w) = w := fun w => by show (ιU ≫ j).base w = w; rw [hιj]; rfl
  have hfe : FormEq (K := Fin N) (fun _ => 𝟙 Q.P.A.left) (fun _ => (1 : ℤ)) (Q.famφB 0) (DegPre.famε N) := by
    intro U _ h
    refine Eq.trans ?_ (GlobalTheory.Mum.OriginSec.formEq_zero Q N U h)
    simp [Finset.prod_const, Fin.prod_univ_one]
  have hσ : ∀ a, ∃ σ : Q.SecB N 0, ∀ (z : Q.P.A.left) J, Good Q.P.L z J → sval σ (𝟙 _) z J = sval (s a) j z J := by
    intro a
    obtain ⟨s', hs'⟩ := GlobalTheory.UU.exists_pullSec_sval
      (s a : LB.Sec (LB.LinComb Q.P.L (K := Fin N) (fun _ => ιU) (fun _ => (1 : ℤ)))) j
      (fun _ : Fin N => 𝟙 Q.P.A.left) (fun _ => hj)
    obtain ⟨σ, hσ⟩ := exists_sec Q.P.isLB hfe s'
    exact ⟨σ, fun z J hJ => (hσ _ _ z J hJ).trans ((hs' _ _ z J hJ).trans (by rw [Category.id_comp]))⟩
  choose σ hσv using hσ
  refine ⟨N, hN, Fin (M + 1), fun a => ιU ''ᵁ nonzeroLocus (s a), fun _ => Fin (M + 1), fun a b => r a b, ?_, ?_, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show j y ∈ ⨆ a, nonzeroLocus (s a) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ⟨j y, ha, show (j ≫ ιU).base y = y by rw [hj]; rfl⟩⟩
  · exact fun a => (haff a).image_of_isOpenImmersion ιU
  · intro a
    have key : ∀ (U U' : (Spec (CommRingCat.of R)).Opens) (_ : U = U') (W : Q.P.A.left.Opens) e e'
        (rr : Fin (M + 1) → Γ(Q.P.A.left, W)),
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U' W e').hom rr) →
        Function.Surjective (MvPolynomial.eval₂Hom (Q.P.A.hom.appLE U W e).hom rr) := by
      rintro _ _ rfl _ _ _ _ h; exact h
    have e2 := morphismRestrict_appLE Q.P.A.hom ⊤ ⊤ (nonzeroLocus (s a)) le_top
    have h' := (congrArg (fun g => Function.Surjective (MvPolynomial.eval₂Hom (CommRingCat.Hom.hom g) (r a))) e2).mp (hsurj a)
    exact key ⊤ ((⊤ : (Spec (CommRingCat.of R)).Opens).ι ''ᵁ ⊤) (Scheme.Opens.ι_image_top _).symm
      (ιU ''ᵁ nonzeroLocus (s a)) _ _ (r a) h'
  · intro a b
    refine ⟨σ b, σ a, fun z hz J hJ => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hσv _ _ _ hJ, hσv _ _ _ hJ]
    have hm := hJ.mem (fun _ : Fin N => ιU) j
    have hw' : j (ιU w) ∈ nonzeroLocus (s a) := by rw [hjι]; exact hw
    refine ⟨(GlobalTheory.Mum.OriginSec.isUnit_sval_iff' (s a) j (ιU w) hJ).2 hw', ?_⟩
    have hm' : j (ιU w) ∈ nonzeroLocus (s a) ⊓ (powOver Q.P.A Q.P.L ⊤ N).U (fun _ => J (j ≫ ιU)) := ⟨hw', hm⟩
    have e := congrArg (gs j (ιU w) _) (hr a b (fun _ => J (j ≫ ιU)))
    rw [gs_res _ _ _ hm', gs_mul _ _ _ hm', gs_res _ _ _ hm', gs_res _ _ _ hm'] at e
    rw [gs_ι _ j hj _ (r a b) _ hw'] at e
    exact e
end GlobalTheory.Heat.Gens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapUniquenessStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_map_uniqueness : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp (algebraMap A _)) (φ u) := by
  first | exact @GlobalTheory.FlatModel.flatSec_unit_at_bdry_height_one | exact GlobalTheory.FlatModel.flatSec_unit_at_bdry_height_one | (intros; apply GlobalTheory.FlatModel.flatSec_unit_at_bdry_height_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterNumRedCloPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.VdmRec

namespace GlobalTheory.DegRec

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

theorem topSelf_cxFibre (p : X ⟶ Sp k) [IsProper (p ≫ spMap (Int.castRingHom k))] {L : LB X} (hL : L.IsLB) (n : ℕ) :
    topSelfIntersection ℂ (L.pull (cxFibre.fst p)) n = topSelfIntersection ℚ (L.pull (ratFibre.fst p)) n := by
  have e : spMap (algebraMap ℚ ℂ) ≫ spMap (Int.castRingHom ℚ) = spMap (Int.castRingHom ℂ) := by
    rw [← Spec.map_comp]
    congr 1
  have H₀ : IsPullback (cxFibre.fst p) (cxFibre.snd p) (p ≫ spMap (Int.castRingHom k))
      (spMap (algebraMap ℚ ℂ) ≫ spMap (Int.castRingHom ℚ)) := by
    rw [e]
    exact IsPullback.of_hasPullback _ _
  let π := (ratFibre.isPullback p).lift (cxFibre.fst p) (cxFibre.snd p ≫ spMap (algebraMap ℚ ℂ))
    (by rw [Category.assoc]; exact H₀.w)
  have hπ : π ≫ ratFibre.fst p = cxFibre.fst p := IsPullback.lift_fst _ _ _ _
  have H : IsPullback π (cxFibre.snd p) (ratFibre.snd p) (spMap (algebraMap ℚ ℂ)) :=
    IsPullback.of_right (hπ ▸ H₀) (IsPullback.lift_snd _ _ _ _) (ratFibre.isPullback p)
  have : IsProper (ratFibre.snd p) := MorphismProperty.of_isPullback (P := @IsProper) (ratFibre.isPullback p) ‹_›
  have hR := pull_isLB hL (ratFibre.fst p)
  refine Eq.trans ?_ (FieldChangeInter.interNum_pull H (L := fun _ : Fin n => L.pull (ratFibre.fst p)) fun _ => hR)
  refine interNum_congr_cls ℂ _ (fun _ => pull_isLB hL _) (fun _ => pull_isLB hR _) fun _ => ?_
  rw [cls_pull hR, cls_pull hL, cls_pull hL, ← pull_comp, hπ]

theorem charZero_iff (g : Y ⟶ X) (y : Y) : CharZero (X.residueField (g y)) ↔ CharZero (Y.residueField y) :=
  (g.residueFieldMap y).hom.charZero_iff (g.residueFieldMap y).hom.injective

theorem charZero_ratFibre (p : X ⟶ Sp k) (y : ratFibre p) : CharZero ((ratFibre p).residueField y) :=
  ((((ratFibre p).Γevaluation y).hom.comp (algebraMap ℚ Γ(ratFibre p, ⊤))).charZero_iff (RingHom.injective _)).1
    inferInstance

theorem isIntegral_ratFibre (p : X ⟶ Sp k) [IsIntegral X] [Nonempty (ratFibre p)] : IsIntegral (ratFibre p) := by
  have h₁ : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  have : IsPreimmersion (ratFibre.fst p) := MorphismProperty.of_isPullback (ratFibre.isPullback p).flip h₁
  have := RatDegZeros.flat_fst p
  exact ratFibre.isIntegral_of_flat_preimmersion (ratFibre.fst p)

theorem redι_genericPoint (z : X) : redι (clo z) (genericPoint _) = z := by
  have hcl : closure ({redι (clo z) (genericPoint _)} : Set X) = closure {z} := by
    rw [← Set.image_singleton, (redι (clo z)).isClosedEmbedding.closure_image_eq,
      (genericPoint_spec _).def, Set.image_univ, range_redι]
    rfl
  exact (inseparable_iff_closure_eq.2 hcl).eq

theorem isEmpty_ratFibre (p : X ⟶ Sp k) {z : X} (hz : ¬ CharZero (X.residueField z)) :
    IsEmpty (ratFibre (redι (clo z) ≫ p)) := by
  by_contra hn
  have : Nonempty (ratFibre (redι (clo z) ≫ p)) := not_isEmpty_iff.1 hn
  have := isIntegral_ratFibre (redι (clo z) ≫ p)
  have h := (charZero_iff (ratFibre.fst (redι (clo z) ≫ p)) _).2 (charZero_ratFibre _ (genericPoint _))
  rw [RatDegZeros.fst_genericPoint, ← charZero_iff (redι (clo z)), redι_genericPoint] at h
  exact hz h

theorem degAt_eq (p : X ⟶ Sp k) [IsProper (p ≫ spMap (Int.castRingHom k))] {L : LB X} (hL : L.IsLB) (z : X) (n : ℕ) :
    degAt p L z n = topSelfIntersection ℚ ((L.pull (redι (clo z))).pull (ratFibre.fst (redι (clo z) ≫ p))) n :=
  haveI : IsProper ((redι (clo z) ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [Category.assoc]; infer_instance
  topSelf_cxFibre _ (pull_isLB hL _) n

theorem degAt_eq_zero (p : X ⟶ Sp k) [IsProper (p ≫ spMap (Int.castRingHom k))] {L : LB X} (hL : L.IsLB) {z : X}
    (hz : ¬ CharZero (X.residueField z)) (n : ℕ) : degAt p L z n = 0 := by
  have := isEmpty_ratFibre p hz
  rw [degAt_eq p hL]
  exact interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _) fun _ => pull_isLB (pull_isLB hL _) _

theorem range_eq_closure (u : Y ⟶ X) [IsClosedImmersion u] [IsIntegral Y] :
    Set.range u = closure {u (genericPoint Y)} := by
  rw [← Set.image_singleton, u.isClosedEmbedding.closure_image_eq, (genericPoint_spec _).def, Set.image_univ]

theorem degAt_fst (p : X ⟶ Sp k) [IsProper (p ≫ spMap (Int.castRingHom k))] {L : LB X} (hL : L.IsLB) (x : ratFibre p)
    (n : ℕ) : degAt p L (ratFibre.fst p x) n = interNumRed ℚ (clo x) fun _ : Fin n => L.pull (ratFibre.fst p) := by
  set i := redι (clo (ratFibre.fst p x)) with hi
  have hg : i (genericPoint _) = ratFibre.fst p x := redι_genericPoint _
  have hc : CharZero ((Scheme.IdealSheafData.vanishingIdeal (clo (ratFibre.fst p x))).subscheme.residueField
      (genericPoint _)) := by
    rw [← charZero_iff i, hg, charZero_iff]
    exact charZero_ratFibre p x
  obtain ⟨y, -⟩ := RatDegZeros.mem_range_fst k _ (i ≫ p) _ hc
  have : Nonempty (ratFibre (i ≫ p)) := ⟨y⟩
  have := isIntegral_ratFibre (i ≫ p)
  have : IsClosedImmersion (ratFibre.map p i) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (ratFibre.isPullback_map p i) inferInstance
  have hux : ratFibre.map p i (genericPoint _) = x := by
    apply (RatDegZeros.isIso_stalkMap_and_injective k X p).2
    rw [← Scheme.Hom.comp_apply, ratFibre.map_fst, Scheme.Hom.comp_apply, RatDegZeros.fst_genericPoint, hg]
  have hr : Set.range (ratFibre.map p i) = clo x := by rw [range_eq_closure, hux]; rfl
  rw [degAt_eq p hL, InterModel.interNumRed_eq_interNumOn _ (ratFibre.map p i) _ hr,
    interNumOn_eq_interNum_pull (appTop_algebraΓOfHom _ _ (ratFibre.map_snd p i)) (fun _ => pull_isLB hL _)]
  refine interNum_congr_cls ℚ _ (fun _ => pull_isLB (pull_isLB hL _) _) (fun _ => pull_isLB (pull_isLB hL _) _)
    fun _ => ?_
  rw [cls_pull (pull_isLB hL _), cls_pull (pull_isLB hL _), cls_pull hL, cls_pull hL, ← pull_comp, ← pull_comp,
    ratFibre.map_fst]

theorem interNumRed_clo_pull {κ : Type} [Field κ] [Algebra κ Γ(X, ⊤)] [Algebra κ Γ(Y, ⊤)] (u : Y ⟶ X)
    [IsClosedImmersion u] (hu : ∀ r : κ, u.appTop (algebraMap κ Γ(X, ⊤) r) = algebraMap κ Γ(Y, ⊤) r) (y : Y)
    {ι : Type} [Fintype ι] {L : ι → LB X} (hL : ∀ a, (L a).IsLB) :
    interNumRed κ (clo (u y)) L = interNumRed κ (clo y) fun a => (L a).pull u := by
  have hr : Set.range (redι (clo y) ≫ u) = clo (u y) := by
    rw [range_eq_closure, Scheme.Hom.comp_apply, redι_genericPoint]; rfl
  rw [InterModel.interNumRed_eq_interNumOn _ (redι (clo y) ≫ u) _ hr, interNumOn_comp hu _ hL]
  rfl

theorem mul_topSelf_eq (q : Y ⟶ Sp k) [IsIntegral Y] [IsLocallyNoetherian Y] {n : ℕ} (hq : IsArithVar q (n + 1))
    {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {m : ℕ} (hc : cls M hM = m • cls L hL) (s : M.Sec)
    (hs : genericPoint Y ∈ Out.nonzeroLocus s) :
    (m : ℤ) * topSelfIntersection ℚ (L.pull (ratFibre.fst q)) (n + 1) = ∑ᶠ y : ratFibre q,
      (divOfSec hM s hs).mult (ratFibre.fst q y) * interNumRed ℚ (clo y) fun _ : Fin n => L.pull (ratFibre.fst q) := by
  have := hq.finite
  have := hq.flat
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hq.finite
  obtain ⟨_, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hq.isProjOver
  have hP : IsProjOver (q ≫ spMap (Int.castRingHom k)) := hA.isProjOver _
  have H : IsPullback (ratFibre.fst q) (ratFibre.snd q) (q ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ)) :=
    ratFibre.isPullback q
  have hd : topologicalKrullDim (ratFibre q) = (n + 1 : ℕ) := ratFibre.dim_eq_of_isPullback _ H hq.dim_eq
  have : Nonempty (ratFibre q) := by
    by_contra hn
    have : IsEmpty (ratFibre q) := not_nonempty_iff.1 hn
    have : IsEmpty (IrreducibleCloseds (ratFibre q)) :=
      ⟨fun Z => Z.isIrreducible.nonempty.elim fun x _ => isEmptyElim x⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot] at hd
    exact WithBot.bot_ne_coe hd
  have := isIntegral_ratFibre q
  have hp : IsProjOver (strHom ℚ (ratFibre q)) := by
    rw [ratFibre.strHom_eq]
    exact ProjSpace.isProjOver_of_isPullback_spMap _ H hP
  have : AlgebraicGeometry.IsNoetherian (ratFibre q) := isNoetherian_of_isProjOver hp
  obtain ⟨r, hr, hmult⟩ := MultPull.exists_isRatSec_pull_mult _ _ (ratFibre.fst q) (RatDegZeros.fst_genericPoint k Y q)
    (RatDegZeros.isIso_stalkMap_and_injective k Y q).1 M hM _ (isRatSec_ratOfSec s hs)
  have hL' := pull_isLB hL (ratFibre.fst q)
  have hM' := LB.isLB_pull hM (ratFibre.fst q)
  have key := GlobalTheory.T.rational_section_cycle_formula_projective ℚ (ratFibre q) hp n hd.le _ hM' (fun _ : Fin n => L.pull (ratFibre.fst q)) (fun _ => hL') r hr
  simp only [hmult] at key
  rw [← key]
  have hv := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom ℚ (ratFibre q)) (structureModule (ratFibre q)) hp
    (d := n + 1) (by rw [QCoh.suppDim_structureModule]; exact hd.le)
  have e := hv.interNum_update_of_cls_eq_zsmul (L := fun _ : Fin (n + 1) => L.pull (ratFibre.fst q)) (by simp)
    (fun _ => hL') 0 hM' hL' m (by rw [cls_pull hM, cls_pull hL, hc, map_nsmul, natCast_zsmul])
  rw [Function.update_eq_self_iff.2 rfl] at e
  refine e.symm.trans (congrArg _ ?_)
  funext a
  refine Fin.cases ?_ (fun b => ?_) a
  · simp
  · rw [Function.update_of_ne (Fin.succ_ne_zero b)]; rfl

open NumberField MvPolynomial Filter Topology in
open scoped Classical in

theorem degAt_recursion : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (N : HermLB p), (∀ (z : X) (n : ℕ), ¬ CharZero (X.residueField z) → degAt p N.B z n = 0) ∧ ∀ (m : ℕ) (s : (N.pow m).B.Sec) (z : X) (n : ℕ), topologicalKrullDim (closure ({z} : Set X)) = (n + 2 : ℕ) → z ∈ Out.nonzeroLocus s → (m : ℤ) * degAt p N.B z (n + 1) = ∑ᶠ w, cutMult (N.pow m).isLB s z w * degAt p N.B w n := by
  intro k _ X _ _ p d hX N
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hX.finite
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver).1
  refine ⟨fun z n hz => degAt_eq_zero p N.isLB hz n, fun m s z n hdim hz => ?_⟩
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (redι (clo z))
  have hs : genericPoint _ ∈ Out.nonzeroLocus (GlobalTheory.ZM.RepBC.secPull _ (redι (clo z)) s) := by
    change _ ∈ Out.nonzeroLocus (Cartier.secPull s (redι (clo z)))
    rw [Cartier.nonzeroLocus_secPull]
    change redι (clo z) (genericPoint _) ∈ Out.nonzeroLocus s
    rwa [redι_genericPoint]
  set i := redι (clo z) with hi
  set j := ratFibre.fst (i ≫ p) with hj
  have hinj : Function.Injective (j ≫ i) := by
    rw [Scheme.Hom.comp_base]
    exact i.isClosedEmbedding.injective.comp (RatDegZeros.isIso_stalkMap_and_injective k _ (i ≫ p)).2
  set F : X → ℤ := fun w => cutMult (N.pow m).isLB s z w * degAt p N.B w n with hF
  have hmul (a) : cutMult (N.pow m).isLB s z (i a) = (divOfSec (LB.isLB_pull (N.pow m).isLB i) _ hs).mult a := by
    rw [cutMult, dif_pos hs]
    exact i.isClosedEmbedding.injective.extend_apply _ _ a
  have hsupp : Function.support F ⊆ Set.range (j ≫ i) := fun w hw => by
    have hw' : cutMult (N.pow m).isLB s z w * degAt p N.B w n ≠ 0 := hw
    obtain ⟨a, rfl⟩ : ∃ a, i a = w := by
      by_contra hn
      refine left_ne_zero_of_mul hw' ?_
      rw [cutMult, dif_pos hs]
      exact Function.extend_apply' _ _ _ hn
    have hc : CharZero (X.residueField (i a)) := by
      by_contra hc
      exact right_ne_zero_of_mul hw' (degAt_eq_zero p N.isLB hc n)
    obtain ⟨y, rfl⟩ := RatDegZeros.mem_range_fst k _ (i ≫ p) a ((charZero_iff i a).1 hc)
    exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩
  have hre : ∑ᶠ y, F ((j ≫ i) y) = ∑ᶠ w, F w := by
    rw [← finsum_mem_range hinj, ← finsum_mem_inter_support, Set.inter_eq_right.2 hsupp, finsum_mem_support]
  rw [← hre]
  by_cases hc : CharZero (X.residueField z)
  swap
  · have := isEmpty_ratFibre p hc
    rw [degAt_eq_zero p N.isLB hc, mul_zero, finsum_of_isEmpty]
  have hc' : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme, ⊤) := by
    rw [← redι_genericPoint z, charZero_iff] at hc
    exact (Scheme.Γevaluation _ (genericPoint _)).hom.charZero
  have hq : IsArithVar (i ≫ p) (n + 1) := hX.of_isClosedImmersion i hc' ((topologicalKrullDim_red (clo z)).trans hdim)
  have : IsClosedImmersion (ratFibre.map p i) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (ratFibre.isPullback_map p i) inferInstance
  rw [degAt_eq p N.isLB, mul_topSelf_eq (i ≫ p) hq (pull_isLB N.isLB i) (LB.isLB_pull (N.pow m).isLB i) (m := m)
    (by rw [cls_pull (N.pow m).isLB, cls_pull N.isLB, ← map_nsmul]; exact congrArg _ (cls_lbPow N.isLB m _)) _ hs]
  refine finsum_congr fun y => ?_
  simp only [hF]
  rw [← ratFibre.map_fst, Scheme.Hom.comp_apply, degAt_fst p N.isLB, ← Scheme.Hom.comp_apply, ratFibre.map_fst,
    Scheme.Hom.comp_apply, hmul,
    interNumRed_clo_pull _ (appTop_algebraΓOfHom _ _ (ratFibre.map_snd p i)) y
      (L := fun _ : Fin n => N.B.pull (ratFibre.fst p)) (fun _ => pull_isLB N.isLB _)]
  congr 1
  refine interNum_congr_cls (ι := Fin n) ℚ _ (fun _ => pull_isLB (pull_isLB N.isLB _) _) (fun _ => pull_isLB (pull_isLB N.isLB _) _)
    fun _ => ?_
  rw [cls_pull (pull_isLB N.isLB _), cls_pull (pull_isLB N.isLB _), cls_pull N.isLB, cls_pull N.isLB, ← pull_comp,
    ← pull_comp, ratFibre.map_fst]

end GlobalTheory.DegRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZero
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem IsInv.apply_constFn {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by

  have key : ∀ (U : G.left.Opens) (hU : IsAffineOpen U) (hle : U ≤ O),
      (G.left.presheaf.map (homOfLE hle).op).hom (dd O (constFn G.hom O r)) = 0 := by
    intro U hU hle
    let g : Sp Γ(G.left, U) ⟶ G.left := hU.fromSpec
    let φ : R →+* Γ(G.left, U) := (Spec.preimage (g ≫ G.hom)).hom
    have hφ : g ≫ G.hom = spMap φ := by simp [φ, spMap]
    have hgU : ⊤ ≤ g ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have hgO : ⊤ ≤ g ⁻¹ᵁ O := hgU.trans (g.preimage_mono hle)

    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) =
        (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have hv : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
      (Over.w (tv v)).trans (Category.comp_id _)
    have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
      show _ = spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom
      refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
      rw [hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    let g' : tEpsG (g ≫ G.hom) ⟶ G :=
      Over.homMk (spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g) (Category.assoc _ _ _)
    let v' : tEpsG (g ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2
    have htr : IsTr G φ g v (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩
    have hval := hinv.2 _ φ g _ O (constFn G.hom O r) hφ hgO htr

    have hw : (g' * v').left ≫ G.hom =
        spMap ((algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ) := by
      refine (Over.w (g' * v')).trans ?_
      show spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom = _
      rw [hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
      by_cases hO : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
      · rw [GlobalTheory.ArcPts.SecValue.valR_constFn G.hom _ _ hw O hO r]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [valR, dif_neg hO]
        rfl
    rw [h0, ← GlobalTheory.HolHom.valR_res g hle _ hgU] at hval
    rw [← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom (dd O (constFn G.hom O r)))]
    exact hval.symm
  refine G.left.sheaf.eq_of_locally_eq' (fun k : {U : G.left.Opens // IsAffineOpen U ∧ U ≤ O} => k.1) O
    (fun k => homOfLE k.2.2) ?_ _ 0 fun k => ?_
  · intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩
  · exact (key k.1 k.2.1 k.2.2).trans (map_zero _).symm

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfInterior
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

namespace GlobalTheory.AffOff

theorem isAffineOpen_inf_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, IsAffineOpen (U.1 ⊓ interior Y) := by
  intro E _ _ _ H Dw l Xo c Y h U
  have hs := snc_gen_iff.1 h
  unfold boundary at hs
  set V := interior Y with hVdef
  have key : ∀ y : Y.X, ∃ W : Y.X.Opens, y ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (V.ι ⁻¹ᵁ W) := by
    intro y
    obtain ⟨-, W, hy, n, f, J, -, hI⟩ := hs y
    have e : W.1 ⊓ V = Y.X.basicOpen (∏ i ∈ J, f i) := by
      ext z
      constructor
      · rintro ⟨hW, hV⟩
        by_contra hz
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
          exact hz
        rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
        exact this hV
      · intro hz
        have hW : z ∈ W.1 := Y.X.basicOpen_le _ hz
        refine ⟨hW, by_contra fun hV ↦ ?_⟩
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
          exact hV
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span,
          Scheme.zeroLocus_singleton] at this
        exact this hz
    refine ⟨W.1, hy, W.2, ?_⟩
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm, e]
    exact W.2.basicOpen _
  have : IsAffineHom V.ι := isAffineHom_of_forall_exists_isAffineOpen _ key
  have h2 := U.2.preimage V.ι
  rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at h2
  rwa [inf_comm]

end GlobalTheory.AffOff
end

