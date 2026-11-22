import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0468
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongDvrArcs
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

open GlobalTheory.FlagMod

variable {X : Scheme.{0}}

theorem gs_spMap_eq {A F : Type} [CommRing A] [Field F] (φ : A →+* F) (y : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (z : Sp F) (a : Γ(X, U)) : gs (spMap φ ≫ y) z U a = toStk z (φ (ev y U h a)) := by
  have h' := le_preimage_comp (spMap φ) h
  have e : φ (ev y U h a) = ev (spMap φ ≫ y) U h' a := by rw [ev_spMap φ y U h h']; rfl
  rw [e, gs_eq _ z U (h' trivial)]
  show _ = ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _))
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE h') z trivial _).symm

theorem exists_gen_const {L : LB X} (hL : L.IsLB) {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ X) (k : L.ι)
    (hk : ⊤ ≤ y ⁻¹ᵁ L.U k) (c : Aˣ) : ∃ e : LB.Gen (L.pull y), e.IsGen ∧
      ∀ (F : Type) [Field F] (φ : A →+* F) (z : Sp F),
        (gm (spMap φ) z (LB.wchart L (fun _ : PUnit => y) fun _ => k) (e.s fun _ => k)).val = toStk z (φ c) := by
  obtain ⟨t, ht⟩ := DVR.exists_gen_of_local L hL (fun _ : PUnit => y) (fun _ => 1)
  have hle : ⊤ ≤ LB.wchart L (fun _ : PUnit => y) fun _ => k := fun p hp => Set.mem_iInter.2 fun _ => hk hp
  let C : Γ(Sp A, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom c
  refine ⟨Geo.Tor.scaleGen t (C * res hle (t.s fun _ => k)⁻¹), scaleGen_isGen hL t ht _, fun F _ φ z => ?_⟩
  have e := gm_scaleGen t (C * res hle (t.s fun _ => k)⁻¹) (spMap φ) z (fun _ => k) (hle trivial)
  have e' : gm (spMap φ) z ⊤ (C * res hle (t.s fun _ => k)⁻¹) = gm (spMap φ) z ⊤ C *
      (gm (spMap φ) z (LB.wchart L (fun _ : PUnit => y) fun _ => k) (t.s fun _ => k))⁻¹ :=
    (map_mul _ _ _).trans (congrArg _ ((gm_res _ z hle trivial _).trans (map_inv _ _)))
  refine (congrArg Units.val ((e.trans (congrArg (· * _) e')).trans (inv_mul_cancel_right _ _))).trans ?_
  rw [gm_val _ z ⊤ trivial]
  have e2 := congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  exact congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom e2.symm

theorem pairing_eq (D : EffCartierData X) {Y Z : Scheme.{0}} {y : Y ⟶ X} {t : LB.Gen ((CechPic.dual D.lb).pull y)}
    (ht : t.IsGen) (r : Z ⟶ Y) (z : Z) {i j : D.ι} (hi : (r ≫ y) z ∈ D.U i) (hj : (r ≫ y) z ∈ D.U j) :
    (gm r z (LB.wchart (CechPic.dual D.lb) (fun _ : PUnit => y) fun _ => i) (t.s fun _ => i)).val *
        gs (r ≫ y) z (D.U i) (D.f i) =
      (gm r z (LB.wchart (CechPic.dual D.lb) (fun _ : PUnit => y) fun _ => j) (t.s fun _ => j)).val *
        gs (r ≫ y) z (D.U j) (D.f j) := by
  have hm : (r ≫ y) z ∈ D.U i ⊓ D.U j := ⟨hi, hj⟩
  have e₁ := gen_trans ht r z (j := fun _ => i) (j' := fun _ => j) (Set.mem_iInter.2 fun _ => hi)
    (Set.mem_iInter.2 fun _ => hj)
  have e₂ : trF (L := CechPic.dual D.lb) (fun _ : PUnit => y) (fun _ => 1) r z (fun _ => i) (fun _ => j) =
      (gm (r ≫ y) z (D.U i ⊓ D.U j) (D.trans i j))⁻¹ := by
    exact (Fintype.prod_unique _).trans ((zpow_one _).trans (map_inv _ _))
  have e₃ : gs (r ≫ y) z (D.U i) (D.f i) =
      (gm (r ≫ y) z (D.U i ⊓ D.U j) (D.trans i j)).val * gs (r ≫ y) z (D.U j) (D.f j) :=
    (gs_res _ z _ hm _).symm.trans ((congrArg (gs (r ≫ y) z _) (D.trans_spec i j)).trans ((gs_mul _ z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_unit _ z _ hm _) (gs_res _ z _ hm _))))
  rw [e₁, e₂, e₃, Units.val_mul, mul_comm (Units.val _⁻¹), _root_.mul_assoc, Units.inv_mul_cancel_left]

theorem exists_gen_pairing (D : EffCartierData X) {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ X) (k : D.ι)
    (hk : ⊤ ≤ y ⁻¹ᵁ D.U k) (c : Aˣ) : ∃ e : LB.Gen ((CechPic.dual D.lb).pull y), e.IsGen ∧
      ∀ (F : Type) [Field F] (φ : A →+* F) (z : Sp F) (i : D.ι), (spMap φ ≫ y) z ∈ D.U i →
        (gm (spMap φ) z (LB.wchart (CechPic.dual D.lb) (fun _ : PUnit => y) fun _ => i) (e.s fun _ => i)).val *
          gs (spMap φ ≫ y) z (D.U i) (D.f i) = toStk z (φ (c * ev y (D.U k) hk (D.f k))) := by
  obtain ⟨e, he, hc⟩ := exists_gen_const (CechPic.isLB_dual D.isLB_lb) y k hk c
  refine ⟨e, he, fun F _ φ z i hi => (pairing_eq D he (spMap φ) z hi (hk trivial)).trans ?_⟩
  rw [map_mul, map_mul]
  exact congrArg₂ (· * ·) (hc F φ z) (gs_spMap_eq φ y _ hk z _)

theorem idlAlong_idealSheaf_eq (D : EffCartierData X) {A : Type} [CommRing A] [IsLocalRing A] (y : Sp A ⟶ X) (k : D.ι)
    (hk : ⊤ ≤ y ⁻¹ᵁ D.U k) : idlAlong D.idealSheaf y = Ideal.span {ev y (D.U k) hk (D.f k)} := by
  obtain ⟨W, hW, hle⟩ := EffCartierData.exists_affine_le (show y (closedPoint A) ∈ D.U k from hk trivial)
  have hW' : ⊤ ≤ y ⁻¹ᵁ W.1 := (Scheme.preimage_eq_top_of_closedPoint_mem y hW).ge
  rw [TraitOrder.idlAlong_eq_map _ y W hW', D.ideal_idealSheaf W k hle, Ideal.map_span, Set.image_singleton,
    ← ev_res y hle hW' hk]
  rfl

theorem exists_dual_gen_extAt : ∀ (X : Scheme.{0}) (BD : GlobalTheory.EffCartierData X) (R : Type) [CommRing R] [IsDomain R] (u : R), u ≠ 0 →
    ∀ (x : Sp (FractionRing R) ⟶ X) (n : ℕ),
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
      ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
      ∀ χ : Sp V ⟶ X, spMap gam ≫ x = Out.jK V ≫ χ → GlobalTheory.LocM.idlAlong BD.idealSheaf χ = Ideal.span {ψ u ^ n}) →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.dual BD.lb).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.dual BD.lb) x e := by
  intro X BD R _ _ u hu x n H
  obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing BD.cover x
  have hu' : algebraMap R (FractionRing R) u ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hu)
  obtain ⟨c, hc⟩ : ∃ c : (FractionRing R)ˣ, ev x (BD.U k) hk (BD.f k) ≠ 0 →
      c * ev x (BD.U k) hk (BD.f k) = algebraMap R (FractionRing R) u ^ n := by
    by_cases ha : ev x (BD.U k) hk (BD.f k) = 0
    · exact ⟨1, fun h => (h ha).elim⟩
    · exact ⟨Units.mk0 _ (div_ne_zero hu' ha), fun _ => div_mul_cancel₀ _ ha⟩
  obtain ⟨e, he, hp⟩ := exists_gen_pairing BD x k hk c
  refine ⟨e, he, fun V _ _ _ hV ψ gam hg χ hsq => ?_⟩
  obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing BD.cover χ
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.1
    ((idlAlong_idealSheaf_eq BD χ k' hk').symm.trans (H V hV ψ gam hg χ hsq))
  obtain ⟨e', he', hp'⟩ := exists_gen_pairing BD χ k' hk' w
  refine ⟨e', he', fun z J hJ => ?_⟩
  have hv : toStk z (algebraMap V (FractionRing V) (w * ev χ (BD.U k') hk' (BD.f k'))) =
      toStk z (gam (algebraMap R (FractionRing R) u ^ n)) := by
    rw [mul_comm, hw, map_pow, map_pow gam, hg]
  have hne : IsUnit (toStk z (gam (algebraMap R (FractionRing R) u ^ n))) := ((Ne.isUnit hu').map gam).map _
  have q' : ∀ i, (spMap gam ≫ x) z ∈ BD.U i →
      (gm (Out.jK V) z (LB.wchart (CechPic.dual BD.lb) (fun _ : PUnit => χ) fun _ => i) (e'.s fun _ => i)).val *
        gs (spMap gam ≫ x) z (BD.U i) (BD.f i) = toStk z (gam (algebraMap R (FractionRing R) u ^ n)) := by
    rw [hsq]
    exact fun i hi => (hp' _ (algebraMap V (FractionRing V)) z i hi).trans hv
  have ha : ev x (BD.U k) hk (BD.f k) ≠ 0 := fun h0 => by
    have := q' k (hk trivial)
    rw [gs_spMap_eq gam x _ hk, h0, map_zero, map_zero, mul_zero] at this
    exact hne.ne_zero this.symm
  have q := hp _ gam z _ (hJ (spMap gam ≫ x))
  rw [hc ha] at q
  have q₂ := q' _ (hJ (spMap gam ≫ x))
  rw [val_of e' (Out.jK V) z J (fun _ => J (spMap gam ≫ x)) (fun _ => congrArg J hsq.symm)]
  have hU : IsUnit (gs (spMap gam ≫ x) z (BD.U (J (spMap gam ≫ x))) (BD.f (J (spMap gam ≫ x)))) :=
    isUnit_of_mul_isUnit_right (q ▸ hne)
  exact Units.ext (hU.mul_right_cancel (q.trans q₂.symm))

end GlobalTheory.TraitGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AtMember

open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

theorem odd_of_mem_levelPrimes (P : Pre) {p : ℕ} (hp : p ∈ P.host.levelPrimes) : Odd p := by
  have h := (P.level_cond p hp).2
  have h2 : (2 : ℕ) ∣ P.host.QS * P.host.q * P.host.d := ((((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans P.host.tower_dvd).mul_right _).mul_right _)
  rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd p h2, h]

set_option maxHeartbeats 4000000 in

theorem fieldTies_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre),
    X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  intro hR X f δ hx
  have := GlobalTheory.Mem.FieldsEx.host_cplx X.B.toPre
  have hFO : FO X.toD7 = X.B.KsC := SetLike.ext fun z => (mem_FO_assembled_iff X z).trans (X.B.mem_KsC).symm
  have hxe : X.B.KsC = Fld.listField δ f := hx
  obtain ⟨hray, -, hchar, -⟩ := Base.KsExact.lower hx
  have key : ∀ p, (p = X.B.host.pde ∨ p = X.B.host.pde') → FieldOK0 X.toD7 p := by
    intro p hp
    have hpl : p ∈ X.B.host.levelPrimes := by
      rcases hp with rfl | rfl
      exacts [X.B.host.pde_level.1, X.B.host.pde_level.2]
    have hpp : p.Prime := (X.B.toPre.level_cond p hpl).1
    have hdvd : X.B.host.g 0 * X.B.host.g 1 * p ∣ Fld.modulus X.B.toPre := by
      rcases hp with rfl | rfl
      · exact dvd_mul_right _ _
      · exact ⟨X.B.host.pde, by unfold Fld.modulus; ring⟩
    have hpd : p ∣ Fld.modulus X.B.toPre := (dvd_mul_left p _).trans hdvd
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rw [hFO]
      exact hray (GlobalTheory.Mem.RayRoots.rootOne_mem_of_isRayFieldIn X.B.host.E X.B.host.φ₀ (Fld.modulus X.B.toPre) p δ.ray (Fld.modulus_ne_zero _) hpd δ.isRay)
    · have hn0 : 0 < X.B.host.g 0 * X.B.host.g 1 * p :=
        Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hpp.pos
      refine GlobalTheory.FieldSize.curveOver_of_weberSet X.toD7 _ hn0 ?_ fun L hL => ?_
      · rw [hFO]
        exact X.B.imField_le_KsC ⟨_, rfl⟩
      · have hodd : Odd (X.B.host.g 0 * X.B.host.g 1 * p) :=
          ((odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 0)).mul
            (odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 1))).mul (odd_of_mem_levelPrimes X.B.toPre hpl)
        have h3 : 3 ≤ X.B.host.g 0 * X.B.host.g 1 * p := by
          have a := (X.B.host.g_prime 0).two_le
          have b := (X.B.host.g_prime 1).two_le
          have c := hpp.two_le
          have := Nat.mul_le_mul (Nat.mul_le_mul a b) c
          omega
        rw [hFO]
        exact (GlobalTheory.FieldSize.WeberRay.weberSet_subset_ray X.B.toPre δ L hL _ hodd h3 hdvd).trans fun z hz => hray hz
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key _ (Or.inl rfl), key _ (Or.inr rfl), fun x => ?_, fun x => ?_, fun L hL => ?_⟩
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del X.B.KsC f.isDel.fin
      ((le_sup_right.trans (le_sup_left.trans le_sup_left)).trans hchar) x
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del' X.B.KsC f.isDel'.fin ((le_sup_right.trans le_sup_left).trans hchar) x
  · have hle : FO X.toD7 ≤ δ.Om := by
      rw [hFO, hxe]
      exact GlobalTheory.Mem.FieldsEx.listField_le_Om δ f
    exact GlobalTheory.FieldSize.sz_mono_and_of_le.2 _ _ _ _ hle (GlobalTheory.T.omegaField_degree_rootDiscr_bounded_by_ringPolynomial hR X.B.toPre δ L hL)

end GlobalTheory.AtMember

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFrameValuationBound
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {U : X.Opens} (hU : IsAffineOpen U) {D : Set X} (hD : Dense D)
    (r : Γ(X, U)) (h : ∀ (k : Type) [Field k] (φ : Γ(X, U) →+* k), Set.range (spMap φ ≫ hU.fromSpec) ⊆ D → φ r = 0) :
    r = 0 := by
  have dn : Dense (hU.fromSpec ⁻¹' D) := hD.preimage hU.fromSpec.isOpenEmbedding.isOpenMap
  have mem : ∀ P : PrimeSpectrum Γ(X, U), r ∈ P.asIdeal := by
    intro P
    by_contra hP
    obtain ⟨Q, hQ1, hQ2⟩ := dn.inter_open_nonempty (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum Γ(X, U)))
      (PrimeSpectrum.basicOpen r).isOpen ⟨P, hP⟩
    apply hQ1
    haveI : Q.asIdeal.IsPrime := Q.2
    let φ : Γ(X, U) →+* Q.asIdeal.ResidueField := algebraMap _ _
    refine Ideal.algebraMap_residueField_eq_zero.1 (h _ φ ?_)
    rintro _ ⟨q, rfl⟩
    have e : (spMap φ) q = Q := by
      haveI : q.asIdeal.IsPrime := q.2
      have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      apply PrimeSpectrum.ext
      show Ideal.comap φ q.asIdeal = Q.asIdeal
      rw [hq, ← RingHom.ker_eq_comap_bot]
      exact Ideal.ker_algebraMap_residueField _
    rw [Scheme.Hom.comp_apply, e]
    exact hQ2
  have hn : r ∈ nilradical Γ(X, U) := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    exact fun I hI => mem ⟨I, hI⟩
  exact (mem_nilradical.1 hn).eq_zero

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X}

theorem eig_of_points {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j))
    (hbas : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) (a : 𝓞 E) (s : R) (j₀ : Fin n)
    (P : ∀ (k : Type) [Field k], (R →+* k) → Prop)
    (hz : ∀ r : R, (∀ (k : Type) [Field k] (φ : R →+* k), P k φ → φ r = 0) → r = 0)
    (hpt : ∀ (k : Type) [Field k] (φ : R →+* k), P k φ →
      (spMap (dualMap φ) ≫ v j₀) ≫ (t.act.act a).left = spMap (epsMul (φ s)) ≫ spMap (dualMap φ) ≫ v j₀) :
    v j₀ ≫ (t.act.act a).left = spMap (epsMul s) ≫ v j₀ := by
  classical
  let T : Fin n → TanM x t.G := fun j => GlobalTheory.LieMet.tanOf (hv j)
  have hT : (tv (T j₀)).left = v j₀ := rfl
  rw [← hT]
  refine (GlobalTheory.ShFam.Pad.Pull.eig_iff (T j₀) a s).2 ?_
  obtain ⟨c, hc, -⟩ := hbas _ (GlobalTheory.LieMet.isTan_tv (actR t.act a (T j₀)))
  have hc' : actR t.act a (T j₀) = ∑ j, c j • T j := (GlobalTheory.LieMet.isComb_iff T c _).1 hc
  have key : ∀ j, c j = if j = j₀ then s else 0 := fun j => by
    rw [← sub_eq_zero]
    refine hz _ fun k _ φ hφ => ?_
    rw [map_sub, sub_eq_zero]
    have hx : spMap φ ≫ x = spMap φ ≫ x := rfl
    have hv' := fun j => GlobalTheory.LieMet.isTan_map φ hx (hv j)
    have hb' := GlobalTheory.GradedPieces.basis_map φ hx hv hbas
    let T' : Fin n → TanM (spMap φ ≫ x) t.G := fun j => GlobalTheory.LieMet.tanOf (hv' j)
    have c1 := GlobalTheory.GradedPieces.comb_map φ hx hc
    have hw' : (tv (φ s • T' j₀)).left = spMap (dualMap φ) ≫ (tv (actR t.act a (T j₀))).left :=
      (hpt k φ hφ).symm
    have c2 : IsCombAtG t (spMap φ ≫ x) (fun j => spMap (dualMap φ) ≫ v j)
        (fun j => φ (if j = j₀ then s else 0)) (spMap (dualMap φ) ≫ (tv (actR t.act a (T j₀))).left) := by
      rw [← hw']
      refine (GlobalTheory.LieMet.isComb_iff T' _ _).2 ?_
      simp only [apply_ite φ, map_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact congrFun ((hb' _ (GlobalTheory.LieMet.isTan_map φ hx (GlobalTheory.LieMet.isTan_tv _))).unique c1 c2) j
  rw [hc']
  simp only [key, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Generic

theorem base_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) {b : Z.i.c.V W →+* Γ(Z.X, U)} (hb : hU.fromSpec ≫ Z.s = spMap b)
    {k : Type} [Field k] {φ : Γ(Z.X, U) →+* k} {a' : Fin Z.m} {φ' : Γ(Z.X, (Z.U a').1) →+* k}
    (h : spMap φ' ≫ Z.chart a' = spMap φ ≫ hU.fromSpec) (y : Z.i.c.V W) : φ (b y) = φ' (Z.alg a' y.1) := by
  have e : spMap (φ.comp b) = spMap ((φ'.comp (Z.alg a')).comp (Z.i.c.V W).subtype) := by
    rw [← ModelRelProbe.spMap_comp, ← ModelRelProbe.spMap_comp, ← GlobalTheory.ShFam.Pad.Pull.affineOpenChart_comp_structure_eq_spMap Z h, Z.π_s, Category.assoc, hb]
  exact congrArg (fun f => f y) (congrArg CommRingCat.Hom.hom
    (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) e))

theorem eig_of_intFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (b : Z.i.c.V W →+* Γ(Z.X, U)), hU.fromSpec ≫ Z.s = spMap b → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (a : 𝓞 E) (h : embK Z.i.c τ a ∈ Z.i.c.V W), w τ i ≫ ((Y Z.i).t.act.act a).left = spMap (epsMul (b ⟨_, h⟩)) ≫ w τ i := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z U hU w hw b hb τ i a h
  obtain ⟨n, v, e, he, hv, hbas⟩ := hw.1 τ
  have := GlobalTheory.ShFam.Pad.Pull.isReduced_model Z
  rw [← he i]
  refine eig_of_points hv hbas a (b ⟨_, h⟩) (e i)
    (fun k _ φ => Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn) (fun r hr => eq_zero_of_dense hU Z.dense r hr)
    fun k _ φ hr => ?_
  have hF2 := hw.2 k φ hr
  unfold GlobalTheory.LocM.Pre.FlagAt at hF2
  obtain ⟨a', φ', hch, hF, -⟩ := hF2
  have eig := (hF.1 τ i).2 a
  have hs : φ (b ⟨_, h⟩) = (φ'.comp (Z.alg a')) (embK Z.i.c τ a) := base_eq Z hU hb hch ⟨_, h⟩
  simp only [Vecs.bc] at eig
  rw [← hs, ← he i] at eig
  exact eig

end GlobalTheory.HTLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_zero_of_diag {X : Type} [AddCommGroup X] {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hp : ∀ y, 0 ≤ β y y) {y : X} (hy : β y y = 0) (z : X) : β y z = 0 := by
  by_contra hb
  have hA := hp z
  have h := hp (z + (-(β z z + 1) * β y z) • y)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hy, hs z y] at h
  have hb2 : 1 ≤ β y z * β y z := mul_self_pos.2 hb
  have h3 := mul_nonneg (by linarith : 0 ≤ β z z + 1) (sub_nonneg.2 hb2)
  nlinarith [h3]

theorem exists_pull_eq {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hk : ∀ y, r y = 0 → ∀ z, β y z = 0) : ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = β := by
  have key1 : ∀ a a' b, r a = r a' → β a b = β a' b := fun a a' b h => by
    have := hk (a - a') (by rw [map_sub, h, sub_self]) b
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  have key : ∀ a a' b b', r a = r a' → r b = r b' → β a b = β a' b' := fun a a' b b' h h' => by
    rw [key1 a a' b h, hs a' b, key1 b b' a' h', hs]
  have hs' : ∀ a, r (Function.surjInv hr a) = a := Function.surjInv_eq hr
  refine ⟨LinearMap.mk₂ ℤ (fun a b => β (Function.surjInv hr a) (Function.surjInv hr b)) ?_ ?_ ?_ ?_,
    LinearMap.ext₂ fun a b => ?_⟩
  · intro a a' b
    rw [← LinearMap.add_apply, ← map_add]
    exact key _ _ _ _ (by rw [map_add, hs', hs', hs']) rfl
  · intro n a b
    rw [← LinearMap.smul_apply, ← map_smul]
    exact key _ _ _ _ (by rw [map_zsmul r, hs', hs']) rfl
  · intro a b b'
    rw [← map_add]
    exact key _ _ _ _ rfl (by rw [map_add, hs', hs', hs'])
  · intro n a b
    rw [← map_smul]
    exact key _ _ _ _ rfl (by rw [map_zsmul r, hs', hs'])
  · simpa using key _ _ _ _ (hs' (r a)) (hs' (r b))

theorem isCone_pull_of_surjective : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (φ : InvFun O) (X₁ : Type) [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₁), IsPolFanOn bar φ X → Function.Surjective r → IsCone bar φ γ → IsCone bar φ (fun i => pull r (γ i)) := by
  intro O _ _ _ _ bar X _ _ _ φ X₁ _ _ _ r m γ hF hr hγ
  classical
  have hx := GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X m (fun i => pull r (γ i)) (fun _ => 1) (fun i => pull_mem r (hγ.mem i))
    (fun i y => hγ.nonneg i _) (fun _ => zero_le_one)
  obtain ⟨m₂, σ, c, hσ, hc, hsum⟩ := hF.cover _ hx
  let J : Finset (Fin m₂) := Finset.univ.filter fun j => c j ≠ 0
  let t : Fin J.card ↪ Fin m₂ := (J.orderEmbOfFin rfl).toEmbedding
  have hpos : ∀ k, c (t k) ≠ 0 := fun k => (Finset.mem_filter.1 (J.orderEmbOfFin_mem rfl k)).2
  have hout : ∀ j, j ∉ Set.range t → c j = 0 := fun j hj => by
    by_contra h0
    refine hj ?_
    have : j ∈ Set.range (J.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)
    exact this
  have hδ := hF.face _ _ σ t hσ
  have hsum' : ∑ i, (1 : ℝ) • toReal (pull r (γ i)) = ∑ k, c (t k) • toReal (σ (t k)) :=
    hsum.trans (Fintype.sum_of_injective t t.injective _ _ (fun j hj => by simp [hout j hj]) fun _ => rfl).symm
  have hvan : ∀ k y, r y = 0 → σ (t k) y y = 0 := fun k y hy => by
    have h1 := LinearMap.congr_fun₂ hsum' y y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, hy, map_zero, LinearMap.zero_apply,
      Int.cast_zero, smul_zero, smul_eq_mul, mul_zero, Finset.sum_const_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hc (t k))
      (by exact_mod_cast hσ.nonneg (t k) y : (0 : ℝ) ≤ (σ (t k) y y : ℝ))).1 h1.symm k (Finset.mem_univ _)
    exact_mod_cast (mul_eq_zero.1 h2).resolve_left (hpos k)
  have hex : ∀ k, ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = σ (t k) := fun k =>
    exists_pull_eq hr (hσ.mem (t k)).1 fun y hy z =>
      apply_eq_zero_of_diag (hσ.mem (t k)).1 (hσ.nonneg (t k)) (hvan k y hy) z
  choose δ hδ' using hex
  have hδc : IsCone bar φ δ := GlobalTheory.PolFan.isCone_of_pull O bar φ X X₁ r _ δ hr (by simpa only [hδ'] using hδ)
  have hsum₁ : ∑ i, (1 : ℝ) • toReal (γ i) = ∑ k, c (t k) • toReal (δ k) := LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have h1 := LinearMap.congr_fun₂ hsum' a b
    simp only [← hδ'] at h1
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply] using h1
  have hmeet := GlobalTheory.PolFan.cone_meet O bar φ X₁ m _ γ δ (fun _ => 1) (fun k => c (t k)) hγ hδc (fun _ => zero_le_one)
    (fun k => hc _) hsum₁
  choose j hj using fun i => hmeet i one_ne_zero
  have hinj : Function.Injective j := fun i i' h =>
    hγ.injective ((hj i).1.trans ((congrArg δ h).trans (hj i').1.symm))
  have hfin := hF.face _ _ _ ⟨j, hinj⟩ hδ
  have heq : (fun i => pull r (γ i)) = fun i => σ (t (j i)) := funext fun i => by rw [(hj i).1, hδ']
  rw [heq]
  exact hfin

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.LocM.MapUniq

theorem isMap_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime →
    (p : ℂ) ∈ W.nonunits → ∀ (Z₁ Z₂ : Mdl Y i₀) (f f' : Z₁.X ⟶ Z₂.X), IsMap Z₁ Z₂ f → IsMap Z₁ Z₂ f' → f = f' := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ Z₁ Z₂ f f' hf hf'
  have := Z₁.normal
  have : IsReduced Z₁.X := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_str (Z₂.i.c.V W) Z₂.n
  have : IsProper Z₂.s := by
    unfold Pre.s
    infer_instance
  have : IsSeparated (Z₂.s ≫ terminal.from _) := inferInstance
  refine ext_of_fromSpecResidueField_eq _ _ (Z₂.s ≫ terminal.from _) Z₁.opn Z₁.dense (fun x hx => ?_)
    (terminal.hom_ext _ _)
  have hr : Set.range (Z₁.X.fromSpecResidueField x) ⊆ Z₁.opn := by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply x a).symm ▸ hx
  exact CommonMod.natImg_unique hf.1 (hf.2 _ _ hr) (hf'.2 _ _ hr)

end GlobalTheory.LocM.MapUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
section
noncomputable section

open Matrix

namespace GlobalTheory.RedTh

structure IsSiegel {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Prop where

  nonneg : ∀ i, 0 ≤ d i

  step : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q

  diag : ∀ i, u i i = 1

  lower : ∀ i j, j < i → u i j = 0

  upper : ∀ i j, i < j → |u i j| ≤ 1 / 2

def gram {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := uᵀ * diagonal d * u

section Act

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {n : ℕ}

def actMat (b : Module.Basis (Fin n) ℤ X) : O →+* Matrix (Fin n) (Fin n) ℤ :=
  ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom).comp (Module.toModuleEnd ℤ X)

theorem actMat_apply (b : Module.Basis (Fin n) ℤ X) (c : O) (i j : Fin n) : actMat b c i j = b.repr (c • b j) i := by
  show LinearMap.toMatrixAlgEquiv b (Module.toModuleEnd ℤ X c) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

end Act

end GlobalTheory.RedTh
end
end

