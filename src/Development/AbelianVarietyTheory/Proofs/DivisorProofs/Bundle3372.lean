import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2955
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3276
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorBundleSectionGenericFibre
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

namespace GlobalTheory.ClearSecB

theorem exists_app_eq_of_local {X Y : Scheme.{0}} (h : Y ⟶ X) (hinj : ∀ W : X.Opens, Function.Injective (h.app W).hom)
    (W : X.Opens) (f : Γ(Y, h ⁻¹ᵁ W))
    (hf : ∀ x ∈ W, ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧ ∃ a : Γ(X, V),
      (h.app V).hom a = (Y.presheaf.map (homOfLE (fun _ hy => hV hy : h ⁻¹ᵁ V ≤ h ⁻¹ᵁ W)).op).hom f) :
    ∃ a : Γ(X, W), (h.app W).hom a = f := by
  choose V hV hxV a ha using hf
  have gp : ∀ (U : X.Opens) (c : Γ(X, U)) (y : Y), h y ∈ U → gs (𝟙 Y) y (h ⁻¹ᵁ U) ((h.app U).hom c) = gs h y U c :=
    fun U c y hy => (gs_pull (𝟙 Y) h y U hy c).trans (by rw [Category.id_comp])
  have gx : ∀ x (hx : x ∈ W) (y : Y), h y ∈ V x hx → gs h y (V x hx) (a x hx) = gs (𝟙 Y) y (h ⁻¹ᵁ W) f := by
    intro x hx y hy
    have hy' : (𝟙 Y) y ∈ h ⁻¹ᵁ V x hx := hy
    exact (gp _ _ y hy).symm.trans ((congrArg (gs (𝟙 Y) y _) (ha x hx)).trans (gs_res (𝟙 Y) y _ hy' _))
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : W => V x.1 x.2) W (fun x => homOfLE (hV x.1 x.2))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV x hx⟩) (fun x => a x.1 x.2) (fun x x' => hinj _ (fn_ext
      fun y hy => by
        have hy' : h y ∈ V x.1 x.2 ⊓ V x'.1 x'.2 := hy
        exact (gp _ _ y hy').trans ((gs_res h y _ hy' _).trans ((gx _ _ y hy'.1).trans ((gx _ _ y hy'.2).symm.trans
          ((gs_res h y _ hy' _).symm.trans (gp _ _ y hy').symm))))))
  refine ⟨s, fn_ext fun y hy => ?_⟩
  have hy' : h y ∈ W := hy
  exact (gp _ _ y hy').trans ((gs_res h y (hV _ hy') (hxV _ hy') s).symm.trans
    ((congrArg (gs h y _) (hs ⟨h y, hy'⟩)).trans (gx _ _ y (hxV _ hy'))))

theorem exists_mul_eq_app {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (V : Q.P.A.left.Opens)
    (hV : IsAffineOpen V) (f : Γ((DegPre.BF Q (FractionRing R)).left, (DegPre.prB Q (FractionRing R)).left ⁻¹ᵁ V)) :
    ∃ r : R, r ≠ 0 ∧ ∃ a : Γ(Q.P.A.left, V), ((DegPre.prB Q (FractionRing R)).left.app V).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) * f := by
  have eT : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  have H0 := (IsPullback.of_hasPullback (TF (R := R) (FractionRing R)).hom Q.P.A.hom).flip
  have H : IsPullback (DegPre.prB Q (FractionRing R)).left (pullback.fst (TF (R := R) (FractionRing R)).hom Q.P.A.hom)
      Q.P.A.hom (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (CommRingCat.of (FractionRing R))))) :=
    IsPullback.of_iso H0 (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; exact eT)
  have hloc := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := CommRingCat.of R) (L := CommRingCat.of (FractionRing R))
    (nonZeroDivisors R) H hV
  letI := ((DegPre.prB Q (FractionRing R)).left.app V).hom.toAlgebra
  obtain ⟨⟨a, _, r, hr, rfl⟩, e⟩ := IsLocalization.surj
    ((nonZeroDivisors (CommRingCat.of R)).map (GlobalTheory.QCoh.Qcqs.baseRingHom Q.P.A.hom V).hom) f
  refine ⟨r, nonZeroDivisors.ne_zero hr, a, ?_⟩
  have e2 : algebraMap Γ(Q.P.A.left, V) Γ((DegPre.BF Q (FractionRing R)).left, (DegPre.prB Q (FractionRing R)).left ⁻¹ᵁ V)
      ((GlobalTheory.QCoh.Qcqs.baseRingHom Q.P.A.hom V).hom r) =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) := by
    show ((DegPre.prB Q (FractionRing R)).left.app V).hom _ = _
    rw [GlobalTheory.QCoh.Qcqs.app_baseRingHom, ← GlobalTheory.QCoh.Qcqs.baseRingHom_res _ (le_top : _ ≤ ⊤), GlobalTheory.QCoh.Qcqs.baseRingHom_top,
      Over.w]
    rfl
  rw [e2] at e
  exact e.symm.trans (mul_comm _ _)

theorem exists_clear : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))), ∃ r : R, r ≠ 0 ∧ ∃ σ : Q.SecB k β, ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ (x ≫ (DegPre.prB Q (FractionRing R)).left) z J = gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * sval s x z J := by
  intro R _ _ _ Q k β s
  classical
  set p := (DegPre.prB Q (FractionRing R)).left with hp
  have hφ : ∀ i, DegPre.famφ Q (FractionRing R) β i = p ≫ Q.famφB β i := ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq Q _ β
  have hw : ∀ j, LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j = p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := by
    intro j
    have e : DegPre.famφ Q (FractionRing R) β = fun k => p ≫ Q.famφB β k := funext hφ
    rw [e]
    ext y
    simp [LB.wchart]
  have inj : ∀ W, Function.Injective (p.app W).hom := fun W => GlobalTheory.IntegralExpansion.prB_app_injective Q W
  have hpw : p ≫ Q.P.A.hom = (DegPre.BF Q (FractionRing R)).hom := Over.w _
  have gp : ∀ (U : Q.P.A.left.Opens) (a : Γ(Q.P.A.left, U)) (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ U →
      gs (𝟙 _) y (p ⁻¹ᵁ U) ((p.app U).hom a) = gs p y U a := fun U a y h =>
    (gs_pull (𝟙 _) p y U h a).trans (by rw [Category.id_comp])
  have gsc : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (c : R),
      gs p y ⊤ (Out.scal Q.P.A.hom c) = gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c) := fun y c =>
    (gs_pull p Q.P.A.hom y ⊤ trivial _).trans ((by rw [hpw, Category.id_comp] :
      gs (p ≫ Q.P.A.hom) y ⊤ _ = gs (𝟙 _ ≫ (DegPre.BF Q (FractionRing R)).hom) y ⊤ _).trans
        (gs_pull (𝟙 _) (DegPre.BF Q (FractionRing R)).hom y ⊤ trivial _).symm)
  have gmul : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (c c' : R),
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom (c * c')) =
        gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c) * gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom c') :=
    fun y c c' => by rw [← gs_mul _ y ⊤ trivial]; simp only [Out.scal, map_mul]
  have htr : ∀ (y : (DegPre.BF Q (FractionRing R)).left) (i j : Fin 4 → Q.P.L.ι),
      trF (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k) (𝟙 _) y i j =
        trF (Q.famφB β) (DegPre.famε k) p y i j := fun y i j => by
    simp only [trF, hφ, Category.id_comp]
  have : IsProper Q.P.A.hom := Q.P.isAb.proper
  have : CompactSpace Q.P.A.left := QuasiCompact.compactSpace_of_compactSpace Q.P.A.hom
  have hb : ∀ b : Q.P.A.left, ∃ j : Fin 4 → Q.P.L.ι, ∃ V : Q.P.A.left.Opens, IsAffineOpen V ∧ b ∈ V ∧
      V ≤ LB.wchart Q.P.L (Q.famφB β) j := by
    intro b
    choose i hi using fun k : Fin 4 => exists_chart Q.P.isLB (Q.famφB β k b)
    have hb : b ∈ LB.wchart Q.P.L (Q.famφB β) i := Set.mem_iInter.2 hi
    obtain ⟨V, hV, hbV, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Q.P.A.left.isBasis_affineOpens) hb
    exact ⟨i, V, hV, hbV, hle⟩
  choose jb Vb hVa hbV hVle using hb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun b => (Vb b : Set Q.P.A.left)) (fun b => (Vb b).isOpen)
    (fun b _ => Set.mem_iUnion.2 ⟨b, hbV b⟩)
  have hA : ∀ b, ∃ r : R, r ≠ 0 ∧ ∃ a : Γ(Q.P.A.left, Vb b), (p.app (Vb b)).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        ((DegPre.BF Q (FractionRing R)).left.presheaf.map (homOfLE (le_trans (show p ⁻¹ᵁ Vb b ≤ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) (jb b) from
          fun _ hy => hVle b hy) (hw (jb b)).ge)).op).hom (s.f (jb b)) :=
    fun b => exists_mul_eq_app Q (Vb b) (hVa b) _
  choose rb hrb ab hab using hA
  have hAg : ∀ b (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ Vb b → gs p y (Vb b) (ab b) =
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom (rb b)) *
        gs (𝟙 _) y (LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) (jb b)) (s.f (jb b)) := by
    intro b y hy
    have hy' : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ Vb b := hy
    have e := congrArg (gs (𝟙 _) y (p ⁻¹ᵁ Vb b)) (hab b)
    exact (gp _ _ y hy).symm.trans (e.trans ((gs_mul _ y _ hy' _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy' _) (gs_res _ y _ hy' _))))
  set r := ∏ b ∈ t, rb b with hr_def
  have hr : r ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hrb b

  have hlift : ∀ j, ∃ a : Γ(Q.P.A.left, LB.wchart Q.P.L (Q.famφB β) j), (p.app _).hom a =
      resTop _ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        ((DegPre.BF Q (FractionRing R)).left.presheaf.map (homOfLE (hw j).ge).op).hom (s.f j) := by
    intro j
    refine exists_app_eq_of_local p inj _ _ fun x hx => ?_
    obtain ⟨b, hbt, hxb⟩ : ∃ b ∈ t, x ∈ Vb b := by simpa using ht (Set.mem_univ x)
    have le1 : Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j ≤ (LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).U j ⊓
        (LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).U (jb b) := le_inf inf_le_right (inf_le_left.trans (hVle b))
    refine ⟨Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j, inf_le_right, ⟨hxb, hx⟩,
      resTop _ (Out.scal Q.P.A.hom (∏ b' ∈ t.erase b, rb b')) *
        (Q.P.A.left.presheaf.map (homOfLE inf_le_left).op).hom (ab b) *
        (Q.P.A.left.presheaf.map (homOfLE le1).op).hom
          ((LB.LinComb Q.P.L (Q.famφB β) (DegPre.famε k)).g j (jb b)).val, ?_⟩
    refine fn_ext fun y hy => ?_
    have hpy : p y ∈ Vb b ⊓ LB.wchart Q.P.L (Q.famφB β) j := hy
    have hyj : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j := (hw j).ge hpy.2
    have hyb : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) (jb b) := (hw (jb b)).ge (hVle b hpy.1)
    have hy1 : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := hpy.2
    refine ((gp _ _ y hpy).trans ((gs_mul p y _ hpy _ _).trans (congrArg₂ (· * ·) ((gs_mul p y _ hpy _ _).trans
      (congrArg₂ (· * ·) ((gs_res p y le_top hpy _).trans (gsc y _)) ((gs_res p y inf_le_left hpy _).trans
        (hAg b y hpy.1)))) ((gs_res p y le1 hpy _).trans ((gs_unit p y _ (le1 hpy) _).trans
          (congrArg Units.val (gm_linComb _ _ _ p y j (jb b) hpy.2 (hVle b hpy.1)))))))).trans
      (Eq.trans ?_ ((gs_res (𝟙 _) y _ hy _).trans ((gs_mul _ y _ hy1 _ _).trans (congrArg₂ (· * ·)
        (gs_res _ y le_top hy1 _) ((gs_res _ y _ hy1 _).trans (sec_trans s (𝟙 _) y hyj hyb))))).symm)
    rw [htr, hr_def, ← Finset.mul_prod_erase t rb hbt, gmul]
    simp only [trF]
    ring
  choose σf hσf using hlift
  have hσg : ∀ j (y : (DegPre.BF Q (FractionRing R)).left), p y ∈ LB.wchart Q.P.L (Q.famφB β) j → gs p y _ (σf j) =
      gs (𝟙 _) y ⊤ (Out.scal (DegPre.BF Q (FractionRing R)).hom r) *
        gs (𝟙 _) y (LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j) (s.f j) := by
    intro j y hy
    have hy' : (𝟙 (DegPre.BF Q (FractionRing R)).left) y ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) j := hy
    exact (gp _ _ y hy).symm.trans ((congrArg (gs (𝟙 _) y _) (hσf j)).trans ((gs_mul _ y _ hy' _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy' _) (gs_res _ y _ hy' _))))
  refine ⟨r, hr, ⟨σf, fun i j => inj _ (fn_ext fun y hy => ?_)⟩, fun Z x z J hJ => ?_⟩
  · have hpy : p y ∈ LB.wchart Q.P.L (Q.famφB β) i ⊓ LB.wchart Q.P.L (Q.famφB β) j := hy
    have hyi : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) i := (hw i).ge hpy.1
    have hyj : y ∈ LB.wchart Q.P.L (DegPre.famφ Q (FractionRing R) β) j := (hw j).ge hpy.2
    refine ((gp _ _ y hpy).trans ((gs_res p y _ hpy _).trans (hσg i y hpy.1))).trans (Eq.trans ?_
      ((gp _ _ y hpy).trans ((gs_mul p y _ hpy _ _).trans (congrArg₂ (· * ·) ((gs_unit p y _ hpy _).trans
        (congrArg Units.val (gm_linComb _ _ _ p y i j hpy.1 hpy.2))) ((gs_res p y _ hpy _).trans
          (hσg j y hpy.2))))).symm)
    rw [sec_trans s (𝟙 _) y hyi hyj]
    simp only [trF, hφ, Category.id_comp]
    ring
  · have hj0 := hJ.mem (Q.famφB β) (x ≫ p)
    have hxz : x z ∈ p ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB β) (fun k => J ((x ≫ p) ≫ Q.famφB β k)) := hj0
    rw [sval_of s x z J (fun k => J ((x ≫ p) ≫ Q.famφB β k)) (fun k => by rw [hφ, Category.assoc])]
    show gs (x ≫ p) z _ (σf _) = _
    refine ((gs_pull x p z _ hj0 _).symm.trans ((congrArg (gs x z _) (hσf _)).trans ((gs_mul x z _ hxz _ _).trans
      (congrArg₂ (· * ·) (gs_res x z le_top hxz _) (gs_res x z _ hxz _))))).trans ?_
    exact congrArg (· * _) (gs_pull x _ z ⊤ trivial _)

end GlobalTheory.ClearSecB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalPointOriginSmoothCommGroupScheme
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

namespace GlobalTheory.FormalOrigin

theorem exists_formalPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  intro R _ _ _ _ _ _ G _ _ hsm hint n v dd hdd D W d hd hW
  have hx0W : origin G ∈ W := hW (show IsLocalRing.closedPoint R ∈ (⊤ : (Sp R).Opens) from trivial)
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨D', hD'⟩ := GlobalTheory.T.exists_derivation_of_vectorFieldLift_near_unit R G D W d hd hW
  choose δ hδ using fun a => GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen G.left ⊤ (dd a) (hdd a).1 (origin G) trivial
  obtain ⟨dA, hdA⟩ := GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen G.left W d hd.1 (origin G) hx0W
  have hcomm : ∀ a b s, δ a (δ b s) = δ b (δ a s) := by
    intro a b s
    obtain ⟨O, hO, f, rfl⟩ := TopCat.Presheaf.germ_exist G.left.presheaf s
    rw [hδ b O hO le_top, hδ a O hO le_top, hδ a O hO le_top, hδ b O hO le_top,
      GlobalTheory.T.invariantVectorFields_commute_of_commGroupScheme R G (v a) (v b) (dd a) (dd b) (hdd a) (hdd b)]
  have hconst : ∀ a r, δ a (constO G r) = 0 := by
    intro a r
    rw [← GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants R G ⊤ trivial r, hδ a ⊤ trivial le_top, GlobalTheory.T.invariantVectorField_apply_constant_eq_zero R G (v a) (dd a) (hdd a), map_zero]
  have hdc : ∀ r, dA (constO G r) = constO G (D' r) := by
    intro r
    rw [← GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants R G W hx0W r, hdA W hx0W le_rfl, hd.2 W le_rfl, ← hD', GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants]
  obtain ⟨z, hz0, hz1, hm⟩ := GlobalTheory.T.smooth_commGroup_local_coordinates_at_origin R G hsm n v dd hdd δ (fun a O hO f => hδ a O hO le_top f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ringHom_eq_taylor _ R n (evO G) δ
  have hTC : ∀ r, T (constO G r) = MvPowerSeries.C r := by
    intro r
    rw [hT, GlobalTheory.T.derivationTaylorPowerSeries_of_derivations_kill _ R n (evO G) δ _ (fun i => hconst i r), GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants]
  have hT0 : ∀ s, MvPowerSeries.constantCoeff (T s) = evO G s := by
    intro s
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hT]
    show (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • evO G (iterOp _ 0 s) = _
    rw [iterOp_zero]
    simp
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left
  have : IsLocalHom T := ⟨fun s hs => by
    have h1 : IsUnit (evO G s) := by rw [← hT0]; exact (MvPowerSeries.isUnit_iff_constantCoeff).1 hs
    exact (isUnit_map_iff (evO G) s).1 h1⟩
  obtain ⟨dΩ, hdΩC, hdΩ⟩ := GlobalTheory.T.derivation_extends_taylorPowerSeriesRing R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm hconst dA D' hdc
  have hval : ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)),
      valR (spMap T ≫ G.left.fromSpecStalk (origin G)) O f = T ((G.left.presheaf.germ O (origin G) hO).hom f) :=
    fun O hO f => GlobalTheory.FlagBundle.valR_spMap_fromSpecStalk T hO f
  have htop : ∀ O : G.left.Opens, ⊤ ≤ (spMap T ≫ G.left.fromSpecStalk (origin G)) ⁻¹ᵁ O → origin G ∈ O :=
    fun O h => (GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem G.left (origin G) _ T inferInstance O).1 h
  refine ⟨MvPowerSeries (Fin n) R, inferInstance, NoZeroDivisors.to_isDomain _, inferInstance, MvPowerSeries.C,
    spMap T ≫ G.left.fromSpecStalk (origin G), fun a => intDer (MvPowerSeries.pderiv R a), intDer dΩ,
    GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian R _ ‹_› n, ?_, (GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem G.left (origin G) _ T inferInstance W).2 hx0W, fun r => ?_, fun a r => ?_,
    fun a O f hO => ?_, fun O f hOW hO => ?_, fun O f hO hf => ?_⟩
  · rw [Category.assoc, GlobalTheory.T.spec_map_fromSpecStalk_origin_comp_structure_eq R G _ T]
    congr 1
    exact RingHom.ext hTC
  · rw [← hD']; exact hdΩC r
  · exact MvPowerSeries.pderiv_C
  · have h := htop O hO
    rw [hval O h, hval O h, ← hδ a O h le_top, hT, hT, GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv _ R n (evO G) δ hcomm]
    rfl
  · have h := htop O hO
    rw [hval O h, hval O h, ← hdA O h hOW, hT, hT]
    exact (hdΩ _).symm
  · have h := htop O hO
    rw [hval O h, hT] at hf
    have h0 := GlobalTheory.T.derivationTaylorPowerSeries_injective_localRing R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm _ hf
    exact germ_injective_of_isIntegral G.left (origin G) h (h0.trans (map_zero _).symm)

end GlobalTheory.FormalOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSeriesOfCoboundaryDvdP
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

set_option maxHeartbeats 1000000 in

theorem exists_series_of_cobOne_dvd : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 ∧ (∀ α, (p : O) ∣ coeff α (cob2 c.μ κ)) ∧ (∀ α, (p : O) ∣ coeff α (Katz.swap κ - κ)) ∧ (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) ∧ c.ev 1 B = b + (p : O) • y := by
  intro p _ O _ G d c b z hbz
  let I : Ideal O := Ideal.span {(p : O)}
  have hpI : (p : O) ^ 1 ∈ I := by rw [pow_one]; exact Ideal.subset_span rfl
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 hpI
  have hmkp : (algebraMap O (O ⧸ I)) (p : O) = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hb' : cobOne (O ⧸ I) ((G.baseChange (O ⧸ I)).A 1) ((G.toBase (O ⧸ I)).app 1 b) = 0 := by
    rw [← SemiBialgHom.two_cobOne, hbz, map_smulₛₗ, hmkp, zero_smul]
  obtain ⟨κ', B', hcoc, hκ0, hcob, hev1⟩ := GlobalTheory.T.exists_series_of_additive_function_first_level p (O ⧸ I) d _ c' _ hlaw _ hb'
  obtain ⟨hl2, hz2, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I
  obtain ⟨hl1, hz1, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ (Fin d ⊕ Fin d)) I
  obtain ⟨hl0, -, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I
  obtain ⟨κ, hκ, hκc⟩ := hl2 κ'
  obtain ⟨B, hB, -⟩ := hl0 B'
  have hdiv : ∀ x : O, x ∈ I ↔ (p : O) ∣ x := fun x => Ideal.mem_span_singleton
  have hμ := c.isLaw.const
  obtain ⟨hm1, hm2, hsw, -, hpull⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ (O ⧸ I) (Ideal.Quotient.mk I)
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) (Ideal.Quotient.mk I)
  have hnm : (fun i => map (Ideal.Quotient.mk I) (nmul c.μ p i)) =
      nmul (fun i => map (Ideal.Quotient.mk I) (c.μ i)) p := funext fun i => (hn p i).2
  obtain ⟨hpl, -⟩ := hpull (nmul c.μ p) fun i => (hn p i).1
  have hy : ∃ y : G.A 1, c.ev 1 B = b + (p : O) • y := by
    have h1 : (G.toBase (O ⧸ I)).app 1 (c.ev 1 B) = (G.toBase (O ⧸ I)).app 1 b := by
      rw [← hev, hB, hev1]
    rw [toBase_app, toBase_app] at h1
    have h2 : (1 : O ⧸ I) ⊗ₜ[O] (c.ev 1 B - b) = 0 := by rw [tmul_sub, h1, sub_self]
    obtain ⟨-, hq, hs⟩ := GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A 1) I
    obtain ⟨y, hy⟩ := (hs (p : O) _).1 ((hq _).1 h2)
    exact ⟨y, by rw [← hy]; abel⟩
  obtain ⟨y, hy⟩ := hy
  refine ⟨κ, B, y, hκc hκ0, ?_, ?_, ?_, hy⟩
  · intro α
    refine (hdiv _).1 ((hz1 _).1 ?_ α)
    rw [hm2, hκ]; exact hcoc.1
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hsw, hκ, hcoc.2, sub_self]
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hm1, hpl, hκ, hB, hnm, hcob, sub_self]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodUnitPartGenerator
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
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UnitPart

theorem exists_psi_val_eq_monomial_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ)
    (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ (χ : Q.X) (n : Fin m → ℕ),
    (∀ i, gam i χ χ = 2 * n i) → ∃ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1),
      ψ₀.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι),
        Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n i) * (val ψ₀ (r ≫ jK R) z J).val := by
  intro R _ _ _ Q m t gam hM χ n hn
  obtain ⟨u, n', hn', hc⟩ := hM χ
  obtain rfl : n = n' := funext fun i => by have := (hn' i).symm.trans (hn i); omega
  obtain ⟨j, hj, h, e⟩ := hc
  have hL := Q.P.isLB
  obtain ⟨e₀, he₀⟩ := exists_gen_of_local (V := R) Q.P.L hL (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1)
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun k => by cases k; exact hj hy
  have hx : Q.xK χ = jK R ≫ (Q.c χ).left := by simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let w : Γ(Spec (CommRingCat.of R), ⊤)ˣ :=
    Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u * (res le (e₀.s j))⁻¹
  let v : LB.Gen (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top w⟩
  have hv : v.IsGen := fun i i' => by
    obtain rfl : i = i' := funext fun k => k.elim
    have e' : (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
      dsimp only [LB.LinComb]
      erw [Fintype.prod_empty]
      rfl
    rw [e', _root_.one_mul]
  have hf : FormEq (Sum.elim (fun _ : PUnit => (Q.c χ).left) (PEmpty.elim : PEmpty.{1} → _))
      (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (PEmpty.elim : PEmpty.{1} → ℤ))
      (fun _ : PUnit => (Q.c χ).left) (fun _ => -1) := fun U _ g => by
    rw [Fintype.prod_sum_type]
    simp
  obtain ⟨ψ₀, hψ₀, vψ₀⟩ := exists_gen hL hf (LB.mulGen Q.P.L _ _ _ _ e₀ v)
    (mulGen_isGen _ _ _ _ _ _ _ he₀ hv)
  refine ⟨ψ₀, hψ₀, fun Z r z J hJ => ?_⟩
  rw [vψ₀ _ _ z J hJ, val_mul hJ]
  have m₁ : r z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j := h trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j := le trivial
  have e₁ : val (Q.psi χ) r z J = _ := gen_trans (Q.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e₀ (r ≫ jK R) z J = _ := gen_trans he₀ (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := Q.P.L) (K := PUnit) (fun _ => Q.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ Q.xK χ)) j =
      trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j := by
    have hq : r ≫ Q.xK χ = (r ≫ jK R) ≫ (Q.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j) ((Q.psi χ).s j)).val =
      cst (r ≫ jK R) z (u * ∏ i, t i ^ n i) := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z h trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) e.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : val v (r ≫ jK R) z J = gm (r ≫ jK R) z ⊤ w := gm_res _ z _ (hJ.mem PEmpty.elim _) _
  have e₆ : (gm (r ≫ jK R) z ⊤ (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)).val = cst (r ≫ jK R) z u := by
    rw [← gs_unit _ z ⊤ trivial, Units.coe_map, cst, ← hto]; rfl
  have e₇ : ∀ a b : R, cst (r ≫ jK R) z (a * b) = cst (r ≫ jK R) z a * cst (r ≫ jK R) z b := fun a b => by
    rw [cst, map_mul, gs_mul _ z ⊤ trivial]; rfl
  have e₈ : gm (r ≫ jK R) z ⊤ (res le (e₀.s j)) =
      gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j) := gm_res _ z le trivial _
  have hg := Units.mul_inv (gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j))
  rw [e₁, e₂, e₅, Units.val_mul, Units.val_mul, e₄]
  erw [e₃]
  rw [map_mul, map_inv, e₈]
  simp only [Units.val_mul]
  rw [e₆, e₇]
  linear_combination (-((trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j).val * cst (r ≫ jK R) z u * cst (r ≫ jK R) z (∏ i, t i ^ n i))) * hg

end GlobalTheory.UnitPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionEvenTranslateSamePolarisedD
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwist

theorem exists_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (a : 𝟙_ (Over (Sp R)) ⟶ G) (P : GlobalTheory.UU.CP G) (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), a ^ 2 = 1 ∧ LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P ∧ IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) ∧ ∀ (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), U₂.LG = P.L → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  obtain ⟨a, ha, hcmp⟩ := GlobalTheory.T.exists_orderTwo_section_translate_refinement R hR D₀ D A G hG U hS
  obtain ⟨P, hP, hE⟩ := GlobalTheory.T.exists_evenCubicalSymmetricBundle_translate_orderTwo R hR D A G hG U a ha
  obtain ⟨A₂, gen₂, hm, hl⟩ := GlobalTheory.T.exists_principal_polarisation_genericFibre_twoTorsion_translate R hR D A G hG U a ha P hP
  refine ⟨a, P, A₂, gen₂, ha, hP, hE, hm, hl, fun D₂ U₂ hU => ?_⟩
  exact hcmp A₂ D₂ U₂ (by rw [hU]; exact hP)

end GlobalTheory.MumTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackHeightCompareStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_pullback_height_compare : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
    ∀ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2) →
    ∀ (a b : ℤ) (F : MvPolynomial (Fin 5) ℝ), (X 4 - X 0) * F = onLine d a b - onBase d a b →
    ∀ (s : Finset (Fin 5 → ℤ)) (c : (Fin 5 → ℤ) → ℝ), F = ∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ (d + 1) →
      -∑ n ∈ s, c n * (comb (fam5 π w H flB fl A) n).archInt ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)) (d + 1) hr = Ψ (G (d + 1) a b) := by
  first | exact @GlobalTheory.LogSinChern.archInt_logSin_eq_chernNumber | exact GlobalTheory.LogSinChern.archInt_logSin_eq_chernNumber | (intros; apply GlobalTheory.LogSinChern.archInt_logSin_eq_chernNumber <;> assumption)
end

