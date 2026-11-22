import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3645
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveDeRham
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPerf

theorem bijective_deRham (HR : GlobalTheory.Published.AbelianDeRham) (HD : GlobalTheory.Published.AbelianDualCrystal) {K : Type} [CommRing K]
    [IsNoetherianRing K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (g : ℕ)
    (hg : SmoothOfRelativeDimension g A.hom) (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hsym : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    (amp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) (e : ℕ) (he0 : 0 < e) (he : IsUnit (e : K))
    (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (hψ : IsCorrForm (dp0 K) (𝟙 _) A A P ψ) : Function.Bijective ψ := by

  have hsw : (swap P).IsLB := pull_isLB hP _
  have ec : cls P hP = cls _ hsw := (cls_eq_iff hP hsw).2 hsym
  have key : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = evc hP b a := fun Y a b ↦ by
    rw [← evc_swap hP hsw a b]
    show CechPic.pull _ (cls P hP) = CechPic.pull _ (cls _ hsw)
    rw [ec]

  obtain ⟨B, _, Q, hB, hBg, hd, hd'⟩ := HD.1 (Sp K) A hA
  have hBg := hBg _ hg
  haveI : IsCommMonObj B := hB.comm

  have hL := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  obtain ⟨H, hH, hamp⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL amp hL amp
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH hamp hP r₁ r₂
  obtain ⟨lam, hlam, hcls⟩ := GlobalTheory.BirigidLift.exists_hom hd hd'.additive hP a₁ a₂

  have hkerl : ∀ (T : Over (Sp K)) (x : T ⟶ A), x ≫ lam = 1 → x ^ e = 1 := by
    intro T x hx
    have tr : Triv (ev P (fst A T) (snd A T ≫ x)) := by
      rw [triv_ev_iff hP, GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP hcls, Category.assoc, hx, comp_one]
      exact evc_one_right hd.isLB hd.zero _
    refine hker T x ((triv_ev_iff hP _ _).2 ?_)
    rw [key]
    exact (triv_ev_iff hP _ _).1 tr
  obtain ⟨μ', hμ', e₁, e₂⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A B g hA hB hg hBg lam hlam e he0 hkerl
  haveI := hlam
  haveI := hμ'
  have hpush := GlobalTheory.PolPrimeTo.bijective_push (dp0 K) (𝟙 _) lam μ' e he e₁ e₂

  obtain ⟨⟨φ, hφ, -⟩, hperf⟩ := GlobalTheory.Published.AbelianDualCrystal.duality HR hA hg hB hBg (hd.isPerfect hd')
  have C := cupSquare_of_free HR.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg)
  have e' : LBIso (ev Q (fst A A) (snd A A ≫ lam)) (ev P (fst A A ≫ 𝟙 A) (snd A A)) := by
    refine (cls_eq_iff (pull_isLB hd.isLB _) (pull_isLB hP _)).1 ?_
    rw [cls_ev hd.isLB, cls_ev hP, GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP hcls, Category.comp_id]
  have hadj : ∀ x y, φ x (push (dp0 K) (𝟙 _) lam y) = ψ x y := fun x y ↦ by
    have k := IsCorrForm.adjoint C hd.isLB hP hφ hψ (𝟙 A) lam e' x y
    rwa [push_id] at k
  haveI := (hperf φ hφ).1
  have hφb : Function.Bijective φ := LinearMap.IsPerfPair.bijective_left φ
  let E := LinearEquiv.ofBijective _ hpush
  have : ⇑ψ = ⇑E.dualMap ∘ ⇑φ := by
    funext x
    refine LinearMap.ext fun y ↦ ?_
    rw [Function.comp_apply, LinearEquiv.dualMap_apply, ← hadj]
    rfl
  rw [this]
  exact E.dualMap.bijective.comp hφb

end GlobalTheory.HTPerf

namespace GlobalTheory.HTPerf

open GlobalTheory.Published.GrothendieckMessing IsLocalRing

set_option maxHeartbeats 1600000 in

theorem skew_bijective : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → (∀ x y, φ x y = -φ y x) ∧ Function.Bijective φ := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ φ hφ
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  haveI : IsNoetherianRing C₀ := isNoetherianRing_of_surjective C C₀ π hπ
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  have hA₀ := o₀.ab
  have hP₀ := o₀.isLB
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A hA₀
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have Cs := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA' hg hA' hg h' h'

  have hsw : (swap o₀.P).IsLB := pull_isLB hP₀ _
  have hs : LBIso (swap o₀.P) o₀.P := (cls_eq_iff hsw hP₀).1 ((cls_eq_iff hP₀ hsw).2 o₀.symm).symm
  have skew : ∀ x y, φ x y = -φ y x := GlobalTheory.SymmPoincare.skew_of_symm Cs hP₀ hs hφ
  refine ⟨skew, ?_⟩

  have HC := (GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1
  obtain ⟨bij, -, -⟩ := HC g o₀.A A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra C C₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 C A' g hA' hg C₀ o₀.A i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  haveI : Module.Finite C (Crys κ (spMap π) o₀.A) := Module.Finite.equiv e.symm
  haveI : Module.Projective C (Crys κ (spMap π) o₀.A) := Module.Projective.of_equiv e.symm

  let red : Crys κ (spMap π) o₀.A →ₛₗ[π] HdR o₀.A := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl o₀.A).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) hP₀).1
      (by rw [GlobalTheory.CechPic.cls_pull hP₀, Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ.pull hP₀ (crysRedMor κ rfl o₀.A) (crysRedMor κ rfl o₀.A)
    (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) hP₀ iso
  have hrel : ∀ x y, φ' (red x) (red y) = π (φ x y) := fun x y ↦ e' x (red x) y (red y) (hm x) (hm y)
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[C] C₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) o₀.A)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this

  obtain ⟨k, hkp, hkerP⟩ := o₀.kerP
  have hk0 : 0 < k := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    rw [h0, Nat.coprime_zero_left] at hkp
    exact (Fact.out : p.Prime).one_lt.ne' hkp
  have hku : IsUnit (k : C₀) := by
    have := (b.unit k hkp).map (π.comp tR)
    rwa [map_natCast] at this
  have hψb : Function.Bijective φ' :=
    bijective_deRham ADR ADC o₀.A hA₀ g₀ hg₀ o₀.P hP₀ o₀.rig₁ o₀.rig₂ o₀.symm o₀.ample k hk0 hku hkerP φ' hφ'
  have skew' : ∀ u v, φ' u v = -φ' v u := fun u v ↦ by
    obtain ⟨x, rfl⟩ := hred u
    obtain ⟨y, rfl⟩ := hred v
    rw [hrel, hrel, skew, map_neg]
  have hψf : Function.Surjective φ'.flip := fun l ↦ by
    obtain ⟨x, hx⟩ := hψb.2 (-l)
    exact ⟨x, LinearMap.ext fun y ↦ by rw [LinearMap.flip_apply, skew', hx, LinearMap.neg_apply, neg_neg]⟩
  have hperf := GlobalTheory.BirigLift.exists_perfect_mod π red φ φ' hπ hψf hred hker hrel

  have htop : (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ LinearMap.range φ.flip ⊔ RingHom.ker π • ⊤ := fun l _ ↦ by
    obtain ⟨z, hz⟩ := hperf l
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (l - φ.flip z) fun c ↦ by
      simpa only [LinearMap.sub_apply, LinearMap.flip_apply] using hz c
    exact Submodule.mem_sup.2 ⟨φ.flip z, ⟨z, rfl⟩, l - φ.flip z, hmem, add_sub_cancel _ _⟩
  have hIle : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ LinearMap.range φ.flip := by
    calc RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C)) ≤ RingHom.ker π • (LinearMap.range φ.flip ⊔ RingHom.ker π • ⊤) :=
          Submodule.smul_mono le_rfl htop
      _ = RingHom.ker π • LinearMap.range φ.flip ⊔ RingHom.ker π • RingHom.ker π • ⊤ := Submodule.smul_sup _ _ _
      _ ≤ LinearMap.range φ.flip := by
          refine sup_le Submodule.smul_le_right ?_
          rw [← Submodule.mul_smul, ← pow_two, hI2, Submodule.bot_smul]
          exact bot_le
  have hsurj : Function.Surjective φ.flip :=
    LinearMap.range_eq_top.1 (top_le_iff.1 (htop.trans (sup_le le_rfl hIle)))
  haveI : Module.Free C (Crys (divided₂ hsq) (spMap π) o₀.A) := Module.free_of_flat_of_isLocalRing
  let bs := Module.finBasis C (Crys (divided₂ hsq) (spMap π) o₀.A)
  have hinj : Function.Injective φ.flip := by
    have hs' : Function.Surjective (bs.toDualEquiv.symm.toLinearMap ∘ₗ φ.flip) :=
      bs.toDualEquiv.symm.surjective.comp hsurj
    have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs'
    exact fun x y hxy ↦ hi (by simp only [LinearMap.coe_comp, Function.comp_apply, hxy])
  have hneg : ∀ x, φ x = -φ.flip x := fun x ↦
    LinearMap.ext fun y ↦ by rw [LinearMap.neg_apply, LinearMap.flip_apply, skew]
  refine ⟨fun x x' hxx ↦ hinj (neg_injective ?_), fun l ↦ ?_⟩
  · rw [← hneg, ← hneg, hxx]
  · obtain ⟨z, hz⟩ := hsurj (-l)
    exact ⟨z, by rw [hneg, hz, neg_neg]⟩

end GlobalTheory.HTPerf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyEndomorphismEqMapLadicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (f : A ⟶ A) [IsMonHom f] (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ A),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      ∀ [Module.Finite k (HdR A)],
        LinearMap.charpoly (push (dp0 k) (𝟙 _) f) = (LinearMap.charpoly φ).map (Int.castRingHom k) := by
  first | (exact @GlobalTheory.DeRham.charpoly_push_eq) | (exact GlobalTheory.DeRham.charpoly_push_eq) | (intros; apply GlobalTheory.DeRham.charpoly_push_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartSeparation_data_defined_over_centre_field : GlobalTheory.Poinc.Sep.SepSt := by
  first | exact @GlobalTheory.Poinc.Sep.sepSt | exact GlobalTheory.Poinc.Sep.sepSt | (intros; apply GlobalTheory.Poinc.Sep.sepSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationHasComplement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem crys_ext (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀}
    (h : ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      e' ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) : e = e' := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  have h1 : ∀ c, (GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c = eqv (1 ⊗ₜ c) := fun c =>
    (one_smul (TrivSqZeroExt k (Fin d → k)) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).symm
  have key : e ∘ₗ eqv.toLinearMap = e' ∘ₗ eqv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun r c => ?_
    have hr : (r ⊗ₜ c : TrivSqZeroExt k (Fin d → k) ⊗[k] primDR A₀) = r • (1 ⊗ₜ c) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr, map_smul, ← h1, h c]
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := eqv.surjective y
  exact LinearMap.congr_fun key t

theorem crys_pull_smul (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a : k) (c : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a • c)) =
      TrivSqZeroExt.inl a * e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) := by
  rw [LinearMap.map_smulₛₗ]
  exact e.map_smul (algebraMap k (TrivSqZeroExt k (Fin d → k)) a) ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)

theorem crys_pull_add (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (a b : primDR A₀) :
    e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull (a + b)) =
      e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull a) + e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull b) := by
  rw [LinearMap.map_add]
  exact e.map_add _ _

def fstVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def sndVal (A₀ : Over (Sp k)) [GrpObj A₀]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (j : Fin d) : HdR A₀ where
  toFun c := (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j
  map_add' a b := by
    rw [crys_pull_add]
    rfl
  map_smul' a c := by
    rw [crys_pull_smul]
    simp

def constSub (A₀ : Over (Sp k)) [GrpObj A₀] (S : Submodule k (HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ S, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ S) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => z j c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply,
        LinearMap.add_apply, zero_add, add_zero, Pi.zero_apply]
  zero_mem' := ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun c => by rw [LinearMap.zero_apply]; ext <;> simp⟩
  smul_mem' := by
    rintro r e ⟨x, hx, z, hz, he⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, fun j => r.fst • z j + r.snd j • x,
      fun j => add_mem (Submodule.smul_mem _ _ (hz j)) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, he c, smul_eq_mul]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, Pi.smul_apply,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]

set_option maxHeartbeats 1000000 in

theorem mem_sup_of_coords (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (x₁ m : HdR A₀) (hx₁ : x₁ ∈ Fil A₀) (hm : m ∈ M₀) (hxm : ∀ c, x₁ c + m c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).fst)
    (z w : Fin d → HdR A₀) (hz : ∀ j, z j ∈ Fil A₀) (hw : ∀ j, w j ∈ M₀)
    (hzw : ∀ j c, z j c + w j c = (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)).snd j - f j x₁ c) :
    e ∈ glueFil A₀ f ⊔ constSub A₀ M₀ := by
  obtain ⟨g, hg⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x₁ + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x₁ + z j)
  have hgv : ∀ c, g ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x₁ c) + TrivSqZeroExt.inr (fun j => (f j x₁ + z j) c) := fun c => by
    rw [hg c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hgm : g ∈ glueFil A₀ f := ⟨x₁, hx₁, z, hz, hgv⟩
  obtain ⟨h, hh⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ m + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => w j)
  have hhv : ∀ c, h ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (m c) + TrivSqZeroExt.inr (fun j => w j c) := fun c => by
    rw [hh c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hhm : h ∈ constSub A₀ M₀ := ⟨m, hm, w, hw, hhv⟩
  refine Submodule.mem_sup.2 ⟨g, hgm, h, hhm, crys_ext A₀ hA fun c => ?_⟩
  rw [LinearMap.add_apply, hgv c, hhv c]
  ext
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hxm c]
  · rename_i j
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
      Pi.add_apply, zero_add, LinearMap.add_apply]
    linear_combination (hzw j c)

theorem isCompl_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (M₀ : Submodule k (HdR A₀)) (hM : IsCompl (Fil A₀) M₀) :
    IsCompl (glueFil A₀ f) (constSub (d := d) A₀ M₀) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro e ⟨x, hx, z, hz, he⟩ ⟨m, hm, w, hw, he'⟩
    have hxm : x = m := LinearMap.ext fun c => by
      have := congrArg TrivSqZeroExt.fst ((he c).symm.trans (he' c))
      simpa using this
    have hx0 : x = 0 := by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hx, hxm ▸ hm⟩
    have hzw : ∀ j, z j = w j := fun j => LinearMap.ext fun c => by
      have := congrFun (congrArg TrivSqZeroExt.snd ((he c).symm.trans (he' c))) j
      simpa [hx0] using this
    have hz0 : ∀ j, z j = 0 := fun j => by
      rw [← Submodule.mem_bot k, ← hM.inf_eq_bot]
      exact ⟨hz j, (hzw j) ▸ hw j⟩
    refine crys_ext A₀ hA fun c => ?_
    rw [he c, LinearMap.zero_apply]
    ext <;> simp [hx0, hz0]
  · rw [codisjoint_iff, eq_top_iff]
    rintro e -
    have hdec : ∀ u : HdR A₀, ∃ a ∈ Fil A₀, ∃ b ∈ M₀, a + b = u := fun u => by
      have hu : u ∈ Fil A₀ ⊔ M₀ := by rw [hM.sup_eq_top]; trivial
      rw [Submodule.mem_sup] at hu
      exact hu
    choose pa hpa pb hpb hpab using hdec
    exact mem_sup_of_coords A₀ hA f M₀ e _ _ (hpa _) (hpb _) (fun c => LinearMap.congr_fun (hpab (fstVal A₀ e)) c)
      (fun j => pa (sndVal A₀ e j - f j (pa (fstVal A₀ e))))
      (fun j => pb (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) (fun _ => hpa _) (fun _ => hpb _)
      (fun j c => LinearMap.congr_fun (hpab (sndVal A₀ e j - f j (pa (fstVal A₀ e)))) c)

end GlobalTheory.HTGlue

open GlobalTheory.HTGlue in

theorem GlobalTheory.HTGlue.glueFil_hasCompl : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _
  obtain ⟨M₀, hM⟩ := Submodule.exists_isCompl (Fil o₀.A)
  exact ⟨_, isCompl_glueFil o₀.A o₀.ab f M₀ hM⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphFiltrationOrderStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem primPull_constMorV_pull {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (q : primDR A₀) :
    primPull (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g
        ((GlobalTheory.FODef.constMorV k V A₀).pull q) =
      (GlobalTheory.FODef.constMorV k V A₀).pull (primPull (dp0 k) (𝟙 _) g q) := by
  have K := (homMor (dp0 k) (𝟙 _) g).comp (GlobalTheory.FODef.constMorV k V A₀)
  have e1 := GrpMor.pull_pull (GlobalTheory.FODef.constMorV k V A₀)
    (homMor (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g) K
    (fun _ ↦ rfl) (by simp) q
  have e2 := GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) g) (GlobalTheory.FODef.constMorV k V A₀) K
    (fun _ ↦ rfl) rfl q
  exact e1.trans e2.symm

theorem push_mem_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ (c : D.O), ∀ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (c)) (e)) ∈ (GlobalTheory.HTGlue.glueFil o₀.A f)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f hf c e he
  haveI := o₀.act.hom c
  obtain ⟨x, hx, z, hz, hxz⟩ := he
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := GlobalTheory.HTCount.crysAct o₀ c
  have hg : ∀ h, g h = push (dp0 k) (𝟙 _) (o₀.act.act c) h := fun _ ↦ rfl
  refine ⟨g x, push_mem_Fil _ hx, fun j ↦ g (z j) - (f j (g x) - g (f j x)),
    fun j ↦ sub_mem (push_mem_Fil _ (hz j)) ((hf j).1 c x hx), fun q ↦ ?_⟩
  rw [push_apply, primPull_constMorV_pull, hxz]
  congr 2
  funext j
  rw [← push_apply, ← hg]
  simp only [map_add, LinearMap.add_apply, LinearMap.sub_apply, map_sub]
  abel

end GlobalTheory.HTGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHomologyClosedFibreSurjectiveKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Functor.grpObjObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamHomology_closedFibre_surjective_kernel : ∀ (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [CommRing O] (a : OAct O A₀), ∃ f : HdR A₀ →ₛₗ[algebraMap C₀ (IsLocalRing.ResidueField C₀)] HdR ((Over.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀)))).obj A₀), Function.Surjective f ∧ (∀ h, f h = 0 → h ∈ IsLocalRing.maximalIdeal C₀ • (⊤ : Submodule C₀ (HdR A₀))) ∧ ∀ (x : O) (h : HdR A₀), f (act (dp0 C₀) (𝟙 _) a x h) = act (dp0 (IsLocalRing.ResidueField C₀)) (𝟙 _) (OAct.pullback (spMap (algebraMap C₀ (IsLocalRing.ResidueField C₀))) A₀ a) x (f h) := by
  first | (exact @GlobalTheory.HdRFibre.fibre_baseChange) | (exact GlobalTheory.HdRFibre.fibre_baseChange) | (intros; apply GlobalTheory.HdRFibre.fibre_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_lift_with_principal_lineBundle : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left) (Q : LB (Y ⊗ Y).left), IsAbelianScheme Y ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ IsSquare i l ∧ Q.IsLB ∧ GlobalTheory.AbDual.IsAdditive Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ LBIso (Q.pull l) (abelian₂ Y₀ L₀) := by
  first | exact @GlobalTheory.AltLift.exists_lift_lam | exact GlobalTheory.AltLift.exists_lift_lam | (intros; apply GlobalTheory.AltLift.exists_lift_lam <;> assumption)
end

