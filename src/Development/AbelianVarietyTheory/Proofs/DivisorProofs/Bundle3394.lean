import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3379
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerThroughGeneratingLineBundleIso
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

namespace GlobalTheory.SecThroughIso

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_sec_of_iso : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → L₁.IsLB → L₂.IsLB → ∀ (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k),
    ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))),
      (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j →
        gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k *
          gs f₁ y _ (σ'.f fun _ => j)) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w hw h₁ h₂ k σ'
  let t : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ))) :=
    TG.pullSec' L₁ (fun _ => 𝟙 X₁) (fun _ => (k : ℤ)) σ' f₁ (fun _ => f₁) (fun _ => (Category.comp_id _).symm)
  refine ⟨secOfIso (u := flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))) t
    (flatIso_isGen L₁ L₂ f₁ f₂ w hw _) (linComb_isLB _ h₂ _ _) (linComb_isLB _ h₁ _ _), ?_⟩
  intro y i j hi hj
  have hz : (𝟙 Y) y ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) ⊓
      (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have e := ps_gs_secOfIso (flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))) t
    (flatIso_isGen L₁ L₂ f₁ f₂ w hw _) (linComb_isLB _ h₂ _ _) (linComb_isLB _ h₁ _ _)
    (fun _ => i) (fun _ => j) (𝟙 Y) y hz
  have hw' : (𝟙 Y) y ∈ ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hj⟩
  have e1 : gm (𝟙 Y) y _ ((flatIso L₁ L₂ f₁ f₂ w (fun _ : Fin 1 => (k : ℤ))).s (fun _ => j, fun _ => i)) =
      gm (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)) ^ (-(k : ℤ)) := by
    show gm (𝟙 Y) y _ (∏ k' : Fin 1, res (flat_le L₁ L₂ f₁ f₂ (fun _ => j, fun _ => i) k')
      (w.s (fun _ => i, fun _ => j)) ^ (-(k : ℤ))) = _
    rw [map_prod, Fin.prod_univ_one, map_zpow]
    congr 1
    exact gm_res _ y _ (show (𝟙 Y) y ∈ LB.wchart L₁ (fun _ : Fin 1 => f₁) (fun _ => j) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) from ⟨hz.2, hz.1⟩) _
  have e2 : gs (𝟙 Y) y _ (t.f fun _ => j) = gs f₁ y _ (σ'.f fun _ => j) := by
    simp only [t]
    rw [TG.pullSec'_f]
    refine (gs_res _ y _ hz.2 _).trans ?_
    refine (gs_pull (𝟙 Y) f₁ y _ (Set.mem_iInter.2 fun _ => hj) _).trans ?_
    rw [Category.id_comp]
    rfl
  rw [e, e1, e2, gs_unit _ y _ hw', zpow_neg, inv_inv, zpow_natCast, Units.val_pow_eq_pow_val]

end GlobalTheory.SecThroughIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackPowerBundleScalarOne
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

namespace GlobalTheory.SecRestr

theorem exists_restr : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k), ∃ s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ 1 := by
  intro X₂ Y L₂ f₂ k σ
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.TG.pullSec' L₂ _ _ σ f₂ (fun _ => f₂) (fun _ => (Category.comp_id _).symm), ?_⟩
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun i => by
    rw [Subsingleton.elim i 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [ReciprocityTheory.ChartRestriction.G.DVR.TG.pullSec'_f]
  have h1 : ReciprocityTheory.ChartRestriction.G.Out.resTop (LB.wchart L₂ (fun _ : Fin 1 => f₂) j₁ ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) j₁) (1 : Γ(Y, ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.SecRestr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint
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

namespace GlobalTheory.HeatV

theorem val_pow_mul_eq {R : Type} [CommRing R] (t b : Rˣ) (a : R) (k : ℕ) :
    ((t ^ k : Rˣ) : R) * a = a * ((b⁻¹ ^ k : Rˣ) : R) * (((t * b) ^ k : Rˣ) : R) := by
  have e : ((b⁻¹ ^ k : Rˣ) : R) * ((b ^ k : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  rw [mul_pow, Units.val_mul]
  linear_combination (-(((t ^ k : Rˣ) : R) * a)) * e

theorem exists_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)), g.IsGen → ∀ (k : ℕ) (σ : SecM (𝟙 X) L k), ∃ ω : Ω, IsValue (𝟙 _) L x g k σ ω := by
  intro X L hL Ω _ _ x g hg k σ
  obtain ⟨j₀, hj₀⟩ : ∃ i, ∀ p : Sp Ω, x.base p ∈ L.U i := by
    have hc : x.base (IsLocalRing.closedPoint Ω) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨i, fun p => ((IsLocalRing.specializes_closedPoint p).map x.continuous).mem_open (L.U i).isOpen hi⟩
  have hW : (⊤ : (Sp Ω).Opens) ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  have hG : (⊤ : (Sp Ω).Opens) ≤ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  let ωs : Γ(Sp Ω, ⊤) := ((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)) *
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs, fun Z r z J hJ => ?_⟩
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs) = ωs := by
    simp
  rw [hinv]
  have hj : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => J ((r ≫ x) ≫ 𝟙 X)) := hJ.mem _ (r ≫ x)
  have hj0 : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) := hW (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hgj : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => J (r ≫ x ≫ 𝟙 X)) := hJ.mem _ r
  have hg0 : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) := hG (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  rw [sval_of σ (r ≫ x) z J _ (fun _ => rfl), sec_trans σ (r ≫ x) z hj hj0, val_of g r z J _ (fun _ => rfl),
    gen_trans hg r z hgj hg0]
  have hT : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (r ≫ x) z (fun _ => J ((r ≫ x) ≫ 𝟙 X)) (fun _ => j₀) =
      trF (L := L) (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => 1) r z (fun _ => J (r ≫ x ≫ 𝟙 X)) (fun _ => j₀) ^ k := by
    simp only [trF]
    rw [Category.assoc]
    simp
  have hp := (gs_pull r x z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀)) hj0 (σ.f fun _ => j₀)).symm
  have hm : r z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have h1 := gs_mul r z ⊤ hm (((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)))
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  have h2 := gm_res r z hG hm (g.s fun _ => j₀)
  rw [gs_res r z hW hm, gs_unit r z ⊤ hm, map_pow, map_inv] at h1
  erw [h2] at h1
  rw [hT, hp, h1]
  exact val_pow_mul_eq _ _ _ _

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtensionNearPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem HasExt.of_comp {W V T : Scheme.{0}} (g : W ⟶ V) (e : V ⟶ T) (B : Over W) [GrpObj B] (h : HasExt (g ≫ e) B) :
    HasExt g B := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  exact ⟨(Over.pullback e).obj G, inferInstance, _, IsSemiAbelian.pullback _ _ hG,
    ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e g hφ⟩

theorem HasExt.of_dense {W V U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian V]
    (hV : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V) (l : W ⟶ V) [IsOpenImmersion l] [IsDominant l] (j : V ⟶ U)
    (A : Over V) [GrpObj A] (hA : IsSemiAbelian A) (B : Over W) [GrpObj B] (κ : B.left ⟶ A.left)
    (hκ : IsGrpPullback B A l κ) (h : HasExt (l ≫ j) B) : HasExt j A := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor j l hφ
  obtain ⟨e, ⟨he, -⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.existsUnique_iso_of_extensions hV hA
    (IsSemiAbelian.pullback j G hG) hκ h2
  exact ⟨G, inferInstance, e.hom.left ≫ pullback.fst _ _, hG,
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G j)).congr (Category.id_comp _) rfl⟩

theorem etale_of_comp_bijective {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion (φ.comp e)) (h' : ((residue R).comp (φ.comp e)).FormallyUnramified) :
    IsEtaleCompletion φ ∧ ((residue R).comp φ).FormallyUnramified := by
  obtain ⟨h1, h2, h3⟩ := h
  let E := RingEquiv.ofBijective e he
  have hφ : φ = (φ.comp e).comp E.symm.toRingHom := by
    ext a
    exact congrArg φ (E.apply_symm_apply a).symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hφ]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective E.symm.bijective) h1
  · rw [← h2, ← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
  · exact RingHom.Finite.of_comp_finite (f := e) h3
  · exact RingHom.FormallyUnramified.of_comp (f := e) h'

theorem etale_of_comp_openImmersion {S S' : Scheme.{0}} (i : S' ⟶ S) [IsOpenImmersion i] {R : Type} [CommRing R]
    [IsLocalRing R] (ξ' : Sp R ⟶ S') (ξ : Sp R ⟶ S) (hξ : ξ' ≫ i = ξ)
    (h : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (h' : ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) :
    IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified := by
  subst hξ
  have hiso : IsIso (i.stalkMap (ξ' (IsLocalRing.closedPoint (CommRingCat.of R)))) :=
    (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
  have hb : Function.Bijective (i.stalkMap (ξ' (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp] at h h'
  exact etale_of_comp_bijective _ hb _ h h'

theorem generic_mem_of_flat {S : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) (U : S.Opens) (t : S) (ht : t ∈ U) (hs : t ⤳ ξ (closedPoint R))
    (z : Sp (FractionRing R)) : (jK R ≫ ξ) z ∈ U := by
  have hfl : Flat ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ]
    have : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 h
    exact MorphismProperty.comp_mem @Flat _ _ this (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  obtain ⟨p, -, hp⟩ := Flat.generalizingMap ξ hs
  have hz : jK R z ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have ha' : algebraMap R (FractionRing R) a ∈ z.asIdeal := ha
    have := z.isPrime
    rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R _)] at ha'
    rw [ha']
    exact zero_mem _
  exact (hz.map ξ.continuous).mem_open U.isOpen (by rw [hp]; exact ht)

theorem Chart.nonempty_restrict {X S X' S' : Scheme.{0}} [IrreducibleSpace S'] [Nonempty X'] (j : X ⟶ S) [Mono j]
    (j' : X' ⟶ S') [IsOpenImmersion j'] (i : S' ⟶ S) [IsOpenImmersion i] (k : X' ⟶ X) (w : k ≫ j = j' ≫ i)
    (A : Over X) [GrpObj A] (x : S') (C : Chart j A (i x)) : Nonempty (Chart j' ((Over.pullback k).obj A) x) := by
  have h1 : Set.range C.ξ ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of C.R) C.ξ (U := i.opensRange)
      ⟨x, C.centre.symm⟩).ge (Set.mem_univ y)
  let ξ' : Sp C.R ⟶ S' := IsOpenImmersion.lift i C.ξ h1
  have hξ : ξ' ≫ i = C.ξ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨he, hu⟩ := etale_of_comp_openImmersion i ξ' C.ξ hξ C.etc C.unr
  have hg : genericPoint S' ∈ j'.opensRange :=
    ((genericPoint_spec S').mem_open_set_iff j'.opensRange.isOpen).2 (by
      rw [Set.univ_inter]; exact Set.range_nonempty _)
  have h2 : Set.range (jK C.R ≫ ξ') ⊆ Set.range j' := by
    rintro _ ⟨z, rfl⟩
    exact generic_mem_of_flat ξ' he.1 j'.opensRange _ hg (genericPoint_specializes _) z
  let y' : Sp (FractionRing C.R) ⟶ X' := IsOpenImmersion.lift j' (jK C.R ≫ ξ') h2
  have hy' : y' ≫ j' = jK C.R ≫ ξ' := IsOpenImmersion.lift_fac _ _ _
  have hk : C.y = y' ≫ k := by
    rw [← cancel_mono j, Category.assoc, w, ← Category.assoc, hy', Category.assoc, hξ, C.hy]
  refine ⟨{ R := C.R, complete := C.complete, charZero := C.charZero, ξ := ξ', centre := ?_, etc := he, unr := hu,
            G := C.G, semi := C.semi, y := y', hy := hy', α := _,
            gen := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor k y' (C.gen.congr hk rfl) }⟩
  apply i.isOpenEmbedding.injective
  exact (congrArg (fun q => q (closedPoint C.R)) hξ).trans C.centre

theorem hasExt_opensRange (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (j : X ⟶ S) [IsOpenImmersion j] [IsDominant j]
    (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : RelAmple A L)
    (hC : ∀ x : S, Nonempty (Chart j A x)) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (i : Sp R ⟶ S) [IsOpenImmersion i] :
    HasExt (j ∣_ i.opensRange) ((Over.pullback (j ⁻¹ᵁ i.opensRange).ι).obj A) := by
  obtain ⟨x₀, p, hp⟩ := j.denseRange.exists_mem_open i.opensRange.isOpen (Set.range_nonempty i)
  obtain ⟨_, ⟨f : R, rfl⟩, hpf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := (i ⁻¹ᵁ j.opensRange).1) ⟨x₀, hp.symm⟩ (i ⁻¹ᵁ j.opensRange).isOpen
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hpf (zero_mem _)
  have hrange : Set.range (awayMap f) = (PrimeSpectrum.basicOpen f).1 :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have : IsOpenImmersion (awayMap f) := IsOpenImmersion.of_isLocalization f
  have hne : Nonempty (Sp (Localization.Away f)) := by
    obtain ⟨q, -⟩ : p ∈ Set.range (awayMap f) := hrange ▸ hpf
    exact ⟨q⟩
  have h1 : Set.range (awayMap f ≫ i) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hf (hrange.le (Set.mem_range_self z))
  let k : Sp (Localization.Away f) ⟶ X := IsOpenImmersion.lift j (awayMap f ≫ i) h1
  have hk : k ≫ j = awayMap f ≫ i := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ j) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k j
  have hL' := pull_isLB hL (pullback.fst A.hom k)
  obtain ⟨u, hu⟩ := GlobalTheory.lbIso_refl hL'
  have hext : HasExt (awayMap f) ((Over.pullback k).obj A) :=
    GlobalTheory.T.extendsToSemiAbelian_away_of_charts R f hf0 _ (isAbelianScheme_pullback_obj k A hA) (L.pull (pullback.fst A.hom k)) hL'
      (relAmple_pull (isGrpPullback_pullback A k).1 hL hL' ((isGen_iff u).1 hu) k.opensRange
        (isAffineOpen_opensRange k) (fun y => ⟨y, rfl⟩) hamp)
      fun x => (hC (i x)).elim fun C => Chart.nonempty_restrict j (awayMap f) i k hk A x C
  have h2 : Set.range k ⊆ Set.range (j ⁻¹ᵁ i.opensRange).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨awayMap f z, (congrArg (fun q => q z) hk).symm⟩
  let l : Sp (Localization.Away f) ⟶ (j ⁻¹ᵁ i.opensRange).toScheme := IsOpenImmersion.lift _ k h2
  have hl : l ≫ (j ⁻¹ᵁ i.opensRange).ι = k := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (l ≫ (j ⁻¹ᵁ i.opensRange).ι) := by rw [hl]; infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (j ⁻¹ᵁ i.opensRange).ι
  have hcomp : l ≫ (j ∣_ i.opensRange) ≫ i.isoOpensRange.inv = awayMap f := by
    rw [← cancel_mono i, Category.assoc, Category.assoc, i.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
      hl, hk]
  have : IsDominant l := by
    have hd : Dense (Set.range (awayMap f)) :=
      (awayMap f).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
    have hg := ((j ∣_ i.opensRange) ≫ i.isoOpensRange.inv).isOpenEmbedding
    refine ⟨(hd.preimage hg.isOpenMap).mono ?_⟩
    rintro y ⟨z, hz⟩
    exact ⟨z, hg.injective ((congrArg (fun q => q z) hcomp).trans hz)⟩
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have : IsLocallyNoetherian (j ⁻¹ᵁ i.opensRange).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion ((j ⁻¹ᵁ i.opensRange).ι ≫ j)
  have : TopologicalSpace.NoetherianSpace (j ⁻¹ᵁ i.opensRange).toScheme :=
    ((j ⁻¹ᵁ i.opensRange).ι ≫ j).isOpenEmbedding.isInducing.noetherianSpace
  have : AlgebraicGeometry.IsNoetherian (j ⁻¹ᵁ i.opensRange).toScheme := {}
  have : GlobalTheory.IsNormalScheme (j ⁻¹ᵁ i.opensRange).toScheme :=
    GlobalTheory.IsNormalScheme.of_isOpenImmersion ((j ⁻¹ᵁ i.opensRange).ι ≫ j)
  refine HasExt.of_dense (GlobalTheory.IsNormalScheme.pred _) l _ _
    (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ A hA)) ((Over.pullback k).obj A) _
    (ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor _ l ((isGrpPullback_pullback A k).congr hl.symm rfl))
    (HasExt.of_comp _ i.isoOpensRange.inv _ ?_)
  rw [Category.assoc, hcomp]
  exact hext

theorem exists_hasExt_near : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A) := by
  intro X S _ hS j _ hj A _ hA L hL hamp hC s
  have := GlobalTheory.IsNormalScheme.of_pred hS
  let Z : S.Opens := GlobalTheory.IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents s⟩
  obtain ⟨U, hU, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := Z) (x := s) mem_irreducibleComponent
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace
    ⟨⟨s, hs⟩, isIrreducible_irreducibleComponent.2.open_subset U.isOpen hle⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : IsIntegral (Spec Γ(S, U)) := IsIntegral.of_isIso hU.isoSpec.hom
  have : IsDomain Γ(S, U) := (affine_isIntegral_iff _).1 this
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(S, U) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hU
  let i : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion i := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  refine ⟨i.opensRange, ?_, hasExt_opensRange X S hS j A hA L hL hamp hC Γ(S, U) i⟩
  exact hU.range_fromSpec.ge hs

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentBasisPullbackToSpecOfAffineOpen
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

namespace GlobalTheory.LocReg.BasisPull

theorem exists_basis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t0 : SAB H X) (U : X.affineOpens) (R : Type) [CommRing R] (ρ : Γ(X, U.1) →+* R) (t : SAB H (Sp R)) (f : Sp R ⟶ X), f = spMap ρ ≫ chart U → ∀ (φ : SABMap t t0 f) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t0.G.left)), (∀ i, IsTanAtG t0 (chart U) (v i)) → (∀ w, IsTanAtG t0 (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t0 (chart U) v cf w) → ∃ vR : Fin n → (Sp (DualNumber Γ(Sp R, ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (vR i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) w → ∃! cf : Fin n → Γ(Sp R, ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) vR cf w) ∧ ∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ)) ≫ v i := by
  intro E _ _ _ H X t0 U R _ ρ t f hf φ n v hv hb
  let ψ : Γ(X, U.1) →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp ρ
  have hx : spMap ψ ≫ chart U = chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) ≫ f := by
    rw [hf, ← Category.assoc]
    congr 1
    rw [chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hv' := fun i => GlobalTheory.LieMet.isTan_map ψ hx (hv i)
  have hb' := GlobalTheory.GradedPieces.basis_map ψ hx hv hb
  choose vR hvR1 hvR2 using fun i => GlobalTheory.ShFam.OpenReg.exists_lift φ
    (spMap (algebraMap Γ(Sp R, ⊤) (DualNumber Γ(Sp R, ⊤))) ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    (spMap (dualMap ψ) ≫ v i) (by rw [(hv' i).1, Category.assoc])
  refine ⟨vR, fun i => (GlobalTheory.ShFam.OpenReg.tan_iff φ rfl (hvR1 i)).1 (by rw [hvR2]; exact hv' i), fun w hw => ?_, hvR2⟩
  have e : (fun i => spMap (dualMap ψ) ≫ v i) = fun i => vR i ≫ φ.φ := funext fun i => (hvR2 i).symm
  have h := hb' (w ≫ φ.φ) ((GlobalTheory.ShFam.OpenReg.tan_iff φ rfl hw.1).2 hw)
  rw [e] at h
  exact (existsUnique_congr fun cf => GlobalTheory.ShFam.OpenReg.comb_iff φ rfl hvR1 cf hw.1).1 h

end GlobalTheory.LocReg.BasisPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

def siegLamData (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := Q.B
  ab := Q.isAb
  P := abelian₂ Q.B Q.M.L
  isLB := LB.isLB_linComb Q.M.isLB _ _
  rig₁ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull Q.M.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG Q.isAb (pull_isLB (LB.isLB_linComb Q.M.isLB _ _) _) _

theorem lbIso_diag_data {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    LBIso ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left)
      (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
  have hL := Q.M.isLB
  have hT : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have hc := fun x y z => diff₃_ptCls (T := Q.B) hL hT x y z
  have hrM : Out.Rigidified Q.B Q.M.L := ⟨Q.M.rig, Q.M.rigGen⟩
  have p1 : ptCls Q.M.L Q.B 1 = 1 := ptCls_one hL hrM Q.B
  have einv : GrpObj.inv (X := Q.B) = (𝟙 Q.B)⁻¹ := by simp [Hom.inv_def]
  have key : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B) =
      ptCls Q.M.L Q.B (𝟙 Q.B) * ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹ := by
    have a := diff₂_mul_right hc (𝟙 Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹
    rw [mul_inv_cancel] at a
    have b : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) 1 = 1 := by
      simp only [diff₂, _root_.mul_one, p1, inv_one, mul_inv_cancel]
    have c : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹ =
        1 * (ptCls Q.M.L Q.B (𝟙 Q.B))⁻¹ * (ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹)⁻¹ * 1 := by
      rw [diff₂, mul_inv_cancel, p1]
    rw [b, c] at a
    exact GlobalTheory.AdjPolLocal.le_val_one_add_pow_sub a
  refine lbIso_nested hL _ _ _ _ _ _ ?_
  rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_two]
  refine (prod_lam _ _ (cls Q.M.L)).trans ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one]
  refine key.trans ?_
  rw [einv]
  rfl

theorem relAmple_diag {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : Data R)
    (hD : ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left).IsLB) :
    RelAmple Q.B ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left) := by
  have := Q.isAb.proper
  have hMa : IsAmpleLB Q.M.L := isAmpleLB_of_relAmple_of_isAffine Q.B Q.M.isLB Q.ample
  have hN : IsAmpleLB (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
    have := GlobalTheory.GraphVolume.isAmpleLB_graph hMa (GrpObj.inv (X := Q.B)).left (N := 1) le_rfl
    rwa [Nat.cast_one] at this
  have hDa := hN.of_lbIso hD (lbIso_diag_data Q)
  refine relAmple_of_isAmpleLB Q.B hD fun U hU => ?_
  have : CompactSpace (Q.B.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := Q.B.hom) _ U.isOpen hU.isCompact)
  exact hDa.pull_of_isOpenImmersion _

end GlobalTheory.MumFam.TensPol

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

end GlobalTheory.MumFam.TensPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogenyStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H), q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q → kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  first | exact @GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le | exact GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le | (intros; apply GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le <;> assumption)
end

