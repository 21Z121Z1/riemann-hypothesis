import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg

theorem affineFromSpec_comp_eq_specMap_cst {R : Type} [CommRing R] {W : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (V : W.affineOpens) :
    V.2.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (cst f V.1)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) V.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

theorem comap_idealSheaf_pow_eq {X Y : Scheme.{0}} (g : Y ⟶ X) (K : X.IdealSheafData) (k : ℕ) :
    (K ^ k).comap g = (K.comap g) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact Scheme.IdealSheafData.comap_top g
  | succ n ih =>
    rw [pow_succ, pow_succ, GlobalTheory.Principalise.comap_mul_idealSheaf, ih]

theorem isIso_pullbackSnd_restrict_preimage {X Y S : Scheme.{0}} (π : X ⟶ S) (g : Y ⟶ S) (U : S.Opens)
    (h : IsIso (π ∣_ U)) : IsIso (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) := by
  have hEq : pullback.fst π g ⁻¹ᵁ π ⁻¹ᵁ U = pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U := by
    show (pullback.fst π g ≫ π) ⁻¹ᵁ U = (pullback.snd π g ≫ g) ⁻¹ᵁ U
    rw [pullback.condition]
  have L : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U).ι (π ⁻¹ᵁ U).ι (pullback.fst π g) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by simpa only [Scheme.Opens.opensRange_ι] using hEq)
  have s := L.paste_vert (IsPullback.of_hasPullback π g)
  have key : IsPullback ((pullback.fst π g).resLE (π ⁻¹ᵁ U) (pullback.snd π g ⁻¹ᵁ g ⁻¹ᵁ U) hEq.ge)
      (pullback.snd π g ∣_ (g ⁻¹ᵁ U)) (π ∣_ U) (g ∣_ U) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_morphismRestrict g U)
    · rw [morphismRestrict_ι, morphismRestrict_ι]
      exact s
    · rw [← cancel_mono U.ι]
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
        Scheme.Hom.resLE_comp_ι_assoc, pullback.condition]
  exact key.isIso_snd_of_isIso h

theorem ideal_eq_of_reduces_affine : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W]
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t →
    ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) →
    ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  intro R _ I W W' _ f π U hπ hU K hK t ht V
  obtain ⟨hbc, hbs, -⟩ := GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support
  obtain ⟨hbC, hloc⟩ := GlobalTheory.T.baseIdealSheafOfIdeal_spec_bijective_calculus
  haveI : IsNoetherianRing Γ(W, V.1) := IsLocallyNoetherian.component_noetherian V
  obtain ⟨C, _, φ, hCn, hφ, hC, hfaith⟩ := GlobalTheory.T.exists_adicCompletion_noetherian_flat_complete Γ(W, V.1) (I.map (cst f V.1))
  haveI := hCn
  haveI := hπ
  have hJjac : (I.map (cst f V.1)).map φ ≤ Ideal.jacobson ⊥ := by
    haveI := hC
    exact IsAdicComplete.le_jacobson_bot _
  haveI hφF : Flat (Spec.map (CommRingCat.ofHom φ)) := AlgebraicGeometry.Flat.SpecMap_iff.mpr hφ
  have hOF : Flat V.2.fromSpec :=
    @HasRingHomProperty.of_isOpenImmersion @Flat RingHom.Flat _ _ _ _ RingHom.Flat.containsIdentities
      V.2.isOpenImmersion_fromSpec
  have hgF : Flat (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) :=
    MorphismProperty.comp_mem @Flat _ _ hφF hOF
  have F1 : ∀ X : W.IdealSheafData, X.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((X.ideal V).map φ) := fun X => hloc W V C φ X
  have F2 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).ideal V = (I.map (cst f V.1)) ^ (e + 1) := by
    intro e
    rw [baseIdeal_ideal, Ideal.map_pow]
  have F4 : ∀ e : ℕ, (baseIdeal f (I ^ (e + 1))).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, F2, Ideal.map_pow]
  have F5 : ∀ e : ℕ, ((t e).ideal V).map φ = ((t (e + 1)).ideal V).map φ ⊔ ((I.map (cst f V.1)).map φ) ^ (e + 1) := by
    intro e
    conv_lhs => rw [ht e]
    rw [← Ideal.map_pow, ← F2 e, ← Ideal.map_sup]
    rfl
  have F6 := GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals C ((I.map (cst f V.1)).map φ) hC (fun e => ((t e).ideal V).map φ) F5
  have F7 : ∀ e : ℕ, (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    rw [F1, ← (hbC C).2, F6 e]
  have F8 : ∀ e : ℕ, (baseIdeal (π ≫ f) (I ^ (e + 1))).comap
      (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) =
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) := by
    intro e
    have hgf : (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ≫ f =
        Spec.map (CommRingCat.ofHom (φ.comp (cst f V.1))) := by
      rw [Category.assoc, affineFromSpec_comp_eq_specMap_cst, ← Spec.map_comp]
      rfl
    rw [hbc, ← Category.assoc, pullback.condition, Category.assoc, hgf, hbs, ← Ideal.map_map,
      Ideal.map_pow, Ideal.map_pow]
  have hKC : ∀ x, x ∉ (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)).support →
      x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U := by
    intro x hx
    refine hK _ (fun h => hx ?_)
    rw [Scheme.IdealSheafData.support_comap]
    exact h
  have hπC : IsProper (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := inferInstance
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.map_inf_eq_of_reductions_jacobson_induction C ((I.map (cst f V.1)).map φ) hJjac _
    (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) _ hπC
    (isIso_pullbackSnd_restrict_preimage π _ U hU) _
    (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ)) hKC
  refine ⟨k₀, fun k hk T' T'' hT' hT'' e => ?_⟩
  have h1 : ∀ e : ℕ, T'.comap (pullback.fst π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ⊔
      baseIdeal (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec))
        (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      (baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1))).comap
        (pullback.snd π (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) := by
    intro e
    have hT'e : T' ⊔ baseIdeal (π ≫ f) (I ^ (e + 1)) = (t e).comap π := hT' e
    rw [← F8 e, ← Scheme.IdealSheafData.comap_sup, hT'e, ← F7 e,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, pullback.condition]
  have h2 : ∀ e : ℕ, T''.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⊔
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) =
      baseIdeal (𝟙 (Spec (CommRingCat.of C))) (⨅ l, ((t l).ideal V).map φ) ⊔
        baseIdeal (𝟙 (Spec (CommRingCat.of C))) (((I.map (cst f V.1)).map φ) ^ (e + 1)) ⊔
        (K.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec)) ^ k := by
    intro e
    have hT''e : T'' ⊔ baseIdeal f (I ^ (e + 1)) = t e ⊔ K ^ k := hT'' e
    rw [← F4 e, ← Scheme.IdealSheafData.comap_sup, hT''e, Scheme.IdealSheafData.comap_sup, F7 e,
      comap_idealSheaf_pow_eq, F4 e]
  have hmain := hk₀ k hk _ _ h1 h2
  have hX : ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).comap
      (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) =
      (t e).comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) := by
    rw [Scheme.IdealSheafData.comap_sup, GlobalTheory.T.idealSheafData_comap_inf_of_flat _ _ _ hgF,
      GlobalTheory.T.map_comap_eq_comap_map_of_flat W W' _ _ π _ (pullback.fst π _) (pullback.snd π _) (IsPullback.of_hasPullback π _) hgF
        inferInstance, hmain, F4 e, F7 e]
  rw [F1, F1] at hX
  have hX' := (hbC C).1.1 hX
  have hle1 : (I.map (cst f V.1)) ^ (e + 1) ≤ ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp le_sup_right V
  have hle2 : (I.map (cst f V.1)) ^ (e + 1) ≤ (t e).ideal V := by
    rw [← F2 e]
    exact Scheme.IdealSheafData.le_def.mp (ht.baseIdeal_le e) V
  calc ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V
      = ((((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V).map φ).comap φ := (hfaith _ _ hle1).symm
    _ = ((((t e).ideal V)).map φ).comap φ := by rw [hX']
    _ = (t e).ideal V := hfaith _ _ hle2

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastExtra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem mapsAt₂_val : ∀ (Y X X₁ X₂ Z : Scheme.{0}) (L : LB X) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ) (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n))) (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))), MapsAt₂ w p n a b₁ b₂ → ∀ (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι), Good L z J → Good L₁ z J₁ → Good L₂ z J₂ → val b₁ r z J₁ * val b₂ r z J₂ = gm (r ≫ p) z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)), J (r ≫ p))) ^ n * val a r z J := by
  intro Y X X₁ X₂ Z L L₁ L₂ f₁ f₂ w p n a b₁ b₂ hM r z J J₁ J₂ hJ hJ₁ hJ₂
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U
      (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)), J (r ≫ p)) :=
    ⟨⟨Set.mem_iInter.2 fun _ => hJ₁ (r ≫ p ≫ f₁), Set.mem_iInter.2 fun _ => hJ₂ (r ≫ p ≫ f₂)⟩, hJ (r ≫ p)⟩
  have e := congrArg (gm r z _) (hM (J₁ (r ≫ p ≫ f₁)) (J₂ (r ≫ p ≫ f₂)) (J (r ≫ p)))
  rw [map_mul, map_mul, map_zpow] at e
  exact (congrArg₂ (· * ·) (gm_res r z _ hm _) (gm_res r z _ hm _)).symm.trans
    (e.trans (congrArg₂ (· * ·) (congrArg (· ^ n) (gm_pull r p z _ hm _)) (gm_res r z _ hm _)))

end GlobalTheory.MumProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_kappaOrbital_unit_eq_signedLatticeSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Monic → Q₂.Monic → Q₁.natDegree + Q₂.natDegree = n → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → ∀ B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → B₁.P = Q₁.map e.symm.toRingHom → B₂.P = Q₂.map e.symm.toRingHom → kapOrb n w Q₁ Q₂ ((KL n w : Set (UL n w)).indicator 1) = (B₁.kapSum B₂ : ℂ) := by
  first | exact @GlobalTheory.InertUnitOrb.kapOrb_unit_eq_kapSum | exact GlobalTheory.InertUnitOrb.kapOrb_unit_eq_kapSum | (intros; apply GlobalTheory.InertUnitOrb.kapOrb_unit_eq_kapSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSumStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  first | exact @GlobalTheory.InertTwUnit.twisted_unit_eq_stSum | exact GlobalTheory.InertTwUnit.twisted_unit_eq_stSum | (intros; apply GlobalTheory.InertTwUnit.twisted_unit_eq_stSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimLeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_finite_of_ringKrullDim_le' : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] (b : A →+* R), b.Finite → ringKrullDim A ≤ ringKrullDim R → Function.Injective b := by
  first | exact @GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le | exact GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le | (intros; apply GlobalTheory.FiniteMapInj.injective_of_finite_of_ringKrullDim_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mum

theorem intAt_of_integral_mul_basicOpen : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ∀ (x : X) (d : Γ(X, W)), x ∈ X.basicOpen d → (α.app W).hom.IsIntegralElem ((α.app W).hom d * chartVal L α s j W hW) → IntAt L α s x := by
  intro X Y L α k s j W hW hWa x d hx hint
  have hle : X.basicOpen d ≤ W := X.basicOpen_le d
  have hW' : X.basicOpen d ≤ L.U j := hle.trans hW
  refine ⟨j, X.basicOpen d, hW', hx, hWa.basicOpen d, ?_⟩
  set ρX := (X.presheaf.map (homOfLE hle).op).hom with hρX
  set ρY := (Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom with hρY
  have hnat : ∀ r, ρY ((α.app W).hom r) = (α.app (X.basicOpen d)).hom (ρX r) := by
    intro r
    have := congrArg (fun g => g.hom r) (Scheme.Hom.naturality α (homOfLE hle).op)
    simpa [ρX, ρY] using this.symm
  have hcv : chartVal L α s j (X.basicOpen d) hW' = ρY (chartVal L α s j W hW) := by
    simp only [chartVal, ρY]
    change _ = (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op ≫
      Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom _
    rw [← Functor.map_comp]
    rfl

  have hint' : (α.app (X.basicOpen d)).hom.IsIntegralElem (ρY ((α.app W).hom d * chartVal L α s j W hW)) := by
    obtain ⟨p, hp, hp0⟩ := hint
    refine ⟨p.map ρX, hp.map ρX, ?_⟩
    rw [Polynomial.eval₂_map]
    have : ((α.app (X.basicOpen d)).hom.comp ρX) = ρY.comp (α.app W).hom := by
      ext r; exact (hnat r).symm
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  obtain ⟨u, hu⟩ : IsUnit (ρX d) := X.toRingedSpace.isUnit_res_basicOpen d
  have hmul : ρY ((α.app W).hom d * chartVal L α s j W hW) =
      (α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW' := by
    rw [map_mul, hnat, hcv]
    congr 2
    exact hu.symm
  rw [hmul] at hint'
  have key : chartVal L α s j (X.basicOpen d) hW' =
      (α.app (X.basicOpen d)).hom ((u⁻¹ : (Γ(X, X.basicOpen d))ˣ) : Γ(X, X.basicOpen d)) *
        ((α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW') := by
    rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
  rw [key]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hint'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGenerated
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem sumForm_add {A C K B : Type} [CommRing A] [CommRing C] [CommRing K] [CommRing B]
    (φ : A →+* K) (gc : C →+* B) (gk : K →+* B) {x y : B}
    (hx : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x = ∑ m, gc (c m) * gk (b m))
    (hy : ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ y = ∑ m, gc (c m) * gk (b m)) :
    ∃ (n : ℕ) (c : Fin n → C) (b : Fin n → K), (∀ m, φ.IsIntegralElem (b m)) ∧ x + y = ∑ m, gc (c m) * gk (b m) := by
  first
  | exact @_root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral
  | (apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralAddSum.add_sum_integral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralAddSum.add_sum_integral ..)

theorem isAffineOpen_Sp_field (K : Type) [Field K] (V : (Sp K).Opens) : IsAffineOpen V := by
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases h : (V : Set (Sp K)).Nonempty
  · obtain ⟨x, hx⟩ := h
    have : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    rw [this]; exact isAffineOpen_top _
  · have : V = ⊥ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    rw [this]; exact isAffineOpen_bot _

theorem eq_sum_of_isIntegral_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU f hf
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have hf' : IsIntegral Γ(G.left, W) f := hf
  have hx : IsIntegral Γ(G.left, W) (e.symm f) := hf'.map e.symm.toAlgHom
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := Γ(M.S, U)) (S := Γ(G.left, W))
    (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))).2 ⟨e.symm f, hx⟩
  have hfy : f = e ((TensorProduct.toIntegralClosure Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) y : _)) := by
    rw [congrArg Subtype.val hy]; exact (e.apply_symm_apply f).symm
  rw [hfy]
  clear hfy hy
  induction y with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun m => m.elim0, by simp⟩
  | tmul c b =>
    refine ⟨1, fun _ => c, fun _ => (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), fun _ => b.2, ?_⟩
    rw [Fin.sum_univ_one]
    exact Algebra.IsPushout.equiv_tmul _ _ _ _ c (b : Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U))
  | add u v hu hv =>
    rw [map_add, Subalgebra.coe_add, map_add]
    exact sumForm_add _ _ _ hu hv

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLatticeLAdicReductionStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_lattice_l_adic_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ))
    (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (A' : Over (Sp ℂ)) [GrpObj A'] (L' : LB A'.left)
    (u : HolUnif A' L' (Module.finrank ℚ (FR E))), IsAbelianScheme A' →
    SmoothOfRelativeDimension (Module.finrank ℚ (FR E)) A'.hom → (∀ w, w ∈ u.Λ ↔ ∀ j, w j ∈ Λ.lattice) →
    ∀ j₀ : Fin (Module.finrank ℚ (FR E)),
    ∃ (α : A' ⟶ X.A) (M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ)) (n N : ℕ),
      IsMonHom α ∧ IsFinite α.left ∧ Flat α.left ∧ Surjective α.left ∧ 1 ≤ N ∧
      (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) ∧ (∀ w, U.u.ex (M w) = u.ex w ≫ α) ∧
      M (Pi.single j₀ 1) = (fun _ ↦ (n : ℂ)) ∧ 0 < n ∧ Sz l lam (a0 𝔣 l) ((n : ℂ)⁻¹) := by
  first | exact @GlobalTheory.CMPowerIsogeny.exists_isogeny | exact GlobalTheory.CMPowerIsogeny.exists_isogeny | (intros; apply GlobalTheory.CMPowerIsogeny.exists_isogeny <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelConjugateEmbedding
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

namespace GlobalTheory.FlatModel

theorem frames_changeOfBasis_det_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (τ : E →+* ℂ) (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ) → Fin g → A) (U₂ h₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧ EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) → IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr) (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧ (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧ (letI := io.toAlgebra; (∀ i, IsCombAt y₀.1.x (y₀.1.u τ) (g₁ i) (w₁ i ≫ ν.φ)) ∧ (∀ i, IsCombAt y₀.1.x (y₀.1.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ))) ∧ (∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₁.det) ∧ ∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₂.det := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A _ _ ξ β hξ g e U₁ h₁ U₂ h₂ he hU hP₁ hP₂ T α io y₀ yy hyy hpt
  letI := io.toAlgebra
  set φ₀ : A →+* T.Fr := (algebraMap T.V T.Fr).comp α with hφ₀
  have hbc := isTanBasis_bc he φ₀
  have htan : ∀ i, IsTanAtG Y.t (yy ≫ Y.j) (bcV Y.t φ₀ e i) := fun i => hyy ▸ hbc.1 i
  choose w₁ hw₁ using fun i : Fin (Dw.mult τ) =>
    GlobalTheory.T.exists_tangent_lift_coefficients E H Dw l' Xo' c' W Y T.Fr yy g (bcV Y.t φ₀ e) htan (fun b => φ₀ (U₁ i b))
  choose w₂ hw₂ using fun i : Fin (Dw.mult (conjEmb τ)) =>
    GlobalTheory.T.exists_tangent_lift_coefficients E H Dw l' Xo' c' W Y T.Fr yy g (bcV Y.t φ₀ e) htan (fun b => φ₀ (U₂ i b))
  have hE₁ := fun i => GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A ξ β hξ g (Dw.mult τ) e U₁ he
    (fun S _ φ => (hU S φ).1) T.Fr φ₀ io y₀.1 yy hyy hpt i (w₁ i) (hw₁ i)
  have hE₂ := fun i => GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI (conjEmb τ) A ξ β hξ g (Dw.mult (conjEmb τ)) e U₂ he
    (fun S _ φ => (hU S φ).2) T.Fr φ₀ io y₀.1 yy hyy hpt i (w₂ i) (hw₂ i)
  choose g₁ hg₁ using fun i => (y₀.1.basis τ (w₁ i ≫ ν.φ) (hE₁ i).1 (hE₁ i).2).exists
  choose g₂ hg₂ using fun i => (y₀.1.basis (conjEmb τ) (w₂ i ≫ ν.φ) (hE₂ i).1 (hE₂ i).2).exists
  refine ⟨w₁, w₂, Matrix.of g₁, Matrix.of g₂, hw₁, hw₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · exact GlobalTheory.T.integral_model_embedding_second E H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A ξ β hξ g e U₁ h₁ he (fun S _ φ => (hU S φ).1) hP₁ T α io y₀ yy hyy hpt
      w₁ (Matrix.of g₁) hw₁ hg₁
  · exact GlobalTheory.T.integral_model_embedding_second E H Dw l l' Xo Xo' c c' W Y r ν hle hOI (conjEmb τ) A ξ β hξ g e U₂ h₂ he (fun S _ φ => (hU S φ).2) hP₂ T α io y₀ yy
      hyy hpt w₂ (Matrix.of g₂) hw₂ hg₂

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLocallyNoetherianStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_locally_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → IsLocallyNoetherian Y.X := by
  first | exact @GlobalTheory.ModelNoeth.isLocallyNoetherian_model | exact GlobalTheory.ModelNoeth.isLocallyNoetherian_model | (intros; apply GlobalTheory.ModelNoeth.isLocallyNoetherian_model <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointClosureExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_closure_extension : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (W : V.X.Opens) (x : V.X), x ∈ W → (l : 𝓞 F) ∈ (V.p x).asIdeal → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal ∧ z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ x ⤳ yt (IsLocalRing.closedPoint e.O) ∧ ∀ g : V.X.functionField, RegAt (yt (IsLocalRing.closedPoint e.O)) g → (e.w (TrueGeo.valAt (z ≫ V.j) g) = 1 ↔ UnitAt (yt (IsLocalRing.closedPoint e.O)) g) := by
  first | exact @GlobalTheory.HtGen.IntPt.exists_intPt | exact GlobalTheory.HtGen.IntPt.exists_intPt | (intros; apply GlobalTheory.HtGen.IntPt.exists_intPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormAbelianVarietyTranslateValueStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantForm_abelianVariety_translate_value : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (v : epsR K ⟶ A) (hv : IsTangent v) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A), ev ω.1 P.sec - ev ω.1 (P.tan hv) = (TrivSqZeroExt.inr (algebraMap K P.B (tanVal v ω)) : DualNumber P.B) := by
  first | exact @GlobalTheory.CechKS.ev_sec_sub_ev_tan | exact GlobalTheory.CechKS.ev_sec_sub_ev_tan | (intros; apply GlobalTheory.CechKS.ev_sec_sub_ev_tan <;> assumption)
end

