import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropicGlobalFormOfDoubling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifSections

open Opposite

theorem isIntegral_of_iso_comp {A B C E : CommRingCat.{0}} (i : A ⟶ B) (f : B ⟶ C) (m : C ⟶ E) [IsIso i]
    [IsIso m] (h : (i ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv i ≫ (i ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv i)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (V : Z₂.Opens) (hV : IsAffineOpen V) : (ρ.app V).hom.IsIntegral := by
  have : IsAffine V.toScheme := hV
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ V)
  rw [morphismRestrict_appTop] at h
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (q : A = B), IsIso (eqToHom q) := fun q => by
    subst q; rw [eqToHom_refl]; infer_instance
  exact @isIntegral_of_iso_comp _ _ _ _ _ _ _ (hi _) (hi _) h

theorem isNormalScheme_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) [Smooth p] :
    GlobalTheory.IsNormalScheme Y :=
  (GlobalTheory.isNormalScheme_iff Y).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
    ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))

theorem exists_germ_eq {Y : Scheme.{0}} [IsIntegral Y] [GlobalTheory.IsNormalScheme Y] (y : Y) (hy : y = genericPoint Y)
    (V : Y.Opens) (hyV : y ∈ V) (t : Y.presheaf.stalk y)
    (h : ∀ x ∈ V, ∃ (W : Y.Opens) (hW : y ∈ W), x ∈ W ∧ W ≤ V ∧
      (Y.presheaf.germ W y hW).hom.IsIntegralElem t) :
    ∃ a : Γ(Y, V), Y.presheaf.germ V y hyV a = t := by
  subst hy
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  refine GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV, hi⟩ := h x hx
  have hne : Nonempty W := ⟨⟨_, hW⟩⟩
  have := GlobalTheory.IsNormalScheme.isIntegrallyClosedIn_functionField (X := Y) W
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(Y, W)) (A := Y.functionField)).1 hi
  exact ⟨W, hne, s, hxW, hWV, hs⟩

theorem isoOver_top {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [GlobalTheory.IsNormalScheme Y]
    (σ : X ⟶ Y) [UniversallyClosed σ] (U : Y.Opens) [IsIso (σ ∣_ U)]
    (hU : ((σ ⁻¹ᵁ U : X.Opens) : Set X).Nonempty) : IsoOver σ ⊤ := by
  intro V _
  have hηU : genericPoint X ∈ σ ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ U).isOpen).2 (by simpa using hU)
  have hmem : ∀ V : Y.Opens, (V : Set Y).Nonempty → σ (genericPoint X) ∈ V := by
    intro V hV
    obtain ⟨y, hyV, hyU⟩ := nonempty_preirreducible_inter V.isOpen U.isOpen hV ⟨_, hηU⟩
    obtain ⟨x, hx⟩ := (σ ∣_ U).surjective ⟨y, hyU⟩
    have hx' : σ x.1 = y := (morphismRestrict_base_coe σ U x).symm.trans (congrArg Subtype.val hx)
    have hne : ((σ ⁻¹ᵁ V : X.Opens) : Set X).Nonempty := ⟨x.1, show σ x.1 ∈ V from hx' ▸ hyV⟩
    exact ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ V).isOpen).2 (by simpa using hne)
  have hgen : σ (genericPoint X) = genericPoint Y := by
    have h1 : σ (genericPoint X) ⤳ genericPoint Y :=
      specializes_iff_forall_open.2 fun s hs hg => hmem ⟨s, hs⟩ ⟨_, hg⟩
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hS : IsIso (σ.stalkMap (genericPoint X)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap σ U ⟨_, hηU⟩)).1
      (((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 inferInstance).2 ⟨_, hηU⟩)
  have hSb := ConcreteCategory.bijective_of_isIso (σ.stalkMap (genericPoint X))
  by_cases hV : (V : Set Y).Nonempty
  swap
  · exact isoOver_of_isIso σ (O := U) V fun y hy => (hV ⟨y, hy⟩).elim
  have hyV := hmem V hV
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a a' e => ?_, fun b => ?_⟩
  · apply germ_injective_of_isIntegral Y (σ (genericPoint X)) hyV
    apply hSb.1
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, e]
  obtain ⟨t, ht⟩ := hSb.2 (X.presheaf.germ (σ ⁻¹ᵁ V) (genericPoint X) hyV b)
  obtain ⟨a, ha⟩ := exists_germ_eq (σ (genericPoint X)) hgen V hyV t fun y hy => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    have hWV' : W ≤ V := hWV
    have hηW : σ (genericPoint X) ∈ W := hmem W ⟨y, hyW⟩
    refine ⟨W, hηW, hyW, hWV', ?_⟩
    have hi := isIntegral_app σ W hW (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b)
    have h2 := RingHom.IsIntegralElem.map hi (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom
    have e1 : (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom.comp (σ.app W).hom =
        (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.germ W (σ (genericPoint X)) hηW).hom :=
      RingHom.ext fun a => (Scheme.Hom.germ_stalkMap_apply σ W _ hηW a).symm
    have e2 : X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW
        (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b) = σ.stalkMap (genericPoint X) t := by
      exact (X.presheaf.germ_res_apply (homOfLE (σ.preimage_mono hWV')) _ hηW b).trans ht.symm
    rw [e1, e2] at h2
    have h3 := RingHom.IsIntegralElem.map h2 (inv (σ.stalkMap (genericPoint X))).hom
    have e3 : (inv (σ.stalkMap (genericPoint X))).hom.comp (σ.stalkMap (genericPoint X)).hom =
        RingHom.id _ := by
      rw [← CommRingCat.hom_comp, IsIso.hom_inv_id]; rfl
    rwa [← RingHom.comp_assoc, e3, RingHom.id_comp, ← RingHom.comp_apply, e3, RingHom.id_apply] at h3
  refine ⟨a, germ_injective_of_isIntegral X (genericPoint X) hyV ?_⟩
  rw [← Scheme.Hom.germ_stalkMap_apply, ha, ht]

theorem modification_lineBundleGlobalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ),
    SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB →
    letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  intro k _ Y _ p U D hs hp M _ B hB
  haveI := hs
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  haveI : IsProper (M.σ ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver M.proj
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI := M.iso
  have hb := (isoOver_top M.σ U M.dense.nonempty).bijective_pull (p := p) hB (W := ⊤) le_top le_top
  letI := algebraΓOfHom p
  letI := algebraΓOfHom M.str
  rw [← H0.finrank_top M.str (B.pull M.σ), ← H0.finrank_top p B]
  exact (LinearEquiv.ofBijective _ hb).finrank_eq.symm

end GlobalTheory.ModifSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFunctionalNonvanishing
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKSoKill

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

open Classical in

theorem pure_update_zero (v : Pl F) (f : SInf F κ) (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hfin : ∀ x : κ → AF F, (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite) :
    pure f (Function.update φ v 0) = 0 := by
  funext x
  rw [GlobalTheory.ThK.LocalOps.pure_split v f φ (Function.update φ v 0) x (hfin x)
    (fun w hw => Function.update_of_ne hw _ _), Function.update_self, Pi.zero_apply, zero_mul, Pi.zero_apply]

open Classical in

theorem pure_update_sum (v : Pl F) (f : SInf F κ) (φ : ∀ w : Pl F, (κ → Fv F w) → ℂ)
    (hfin : ∀ x : κ → AF F, (Function.mulSupport fun w => φ w fun i => evFin F w (x i)).Finite)
    {N : ℕ} (a : Fin N → ℂ) (g : Fin N → (κ → Fv F v) → ℂ) :
    pure f (Function.update φ v (∑ m, a m • g m)) = ∑ m, a m • pure f (Function.update φ v (g m)) := by
  funext x
  rw [GlobalTheory.ThK.LocalOps.pure_split v f φ _ x (hfin x) (fun w hw => Function.update_of_ne hw _ _),
    Function.update_self, Finset.sum_apply, Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := GlobalTheory.ThK.LocalOps.pure_split v f φ (Function.update φ v (g m)) x (hfin x)
    (fun w hw => Function.update_of_ne hw _ _)
  rw [Function.update_self] at h
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h, mul_assoc]

end GlobalTheory.ThKSoKill

namespace GlobalTheory.ThKSoKill

theorem at_vecMulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (v : Pl F) (c : Fin n → AE F E) (z : Fin d → AE F E) (hz : At (evFin F v) z) :
    At (evFin F v) (Matrix.vecMulVec c z) := by
  intro u hu
  ext i j
  have h := congrFun (hz u hu) j
  simp only [Pi.smul_apply, Pi.zero_apply] at h
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  rw [← mul_smul_comm, h, mul_zero]

open Classical in

theorem so_kill : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (Λ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (c : Fin n → AE F E),
    (fun k => piW B.τ₁ (c k)) ≠ 0 →
    (∀ z : Fin d → AE F E, At (evFin F B.v₁) z → (∀ l, piW (B.τ₁.comp σ) (z l) = 0) →
      ∀ Ψ ∈ schA F (Fin n × Fin d), Λ (M.co.rho B.ψ (Matrix.vecMulVec c z) Ψ) = Λ Ψ) →
    ∀ Φ ∈ M.So B.ψ B.τ₁, Λ Φ = 0 := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Λ c hc hinv Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero => exact map_zero Λ
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]
  | mem x hx =>
    obtain ⟨f, φ, hSB, hcof, ⟨hSB1, ι, hι, hrank⟩, rfl⟩ := hx
    have hstd := (hcof.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    have hfin := fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x
    have hpure := GlobalTheory.ConeMeasV.pure_mem_schA hP.good f φ hSB hcof
    obtain ⟨N, a, w, ha1, hkill⟩ := GlobalTheory.T.rank_deficient_schwartz_average F B.v₁ (GlobalTheory.LatVac.psiAt B.ψ B.v₁)
      (GlobalTheory.SchrSB.continuous_psiAt B.ψ hP.base.std.1 B.v₁) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hP.base.std B.v₁)
      n d (fun k => piW B.τ₁ (c k)) hc (ι (φ B.v₁)) (hι.bij.mapsTo hSB1) hrank
    have hmult := fun m => GlobalTheory.T.pair_linear_bar_vector F E σ B n d X W M χX χW om r s r' s' hP c ι hι (w m)
    choose z hzat hzpi hzmul using hmult
    have hAE := GlobalTheory.ThK.LocalOps.actsEx hKP.base
    have hex : ∀ m, ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F B.v₁) ∧
        Acts (evFin F B.v₁) (M.co.rho B.ψ (Matrix.vecMulVec c (z m))) (φ B.v₁) φ₁ := fun m =>
      ((hAE F E σ B n d X W M χX χW om r s r' s' hP B.v₁).2.1 _ (at_vecMulVec B.v₁ c (z m) (hzat m)) _ hSB1).exists
    choose φ₁ hφ₁SB hφ₁ using hex

    have hsumSB : ∑ m, a m • φ₁ m ∈ SB (Fin n × Fin d → Fv F B.v₁) :=
      Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hφ₁SB m)
    have hsum0 : ∑ m, a m • φ₁ m = 0 := by
      refine hι.bij.injOn hsumSB (Submodule.zero_mem _) ?_
      rw [map_zero, map_sum]
      funext Y
      rw [Finset.sum_apply, Pi.zero_apply]
      have hY := hkill Y
      rw [Finset.sum_mul] at hY
      rw [← hY]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, hzmul m (φ B.v₁) hSB1 (φ₁ m) (hφ₁SB m) (hφ₁ m) Y,
        GlobalTheory.LatVac.psiAt_apply, mul_assoc]

    have hact : ∀ m, M.co.rho B.ψ (Matrix.vecMulVec c (z m)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pure f (Function.update φ B.v₁ (φ₁ m)) :=
      fun m => GlobalTheory.ThK.LocalOps.acts_pure B.v₁ _ f φ (φ₁ m) hpure hfin (hφ₁ m)
    calc Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = ∑ m, a m • Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by rw [← Finset.sum_smul, ha1, one_smul]
      _ = ∑ m, a m • Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ (φ₁ m))) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← hact m, hinv (z m) (hzat m) (hzpi m) _ hpure]
      _ = Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ B.v₁ (∑ m, a m • φ₁ m))) := by
          rw [pure_update_sum B.v₁ f φ hfin a φ₁, map_sum]
          simp only [map_smul]
      _ = 0 := by rw [hsum0, pure_update_zero B.v₁ f φ hfin, map_zero]

end GlobalTheory.ThKSoKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLeTopLevelClassSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_le_topLevel_classSum : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ j : Fin D.R.m, congLev D.sp.cm (ch.G.V (.top j)).gram (ch.G.Λ (.top j)) ch.G.modul ≤ ch.S.levTop A.μ0 Φ β j j.2 := by
  first | exact @GlobalTheory.LevTopCong.congLev_le_levTop | exact GlobalTheory.LevTopCong.congLev_le_levTop | (intros; apply GlobalTheory.LevTopCong.congLev_le_levTop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicStabiliserSplitLatticeStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_isotropicStabiliser_splitLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν → ν DN = 1 → ∃ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), SemiLat (unipRad σ J X) (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) ν π DN DM := by
  first | exact @GlobalTheory.ResidueEisenstein.semiLat_frameGrp | exact GlobalTheory.ResidueEisenstein.semiLat_frameGrp | (intros; apply GlobalTheory.ResidueEisenstein.semiLat_frameGrp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReScalNonzeroIndexPlaceIff
section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

namespace GlobalTheory.BigOn

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isLev_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.toLevCh.Is A.μ0) :
    (reScal R lam kap).toLevCh.Is A.μ0 := h

theorem isGrp_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsGrp F) :
    (reScal R lam kap).IsGrp F := { h with }

theorem isFam_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsFam) :
    (reScal R lam kap).IsFam := { h with }

theorem isModels_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsModels) :
    (reScal R lam kap).IsModels := { h with }

theorem isChain_reScal (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsChain) :
    (reScal R lam kap).IsChain := { h with }

theorem isThP_rescale (R : RealDat D A Ks) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsThP) :
    (reScal R lam kap).IsThP := { h with }

def reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) : CxData B :=
  { X with lam := lam, κ := κ }

theorem liftMatC_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) :
    (reScalCx X lam κ).liftMatC cr b j t = X.liftMatC cr b j t := rfl

theorem liftMat_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) :
    (reScalCx X lam κ).liftMat cr b j t = X.liftMat cr b j t :=
  congrArg (kMat Bs.v0.embedding) (liftMatC_reScalCx X lam κ cr b j t)

theorem iw_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) {fc : DefSub B → DefFace Bs} (cr : Crd B fc)
    (b : Bool) : ((reScalCx X lam κ).data cr b).Iw = (X.data cr b).Iw := by
  funext j t w
  exact congrArg (fun θ => idx w (X.M b j) (matLat θ ((lv (fc X.zs) b).Tl j t))) (liftMat_reScalCx X lam κ cr b j t)

theorem zs_reScalCx {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {B : DefAmb Bs} (X : CxData B)
    (lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ) (κ : InfinitePlace K → ℝ) : (reScalCx X lam κ).zs = X.zs := rfl

set_option maxHeartbeats 1000000 in
theorem toCx_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) :
    (reScal R lam kap).toCx F = reScalCx (R.toCx F) lam (fun _ => kap) := rfl

theorem reScal_nonzeroIndexPlace_iff (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : (reScal R lam kap).NonzeroIndexPlace F w ↔ R.NonzeroIndexPlace F w := by
  unfold RealDat.NonzeroIndexPlace
  rw [toCx_reScal, iw_reScalCx, zs_reScalCx]

theorem isTup_reScal (R : RealDat D A Ks) (F : Face D A) (lam : type_of% R.lam) (kap : ℝ) (h : R.IsTup F) :
    (reScal R lam kap).IsTup F :=
  ⟨fun w hw => h.tw w ((reScal_nonzeroIndexPlace_iff R F lam kap w).1 hw), h.mu_off, h.mu_used, h.mu_ne, h.mu_conj, h.mu_on⟩

end

theorem char_charOf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → R.IsTup F → (charOf R F).Char F := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h1 h2 h3 h4 h5 h6 h7
  obtain ⟨lam, kap, hs⟩ := GlobalTheory.ScalChoice.exists_isScal D G Pl0 T0 A Ks R F
  have hex : ∃ q : (type_of% R.lam) × ℝ, (reScal R q.1 q.2).Char F :=
    ⟨(lam, kap), isLev_reScal R lam kap h1, isGrp_reScal R F lam kap h2, isFam_reScal R lam kap h3,
      isModels_reScal R lam kap h4, isChain_reScal R lam kap h5, isThP_rescale R lam kap h6, hs,
      isTup_reScal R F lam kap h7⟩
  exact Classical.epsilon_spec hex

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsActFockVectorsAnyDatumStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_act_fock_vectors_any_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (φ : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg Q ξR (R.vacP i) φ → ∀ u ∈ GinfC (Vc D i), ∀ x w, R.ωP i A.μ0 (u, 1) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x w)) = pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x ((R.cV i).ρ u w)) := by
  first | exact @GlobalTheory.FockAnyDatum.om_ioP_of_datum | exact GlobalTheory.FockAnyDatum.om_ioP_of_datum | (intros; apply GlobalTheory.FockAnyDatum.om_ioP_of_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropicGlobalFormOfDoublingStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_anisotropic_global_form_of_doubling : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DoublingMethod → ∀ D : D7, GlobalTheory.BottomRallis.SiegelWeilFockAniso D → GlobalTheory.BottomRallis.GlobalFormAniso D := by
  first | exact @GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso | exact GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso | (intros; apply GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelEquivariant
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix
noncomputable section
namespace GlobalTheory.SplitBarVac

theorem linBar_vac_indicator : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ b₁ : GL (Fin n) (Fv F v), (PsiUnr B.ψ v → b₁ = b) ∧ ∃ ι, M.IsLinBar B.ψ t b₁ c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c hb hc
  have hcm : IsCMExt F E σ := hPair.base.cm
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have htt : (t.comp σ).comp σ = t := AlgHom.ext fun x => by simp [hσσ]
  have hJX : IsHermND σ X.Jᵀ := ⟨fun i j => by simp [Matrix.transpose_apply, hPair.herm.herm],
    by rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hPair.herm⟩
  have hL := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hPair.base hPair.herm v
  have hb2 := hb.dual hcm hJX hL
  obtain ⟨z, c₂, hz1, hc2v, hc2⟩ := GlobalTheory.T.skewHermitianLattice_splitPlace_components_dual F E σ B d W r' s' hPair.base hPair.skew v t c hc
  have hc3 : IsSplitBasis (t.comp σ) W.L (-c₂) := fun u => by
    have := hc2 (-u)
    simp only [Pi.neg_apply, neg_mem_iff, Matrix.mulVec_neg] at this
    simpa [Units.val_neg, Matrix.neg_mulVec, Matrix.mulVec_neg] using this
  refine ⟨Units.map (Matrix.scalar (Fin n) : Fv F v →+* Matrix (Fin n) (Fin n) (Fv F v)).toMonoidHom z * b,
    fun hu => by simp [hz1 hu], ?_⟩
  obtain ⟨ι, hι, hvac⟩ := GlobalTheory.T.split_basis_witt_model_local hP F E σ B n d X W M χX χW om r s r' s' hPair v (t.comp σ) _ _ hb2 hc3
  refine ⟨ι, ?_, hvac⟩
  unfold Model.IsLinW at hι
  rw [htt] at hι
  unfold Model.IsLinBar
  convert hι using 1
  have e1 : ((dualConj 1 (splitGram hJX t * b))⁻¹).1 = b.1ᵀ * X.J.map t := by
    rw [← map_inv, dualConj_val]
    simp [Matrix.transpose_mul, Matrix.transpose_map]
  have e2 : ((-c₂)⁻¹).1 = -((z : Fv F v) • (c.1ᵀ * W.J.map t)) := by
    first
    | (rw [← hc2v]; simp)
    | (rw [← hc2v, Units.neg_inv]; rfl)
    | (rw [← hc2v]; exact congrArg Units.val (neg_inv c₂))
  ext Y i j
  rw [e1, e2]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.transpose_mul, Matrix.scalar_apply,
    Matrix.transpose_neg, Matrix.transpose_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.diagonal_transpose, Matrix.mul_assoc, neg_neg]
  simp [Matrix.mul_assoc, ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, Matrix.smul_mul]
end GlobalTheory.SplitBarVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceSiegelLawDiagonalLagrangianCharacter
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.splitPlace_siegelLaw_diagonalLagrangian_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle,
        (∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f) →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f₀ ≠ 0 →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) → α t = χS (Matrix.GeneralLinearGroup.det t) := by
  first | exact @PositivityTheory.ThKW.lagrangian_integral_parseval | exact PositivityTheory.ThKW.lagrangian_integral_parseval | (intros; apply PositivityTheory.ThKW.lagrangian_integral_parseval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimesStatement
section
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert | exact GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert | (intros; apply GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert <;> assumption)
end

