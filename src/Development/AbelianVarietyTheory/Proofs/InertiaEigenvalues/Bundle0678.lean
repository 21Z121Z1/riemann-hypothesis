import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0671
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetHeckeSumPreservesPrincipalForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TransSum

def conjMeet {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ) : Subgroup Γ :=
  K ⊓ K.comap (MulAut.conj γ⁻¹).toMonoidHom

theorem mem_conjMeet {Γ : Type*} [Group Γ] {K : Subgroup Γ} {γ x : Γ} :
    x ∈ conjMeet K γ ↔ x ∈ K ∧ γ⁻¹ * x * γ ∈ K := by
  simp [conjMeet, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]

theorem exists_sum_inv {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ)
    [hf : ((conjMeet K γ).subgroupOf K).FiniteIndex] :
    ∃ C : Finset Γ, C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ K, δ = k * γ) ∧
      ∀ F : Γ → ℂ, (∀ k ∈ K, ∀ g, F (g * k) = F g) → ∀ k ∈ K, ∀ g,
        ∑ δ ∈ C, F (g * k * δ) = ∑ δ ∈ C, F (g * δ) := by
  classical
  set H := (conjMeet K γ).subgroupOf K
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let r : K ⧸ H → Γ := fun q => ((Quotient.out q : K) : Γ) * γ
  have hr : Function.Injective r := by
    intro q₁ q₂ h
    have h' : (Quotient.out q₁ : K) = Quotient.out q₂ := Subtype.ext (mul_right_cancel h)
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, h']
  refine ⟨Finset.univ.image r, ?_, ?_, ?_⟩
  · exact Finset.image_nonempty.2 ⟨(QuotientGroup.mk 1 : K ⧸ H), Finset.mem_univ _⟩
  · intro δ hδ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨_, (Quotient.out q).2, rfl⟩
  · intro F hF k hk g
    rw [Finset.sum_image (fun a _ b _ h => hr h), Finset.sum_image (fun a _ b _ h => hr h)]
    let kk : K := ⟨k, hk⟩

    have key : ∀ q : K ⧸ H, F (g * k * r q) = F (g * r (kk • q)) := by
      intro q
      have hq : (QuotientGroup.mk (Quotient.out (kk • q)) : K ⧸ H) = QuotientGroup.mk (kk * Quotient.out q) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hm := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf, mem_conjMeet] at hm
      have e : g * k * r q = g * r (kk • q) * (γ⁻¹ * ((((Quotient.out (kk • q))⁻¹ * (kk * Quotient.out q) : K) : Γ)) * γ) := by
        simp only [r, Subgroup.coe_mul, Subgroup.coe_inv, kk]
        group
      rw [e, hF _ hm.2]

    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (MulAction.toPerm kk) _ _ (fun q => rfl)

end GlobalTheory.TransSum

namespace GlobalTheory.TransSum

theorem heckeOn_doubleCoset_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (γ : GA D (Wc D i)), γ ∈ GfC (Wc D i) → ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧ ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hP γ hγ
  have topgrp := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Wc D i).gram
  haveI : CompactSpace (levW R i) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  have hU := GlobalTheory.LevelOpen.isOpen_levG (Wc D i) (R.βW i) (R.datWp i R.triv)
  have hopen : IsOpen (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) := by
    let φ : levW R i → GfC (Wc D i) := fun x =>
      ⟨γ⁻¹ * (x : GA D (Wc D i)) * γ, mul_mem (mul_mem (inv_mem hγ) (hP.1 x.2)) hγ⟩
    have hφ : Continuous φ := by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have e : (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) =
        φ ⁻¹' {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_conjMeet, Set.mem_preimage, Set.mem_setOf_eq, φ]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hU.preimage hφ
  haveI : Finite (levW R i ⧸ (conjMeet (levW R i) γ).subgroupOf (levW R i)) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : ((conjMeet (levW R i) γ).subgroupOf (levW R i)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨C, hne, hC, hsum⟩ := exists_sum_inv (levW R i) γ
  refine ⟨C, hne, hC, fun Tm hT => ?_⟩
  have hCf : ∀ a ∈ C, a ∈ GfC (Wc D i) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := hC a ha
    exact mul_mem (hP.1 hk) hγ
  unfold RealDat.Wall at hT ⊢
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  refine GlobalTheory.HeckeParts.isMultMap_heckeOn hT hCf fun v k hk g => ?_
  have h1 : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := hP.2.1 k hk
  rw [h1, one_mul, heckeLin_apply, heckeLin_apply]
  exact hsum (Tm v) (fun k' hk' g' => by rw [hT.lev v k' hk' g', hP.2.1 k' hk', one_mul]) k hk g

end GlobalTheory.TransSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftRealPointsEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenInfEquiv

theorem representation_inv_mul_left_translate {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H) (w : W) :
    ρ (γ * h)⁻¹ (ρ γ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem representation_right_translate_inv_mul {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (u h : H) (w : W) :
    ρ u (ρ (h * u)⁻¹ w) = ρ h⁻¹ w := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ext_apply' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (h : GA D V) :
    c.ext φ h = c.ρ h⁻¹ (φ ((finHom V).rangeRestrict h)) := rfl

theorem ext_left' {V : HSp D} (c : CoefA V) (J : Subgroup (Formalism.IndefR.Bridge.Gf V)) (χ : J →* ℂˣ)
    (φ : Formalism.IndefR.Bridge.Gf V → c.W)
    (hφ : φ ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ J χ) (γ : GA D V) (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext φ (γ * h) = c.ext φ h := by
  have h1 := hφ ⟨γ, hγ⟩ ((finHom V).rangeRestrict h) 1
  simp only [map_one, Units.val_one, one_smul, OneMemClass.coe_one, mul_one] at h1
  have h2 : φ ((finHom V).rangeRestrict γ * (finHom V).rangeRestrict h) = c.ρ γ (φ ((finHom V).rangeRestrict h)) := h1
  rw [ext_apply', ext_apply', map_mul (finHom V).rangeRestrict, h2]
  exact representation_inv_mul_left_translate c.ρ γ h _

theorem ext_inf' {V : HSp D} (c : CoefA V) (φ : Formalism.IndefR.Bridge.Gf V → c.W) (u : GA D V) (hu : u ∈ GinfC V)
    (h : GA D V) : c.ρ u (c.ext φ (h * u)) = c.ext φ h := by
  have e1 : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    have h1 : finHom V u = 1 := hu
    show finHom V (h * u) = finHom V h
    rw [map_mul, h1, mul_one]
  rw [ext_apply', ext_apply', e1]
  exact representation_right_translate_inv_mul c.ρ u h _

theorem om_left' {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (H : IsWeilDatumO ψ S T' χS χT om) (γ : GA D S)
    (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T') (f : WO S T' → ℂ) (hf : IsThetaFunO ψ S T' f) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have e : ((γ * h, g) : GA D S × GA D T') = (γ, (1 : GA D T')) * (h, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact H.om_aut _ hγ _ (Subgroup.one_mem _) _ (H.om_pres _ _ hf)

theorem om_right' {S T' : HSp D} (om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (u h : GA D S)
    (g : GA D T') (f : WO S T' → ℂ) : thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have e : ((h * u, g) : GA D S × GA D T') = (h, g) * (u, (1 : GA D T')) := by simp
  rw [e, map_mul, Module.End.mul_apply]

theorem mem_of_hmodIs {X : Type} [AddCommGroup X] [Module ℂ X] (M : HMod X) (V : Submodule ℂ X) (ip : X → X → ℂ)
    (h : M.Is V ip) (x : M.H) : M.e x ∈ V := h.2.1 ▸ ⟨x, rfl⟩

end GlobalTheory.DownLift.GenInfEquiv

open GlobalTheory.DownLift.GenInfEquiv in

theorem GlobalTheory.DownLift.downInt_realEquiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y u hu f hf l g
  have hM : R.IsModels := hG.core.models
  have hν := hM.νV i t
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Vc D i)
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Vc D i)
  haveI : (R.νV i t).IsHaarMeasure := hν.1.1
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds (Vc D i) _ hν.1.1
  have hx := mem_of_hmodIs _ _ _ (hM.HV i t) y
  have hW := (hP i t).datum
  let Ψ : GA D (Vc D i) → ℂ := fun h =>
    thetaKO (R.ωP i t) h g f * (l ∘ₗ (R.cV i).ρ u) ((R.cV i).ext ((R.HV i t).e y) h)
  have hL : ∀ γ ∈ GQ (Vc D i), ∀ h, Ψ (γ * h) = Ψ h := by
    intro γ hγ h
    exact congrArg₂ (fun a b => a * (l ∘ₗ (R.cV i).ρ u) b) (om_left' hW γ hγ h g f hf)
      (ext_left' (R.cV i) _ _ _ hx γ hγ h)
  have hR : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (u, 1) f) * l (R.extV i t y h) = Ψ (h * u) := by
    intro h
    exact congrArg₂ (fun a b => a * l b) (om_right' (R.ωP i t) u h g f).symm
      (ext_inf' (R.cV i) ((R.HV i t).e y) u hu h).symm
  have key := (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D i)) (R.νV i t) _ hν.2 Ψ hL u).2
  have e1 : downInt R i t y (R.ωP i t (u, 1) f) l g = ∫ h in R.fdV i t, Ψ (h * u) ∂(R.νV i t) := by
    unfold downInt
    exact integral_congr_ae (Filter.Eventually.of_forall hR)
  have e2 : downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g = ∫ h in R.fdV i t, Ψ h ∂(R.νV i t) := rfl
  rw [e1, e2, key]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisLimitLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem limit_pre_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val), ∃ (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), ∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r := by
  intro l _ K bk τ hτ d N ρ tw F
  obtain ⟨T0, hT0, hT0R⟩ := GlobalTheory.T.exists_etale_basis_limit_lattice_tower l K bk τ hτ d N ρ tw F
  obtain ⟨hfix0, A0, A0', hA0, hA0', hφ0, hAA0⟩ := GlobalTheory.T.limit_breuilKisin_basis_invariant_etale l K bk τ hτ d N ρ tw F T0 hT0 hT0R
  choose R R' hRO hR'O hR hRR' using hT0R
  obtain ⟨Yt, hYt⟩ := GlobalTheory.T.approximatingLattices_transitionMatrix_modPow l K bk τ hτ d N ρ tw F T0 R hT0 hR
  have hc := GlobalTheory.T.latticeApproximation_mittagLeffler l K bk τ hτ d N ρ tw F T0 R hT0 hRO hR
  have hlim := GlobalTheory.T.mittagLeffler_image_breuilKisin_modPow l K bk d tw.d' R Yt hYt hc
  have hL3 := GlobalTheory.T.limitVector_mem_OE_and_ainf l K bk τ hτ d N ρ tw F T0 R hRO hR
  obtain ⟨V, V', hVO, hV'O, hVV, hVlim⟩ := GlobalTheory.T.limitVectors_invertible_basis_over_OE l K bk d tw.d' R (fun n => ⟨R' n, hR'O n, hRR' n⟩) hlim hRO
  choose y1 hy1 using fun j => (hL3 _ (hVlim j)).2
  have hY1 : (Matrix.of fun i j => y1 j i).map (inclW l) = inclW l τ ^ N • (T0 * V) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hy1 j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  obtain ⟨Y, Wm, Wm', hYu, hWO, hW'O, hWW, hYW, hmem⟩ := GlobalTheory.T.saturatedAinfLattice_free_over_breuilKisin l K bk τ hτ d N T0 V V' _ hT0 hVO hV'O hVV hY1
  have hlink := GlobalTheory.T.twisted_matrix_congruence_lift_sequence l K bk τ hτ d N ρ tw F T0 R hR hlim hL3 Y (T0 * Wm) hYW hmem
  obtain ⟨Y', hYY'⟩ := GlobalTheory.T.ainf_exists_mul_eq_pow_smul_of_mod_lPow l d (2 * N) τ Y hYu (fun n => by
    obtain ⟨m, _, Rn, Q, _, h⟩ := hlink n
    exact ⟨Rn.map bk.ev * Q, h⟩)
  obtain ⟨hfixT, A1, A1', hA1, hA1', hφ1, hAA1⟩ := GlobalTheory.T.invariantEtaleBasis_change_by_OE_unit l K bk d (fun g => (ρ g).val) T0 Wm Wm' A0 A0' hfix0 hA0 hA0' hφ0 hAA0 hWO hW'O hWW
  have hTu : IsUnit (T0 * Wm) := hT0.mul ⟨⟨Wm, Wm', hWW, mul_eq_one_comm.1 hWW⟩, rfl⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.breuilKisin_basis_of_etale_invariant_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) (T0 * Wm) A1 A1' Y Y' hTu hA1 hA1' hφ1 hAA1 hfixT hYW hYY'
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_right_inverse_mod_pow_of_ev l K bk τ hτ (2 * N)
  refine ⟨P, r, fun n => ?_⟩
  obtain ⟨m, hnm, Rn, Q, h1, h2⟩ := hlink n
  have h3 := GlobalTheory.T.ainf_rightInverse_up_to_pow_mod_lPow l d (tw.d' m) n (2 * N) τ Y Y' (Rn.map bk.ev) Q (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).1 hYu hYY' h2
  obtain ⟨G, hG⟩ := hr d (tw.d' m) n Rn (Q * Y) h3
  exact ⟨m, hnm, Rn, G, by rw [hP]; exact h1, hG⟩

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineCharJumpOneStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_char_jump_one_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ IsCrys (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) ∧ ∀ τ b, multV (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  first | exact @GlobalTheory.LTChar.exists_crystalline_char_jump_one | exact GlobalTheory.LTChar.exists_crystalline_char_jump_one | (intros; apply GlobalTheory.LTChar.exists_crystalline_char_jump_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UnitaryBC

namespace GlobalTheory.BaseChangeBridge

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_equiv_of_isSubquotient {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible) (h : GlobalTheory.SmGL.IsSubquotient σ ρ) :
    ∃ e : W ≃ₗ[ℂ] V, ∀ g x, e (σ g x) = ρ g (e x) := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨hW, -⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ
  obtain ⟨-, hρ'⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hρ
  have hS : S.toSubmodule = ⊤ := by
    rcases hρ' S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := hf x
      have hv : v = 0 := by
        exact Subtype.ext ((Submodule.eq_bot_iff _).1 e v v.2)
      subst hv
      exact hx (map_zero f.toLinearMap)
    · exact e
  let g : V →ₗ[ℂ] W := f.toLinearMap ∘ₗ (LinearEquiv.ofTop S.toSubmodule hS).symm.toLinearMap
  have hg : ∀ x v, g (ρ x v) = σ x (g v) := fun x v => by
    have := LinearMap.congr_fun (f.isIntertwining' x) ((LinearEquiv.ofTop S.toSubmodule hS).symm v)
    exact this
  have gsurj : Function.Surjective g := fun y => by
    obtain ⟨v, rfl⟩ := hf y
    refine ⟨(v : V), ?_⟩
    change f ((LinearEquiv.ofTop S.toSubmodule hS).symm (v : V)) = f v
    congr 1
  have ginj : Function.Injective g := by
    rcases hρ' (LinearMap.ker g) (fun x v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hg, hv, map_zero]) with e | e
    · exact LinearMap.ker_eq_bot.1 e
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := gsurj y
      exact hy (LinearMap.mem_ker.1 (e ▸ Submodule.mem_top))
  let e0 := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
  refine ⟨e0.symm, fun x y => e0.injective ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  change σ x y = g (ρ x (e0.symm y))
  rw [hg]
  change σ x y = σ x (e0 (e0.symm y))
  rw [LinearEquiv.apply_symm_apply]

variable {H : Type} [Group H]

theorem isSpherical_of_equiv {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) {K : Subgroup H} (h : GlobalTheory.LGrp.IsSpherical σ K) :
    GlobalTheory.LGrp.IsSpherical ρ K := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  exact (Submodule.ne_bot_iff _).2 ⟨e x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← he, GlobalTheory.LGrp.mem_fixed.1 hx k hk],
    by simpa using h0⟩

theorem symm_equivariant {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) (g : H) (y : V) : e.symm (ρ g y) = σ g (e.symm y) :=
  e.injective (by rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply])

end General

section Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasSatGL_of_equiv {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} (e : W ≃ₗ[ℂ] V) (he : ∀ g x, e (σ g x) = ρ g (e x))
    {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w σ B) : GlobalTheory.LFun.HasSatGL w ρ B := by
  refine ⟨isSpherical_of_equiv e he h.1, fun y hy h0 => ?_⟩
  have hx : e.symm y ∈ GlobalTheory.PRep.fixed σ (GlobalTheory.LFun.KGL w n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← symm_equivariant e he, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
  have h0' : e.symm y ≠ 0 := by simpa using h0
  have := (h.2 _ hx h0').map e.toLinearMap he (by simpa using h0)
  simpa using this

end Local

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isCompAlong_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {Gv : Subgroup (UA E n)} {H : Type} [Group H]
    {p : Gv →* H} {σ : Representation ℂ H W} {ρ : Representation ℂ H V} (e : W ≃ₗ[ℂ] V)
    (he : ∀ g x, e (σ g x) = ρ g (e x)) (hρ : ρ.IsIrreducible) (h : IsCompAlong π Gv p σ) :
    IsCompAlong π Gv p ρ := by
  obtain ⟨-, f, h0, hf, hfi⟩ := h
  refine ⟨hρ, f ∘ₗ e.symm.toLinearMap, fun h1 => h0 ?_, fun v => hf _, fun x v => ?_⟩
  · refine LinearMap.ext fun y => ?_
    simpa using LinearMap.congr_fun h1 (e y)
  · simp [symm_equivariant e he, hfi]

end CM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem main : GlobalTheory.Published.BaseChangeIsobaric → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.BaseChangeDefiniteUnitary := by
  intro hBC hB E _ _ _ hun n hn π hπ
  obtain ⟨c, N, h, V, σ, m, P, H⟩ := hBC E hun n hn π hπ
  refine ⟨c, N, h, V, σ, m, ?_⟩
  have hirr : ∀ w, (locProd h w (σ · w)).IsIrreducible := fun w =>
    ((GlobalTheory.SmGL.MultiIrr.products_irreducible hB (w.adicCompletion E)).1 c N (Fin n) (GlobalTheory.SmGL.stdBlocks N h)
      (fun i => (σ i w).V) (fun i => (σ i w).ρ) (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
      (fun i => GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E (N i) (V i) (H.discrete i) w (σ i w)
        (H.loc i w))).2.1
  exact
    { pos := H.pos
      discrete := H.discrete
      csd := H.csd
      loc := H.loc
      inf := H.inf
      unram := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isSpherical_of_equiv e he (H.unram w hw)
      inert := fun w s ϖ q hs hq α hα => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact hasSatGL_of_equiv e he (H.inert w s ϖ q hs hq α hα)
      split := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isCompAlong_of_equiv e he (hirr w) (H.split w hw)
      weight := H.weight }

end GlobalTheory.BaseChangeBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfStratifiedPhiModuleHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d} {M : FCrys l ↥(OL K)}
  {e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)}

theorem IsCoord.v_eq_of_sum {B Q : Obj l ↥(OL K)} {V : Eval S B (M.M B)} (hV : IsCoord e V) (a : Hom B Q)
    (g : Hom bk.prism Q) (x : M.M B) (z : Fin d → Q.A) (hz : M.tr a x = ∑ i, z i • M.tr g (e i)) :
    V.v a g x = z := by
  obtain ⟨b, hb⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e
  have h := (hV a g x).symm.trans hz
  simp only [← hb] at h
  funext i
  have := congrArg (fun y => b.repr y i) h
  simpa [Finsupp.single_apply, Module.Basis.repr_self] using this

theorem IsCoord.v_tr {B B' Q : Obj l ↥(OL K)} {V : Eval S B (M.M B)} {V' : Eval S B' (M.M B')}
    (hV : IsCoord e V) (hV' : IsCoord e V') (k : Hom B B') (a : Hom B' Q) (g : Hom bk.prism Q) (x : M.M B) :
    V'.v a g (M.tr k x) = V.v (a.comp k) g x :=
  hV'.v_eq_of_sum a g _ _ (by rw [← M.tr_comp]; exact hV _ g x)

theorem exists_fHom_of_isStratHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ)
    (S : Strat bk d) (S' : Strat bk d') (M M' : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)),
    Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y →
    ∃ u : FHom M M', ∀ j, u.u bk.prism (e j) = ∑ i, bk.toP (Y i j) • e' i := by
  intro l _ K bk d d' S S' M M' e e' hF hF' Y hY
  choose V hV using GlobalTheory.T.framedFCrystal_exists_coords_every_prism l K bk d S M e hF
  choose V' hV' using GlobalTheory.T.framedFCrystal_exists_coords_every_prism l K bk d' S' M' e' hF'
  choose w hw using fun B => GlobalTheory.T.exists_stratifiedPhiModuleHom_valueMap l K bk d d' S S' Y hY B (M.M B) (M'.M B) (V B) (V' B)
  refine ⟨⟨w, fun {P P'} k x => ?_, fun P t x m k h =>
    GlobalTheory.T.stratifiedCrystalValueMap_comm_frobenius l K bk d d' S S' M e M' e' hF hF' Y hY P (V P) (V' P) (hV P) (hV' P) (w P) (hw P) t x m k h⟩,
    fun j => ?_⟩
  · obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk P'
    apply (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' P' C (M'.M P') (V' P') h f hc).1
    rw [hw, IsCoord.v_tr (hV P) (hV P'), IsCoord.v_tr (hV' P) (hV' P'), hw]
  · have h1 := hV' bk.prism (Hom.id _) (Hom.id _) (w bk.prism (e j))
    have h2 : (V bk.prism).v (Hom.id _) (Hom.id _) (e j) = Pi.single j 1 :=
      IsCoord.v_eq_of_sum (hV _) _ _ _ _ (by simp [M.tr_id, Pi.single_apply])
    have h3 := ((hw bk.prism _ (Hom.id _) (Hom.id _) (e j)).trans (congrArg _ h2)).trans
      (Matrix.mulVec_single_one _ j)
    rw [h3] at h1
    simp only [M'.tr_id] at h1
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun c : bk.prism.A => c • e' i) (show ((Y.map (BK.hf (Hom.id bk.prism))).col j) i = bk.toP (Y i j) from rfl)

end GlobalTheory.BSP
end

