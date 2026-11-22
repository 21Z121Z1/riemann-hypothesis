import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSemiStable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianIdentityComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj
open GlobalTheory.MBLit

noncomputable section

namespace GlobalTheory.SemiStableId

def transportExt {K : Type} [Field K] {G₁ H : Over (Spec (.of K))} [GrpObj G₁] [GrpObj H]
    (E : TorusExtension G₁) (e : G₁ ≅ H) [IsMonHom e.hom] : TorusExtension H where
  X := E.X
  addCommGroup := E.addCommGroup
  free := E.free
  finite := E.finite
  B := E.B
  grpB := E.grpB
  isAbelian := E.isAbelian
  q := e.inv ≫ E.q
  q_hom := by have := E.q_hom; infer_instance
  q_flat := by have := E.q_flat; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show Flat (e.inv.left ≫ E.q.left); infer_instance
  q_surjective := by have := E.q_surjective; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show Surjective (e.inv.left ≫ E.q.left); infer_instance
  q_quasiCompact := by
    have := E.q_quasiCompact; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show QuasiCompact (e.inv.left ≫ E.q.left); infer_instance
  i := E.i ≫ e.hom
  i_hom := by have := E.i_hom; infer_instance
  isKernel := by
    have h2 : IsPullback e.hom E.q (e.inv ≫ E.q) (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa using E.isKernel.paste_horiz h2

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] (j : G₀ ⟶ G)

abbrev RangeIsId : Prop := ∀ x : G.left, x ∈ Set.range j.left ↔
  x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

include j in
theorem unit_mem_fibre (s : S) : (η[G]).left s ∈ G.hom ⁻¹' {s} := by
  show G.hom ((η[G]).left s) = s
  rw [← Scheme.Hom.comp_apply, Over.w]
  rfl

theorem isConnected_fibre [IsOpenImmersion j.left] (hr : RangeIsId j) (s : S) :
    _root_.IsConnected (G₀.hom ⁻¹' {s}) := by
  have hw : ∀ x, G.hom (j.left x) = G₀.hom x := fun x => by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have himg : j.left '' (G₀.hom ⁻¹' {s}) = connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hr (j.left x)).1 ⟨x, rfl⟩
      rwa [hw, show G₀.hom x = s from hx] at this
    · intro hy
      have hys : G.hom y = s := connectedComponentIn_subset (G.hom ⁻¹' {s}) _ hy
      obtain ⟨x, rfl⟩ := (hr y).2 (by rwa [hys])
      exact ⟨x, by rw [Set.mem_preimage, ← hw, hys]; rfl, rfl⟩
  have hc : _root_.IsConnected (connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s)) :=
    isConnected_connectedComponentIn_iff.mpr (unit_mem_fibre j s)
  rw [← himg] at hc
  exact ⟨hc.nonempty.of_image, j.left.isOpenEmbedding.isInducing.isPreconnected_image.1 hc.isPreconnected⟩

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelSpreadLocal

theorem exists_spread_of_pullbacks : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := by
  intro g n B _ ζ R _ _ β 𝔭 _ d Y sY _ u r₀ ι₀ h e hr₀ hι₀ hh hed heu
  obtain ⟨t₁, ht₁, hinj⟩ := GlobalTheory.T.localization_away_injective_atPrime_of_dvd R 𝔭
  have hrange := GlobalTheory.T.finset_mem_range_localization_away_of_dvd R 𝔭
  have hmono := GlobalTheory.T.localization_away_range_le_of_dvd_of_comp R (Localization.AtPrime 𝔭) (algebraMap R (Localization.AtPrime 𝔭))
  have spc : ∀ {A₁ A₂ A₃ : Type} [CommRing A₁] [CommRing A₂] [CommRing A₃] (a : A₁ →+* A₂) (b : A₂ →+* A₃),
      spMap (b.comp a) = spMap b ≫ spMap a := by
    intro A₁ A₂ A₃ _ _ _ a b
    simp only [spMap, ← Spec.map_comp]
    rfl
  have unit : ∀ x : R, x ∉ 𝔭 → IsUnit (algebraMap R (Localization.AtPrime 𝔭) x) := fun x hx =>
    IsLocalization.map_units (M := 𝔭.primeCompl) (Localization.AtPrime 𝔭) ⟨x, hx⟩
  have nmul : ∀ x y : R, x ∉ 𝔭 → y ∉ 𝔭 → x * y ∉ 𝔭 := fun x y hx hy hm =>
    ((inferInstance : 𝔭.IsPrime).mem_or_mem hm).elim hx hy
  let lam : ∀ c : R, c ∉ 𝔭 → Localization.Away c →+* Localization.AtPrime 𝔭 := fun c hc =>
    IsLocalization.Away.lift c (unit c hc)
  have lamc : ∀ (c : R) (hc : c ∉ 𝔭), (lam c hc).comp (algebraMap R (Localization.Away c)) =
      algebraMap R (Localization.AtPrime 𝔭) := fun c hc => IsLocalization.Away.lift_comp _ _

  have ht : r₀ * t₁ ∉ 𝔭 := nmul _ _ hr₀ ht₁
  let R₀ : Subring (Localization.AtPrime 𝔭) := (lam _ ht).range
  have memR₀ : ∀ x : R, algebraMap R (Localization.AtPrime 𝔭) x ∈ R₀ := fun x =>
    ⟨algebraMap R _ x, by rw [← RingHom.comp_apply, lamc _ ht]⟩
  let a₀ : R →+* R₀ := (algebraMap R (Localization.AtPrime 𝔭)).codRestrict R₀ memR₀
  obtain ⟨⟨d₀, hd₀⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp R₀) (spMap β) (spMap a₀ ≫ spMap β)
    (spMap a₀) d rfl
  have hsub : R₀.subtype.comp a₀ = algebraMap R (Localization.AtPrime 𝔭) := RingHom.ext fun _ => rfl
  have hed₀ : SiegPB e d₀ (spMap R₀.subtype) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd₀ (by rw [← spc, hsub]; exact hed)
  have memι₀ : ∀ x, ι₀ x ∈ R₀ := fun x =>
    hmono r₀ (r₀ * t₁) (dvd_mul_right _ _) ι₀ (lam _ ht) hι₀ (lamc _ ht) ⟨x, rfl⟩
  let j₀ : Localization.Away r₀ →+* R₀ := ι₀.codRestrict R₀ memι₀
  have hj₀ : R₀.subtype.comp j₀ = ι₀ := RingHom.ext fun _ => rfl
  have heu₀ : SiegPB e u (spMap R₀.subtype ≫ (spMap j₀ ≫ h)) := by
    rw [← Category.assoc, ← spc, hj₀]; exact heu
  obtain ⟨F, hF⟩ := GlobalTheory.T.siegelPullback_spreads_to_intermediate_subring g n B ζ (Localization.AtPrime 𝔭) R₀ _ d₀ Y sY u (spMap j₀ ≫ h) _ e hed₀ heu₀
  obtain ⟨s, hs, hsF⟩ := hrange F

  have hr : r₀ * t₁ * s ∉ 𝔭 := nmul _ _ ht hs
  let lr := lam _ hr
  let R₁ : Subring (Localization.AtPrime 𝔭) := lr.range
  have hle : R₀ ≤ R₁ := hmono _ _ (dvd_mul_right _ _) _ _ (lamc _ ht) (lamc _ hr)
  have hFR : (F : Set (Localization.AtPrime 𝔭)) ⊆ R₁ := fun x hx =>
    hsF _ (dvd_mul_left _ _) lr (lamc _ hr) x hx
  have hlinj : Function.Injective lr :=
    hinj _ ⟨r₀ * s, by ring⟩ lr (lamc _ hr)
  let er : Localization.Away (r₀ * t₁ * s) ≃+* R₁ :=
    RingEquiv.ofBijective lr.rangeRestrict ⟨fun x y hxy => hlinj (congrArg Subtype.val hxy), lr.rangeRestrict_surjective⟩
  have erv : ∀ x, (er x : Localization.AtPrime 𝔭) = lr x := fun _ => rfl
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R) (Sp (Localization.Away (r₀ * t₁ * s)))
    (spMap β) (spMap ((algebraMap R (Localization.Away (r₀ * t₁ * s))).comp β))
    (spMap (algebraMap R (Localization.Away (r₀ * t₁ * s)))) d (spc _ _).symm
  obtain ⟨⟨d₁, hd₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ _ (Sp R₁) _ _ (spMap er.toRingHom) d' rfl
  have hd₁₀ : SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₀ ?_
    have e₁ : spMap (Subring.inclusion hle) ≫ spMap a₀ = spMap er.toRingHom ≫ spMap (algebraMap R (Localization.Away (r₀ * t₁ * s))) := by
      rw [← spc, ← spc]
      congr 1
      refine RingHom.ext fun x => Subtype.ext ?_
      show algebraMap R (Localization.AtPrime 𝔭) x = lr (algebraMap R _ x)
      rw [← RingHom.comp_apply, lamc _ hr]
    rw [e₁]
    exact GlobalTheory.SiegelPullComp.pb_comp hd' hd₁
  have hd₁u := hF R₁ hle hFR _ d₁ hd₁₀
  have hd'd₁ : SiegPB d' d₁ (spMap er.symm.toRingHom) := by
    refine GlobalTheory.SiegelPullComp.pb_cancel hd₁ ?_
    have e₂ : spMap er.symm.toRingHom ≫ spMap er.toRingHom = 𝟙 _ := by
      rw [← spc]
      have : er.symm.toRingHom.comp er.toRingHom = RingHom.id _ := RingHom.ext fun x => er.symm_apply_apply x
      rw [this]
      simp [spMap]
    rw [e₂]
    exact GlobalTheory.SiegelPullComp.pb_id d'
  let κ : Localization.Away r₀ →+* Localization.Away (r₀ * t₁ * s) :=
    er.symm.toRingHom.comp ((Subring.inclusion hle).comp j₀)
  refine ⟨r₀ * t₁ * s, hr, κ, d', ?_, hd', ?_⟩
  · refine RingHom.ext fun x => hlinj ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have hk : er (κ (algebraMap R _ x)) = (Subring.inclusion hle) (j₀ (algebraMap R _ x)) := er.apply_symm_apply _
    calc lr (κ (algebraMap R _ x)) = (er (κ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := rfl
      _ = ((Subring.inclusion hle) (j₀ (algebraMap R _ x)) : Localization.AtPrime 𝔭) := congrArg Subtype.val hk
      _ = ι₀ (algebraMap R _ x) := rfl
      _ = algebraMap R (Localization.AtPrime 𝔭) x := by rw [← RingHom.comp_apply, hι₀]
      _ = lr (algebraMap R _ x) := by rw [← RingHom.comp_apply, lamc _ hr]
  · have e₃ : spMap κ ≫ h = spMap er.symm.toRingHom ≫ (spMap (Subring.inclusion hle) ≫ (spMap j₀ ≫ h)) := by
      simp only [κ, spc, Category.assoc]
    rw [e₃]
    exact GlobalTheory.SiegelPullComp.pb_comp hd₁u hd'd₁

end GlobalTheory.SiegelSpreadLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtFixedNearOneCommutativeCentralizer
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.SqrtFixCent

theorem eq_mul_of_comm_mulRight {K A : Type} [Field K] [Ring A] [Algebra K A] (f : Module.End K A)
    (hf : ∀ y : A, LinearMap.mulRight K y * f = f * LinearMap.mulRight K y) (y : A) :
    f y = f 1 * y := by
  have h := congrArg (fun g : Module.End K A => g 1) (hf y)
  change f 1 * y = f (1 * y) at h
  rw [one_mul] at h
  exact h.symm

end GlobalTheory.SqrtFixCent

namespace GlobalTheory

theorem sqrt_fix_near_one_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  intro p _ v B _ _ _
  letI tB : TopologicalSpace B := moduleTopology (Qv v) B
  haveI : IsModuleTopology (Qv v) B := ⟨rfl⟩
  intro e σ _ hσe hσm hσ1
  let M : Subalgebra (Qv v) B := Subalgebra.centralizer (Qv v) {e}
  have hM : ∀ x : B, x ∈ M ↔ x * e = e * x := by
    intro x
    simp [M, Subalgebra.mem_centralizer_iff, eq_comm]
  haveI : CharZero (Qv v) := charZero_of_injective_algebraMap (algebraMap ℚ (Qv v)).injective
  letI : NontriviallyNormedField (Qv v) := Valued.toNontriviallyNormedField _ _
  let d := Module.finrank (Qv v) M
  let bM := Module.finBasis (Qv v) M
  let Lm : M →ₐ[Qv v] Matrix (Fin d) (Fin d) (Qv v) :=
    (LinearMap.toMatrixAlgEquiv bM).toAlgHom.comp (Algebra.lmul (Qv v) M)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Subalgebra.toSubmodule M)
  let P : B →ₗ[Qv v] M := Submodule.linearProjOfIsCompl (Subalgebra.toSubmodule M) q hq
  have hP : ∀ x : M, P x = x := fun x => Submodule.linearProjOfIsCompl_apply_left hq x
  let L : B →ₗ[Qv v] Matrix (Fin d) (Fin d) (Qv v) := Lm.toLinearMap ∘ₗ P
  have hLc : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have hL1 : L 1 = 1 := by
    show Lm (P ((1 : M) : B)) = 1
    rw [hP, map_one]
  obtain ⟨W₀, hW₀, hW₀s⟩ := GlobalTheory.matrix_sqrt_near_one_ultrametric (Qv v) d (RingHom.id _) continuous_id
  refine ⟨L ⁻¹' W₀, hLc.continuousAt.preimage_mem_nhds (by rw [hL1]; exact hW₀), ?_⟩
  intro s hs hse hσs
  let sM : M := ⟨s, (hM s).2 hse⟩
  have hLs : L s = Lm sM := by
    show Lm (P (sM : B)) = Lm sM
    rw [hP]
  obtain ⟨R, hRR, hRc, -⟩ := hW₀s _ (show L s ∈ W₀ from hs)
  rw [hLs] at hRR hRc
  let T := LinearMap.toMatrixAlgEquiv bM
  let f : Module.End (Qv v) M := T.symm R
  have hTs : Lm sM = T (LinearMap.mulLeft (Qv v) sM) := rfl
  have hf : ∀ g : Module.End (Qv v) M, g * LinearMap.mulLeft (Qv v) sM = LinearMap.mulLeft (Qv v) sM * g →
      g * f = f * g := by
    intro g hg
    apply T.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
    apply hRc
    rw [hTs, ← map_mul, ← map_mul, hg]
  have hff : f * f = LinearMap.mulLeft (Qv v) sM := by
    apply T.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, hRR]
    exact hTs
  have hfy : ∀ y : M, f y = f 1 * y := by
    refine GlobalTheory.SqrtFixCent.eq_mul_of_comm_mulRight f fun y => (hf _ ?_)
    exact LinearMap.ext fun x => mul_assoc sM x y
  have hρρ : f 1 * f 1 = sM := by
    have h := LinearMap.congr_fun hff 1
    change f (f 1) = sM * 1 at h
    rw [hfy (f 1), mul_one] at h
    exact h
  let σM : Module.End (Qv v) M :=
    { toFun := fun x => ⟨σ x, (hM _).2 (hσe x ((hM x).1 x.2))⟩
      map_add' := fun x y => Subtype.ext (by show σ ((x : B) + y) = σ x + σ y; exact map_add σ _ _)
      map_smul' := fun c x => Subtype.ext (by show σ (c • (x : B)) = c • σ x; exact map_smul σ _ _) }
  have hσM : ∀ x : M, ((σM x : M) : B) = σ x := fun x => rfl
  have hcomm : σM * LinearMap.mulLeft (Qv v) sM = LinearMap.mulLeft (Qv v) sM * σM := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show σ ((sM : B) * x) = (sM : B) * σ x
    rw [hσm s x hse ((hM x).1 x.2), hσs]
  have hσ1M : σM 1 = 1 := Subtype.ext (by show σ ((1 : M) : B) = ((1 : M) : B); exact hσ1)
  have hσρ : σM (f 1) = f 1 := by
    have h := LinearMap.congr_fun (hf σM hcomm) 1
    change σM (f 1) = f (σM 1) at h
    rw [hσ1M] at h
    exact h
  refine ⟨((f 1 : M) : B), (hM _).1 (f 1).2, congrArg Subtype.val hσρ, congrArg Subtype.val hρρ⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumTwoSidedMulEqMatrixUnitUnitaryDatum
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

section DensityCentralizer

variable {F C : Type} [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
  [Algebra.IsCentral F C] [IsSimpleRing C]

theorem exists_sum_mul_mul_eq_matrixUnit (n : ℕ) (hn : 0 < n) (hC : Module.finrank F C = n ^ 2)
    (γ : C) (hγ : (minpoly F γ).natDegree = n)
    (L : Type) [Field L] (ι : L →+* C) (hιinj : Function.Injective ι)
    (hι : ∀ z : C, z * γ = γ * z ↔ ∃ w, ι w = z) (r : ℕ) (e : Fin r → C)
    (he : ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) (i i' : Fin r) :
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  classical
  let S : Subalgebra F C := Subalgebra.centralizer F {γ}
  have memS : ∀ z : C, z ∈ S ↔ ∃ w, ι w = z := by
    intro z
    rw [← hι z]
    simp [S, Subalgebra.mem_centralizer_iff, eq_comm]
  have hιS : ∀ w, ι w ∈ S := fun w => (memS _).2 ⟨w, rfl⟩
  have hγS : γ ∈ S := (memS γ).2 ((hι γ).1 rfl)
  have hcomm : ∀ s t : C, s ∈ S → t ∈ S → s * t = t * s := by
    intro s t hs ht
    obtain ⟨a, rfl⟩ := (memS s).1 hs
    obtain ⟨b, rfl⟩ := (memS t).1 ht
    rw [← map_mul, ← map_mul, mul_comm]
  let j : L →+* S :=
    { toFun := fun w => ⟨ι w, hιS w⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hj : Function.Bijective j := by
    refine ⟨fun a b h => hιinj (congrArg Subtype.val h), fun s => ?_⟩
    obtain ⟨w, hw⟩ := (memS s).1 s.2
    exact ⟨w, Subtype.ext hw⟩
  haveI : IsSimpleRing S := IsSimpleRing.of_ringEquiv (RingEquiv.ofBijective j hj) inferInstance
  let Φ : S ⊗[F] Cᵐᵒᵖ →ₐ[F] Module.End F C :=
    (AlgHom.mulLeftRight F C).comp (Algebra.TensorProduct.map S.val (AlgHom.id F Cᵐᵒᵖ))
  have hΦ : ∀ (s : S) (b : Cᵐᵒᵖ) (x : C), Φ (s ⊗ₜ b) x = (s : C) * x * b.unop := by
    intro s b x
    simp [Φ, AlgHom.mulLeftRight_apply]
  have hΦinj : Function.Injective Φ :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain Φ.toRingHom).resolve_right
      (not_subsingleton _)

  have hWl : ∀ t : S ⊗[F] Cᵐᵒᵖ, ∀ (s : S) (x : C), Φ t ((s : C) * x) = (s : C) * Φ t x := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => intro s x; simp
    | tmul a b =>
      intro s x
      rw [hΦ, hΦ, ← mul_assoc, hcomm _ _ a.2 s.2, mul_assoc, mul_assoc, mul_assoc]
    | add t u ht hu =>
      intro s x
      simp only [map_add, LinearMap.add_apply, ht, hu, mul_add]
  let W : Submodule F (Module.End F C) :=
    { carrier := {f | ∀ (s : S) (x : C), f ((s : C) * x) = (s : C) * f x}
      add_mem' := by
        intro a b ha hb s x
        simp only [Set.mem_setOf_eq] at ha hb
        simp [ha s x, hb s x, mul_add]
      zero_mem' := by intro s x; simp
      smul_mem' := by
        intro c f hf s x
        simp only [Set.mem_setOf_eq] at hf
        simp [hf s x, mul_smul_comm] }
  have hrange : LinearMap.range Φ.toLinearMap ≤ W := by
    rintro _ ⟨t, rfl⟩
    exact hWl t

  let θ : (Fin r → S) →ₗ[F] C :=
    { toFun := fun β => ∑ k, (β k : C) * e k
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [Finset.smul_sum, smul_mul_assoc] }
  have hθ : ∀ β, θ β = ∑ k, (β k : C) * e k := fun β => rfl
  have hθinj : Function.Injective θ := by
    intro a b hab
    let wa : Fin r → L := fun k => ((memS _).1 (a k).2).choose
    let wb : Fin r → L := fun k => ((memS _).1 (b k).2).choose
    have hwa : ∀ k, ι (wa k) = a k := fun k => ((memS _).1 (a k).2).choose_spec
    have hwb : ∀ k, ι (wb k) = b k := fun k => ((memS _).1 (b k).2).choose_spec
    have h1 : θ a = ∑ k, ι (wa k) * e k := by simp [hθ, hwa]
    have h2 : θ a = ∑ k, ι (wb k) * e k := by rw [hab]; simp [hθ, hwb]
    have := (he (θ a)).unique h1 h2
    funext k
    apply Subtype.ext
    rw [← hwa, ← hwb, this]
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨c, hc, -⟩ := he x
    exact ⟨fun k => ⟨ι (c k), hιS _⟩, by simp [hθ, hc]⟩
  let θe : (Fin r → S) ≃ₗ[F] C := LinearEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  have hθe : ∀ β, θe β = ∑ k, (β k : C) * e k := fun β => rfl
  have hθsmul : ∀ (s : S) (x : C), θe.symm ((s : C) * x) = fun k => s * θe.symm x k := by
    intro s x
    rw [θe.symm_apply_eq, hθe]
    conv_lhs => rw [← θe.apply_symm_apply x, hθe]
    simp [Finset.mul_sum, mul_assoc]

  have hdimC : Module.finrank F C = r * Module.finrank F S := by
    rw [← θe.finrank_eq, Module.finrank_pi_fintype]
    simp
  have hdS : n ≤ Module.finrank F S := by
    let γS : S := ⟨γ, hγS⟩
    have hmin : minpoly F γS = minpoly F γ := by
      have := minpoly.algHom_eq S.val Subtype.val_injective γS
      simpa [γS] using this.symm
    have := (linearIndependent_pow (K := F) γS).fintype_card_le_finrank
    simpa [hmin, hγ] using this
  have hsrc : Module.finrank F (S ⊗[F] Cᵐᵒᵖ) = Module.finrank F S * n ^ 2 := by
    rw [Module.finrank_tensorProduct, MulOpposite.finrank, hC]
  have hrk : Module.finrank F (LinearMap.range Φ.toLinearMap) = Module.finrank F S * n ^ 2 := by
    rw [LinearMap.finrank_range_of_inj hΦinj, hsrc]
  let Ψ : W →ₗ[F] (Fin r → Fin r → S) :=
    { toFun := fun f k => θe.symm ((f : Module.End F C) (e k))
      map_add' := by intro a b; funext k; simp
      map_smul' := by intro c a; funext k; simp }
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hfe : ∀ k, (f : Module.End F C) (e k) = 0 := by
      intro k
      have := congrFun hf k
      simpa [Ψ] using this
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨c, hc, -⟩ := he x
    rw [hc, map_sum]
    have hfW := f.2
    simp only [W, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hfW
    simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [show ι (c k) = ((⟨ι (c k), hιS _⟩ : S) : C) from rfl, hfW, hfe, mul_zero]
  have hW : Module.finrank F W ≤ r * (r * Module.finrank F S) := by
    have := LinearMap.finrank_le_finrank_of_injective hΨ
    simpa [Module.finrank_pi_fintype] using this
  have hrn : r ≤ n := by
    have h1 : r * n ≤ n * n := by
      calc r * n ≤ r * Module.finrank F S := Nat.mul_le_mul_left _ hdS
        _ = n * n := by rw [← hdimC, hC, sq]
    exact Nat.le_of_mul_le_mul_right h1 hn
  have hWeq : LinearMap.range Φ.toLinearMap = W := by
    apply Submodule.eq_of_le_of_finrank_le hrange
    rw [hrk]
    refine hW.trans ?_
    calc r * (r * Module.finrank F S) ≤ n * (n * Module.finrank F S) :=
          Nat.mul_le_mul hrn (Nat.mul_le_mul_right _ hrn)
      _ = Module.finrank F S * n ^ 2 := by ring

  let E : Module.End F C :=
    LinearMap.mulRight F (e i) ∘ₗ (S.val.toLinearMap ∘ₗ
      ((LinearMap.proj i' : (Fin r → S) →ₗ[F] S) ∘ₗ θe.symm.toLinearMap))
  have hE : ∀ x, E x = (θe.symm x i' : C) * e i := fun x => rfl
  have hEW : E ∈ W := by
    intro s x
    rw [hE, hE, hθsmul]
    simp [mul_assoc]
  rw [← hWeq] at hEW
  obtain ⟨t, ht⟩ := hEW
  have hrep : ∀ t : S ⊗[F] Cᵐᵒᵖ, ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → C),
      ∀ x, Φ t x = ∑ k, ι (l k) * x * c k := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | tmul a b =>
      obtain ⟨w, hw⟩ := (memS a).1 a.2
      exact ⟨1, fun _ => w, fun _ => b.unop, by intro x; simp [hΦ, hw]⟩
    | add t u ht hu =>
      obtain ⟨N₁, l₁, c₁, h₁⟩ := ht
      obtain ⟨N₂, l₂, c₂, h₂⟩ := hu
      exact ⟨N₁ + N₂, Fin.append l₁ l₂, Fin.append c₁ c₂, by
        intro x; simp [Fin.sum_univ_add, h₁, h₂]⟩
  obtain ⟨N, l, c, hlc⟩ := hrep t
  refine ⟨N, l, c, fun β => ?_⟩
  set x := ∑ i'', ι (β i'') * e i'' with hx
  have hsym : θe.symm x = fun k => ⟨ι (β k), hιS _⟩ := by
    rw [θe.symm_apply_eq, hθe]
  rw [← hlc, show Φ t x = E x from congrArg (fun f => f x) ht, hE, hsym]

end DensityCentralizer

theorem exists_sum_mul_mul_eq_matrixUnit_htGroup : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (r : ℕ) (e : Fin r → G.C),
    (∀ x : G.C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) → ∀ i i' : Fin r,
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → G.C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  intro p _ G γ hγ L _ _ ι hinj hι r e he i i'
  exact exists_sum_mul_mul_eq_matrixUnit G.n G.n_pos G.rankC (γ : G.C) hγ L ι.toRingHom hinj hι r e he i i'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPointStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_degree_le_chowForm_degree_algebraic_point : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  first | exact @GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | exact GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt <;> assumption)
end

