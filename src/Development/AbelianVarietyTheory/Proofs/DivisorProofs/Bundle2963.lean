import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportGaloisCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjUnifLattice

theorem lattice_of_conj_unif : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) → (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) := by
  intro _ _ _ K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hio c y hc 𝔠 T X' p hp u' H

  have hex0 : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {m : ℕ} (u : HolUnif A L m), u.ex 0 = 1 := by
    intro A _ L m u
    have h := u.ex_add 0 0
    rw [add_zero] at h
    simpa using h

  have hpb : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ X'.A, a.left ≫ p = b.left ≫ p → a = b := by
    intro a b h
    exact Over.OverMorphism.ext (hp.grp.1.hom_ext h (by rw [Over.w a, Over.w b]))

  have hepi : ∀ a b : 𝟙_ (Over (Sp ℂ)) ⟶ T.X.A, spMap (g : ℂ →+* ℂ) ≫ a.left = spMap (g : ℂ →+* ℂ) ≫ b.left → a = b := by
    intro a b h
    haveI : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) := (RingEquiv.toCommRingCatIso g).isIso_hom
    haveI : IsIso (spMap (g : ℂ →+* ℂ)) := by unfold spMap; infer_instance
    exact Over.OverMorphism.ext ((cancel_epi _).1 h)
  have H0 : (u'.ex 0).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex 0).left := by
    have := H 0 0 (by simp)
    simp only [map_zero] at this
    exact this

  have hmemL : ∀ x' : E, x' ∈ lattice c (y * (upIdele K E t)⁻¹) ↔
      ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) 0) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro x'
    have e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹ := by rw [mul_inv_rev, inv_inv]
    show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c ↔ _
    rw [e, Units.val_mul, map_zero, sub_zero]
    constructor <;> intro h <;> convert h using 1 <;> ring
  have hdef : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) =
      fun j ↦ g (φ (T.U.e j) x) := by
    intro x; funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hdef0 : ∀ x : E, (fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord φ 0 x (T.U.e j)) = fun j ↦ φ (T.U.e j) x := by
    intro x; funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]

  have hsup : ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹), (fun j ↦ g (φ (T.U.e j) x')) ∈ u'.Λ := by
    intro x' hx'
    have h1 := H 0 x' ((hmemL x').1 hx')
    simp only [map_zero] at h1
    rw [← u'.ker, ← hex0 u']
    refine hpb _ _ ?_
    rw [H0]
    exact h1

  have hsubL : ∀ y₁ : (Af E)ˣ, ∃ S : AddSubgroup E, (S : Set E) = lattice c y₁ := by
    intro y₁
    refine ⟨{ carrier := lattice c y₁, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, rfl⟩
    · intro a b ha hb
      show _ ∈ hatO c
      rw [map_add, add_mul]
      exact add_mem ha hb
    · show _ ∈ hatO c
      rw [map_zero, zero_mul]
      exact zero_mem _
    · intro a ha
      show _ ∈ hatO c
      rw [map_neg, neg_mul]
      exact neg_mem ha
  obtain ⟨SL, hSL⟩ := hsubL y
  obtain ⟨SL', hSL'⟩ := hsubL (y * (upIdele K E t)⁻¹)
  have hpos : 0 < Module.finrank ℚ (FR E) := Module.finrank_pos
  let j₀ : Fin (Module.finrank ℚ (FR E)) := ⟨0, hpos⟩
  let Φ : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j ↦ φ (T.U.e j) x
      map_add' := by intros; funext j; simp
      map_smul' := by intros; funext j; simp }
  let Φ' : E →ₗ[ℤ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun x j ↦ g (φ (T.U.e j) x)
      map_add' := by intros; funext j; simp
      map_smul' := by intros; funext j; simp }
  have hΦinj : Function.Injective Φ := fun a b h ↦ (φ (T.U.e j₀)).injective (congrFun h j₀)
  have hΦ'inj : Function.Injective Φ' := fun a b h ↦ (φ (T.U.e j₀)).injective (g.injective (congrFun h j₀))
  have hΛ : T.U.u.Λ = SL.toIntSubmodule.map Φ := by
    ext w
    rw [T.U.lat, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · show x ∈ (SL : Set E)
        rw [hSL]; exact hx
      · rw [hdef0]; rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, ?_, ?_⟩
      · rw [← hSL]; exact hx
      · rw [hdef0]; rfl
  let M : Submodule ℤ (Fin (Module.finrank ℚ (FR E)) → ℂ) := SL'.toIntSubmodule.map Φ'
  have hMle : M ≤ u'.Λ := by
    rintro w ⟨x', hx', rfl⟩
    exact hsup x' (by rw [← hSL']; exact hx')
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.T.finite_adele_clear_denominator E c hc (upIdele K E t : Af E)
  have hrank : Module.rank ℤ T.U.u.Λ ≤ Module.rank ℤ M := by
    rw [hΛ, ← (Submodule.equivMapOfInjective _ hΦinj _).rank_eq,
      ← (Submodule.equivMapOfInjective _ hΦ'inj _).rank_eq]
    let mulm : E →ₗ[ℤ] E := (AddMonoidHom.mulLeft m).toIntLinearMap
    have hmulm : Function.Injective mulm := mul_right_injective₀ hm0
    calc Module.rank ℤ SL.toIntSubmodule = Module.rank ℤ (SL.toIntSubmodule.map mulm) :=
          (Submodule.equivMapOfInjective _ hmulm _).rank_eq
      _ ≤ Module.rank ℤ SL'.toIntSubmodule := by
          refine Submodule.rank_mono ?_
          rintro _ ⟨x, hx, rfl⟩
          have hx' : x ∈ lattice c y := by rw [← hSL]; exact hx
          show m * x ∈ (SL' : Set E)
          rw [hSL']
          have e : ((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) = upIdele K E t * y⁻¹ := by rw [mul_inv_rev, inv_inv]
          show _ * ((((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ)) : Af E) ∈ hatO c
          rw [e, Units.val_mul, map_mul]
          have := mul_mem hm hx'
          convert this using 1
          ring
  intro w
  constructor
  · intro hw
    obtain ⟨k, hk, hkw⟩ := GlobalTheory.T.lattice_multiple_mem_sublattice _ u'.Λ T.U.u.Λ M u'.discrete T.U.u.discrete u'.full T.U.u.full hMle hrank w hw
    obtain ⟨x'', hx'', hx''e⟩ := Submodule.mem_map.1 hkw
    have hk' : (k : E) ≠ 0 := Int.cast_ne_zero.2 hk
    have hw' : w = Φ' (x'' / k) := by
      apply smul_right_injective (Fin (Module.finrank ℚ (FR E)) → ℂ) hk
      show k • w = k • Φ' (x'' / k)
      rw [← map_zsmul, ← hx''e]
      congr 1
      rw [zsmul_eq_mul, mul_div_cancel₀ _ hk']
    set x' := x'' / k
    obtain ⟨x, hx⟩ := GlobalTheory.T.finite_adele_approximation_mod_conductor E c hc y ((upIdele K E t : Af E) * algebraMap E (Af E) x')
    have h1 := H x x' hx
    have hw1 : u'.ex (fun j ↦ g (φ (T.U.e j) x')) = 1 := (u'.ker _).2 (by rw [hw'] at hw; exact hw)
    rw [hw1, ← hex0 u', H0] at h1
    have h2 := hepi _ _ h1
    have h3 : (fun j ↦ φ (T.U.e j) x) ∈ T.U.u.Λ := (T.U.u.ker _).1 (by rw [← h2, hex0])
    rw [T.U.lat] at h3
    obtain ⟨x₀, hx₀, he⟩ := h3
    rw [hdef0] at he
    have hxx : x = x₀ := (φ (T.U.e j₀)).injective (congrFun he j₀)
    subst hxx
    refine ⟨x', ?_, by rw [hdef]; exact hw'⟩
    rw [hmemL, map_zero, sub_zero]
    have := add_mem hx hx₀
    convert this using 1
    ring
  · rintro ⟨x', hx', rfl⟩
    rw [hdef]
    exact hsup x' hx'

end GlobalTheory.ConjUnifLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat.ClosedLift

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem endo_of_closed {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {V : Type} [CommRing V]
    [IsDomain V] {ξ : Sp V ⟶ S} {G₁ : Over (Sp V)} [GrpObj G₁] {φ₁ : G₁.left ⟶ G.left}
    (h : IsGrpPullback G₁ G ξ φ₁) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (j : splitTorus (Sp V) X ⟶ G₁) [IsMonHom j] {GK : Over (Sp (FractionRing V))} [GrpObj GK]
    {ψ : GK.left ⟶ G₁.left} (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ)
    (hK : IsTorPart (pullTorus hψ j)) {κ : Type} [Field κ] {b : V →+* κ} {G₀ : Over (Sp κ)} [GrpObj G₀]
    {ψ₀ : G₀.left ⟶ G₁.left} (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (h0 : IsTorPart (pullTorus hψ₀ j))
    (u : G ⟶ G) [IsMonHom u] (r : X →+ X)
    (hr : (pullTorus hψ₀ j).left ≫ (ψ₀ ≫ φ₁) ≫ u.left = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁) :
    j.left ≫ φ₁ ≫ u.left = (torusMap _ r ≫ j).left ≫ φ₁ := by
  obtain ⟨u₁, hu₁, pa⟩ := GlobalTheory.SymBaseChange.exists_endo h u
  have hw : u₁.left ≫ φ₁ = φ₁ ≫ u.left := by
    have := congrArg CommaMorphism.left (pa (𝟙 G₁))
    simpa [pushPt] using this
  haveI := hu₁
  obtain ⟨s, hs⟩ := hK.factor (pullTorus hψ (j ≫ u₁)) inferInstance
  rw [← pullTorus_torusMap_comp] at hs
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap V (FractionRing V))) ∧
      IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSeparated G₁.hom := MorphismProperty.of_isPullback h.1 ‹_›
  have key : j ≫ u₁ = torusMap _ s ≫ j :=
    GlobalTheory.ExtUnique.over_hom_ext_of_isPullback
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap (algebraMap V (FractionRing V))) X)
      (by rw [← pullTorus_left hψ, ← pullTorus_left hψ, hs])
  have k0 : torusMap _ s ≫ pullTorus hψ₀ j = torusMap _ r ≫ pullTorus hψ₀ j := by
    apply hom_ext_of_pullback (hψ₀.comp h)
    have e1 := pullTorus_left hψ₀ (j ≫ u₁)
    have e2 := pullTorus_left hψ₀ j
    calc (torusMap _ s ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁
        = ((pullTorus hψ₀ (j ≫ u₁)).left ≫ ψ₀) ≫ φ₁ := by
          rw [← pullTorus_torusMap_comp, ← key, Category.assoc]
      _ = bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ u.left := by
          rw [e1]; simp [Category.assoc, hw]
      _ = ((pullTorus hψ₀ j).left ≫ ψ₀) ≫ φ₁ ≫ u.left := by
          rw [e2]; simp only [Category.assoc]
      _ = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := by
          rw [← hr]; simp only [Category.assoc]
  have hsr : s = r := h0.cancel k0
  subst hsr
  rw [← key, Over.comp_left, Category.assoc, hw]

theorem compat_of_closed : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ e, IsMonHom (f e)) → (∀ t, gγ t ^ L = 1) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), IsMonHom j → (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀), IsTorPart (pullTorus hψ₀ j) → Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ₀ ≫ φ₁) (pullTorus hψ₀ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hLu hf hgγ X _ _ _ m c V _ _ _ ξ a G₁ _ φ₁ h j hj hext GK _ ψ hψ hK
    κ _ b hb G₀ _ ψ₀ hψ₀ h0 hC
  haveI := hG.separated
  haveI := hj
  haveI : NeZero L := ⟨hL.ne'⟩
  refine ⟨fun e => ?_, fun t => ?_⟩
  · haveI := hf e
    exact endo_of_closed h j hψ hK hψ₀ h0 (f e) (m e) (hC.1 e)
  obtain ⟨z₀, hz₀, hv₀⟩ := hC.2 t
  have hζV : (Units.map a.toMonoidHom ζ) ^ L = 1 := by rw [← map_pow, hζ, map_one]
  have hpow : ∀ k : ℕ, ((Units.map a.toMonoidHom ζ) ^ k) ^ L = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζV, one_pow]
  let F : Multiplicative X →* Γ(Sp V, ⊤)ˣ :=
    { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
      map_one' := by simp [unitOn]
      map_mul' := fun x y => by
        rw [toAdd_mul, map_add, ZMod.val_add, ← pow_eq_pow_mod _ hζV, pow_add]
        simp [unitOn] }
  let Z1 : Over (Sp V) := Over.mk (𝟙 (Sp V))
  obtain ⟨z, hz⟩ : ∃ z : Z1 ⟶ splitTorus (Sp V) X, GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z = F :=
    ⟨_, MulEquiv.apply_symm_apply _ _⟩
  have hzχ : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    show GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z (Multiplicative.ofAdd χ) = _
    rw [hz]; rfl
  have hzL : z ^ L = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1).injective
    rw [map_pow, hz, map_one]
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show unitOn _ ^ L = 1
    rw [unitOn, ← map_pow, hpow, map_one]

  let x : Over.mk (Z1.hom ≫ ξ) ⟶ G := pushPt h.1.w (z ≫ j)
  have hxL : x ^ L = 1 := by
    have e1 : pushPt h.1.w ((z ≫ j) ^ L) = x ^ L := map_pow (pushHom h Z1) (z ≫ j) L
    rw [← e1, ← pow_comp, hzL, one_comp]
    exact map_one (pushHom h Z1)

  obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
  have hvb : spMap b ≫ v = (z₀ ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := ValAt.unique (hv.comp (spMap b)) hv₀
  obtain ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩ := hv
  let H : Over.mk W.ι ⟶ G := Over.homMk hW hW1
  have hne : (W : Set M.Z).Nonempty := ⟨ξ (closedPoint V), by rw [← hs']; exact (s' (closedPoint V)).2⟩
  haveI : Nonempty W.toScheme := ⟨⟨_, hne.some_mem⟩⟩
  haveI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have hr : Set.range M.pt ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let x₀ := IsOpenImmersion.lift W.ι M.pt hr
  have hx₀ : x₀ ≫ W.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant (x₀ ≫ W.ι) := hx₀ ▸ M.isDominant_pt
  haveI : IsDominant x₀ := IsDominant.of_comp_of_isOpenImmersion x₀ W.ι
  have hHL : H ^ L = 1 := by
    let u : Over.mk M.pt ⟶ Over.mk W.ι := Over.homMk x₀ hx₀
    have hu : u ≫ H = gγ t := Over.OverMorphism.ext (hW2 x₀ hx₀)
    have e : u ≫ H ^ L = u ≫ 1 := by rw [comp_pow, hu, hgγ t, comp_one]
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk W.ι).left := inferInstanceAs (IsReduced W.toScheme)
    refine ext_of_isDominant_of_isSeparated (s := G.hom) ?_ x₀ ?_
    · rw [Over.w, Over.w]
    · exact congrArg CommaMorphism.left e
  let σ : Over.mk (Z1.hom ≫ ξ) ⟶ Over.mk W.ι := Over.homMk s' (by
    show s' ≫ W.ι = 𝟙 _ ≫ ξ
    rw [hs', Category.id_comp])
  let y : Over.mk (Z1.hom ≫ ξ) ⟶ G := σ ≫ H
  have hyL : y ^ L = 1 := by
    show (σ ≫ H) ^ L = 1
    rw [← comp_pow, hHL, comp_one]

  have hw' : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
    rw [Category.assoc, Over.w z]; simp [Z1]
  let z' : Over.mk (𝟙 (Sp κ)) ⟶ splitTorus (Sp κ) X :=
    Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hw')
      ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
  have hz'l : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
    (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
  have hz'χ : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    ext
    have e := congrArg Units.val (hzχ χ)
    rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
    rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz'l,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    erw [e]
    simp only [unitOn, Units.coe_map]
    have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.symm.trans ?_
    simp
  have hzz : z₀ = z' := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp κ) X _).injective
    refine MonoidHom.ext fun χ => ?_
    exact (hz₀ (Multiplicative.toAdd χ)).trans (hz'χ (Multiplicative.toAdd χ)).symm
  have hcl : spMap b ≫ x.left = spMap b ≫ y.left := by
    show spMap b ≫ (z ≫ j).left ≫ φ₁ = spMap b ≫ s' ≫ hW
    rw [hsv, hvb, hzz]
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% (pullTorus_left hψ₀ j), reassoc_of% hz'l]
  have hLV : IsUnit (L : V) := by simpa using hLu.map a
  have hxy : x = y := GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint M.Z G hG.smooth V (Z1.hom ≫ ξ) L hLV x y
    (by rw [hxL, hyL]) κ b hb hcl
  refine ⟨z, hzχ, ?_⟩
  have e' : (z ≫ j).left ≫ φ₁ = v := (congrArg CommaMorphism.left hxy).trans hsv
  rw [e']
  exact ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩

end GlobalTheory.Poinc.FibLat.ClosedLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatOverField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem compat_of_compat_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (X : Type) [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (K : Type) [Field K] (b : V →+* K), Function.Injective b → ∀ (GK : Over (Sp K)) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap b) ψ), Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ ≫ φ₁) (pullTorus hψ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ X _ m c V _ _ _ ξ a G₁ _ φ₁ h₁ j hext K _ b hb GK _ ψ hψ hK
  haveI hsep : IsSeparated G.hom := hG.separated
  haveI : Flat (splitTorusAff ZU X).hom := (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
  haveI : Flat (splitTorus (Sp V) X).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : IsSchemeTheoreticallyDominant (spMap b) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hb
  haveI : QuasiCompact (spMap b) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (bcMap (spMap b) X) :=
    IsSchemeTheoreticallyDominant.of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).flip
  have hw : φ₁ ≫ G.hom = G₁.hom ≫ ξ := h₁.1.w
  refine ⟨fun e => ?_, fun t => ?_⟩
  · have h1 := hK.1 e
    rw [← pullTorus_torusMap_comp] at h1
    simp only [Category.assoc] at h1
    have e1 := pullTorus_left hψ j
    have e2 := pullTorus_left hψ (torusMap (Sp V) (m e) ≫ j)
    refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (bcMap (spMap b) X) ?_
    · simp only [Category.assoc, Over.w, hw, Over.w_assoc, Over.comp_left]
    · calc bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ (f e).left
          = (pullTorus hψ j).left ≫ ψ ≫ φ₁ ≫ (f e).left := by rw [reassoc_of% e1]
        _ = (pullTorus hψ (torusMap (Sp V) (m e) ≫ j)).left ≫ ψ ≫ φ₁ := h1
        _ = bcMap (spMap b) X ≫ (torusMap (Sp V) (m e) ≫ j).left ≫ φ₁ := by rw [reassoc_of% e2]
  · obtain ⟨zK, hzK, hvK⟩ := hK.2 t
    haveI : NeZero L := ⟨hL.ne'⟩
    have huL : Units.map a.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
    let φh : Multiplicative X →* (Γ(Sp V, ⊤))ˣ :=
      { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
        map_one' := by simp [unitOn]
        map_mul' := fun x y => by
          simp only [toAdd_mul, map_add, unitOn]
          rw [ZMod.val_add, ← pow_eq_pow_mod _ huL, pow_add, map_mul] }
    let z : Over.mk (𝟙 (Sp V)) ⟶ splitTorus (Sp V) X := (GlobalTheory.splitTorusPointsEquiv (Sp V) X _).symm φh
    have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
      rfl
    have hwz : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
      rw [Category.assoc, Over.w z]; simp
    let z' : Over.mk (𝟙 (Sp K)) ⟶ splitTorus (Sp K) X :=
      Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hwz)
        ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
    have hz' : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
    have hcz' : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      ext
      have e := congrArg Units.val (hz χ)
      rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
      rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz',
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [e]
      simp only [unitOn, Units.coe_map]
      have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      refine this.symm.trans ?_
      simp
    have hzz : zK = z' := GlobalTheory.SplitTorus.hom_ext fun χ => by
      rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.UU.chV_val,
        ← GlobalTheory.UU.chV_val, hzK, hcz']
    have hvK' : ValAt (gγ t) (spMap b ≫ ξ) (spMap b ≫ (z ≫ j).left ≫ φ₁) := by
      convert hvK using 1
      rw [hzz, Over.comp_left, Over.comp_left]
      simp only [Category.assoc]
      rw [reassoc_of% (pullTorus_left hψ j), reassoc_of% hz']
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
    have hvv : spMap b ≫ v = spMap b ≫ (z ≫ j).left ≫ φ₁ := (hv.comp (spMap b)).unique hvK'
    have hveq : v = (z ≫ j).left ≫ φ₁ := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap b) hvv
      rw [hv.over]
      simp only [Category.assoc, hw, Over.comp_left, Over.w_assoc]
      exact (Category.id_comp _).symm
    exact ⟨z, hz, hveq ▸ hv⟩

end GlobalTheory.Poinc.FibLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharactersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionMap_welldefined_additive_characters : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X), IsMonHom b → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ g : GtPtF D₁ F, ∃! g' : GtPtF D₂ F, Act D₁ D₂ b h g g') ∧ (∀ (g₁ g₂ g₃ : GtPtF D₁ F) (g₁' g₂' g₃' : GtPtF D₂ F), g₁.IsAdd g₂ g₃ → Act D₁ D₂ b h g₁ g₁' → Act D₁ D₂ b h g₂ g₂' → Act D₁ D₂ b h g₃ g₃' → g₁'.IsAdd g₂' g₃') ∧ ∀ (t : Multiplicative D₁.X →* Fˣ) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), IsTor t g → Act D₁ D₂ b h g g' → IsTor (t.comp (AddMonoidHom.toMultiplicative h)) g' := by
  first | exact @GlobalTheory.Mum.Two.act_two_hom | exact GlobalTheory.Mum.Two.act_two_hom | (intros; apply GlobalTheory.Mum.Two.act_two_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFielStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPointAction_period_value_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : D'.X) (y₀ : D₀.X) (g : GtPtF D' F) (g' : GtPtF D₀ F), GtPtF.IsIota y g → GtPtF.IsIota y₀ g' → Act D' D₀ pr h g g' → ∀ (χ : D₀.X) (u : LB.Gen (CmpLB D' D₀ pr (h χ) χ)), Nrm u → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ (D'.P.A.left ⨿ D₀.P.A.left : Scheme.{0})) → (JN D' D₀).ι), Good (JN D' D₀) z J → val (D₀.tau y₀ χ) (𝟙 _) z (rr J) = val (D'.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D'.c y)) z J := by
  first | exact @GlobalTheory.Mum.Two.act_val_frac | exact GlobalTheory.Mum.Two.act_val_frac | (intros; apply GlobalTheory.Mum.Two.act_val_frac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPullbackDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPointAction_pullback_data : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D₁ D₂ : DegPre R) (D₁' D₂' : DegPre R') (hD₁ : IsPullDeg φ D₁ D₁') (hD₂ : IsPullDeg φ D₂ D₂') (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (b' : D₁'.P.A ⟶ D₂'.P.A) (h' : D₂'.X →+ D₁'.X), IsMonHom b → IsMonHom b' → b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b → (∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ)) → (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ), Nrm u) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (g₁ : GtPtF D₁ F) (g₂ : GtPtF D₂ F) (g₁' : GtPtF D₁' F) (g₂' : GtPtF D₂' F), IsPullGtF φ hD₁ F g₁ g₁' → IsPullGtF φ hD₂ F g₂ g₂' → (Act D₁ D₂ b h g₁ g₂ ↔ Act D₁' D₂' b' h' g₁' g₂') := by
  first | exact @GlobalTheory.Mum.Two.ActPull.main | exact GlobalTheory.Mum.Two.ActPull.main | (intros; apply GlobalTheory.Mum.Two.ActPull.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointOfThickeningEqTransportStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPoint_of_thickening_eq_transport : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  first | exact @GlobalTheory.Mum.isPullPt_of_carries | exact GlobalTheory.Mum.isPullPt_of_carries | (intros; apply GlobalTheory.Mum.isPullPt_of_carries <;> assumption)
end

