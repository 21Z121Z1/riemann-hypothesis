import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2525
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionDvdEverywhereSmoothConnectedFib
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DivSpread

theorem dvd_of_specializes {X : Scheme.{0}} {V : Type} [CommRing V] (p : X ⟶ Spec (CommRingCat.of V)) {L : LB X}
    (hL : L.IsLB) (s : LB.Sec L) (a : V) {x y : X} (hyx : y ⤳ x)
    (h : ∀ j, x ∈ L.U j → cst p x a ∣ gs (𝟙 X) x (L.U j) (s.f j)) :
    ∀ j, y ∈ L.U j → cst p y a ∣ gs (𝟙 X) y (L.U j) (s.f j) := by
  intro i hyi
  obtain ⟨k, hxk⟩ : ∃ k, x ∈ L.U k := by
    have : x ∈ (⨆ k, L.U k) := hL.cover ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hyk : y ∈ L.U k := hyx.mem_open (L.U k).isOpen hxk
  have sp : ∀ (U : X.Opens) (hx : x ∈ U) (b : Γ(X, U)),
      gs (𝟙 X) y U b = (X.presheaf.stalkSpecializes hyx).hom (gs (𝟙 X) x U b) := by
    intro U hx b
    rw [gs_eq _ y U (hyx.mem_open U.isOpen hx), gs_eq _ x U hx]
    exact (congrArg (fun φ => φ.hom ((Scheme.Hom.app (𝟙 X) U).hom b))
      (X.presheaf.germ_stalkSpecializes _ hyx)).symm
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z a := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨t, ht⟩ := h k hxk
  have hk : cst p y a ∣ gs (𝟙 X) y (L.U k) (s.f k) := by
    refine ⟨(X.presheaf.stalkSpecializes hyx).hom t, ?_⟩
    rw [sp _ hxk, ht, map_mul, ← hc, ← hc, ← sp (p ⁻¹ᵁ ⊤) (show p x ∈ (⊤ : (Spec (CommRingCat.of V)).Opens) from trivial)]
  have hm : y ∈ L.U i ⊓ L.U k := ⟨hyi, hyk⟩
  have e := congrArg (gs (𝟙 X) y (L.U i ⊓ L.U k)) (s.compat i k)
  rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm] at e
  rw [e]
  exact Dvd.dvd.mul_left hk _

theorem exists_specializes_not_dvd {X : Scheme.{0}} {U W : X.Opens} (c : Γ(X, W)) (f : Γ(X, U)) {x : X}
    (hxU : x ∈ U) (hxW : x ∈ W) [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsNoetherianRing (X.presheaf.stalk x)] (h : ¬ gs (𝟙 X) x W c ∣ gs (𝟙 X) x U f) :
    ∃ y, y ⤳ x ∧ Order.coheight y ≤ 1 ∧ ¬ gs (𝟙 X) y W c ∣ gs (𝟙 X) y U f := by
  by_contra H
  push_neg at H
  apply h
  obtain ⟨V, hV, hxV, hVle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U ⊓ W) (x := x) ⟨hxU, hxW⟩
  have hVU : V ≤ U := fun z hz => (hVle hz).1
  have hVW : V ≤ W := fun z hz => (hVle hz).2
  let fV : Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom f
  let cV : Γ(X, V) := (X.presheaf.map (homOfLE hVW).op).hom c
  have hgf : ∀ z (hz : z ∈ V), gs (𝟙 X) z U f = (X.presheaf.germ V z hz).hom fV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVU hz, gs_eq _ z V hz]; rfl
  have hgc : ∀ z (hz : z ∈ V), gs (𝟙 X) z W c = (X.presheaf.germ V z hz).hom cV := fun z hz => by
    rw [← gs_res (𝟙 X) z hVW hz, gs_eq _ z V hz]; rfl
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  haveI hlocx := hV.isLocalization_stalk ⟨x, hxV⟩
  rw [← Ideal.mem_span_singleton]
  refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one _ _ fun Q hQ hQ1 => ?_
  let P : Ideal Γ(X, V) := Q.comap (algebraMap Γ(X, V) (X.presheaf.stalk x))
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ Q
  let Pt : PrimeSpectrum Γ(X, V) := ⟨P, hPp⟩
  have hyV : hV.fromSpec Pt ∈ V := by
    have : hV.fromSpec Pt ∈ Set.range hV.fromSpec := ⟨Pt, rfl⟩
    rwa [hV.range_fromSpec] at this
  let yV : V := ⟨hV.fromSpec Pt, hyV⟩
  have hPt : hV.primeIdealOf yV = Pt := hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf yV)
  have hsp : yV.1 ⤳ x := by
    have hle : Pt ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
      show P ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
      rw [← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  letI : Algebra Γ(X, V) (X.presheaf.stalk yV.1) := X.presheaf.algebra_section_stalk yV
  have hlocy := hV.isLocalization_stalk yV
  rw [hPt] at hlocy
  have hdim : Order.coheight yV.1 ≤ 1 := by
    rw [← GlobalTheory.ringKrullDim_stalk_le_one_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P (X.presheaf.stalk yV.1)]
    have := IsLocalization.height_comap (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl Q
    change (P.height : WithBot ℕ∞) ≤ 1
    rw [show P = Ideal.under Γ(X, V) Q from rfl, this]
    exact_mod_cast hQ1
  obtain ⟨t, ht⟩ := H yV.1 hsp hdim
  rw [hgf _ hyV, hgc _ hyV] at ht
  change algebraMap Γ(X, V) _ fV = algebraMap Γ(X, V) _ cV * t at ht
  obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl t
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq, ← map_mul] at ht
  obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) ht
  refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * w), ?_, ?_⟩
  · exact (P.primeCompl.mul_mem m.2 w.2 : (m : Γ(X, V)) * w ∉ P)
  · rw [Ideal.mem_span_singleton, hgf x hxV, hgc x hxV]
    change algebraMap Γ(X, V) _ cV ∣ algebraMap Γ(X, V) _ (m * w) * algebraMap Γ(X, V) _ fV
    refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk x) (m * a), ?_⟩
    rw [← map_mul, ← map_mul, show (m : Γ(X, V)) * w * fV = m * (fV * w) by ring, hm,
      show (m : Γ(X, V)) * (cV * a) = cV * (m * a) by ring]

theorem eq_of_specializes_of_coheight_le_one {X S : Scheme.{0}} (p : X ⟶ S) [Flat p] {y w : X}
    (hy : Order.coheight y ≤ 1) {P' : S} (hP' : P' ⤳ p y) (hne : P' ≠ p y) (hw : w ⤳ y) (he : p w = p y) :
    w = y := by
  by_contra hne'
  have hlt : y < w := lt_of_le_not_ge (show y ≤ w from hw) (fun h => hne' (hw.antisymm h).eq)
  have hmaxw : IsMax w := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hy w hlt
  obtain ⟨z, hz, hpz⟩ := Flat.generalizingMap p (show P' ⤳ p w from he ▸ hP')
  have h1 : w ≤ z := hz
  have h2 : z = w := (hz.antisymm (hmaxw h1)).eq
  exact hne (hpz.symm.trans (h2 ▸ he))

theorem mem_of_not_isUnit_cst {X : Scheme.{0}} {R : Type} [CommRing R] (p : X ⟶ Spec (CommRingCat.of R)) (y : X)
    (a : R) (h : ¬ IsUnit (cst p y a)) : a ∈ (p y).asIdeal := by
  by_contra ha
  apply h
  have hy : y ∈ p ⁻¹ᵁ ⊤ := show p y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial
  rw [cst, gs_eq p y ⊤ hy]
  refine (X.mem_basicOpen _ y hy).1 ?_
  rw [← Scheme.preimage_basicOpen]
  show p y ∈ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  rw [basicOpen_eq_of_affine]
  exact ha

theorem specializes_of_mem_fibre {X S : Scheme.{0}} (p : X ⟶ S) [GeometricallyIrreducible p] {y : X}
    (hmax : ∀ w, w ⤳ y → p w = p y → w = y) {z : X} (hz : p z = p y) : y ⤳ z := by
  obtain ⟨y', hy'⟩ : y ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; rfl
  obtain ⟨z', hz'⟩ : z ∈ Set.range (p.fiberι (p y)) := by rw [Scheme.Hom.range_fiberι]; exact hz
  have hg : ∀ t, genericPoint (p.fiber (p y)) ⤳ t := fun t => (genericPoint_spec _).specializes trivial
  have hgm : p (p.fiberι (p y) (genericPoint (p.fiber (p y)))) = p y := by
    have : p.fiberι (p y) (genericPoint (p.fiber (p y))) ∈ Set.range (p.fiberι (p y)) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have h1 : p.fiberι (p y) (genericPoint (p.fiber (p y))) = y :=
    hmax _ (by have := (hg y').map (p.fiberι (p y)).continuous; rwa [hy'] at this) hgm
  rw [← h1, ← hz']
  exact (hg z').map (p.fiberι (p y)).continuous

end GlobalTheory.DivSpread

open GlobalTheory.DivSpread in
theorem GlobalTheory.DivSpread.dvd_everywhere : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Smooth p → GeometricallyConnected p → ∀ (e : Spec (CommRingCat.of R) ⟶ X), e ≫ p = 𝟙 _ → ∀ (L : LB X), L.IsLB → ∀ (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X), p x = closedPoint R → ∀ j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t := by
  intro R _ _ _ _ _ X p hsm hgc e he L hL s q hq hcl x j hxj
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hnot
  let c : Γ(X, p ⁻¹ᵁ ⊤) := (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom q)
  have hc : ∀ z, gs (𝟙 X) z (p ⁻¹ᵁ ⊤) c = cst p z q := fun z =>
    (gs_pull (𝟙 X) p z ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
  obtain ⟨y, hyx, hy1, hyn⟩ := exists_specializes_not_dvd c (s.f j) hxj trivial (by rw [hc]; exact hnot)
  rw [hc] at hyn
  have hyj : y ∈ L.U j := hyx.mem_open (L.U j).isOpen hxj
  have hqP : q ∈ (p y).asIdeal := mem_of_not_isUnit_cst p y q fun hu =>
    hyn ⟨hu.unit⁻¹ * gs (𝟙 X) y (L.U j) (s.f j), by rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]⟩
  let P0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hP0 : P0 ⤳ p y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have hP0' : P0 ≠ p y := fun h => hq (by
    have : q ∈ P0.asIdeal := h ▸ hqP
    exact this)
  have hmax : ∀ w, w ⤳ y → p w = p y → w = y := fun w hw hpe =>
    eq_of_specializes_of_coheight_le_one p hy1 hP0 hP0' hw hpe
  have hey : p (e (p y)) = p y := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have h1 : y ⤳ e (p y) := specializes_of_mem_fibre p hmax hey
  have h2 : e (p y) ⤳ e (closedPoint R) := (IsLocalRing.specializes_closedPoint (p y)).map e.continuous
  have hcm : p (e (closedPoint R)) = closedPoint R := by
    show (e ≫ p) (closedPoint R) = _
    rw [he]; rfl
  exact hyn (dvd_of_specializes p hL s q (h1.trans h2) (fun k hk => hcl _ hcm k hk) j hyj)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIsoTransportCochainsInIdeal
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem mul_eq_zero_of_mem_sqMap {R : Type} [CommRing R] {I : Ideal R} {B : Type} [CommRing B] [Algebra R B]
    (hJ : I.map (algebraMap R B) ^ 2 = 0) {u v : B} (hu : u ∈ I.map (algebraMap R B))
    (hv : v ∈ I.map (algebraMap R B)) : u * v = 0 := by
  have := Ideal.mul_mem_mul hu hv
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

theorem algHom_apply_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (f : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (f : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem eq_of_sub_mem_map {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (hJ : I.map (algebraMap R B) ^ 2 = 0) (f g : A →ₐ[R] B)
    (h : ∀ b, f b - g b ∈ I.map (algebraMap R B)) {x : A} (hx : x ∈ I.map (algebraMap R A)) : f x = g x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, -, rfl⟩ := hy
    rw [AlgHom.commutes, AlgHom.commutes]
  | zero => rw [map_zero, map_zero]
  | add y y' _ _ h1 h2 => rw [map_add, map_add, h1, h2]
  | smul a y hy ih =>
    rw [smul_eq_mul, map_mul, map_mul, ← ih, ← sub_eq_zero, ← sub_mul]
    exact mul_eq_zero_of_mem_sqMap hJ (h a) (algHom_apply_mem_map f hy)

theorem locIso_transport : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S'), (∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a)) ∧ (∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a, d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a)) ∧ ∀ c ∈ I • (⊤ : Submodule R (Cr hI π s₀)), ∃ (z : Z1 S.F) (z' : Z1 S'.F), S.IsIdealValuedLiftSystemCocycle z ∧ H1.mk _ z = S.r hI c ∧ H1.mk _ z' = S'.r hI c ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' Φ
  have hres : ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U),
      mp S'.F a (Φ.φ U b) - Φ.φ V (mp S.F a b) ∈ I.map (algebraMap R (S'.F.obj V)) := fun U V a b ↦ by
    rw [← S'.ker V, map_sub, S'.nat a, Φ.red, Φ.red, S.nat a, sub_self]
  have hcomm : ∀ (U V : AffOp X₀) (a : U ⟶ V) (x : S.F.obj U), x ∈ I.map (algebraMap R (S.F.obj U)) →
      mp S'.F a (Φ.φ U x) = Φ.φ V (mp S.F a x) := fun U V a x hx ↦
    eq_of_sub_mem_map (map_sq hI _) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))
      ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a) hx
  have c1 : ∀ z : Z1 S.F, S.IsIdealValuedLiftSystemCocycle z → ∃ z' : Z1 S'.F, S'.IsIdealValuedLiftSystemCocycle z' ∧ ∀ U V a, z'.1 U V a = Φ.φ V (z.1 U V a) := by
    intro z hz
    refine ⟨⟨fun U V a ↦ Φ.φ V (z.1 U V a), ?_⟩, fun U V a ↦ ?_, fun _ _ _ ↦ rfl⟩
    · intro U V W a b
      show Φ.φ W (z.1 U W (a ≫ b)) = mp S'.F b (Φ.φ V (z.1 U V a)) + Φ.φ W (z.1 V W b)
      rw [Z1.comp z a b, map_add, hcomm V W b _ (hz U V a)]
    · exact algHom_apply_mem_map (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (hz U V a)
  have c2 : ∀ g : C0 S.F, S.IsIdealValuedLiftSystemCochain g → ∀ U V a,
      d0 S'.F (fun W ↦ Φ.φ W (g W)) U V a = Φ.φ V (d0 S.F g U V a) := by
    intro g hg U V a
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, hcomm U V a _ (hg U)]
  refine ⟨c1, c2, fun c hc ↦ ?_⟩
  refine Submodule.smul_induction_on hc ?_ ?_
  · intro r hr c₀ _
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c₀
    let z : Z1 S.F := r • (S.coef hI).pullbackOneCocycle f
    have hzI : S.IsIdealValuedLiftSystemCocycle z := fun U V a ↦ by
      show r • (show S.F.obj V from ev f ((S.thick hI).map a)) ∈ I.map (algebraMap R (S.F.obj V))
      rw [Algebra.smul_def, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hr)
    obtain ⟨z', -, hz'⟩ := c1 z hzI
    refine ⟨z, z', hzI, ?_, ?_, hz'⟩
    · show H1.mk _ (r • _) = S.r hI (r • H1.mk _ f)
      rw [map_smul, map_smul]
      rfl
    · rw [map_smul, show S'.r hI (H1.mk _ f) = H1.mk _ ((S'.coef hI).pullbackOneCocycle f) from rfl, ← map_smul,
        H1.mk_eq_mk]
      let ΦH : ∀ W : AffOp X₀, S.thickObj hI W ⟶ S'.thickObj hI W := fun W ↦
        S.thickHom S' hI (𝟙 W) (Φ.φ W : S.F.obj W →ₐ[R] S'.F.obj W)
          (fun b ↦ (Φ.red W b).trans (mp_id (OAff s₀) W (S.p W b)).symm)
      refine ⟨fun W ↦ -(r • @id (S'.F.obj W) (ev f (ΦH W))), ?_⟩
      funext U V a
      have hz'' := hz' U V a
      have e1 : @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) =
          mp S'.F a (@id (S'.F.obj U) (ev f (ΦH U))) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) :=
        ev_comp f (ΦH U) ((S'.thick hI).map a)
      have e2 : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) =
          Φ.φ V (@id (S.F.obj V) (ev f ((S.thick hI).map a))) + @id (S'.F.obj V) (ev f (ΦH V)) :=
        ev_comp f ((S.thick hI).map a) (ΦH V)
      have e3 : algebraMap R (S'.F.obj V) r * (@id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
          @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a))) = 0 := by
        obtain ⟨⟨Q, hQ⟩, tay⟩ := GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V
        obtain ⟨θ, hθ, -⟩ := (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj V) I hI π hπ (S.p U)
          (S.semi U) (S.surj U) (S.ker U) ((mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U))).1
          ((Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V).comp (mp S.F a)) (hres U V a)
        have t := tay Q hQ (ΦH U ≫ (S'.thick hI).map a) ((S.thick hI).map a ≫ ΦH V) θ hθ f
        have t' : @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) ∈ I.map (algebraMap R (S'.F.obj V)) := by
          rw [show @id (S'.F.obj V) (ev f ((S.thick hI).map a ≫ ΦH V)) -
            @id (S'.F.obj V) (ev f (ΦH U ≫ (S'.thick hI).map a)) = _ from t]
          exact hθ.mem _
        exact mul_eq_zero_of_mem_sqMap (map_sq hI _) (Ideal.mem_map_of_mem _ hr) t'
      show -(r • @id (S'.F.obj V) (ev f (ΦH V))) - mp S'.F a (-(r • @id (S'.F.obj U) (ev f (ΦH U)))) =
        z'.1 U V a - r • @id (S'.F.obj V) (ev f ((S'.thick hI).map a))
      rw [hz'']
      show _ = Φ.φ V (r • @id (S.F.obj V) (ev f ((S.thick hI).map a))) - _
      rw [map_neg, map_smul, map_smul]
      simp only [Algebra.smul_def]
      linear_combination -(algebraMap R (S'.F.obj V) r) * (e1 - e2) - e3
  · rintro x y ⟨z₁, z₁', h₁, hx₁, hx₁', e₁⟩ ⟨z₂, z₂', h₂, hy₂, hy₂', e₂⟩
    refine ⟨z₁ + z₂, z₁' + z₂', fun U V a ↦ ?_, ?_, ?_, fun U V a ↦ ?_⟩
    · show z₁.1 U V a + z₂.1 U V a ∈ _
      exact Ideal.add_mem _ (h₁ U V a) (h₂ U V a)
    · rw [map_add, map_add, hx₁, hy₂]
    · rw [map_add, map_add, hx₁', hy₂']
    · show z₁'.1 U V a + z₂'.1 U V a = Φ.φ V (z₁.1 U V a + z₂.1 U V a)
      rw [map_add, e₁, e₂]

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFormsTensorSectionGenericFibreTransitionGer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeySecRel

theorem appLE_map' {X Y : Scheme.{0}} (p : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U) {W : Y.Opens} (h : W ≤ p ⁻¹ᵁ V)
    (h' : W ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    (p.appLE V W h).hom ((X.presheaf.map (homOfLE hVU).op).hom a) = (p.appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_app' {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) {U : S.Opens} {W : Y.Opens}
    (h : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ U)) (h' : W ≤ (p ≫ π) ⁻¹ᵁ U) (a : Γ(S, U)) :
    (p.appLE _ W h).hom ((π.app U).hom a) = ((p ≫ π).appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.comp_appLE]

theorem appLE_sec_tens {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) (A : LB X) (hA : A.IsLB) (δ : LB S)
    (σ : (CechPic.tens A (δ.pull π)).Sec) (l : A.ι) (i i' : δ.ι) (W : Y.Opens)
    (h : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i))
    (h' : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i'))
    (hW : W ≤ (p ≫ π) ⁻¹ᵁ (δ.U i ⊓ δ.U i')) :
    (p.appLE _ W h).hom (σ.f (l, fun _ => i)) =
      ((p ≫ π).appLE _ W hW).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) * (p.appLE _ W h').hom (σ.f (l, fun _ => i')) := by
  have hh : W ≤ p ⁻¹ᵁ ((CechPic.tens A (δ.pull π)).U (l, fun _ => i) ⊓ (CechPic.tens A (δ.pull π)).U (l, fun _ => i')) :=
    fun y hy => ⟨h hy, h' hy⟩
  have e := congrArg (p.appLE _ W hh).hom (σ.compat (l, fun _ => i) (l, fun _ => i'))
  rw [map_mul, appLE_map' p _ hh h, appLE_map' p _ hh h'] at e
  rw [e]
  congr 1
  have h1 : W ≤ p ⁻¹ᵁ (A.U l) := fun y hy => (h hy).1
  have h11 : W ≤ p ⁻¹ᵁ (A.U l ⊓ A.U l) := fun y hy => ⟨h1 hy, h1 hy⟩
  have hg : (p.appLE _ W h11).hom (A.g l l : Γ(X, A.U l ⊓ A.U l)) = 1 := by
    have := congrArg (fun u : Γ(X, A.U l)ˣ => (p.appLE _ W h1).hom (u : Γ(X, A.U l))) (hA.g_self l)
    simp only [Units.val_one, map_one] at this
    rw [← this]
    exact (appLE_map' p _ h1 h11 _).symm
  have h2 : W ≤ p ⁻¹ᵁ ((δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i')) := fun y hy => ⟨(h hy).2, (h' hy).2⟩
  have hd : ((δ.pull π).g (fun _ => i) (fun _ => i') : Γ(X, (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i'))) =
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i) PUnit.unit))
        (inf_le_right.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i') PUnit.unit)) :
        (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i') ≤ π ⁻¹ᵁ (δ.U i ⊓ δ.U i'))).op).hom
        ((π.app _).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) := by
    unfold LB.pull LB.LinComb
    dsimp only
    erw [Fintype.prod_unique, zpow_one]
    rfl
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) ((appLE_map' p _ hh h11 _).trans hg) (appLE_map' p _ hh h2 _)).trans ?_
  rw [_root_.one_mul]
  refine (congrArg (p.appLE _ W h2).hom hd).trans ?_
  have hW' : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ (δ.U i ⊓ δ.U i')) := hW
  exact (appLE_map' p _ h2 hW' _).trans (appLE_app' p π hW' hW _)

theorem genPt_appLE {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    ((KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU)).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (KeyVals.FF S))).inv.hom (S.presheaf.germ U (genericPoint S) hU a) := by
  have e := Scheme.fromSpecStalk_app (X := S) (x := genericPoint S) hU
  have : (KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU) =
      S.presheaf.germ U (genericPoint S) hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    unfold KeyVals.genPt Scheme.Hom.appLE
    erw [e]
    simp only [Category.assoc]
    erw [← Functor.map_comp]
    refine congrArg (fun z => _ ≫ z) ?_
    refine (congrArg (fun z => _ ≫ (Spec (S.presheaf.stalk (genericPoint S))).presheaf.map z)
      (Subsingleton.elim _ (𝟙 _))).trans ?_
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this]
  rfl

theorem locSec_eq_germ_mul : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), δ.IsLB → ∀ (i i' : δ.ι) (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i')
    (t t' : (KeyVals.bL L (KeyVals.genPt S)).L.Sec), KeyVals.IsLocSec σ i (KeyVals.genPt S) t →
    KeyVals.IsLocSec σ i' (KeyVals.genPt S) t' → ∀ j, t.f j =
      constFn (KeyVals.bG G (KeyVals.genPt S)).hom _ (S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) * t'.f j := by
  intro S _ G _ _ L δ σ _ i i' h2 t t' ht ht' j
  have hc : pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom =
      (KeyVals.bG G (KeyVals.genPt S)).hom ≫ KeyVals.genPt S := pullback.condition
  have hW : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      (pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom) ⁻¹ᵁ (δ.U i ⊓ δ.U i') := by
    rw [hc]
    exact fun y _ => KeyVals.genPt_le _ h2 (Set.mem_univ _)
  have hl : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ L.L.U (j PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => pullback.fst G.hom (KeyVals.genPt S)) j PUnit.unit
  have h : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i) :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).1⟩
  have h' : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i') :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).2⟩
  rw [ht j h, ht' j h']
  refine (appLE_sec_tens _ G.hom L.L L.isLB δ σ _ i i' _ h h' hW).trans ?_
  congr 1
  unfold constFn
  rw [← genPt_appLE, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ {Y : Scheme.{0}} (f f' : Y ⟶ S) (_ : f = f') (U : S.Opens) (W : Y.Opens) (a : W ≤ f ⁻¹ᵁ U)
      (a' : W ≤ f' ⁻¹ᵁ U) (x : Γ(S, U)), (f.appLE U W a).hom x = (f'.appLE U W a').hom x := by
    intro Y f f' e; subst e; intros; rfl
  exact key _ _ hc _ _ _ _ _

end GlobalTheory.KeySecRel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeNearGenerisationOfPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyOfFiniteType_near_generisation_of_point : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  first | exact @GlobalTheory.USpread.locally_finiteType_near | exact GlobalTheory.USpread.locally_finiteType_near | (intros; apply GlobalTheory.USpread.locally_finiteType_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogChernCocycleContractionInvariantFieldTrivialiStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logChernCocycle_contraction_invariantField_trivialised : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (c : Small L.U → L.ι) (hc : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (c T)) (u : ∀ T T' : Small L.U, (T ⟶ T') → T'.obj.B) (l : C2 (OSmall L.U)), (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (c T') ⊓ L.U (c T)) (le_inf (hc T') (φ.hom.le_preimage (hc T))) (L.g (c T') (c T)).val) → (∀ T T' T'' φ ψ, (l T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧ dpExp T''.obj.δ (l T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) → ∀ (v : epsR K ⟶ A) (hv : IsTangent v), ∃ N : L.ι → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ (j : L.ι) (P Q : GPt A) (φ : P.Hom Q) (hP : P.In (L.U j)), prism l hv φ ⟨j, hP⟩ = N j Q - φ.ρ (N j P)) ∧ ∀ (j j' : L.ι) (P : GPt A), P.In (L.U j) → P.In (L.U j') → N j P - N j' P = dlog L v j j' P := by
  first | exact @GlobalTheory.CechKS.prism_trivialised | exact GlobalTheory.CechKS.prism_trivialised | (intros; apply GlobalTheory.CechKS.prism_trivialised <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationDetEqUnitMulProdNormalCrossingsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDerivation_det_eq_unit_mul_prod_normalCrossings : ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n m : ℕ) (x : Fin n → A) (e : Fin m ↪ Fin n) (J : Finset (Fin m)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun j => algebraMap A R (x (e j))) → (∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i))) → ∀ (I : Ideal A), I.map (algebraMap A R) = Ideal.span {algebraMap A R (∏ j ∈ J, x (e j))} → ∀ (b : Fin n → Derivation ℤ A A), (∀ j c, b j (algebraMap F A c) = 0) → (∀ j, ∀ f ∈ I, b j f ∈ I) → (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∃ u : Rˣ, algebraMap A R (GlobalTheory.LogPole.logDet b x) = u * algebraMap A R (∏ j ∈ J, x (e j)) := by
  first | exact @GlobalTheory.logDet_local_eq_unit_mul_prod | exact GlobalTheory.logDet_local_eq_unit_mul_prod | (intros; apply GlobalTheory.logDet_local_eq_unit_mul_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInduction
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem eq_of_sup_baseIdeal_pow_eq {C : Type} [CommRing C] [IsNoetherianRing C] {J : Ideal C}
    (hJ : J ≤ Ideal.jacobson ⊥) {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of C)) [IsProper p]
    (a a' : V.IdealSheafData)
    (h : ∀ e : ℕ, a ⊔ baseIdeal p (J ^ (e + 1)) = a' ⊔ baseIdeal p (J ^ (e + 1))) : a = a' := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  refine le_antisymm ?_ ?_
  · exact GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a a' inferInstance fun e => (h e) ▸ le_sup_left
  · exact GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a' a inferInstance fun e => (h e).symm ▸ le_sup_left

theorem map_inf_eq_of_reductions : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  intro C _ _ J hJ W' π U hπ hU K τ hK
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.exists_map_comap_inf_sup_pow_eq (Spec (CommRingCat.of C)) W' π U inferInstance hU K τ hK
  refine ⟨k₀, fun k hk T' T'' h' h'' => ?_⟩
  have e' : T' = τ.comap π := by
    refine eq_of_sup_baseIdeal_pow_eq hJ π _ _ fun e => ?_
    rw [h' e, Scheme.IdealSheafData.comap_sup, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, Category.comp_id]
  have e'' : T'' = τ ⊔ K ^ k := by
    refine eq_of_sup_baseIdeal_pow_eq hJ (𝟙 _) _ _ fun e => ?_
    rw [h'' e, sup_right_comm]
  rw [e', e'']
  exact hk₀ k hk

end GlobalTheory.FormalAlg
end

