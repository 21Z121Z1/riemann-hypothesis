import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFin

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField TopologicalSpace

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U : X.Opens} (h : genPt ξ ∈ U) {q : X} (hq : q ∈ U)
    (hs : genPt ξ ⤳ q) (s : Γ(X, U)) :
    genMap ξ ⟨q, hs⟩ (X.presheaf.germ U q hq s) = secVal ξ U h s := by
  have e := X.presheaf.germ_stalkSpecializes (U := U) hq hs
  simp only [genMap, secVal]
  rw [← e]
  rfl

theorem secVal_res (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (hV : genPt ξ ∈ V)
    (hU : genPt ξ ∈ U) (s : Γ(X, U)) :
    secVal ξ V hV (X.presheaf.map i.op s) = secVal ξ U hU s := by
  have e : X.presheaf.map i.op ≫ X.presheaf.germ V (genPt ξ) hV = X.presheaf.germ U (genPt ξ) hU :=
    X.presheaf.germ_res i _ hV
  simp only [secVal]
  rw [← e]
  rfl

theorem secVal_injective {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q)
    (hinj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)) (U : X.Opens) (h : genPt ξ ∈ U) :
    Function.Injective (secVal ξ U h) := by
  intro s t e
  refine TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => ?_
  apply hinj ⟨q, hall q⟩
  change genMap ξ ⟨q, hall q⟩ (X.presheaf.germ U q hq s) = genMap ξ ⟨q, hall q⟩ (X.presheaf.germ U q hq t)
  rw [genMap_germ ξ h hq, genMap_germ ξ h hq, e]

theorem exists_secVal {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hall : ∀ q : X, genPt ξ ⤳ q)
    (hinj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)) (U : X.Opens) (h : genPt ξ ∈ U) (a : Ω)
    (ha : ∀ q (_ : q ∈ U), a ∈ regAt ξ ⟨q, hall q⟩) : ∃ s : Γ(X, U), secVal ξ U h s = a := by
  have key : ∀ q : U, ∃ (V : X.Opens) (_ : q.1 ∈ V) (i : V ⟶ U) (s : Γ(X, V)) (hV : genPt ξ ∈ V),
      secVal ξ V hV s = a := by
    intro q
    obtain ⟨g, hg⟩ := ha q.1 q.2
    obtain ⟨V, hqV, s, rfl⟩ := X.presheaf.germ_exist g
    have hV : genPt ξ ∈ V := (hall q.1).mem_open V.isOpen hqV
    have hVU : genPt ξ ∈ V ⊓ U := ⟨hV, h⟩
    refine ⟨V ⊓ U, ⟨hqV, q.2⟩, homOfLE inf_le_right, X.presheaf.map (homOfLE inf_le_left).op s, hVU, ?_⟩
    exact (secVal_res ξ (homOfLE inf_le_left) hVU hV s).trans ((genMap_germ ξ hV hqV (hall q.1) s).symm.trans hg)
  choose V hq i s hV hs using key
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.presheaf V s := by
    intro p q
    have hpq : genPt ξ ∈ V p ⊓ V q := ⟨hV p, hV q⟩
    have hI := secVal_injective hall hinj (V p ⊓ V q) hpq
    have e : secVal ξ (V p ⊓ V q) hpq (X.presheaf.map (Opens.infLELeft (V p) (V q)).op (s p)) =
        secVal ξ (V p ⊓ V q) hpq (X.presheaf.map (Opens.infLERight (V p) (V q)).op (s q)) := by
      rw [secVal_res ξ _ hpq (hV p), secVal_res ξ _ hpq (hV q), hs, hs]
    exact hI e
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' V U i
    (fun q hq' => Opens.mem_iSup.2 ⟨⟨q, hq'⟩, hq ⟨q, hq'⟩⟩) s hcomp
  refine ⟨t, ?_⟩
  have e := ht ⟨genPt ξ, h⟩
  rw [← secVal_res ξ (i ⟨genPt ξ, h⟩) (hV ⟨genPt ξ, h⟩) h t]
  exact (congrArg _ e).trans (hs _)

theorem secVal_congr {z w : Spec (CommRingCat.of Ω) ⟶ X} (e : z = w) (U : X.Opens) (hz : genPt z ∈ U)
    (hw : genPt w ∈ U) (s : Γ(X, U)) : secVal z U hz s = secVal w U hw s := by
  subst e
  rfl

theorem secVal_comp (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (U : X.Opens)
    (h : genPt (ξ' ≫ f) ∈ U) (h' : genPt ξ' ∈ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    secVal (ξ' ≫ f) U h s = secVal ξ' (f ⁻¹ᵁ U) h' (f.app U s) := by
  have e := f.germ_stalkMap U (genPt ξ') h'
  have e2 := Scheme.stalkClosedPointTo_comp ξ' f
  simp only [secVal]
  rw [e2]
  change ((X.presheaf.germ U (f (genPt ξ')) h' ≫ f.stalkMap (genPt ξ')) ≫ Scheme.stalkClosedPointTo ξ').hom s = _
  rw [e]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem secVal_spec (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* Ω') (U : X.Opens)
    (h : genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ) ∈ U) (h' : genPt ξ ∈ U) (s : Γ(X, U)) :
    secVal (Spec.map (CommRingCat.ofHom i) ≫ ξ) U h s = i (secVal ξ U h' s) := by
  have : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit ((Scheme.stalkClosedPointTo ξ).hom a) := by
      rw [isUnit_iff_ne_zero]
      intro h0
      have : (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom a = 0 := by
        change i ((Scheme.stalkClosedPointTo ξ).hom a) = 0
        rw [h0, map_zero]
      rw [this] at ha
      exact not_isUnit_zero ha
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom a h1
  have e0 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e : Spec.map (CommRingCat.ofHom i) ≫ ξ =
      Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (genPt ξ) := by
    conv_lhs => rw [← e0]
    rw [Spec.map_comp, Category.assoc]
  have h2 : genPt (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (genPt ξ)) ∈ U :=
    e ▸ h
  rw [secVal_congr e U h h2]
  have e3 := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) U h2
  exact congrArg (fun φ => φ.hom s) e3

theorem secVal_app {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (hd : Dominates ξ' ξ f i) (U : X.Opens) (h : genPt ξ ∈ U) (h' : genPt ξ' ∈ f ⁻¹ᵁ U)
    (s : Γ(X, U)) : secVal ξ' (f ⁻¹ᵁ U) h' (f.app U s) = i (secVal ξ U h s) := by
  have h1 : genPt (ξ' ≫ f) ∈ U := h'
  have h2 : genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ) ∈ U := hd ▸ h1
  rw [← secVal_comp ξ' f U h1 h', secVal_congr hd U h1 h2, secVal_spec ξ i U h2 h]

theorem finite_of_values {o A B : Type} [CommRing o] [CommRing A] [CommRing B] [Algebra o Ω'] (φ : A →+* B)
    (v : A →+* Ω) (v' : B →+* Ω') (i : Ω →+* Ω') (hv' : Function.Injective v')
    (hc : ∀ a, v' (φ a) = i (v a)) (R₀ : Subalgebra o Ω') (hR : ∀ r ∈ R₀, ∃ a, i (v a) = r) (s : Finset Ω')
    (hs : ∀ t ∈ s, ∃ b, v' b = t) (hb : ∀ b, v' b ∈ Submodule.span R₀ (s : Set Ω')) : φ.Finite := by
  classical
  choose! σ hσ using hs
  letI := φ.toAlgebra
  have hsm : ∀ a (b : B), a • b = φ a * b := fun a b => Algebra.smul_def a b
  have key : ∀ z ∈ Submodule.span R₀ (s : Set Ω'),
      ∃ b ∈ Submodule.span A ((s.image σ : Finset B) : Set B), v' b = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem t ht =>
      exact ⟨σ t, Submodule.subset_span (by simpa using ⟨t, ht, rfl⟩), hσ t ht⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨b', hb', rfl⟩ := hy
      exact ⟨b + b', Submodule.add_mem _ hb hb', map_add _ _ _⟩
    | smul r x _ hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hR r r.2
      refine ⟨a • b, Submodule.smul_mem _ a hb, ?_⟩
      rw [hsm, map_mul, hc, ha]
      rfl
  refine ⟨⟨s.image σ, ?_⟩⟩
  rw [eq_top_iff]
  intro b _
  obtain ⟨b', hb', e⟩ := key _ (hb b)
  rwa [← hv' e]

theorem inChart_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) {κ : Type} {x : κ → Ω} {c : κ}
    (hc : x c ≠ 0) : InChart ξ x c ⟨genPt ξ, specializes_rfl⟩ := by
  refine ⟨hc, fun c' => ?_⟩
  obtain ⟨g, hg'⟩ := hg.bij.2 (x c' / x c)
  refine ⟨g, ?_⟩
  simp only [genMap]
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact hg'

theorem mem_chRing_iff {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω} (M : PModel o x) {c : κ}
    (hc : x c ≠ 0) {U : M.X.Opens} (hU : ∀ q : M.X, q ∈ U ↔ ∃ h : genPt M.ξ ⤳ q, InChart M.ξ x c ⟨q, h⟩)
    (h : genPt M.ξ ∈ U) (a : Ω) : a ∈ chRing o x c ↔ ∃ s : Γ(M.X, U), secVal M.ξ U h s = a := by
  rw [chRing, M.tie.ring c hc a]
  constructor
  · intro H
    refine exists_secVal M.all M.tie.gen.inj U h a fun q hq => ?_
    obtain ⟨h', hi⟩ := (hU q).1 hq
    exact H _ hi
  · rintro ⟨s, rfl⟩ p hp
    have hq : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
    exact ⟨_, genMap_germ M.ξ h hq p.2 s⟩

theorem chart_step {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (M : PModel o x) {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] {κ' : Type}
    {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ') (hd : Dominates M'.ξ M.ξ f (algebraMap Ω Ω'))
    {c : κ} (hc : x c ≠ 0) (hne : y (e c) ≠ 0)
    (hpre : ∀ p' : Cpt M'.ξ, InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p)
    (hfin : ∃ s : Finset Ω', ∀ a : Ω', a ∈ chRing o y (e c) ↔
      a ∈ Submodule.span (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (s : Set Ω'))
    {U : M.X.Opens} (hUm : ∀ q : M.X, q ∈ U ↔ ∃ h : genPt M.ξ ⤳ q, InChart M.ξ x c ⟨q, h⟩) :
    IsAffineOpen (f ⁻¹ᵁ U) ∧ (f.app U).hom.Finite := by
  obtain ⟨U', hU'a, hU'm⟩ := M'.tie.affine (e c) hne
  have hV : ∀ q : M'.X, q ∈ f ⁻¹ᵁ U ↔ ∃ h : genPt M'.ξ ⤳ q, InChart M'.ξ y (e c) ⟨q, h⟩ := by
    intro q
    have hq := hpre ⟨q, M'.all q⟩
    constructor
    · intro hfq
      obtain ⟨h, hi⟩ := (hUm (f q)).1 hfq
      exact ⟨M'.all q, hq.2 ⟨⟨f q, h⟩, rfl, hi⟩⟩
    · rintro ⟨h₀, hi⟩
      obtain ⟨⟨p, h⟩, hp, hpi⟩ := hq.1 hi
      change p = f q at hp
      subst hp
      exact (hUm _).2 ⟨h, hpi⟩
  have hEq : f ⁻¹ᵁ U = U' := Opens.ext (Set.ext fun q => (hV q).trans (hU'm q).symm)
  refine ⟨hEq ▸ hU'a, ?_⟩
  have hg : genPt M.ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt M.tie.gen hc⟩
  have hg' : genPt M'.ξ ∈ f ⁻¹ᵁ U := (hV _).2 ⟨specializes_rfl, inChart_genPt M'.tie.gen hne⟩
  obtain ⟨s, hs⟩ := hfin
  have hmap : chRing o (fun k => algebraMap Ω Ω' (x k)) c = (chRing o x c).map (IsScalarTower.toAlgHom o Ω Ω') := by
    simp only [chRing]
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    funext j
    simp
  refine finite_of_values (o := o) (f.app U).hom (secVal M.ξ U hg) (secVal M'.ξ _ hg') (algebraMap Ω Ω')
    (secVal_injective M'.all M'.tie.gen.inj _ hg') (secVal_app hd U hg hg')
    (chRing o (fun k => algebraMap Ω Ω' (x k)) c) ?_ s ?_ ?_
  · intro r hr
    rw [hmap] at hr
    obtain ⟨r₀, h₀, rfl⟩ := hr
    obtain ⟨a, ha⟩ := (mem_chRing_iff M hc hUm hg r₀).1 h₀
    exact ⟨a, by rw [ha]; rfl⟩
  · intro t ht
    exact (mem_chRing_iff M' hne hV hg' t).1 ((hs t).2 (Submodule.subset_span ht))
  · intro b
    exact (hs _).1 ((mem_chRing_iff M' hne hV hg' _).2 ⟨b, rfl⟩)

set_option backward.isDefEq.respectTransparency false in

theorem isFinite_of_charts {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω']
    {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ') :
    Dominates M'.ξ M.ξ f (algebraMap Ω Ω') → (∀ c, x c ≠ 0 → y (e c) ≠ 0) →
    (∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p) →
    (∀ c, x c ≠ 0 → ∃ s : Finset Ω', ∀ a : Ω', a ∈ chRing o y (e c) ↔
      a ∈ Submodule.span (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (s : Set Ω')) → IsFinite f := by
  intro hd hne hpre hfin
  choose U hUa hUm using fun c : {c // x c ≠ 0} => M.tie.affine c.1 c.2
  have hcov : ⨆ i, ((⟨U i, hUa i⟩ : M.X.affineOpens) : M.X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨c, hc⟩ := M.tie.cover ⟨q, M.all q⟩
    exact Opens.mem_iSup.2 ⟨⟨c, hc.1⟩, (hUm ⟨c, hc.1⟩ q).2 ⟨M.all q, hc⟩⟩
  refine (HasAffineProperty.iff_of_iSup_eq_top (P := @IsFinite) (fun i => ⟨U i, hUa i⟩) hcov).2 fun i => ?_
  obtain ⟨h1, h2⟩ := chart_step M M' f e hd i.2 (hne i.1 i.2) (hpre i.1 i.2) (hfin i.1 i.2) (hUm i)
  refine ⟨h1, ?_⟩
  dsimp only
  rw [morphismRestrict_appTop, CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_right_isIso]
  change (Scheme.Hom.app f ((U i).ι ''ᵁ ⊤)).hom.Finite
  rw [Scheme.Opens.ι_image_top]
  exact h2

end GlobalTheory.CompanionTheory.Ar.ChartFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RegSection

theorem section_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (s t : Γ(X, U))
    (e : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) =
      genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq t)) : s = t :=
  TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => h.inj ⟨q, hU q hq⟩ (e q hq)

theorem existsUnique_section : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → ∀ (U : X.Opens) (hU : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω), (U : Set X).Nonempty → (∀ q (hq : q ∈ U), a ∈ regAt ξ ⟨q, hU q hq⟩) → ∃! g : Γ(X, U), ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq g) = a := by
  intro X Ω _ ξ _ h U hU a _ ha
  have loc : ∀ x : U, ∃ (W : X.Opens) (_ : W ≤ U) (hx : x.1 ∈ W) (t : Γ(X, W)),
      genMap ξ ⟨x.1, hU x.1 x.2⟩ (X.presheaf.germ W x.1 hx t) = a := by
    intro x
    obtain ⟨g, hg⟩ := ha x.1 x.2
    obtain ⟨W, hx, t, rfl⟩ := X.presheaf.exists_germ_eq g
    refine ⟨W ⊓ U, inf_le_right, ⟨hx, x.2⟩, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
    exact (congrArg (genMap ξ ⟨x.1, hU x.1 x.2⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) x.1 ⟨hx, x.2⟩ t)).trans hg
  choose W hWU hx t ht using loc
  have val : ∀ (x : U) (y : X) (hy : y ∈ W x),
      genMap ξ ⟨y, hU y (hWU x hy)⟩ (X.presheaf.germ (W x) y hy (t x)) = a := fun x y hy =>
    (genMap_germ_eq_genMap_germ ξ (W x) ⟨y, hU y (hWU x hy)⟩ ⟨x.1, hU x.1 x.2⟩ hy (hx x) (t x)).trans (ht x)
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    apply h.inj ⟨y, hU y (hWU i hi)⟩
    exact (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i))).trans
      ((val i y hi).trans ((val j y hj).symm.trans
        (congrArg (genMap ξ ⟨y, hU y (hWU i hi)⟩) (TopCat.Presheaf.germ_res_apply X.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j))).symm))
  have hcov : U ≤ iSup W := fun y hy =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun i => homOfLE (hWU i)) hcov t compat
  have spec : ∀ q (hq : q ∈ U), genMap ξ ⟨q, hU q hq⟩ (X.presheaf.germ U q hq s) = a := by
    intro q hq
    have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hWU ⟨q, hq⟩)) q (hx ⟨q, hq⟩) s
    have e2 : (X.presheaf.map (homOfLE (hWU ⟨q, hq⟩)).op).hom s = t ⟨q, hq⟩ := hs ⟨q, hq⟩
    exact (congrArg (genMap ξ ⟨q, hU q hq⟩) e).symm.trans
      ((congrArg (fun z => genMap ξ ⟨q, hU q hq⟩ ((X.presheaf.germ (W ⟨q, hq⟩) q (hx ⟨q, hq⟩)).hom z)) e2).trans
        (ht ⟨q, hq⟩))
  exact ⟨s, spec, fun s' hs' => section_eq h U hU s' s fun q hq => (hs' q hq).trans (spec q hq).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RegSection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSchemeMapFromSpecialFibre
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.CompanionTheory.FinFlatModel

open IsLocalRing

section Model

variable {R : Type} [CommRing R] [IsLocalRing R]

noncomputable def quotEquiv : (R ⧸ maximalIdeal R ^ (0 + 1)) ≃+* ResidueField R :=
  Ideal.quotEquivOfEq (by simp)

noncomputable def specIso :
    Spec (CommRingCat.of (ResidueField R)) ≅
      Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))) where
  hom := Spec.map (CommRingCat.ofHom (quotEquiv (R := R)).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (quotEquiv (R := R)).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (quotEquiv (R := R)).toRingHom.comp (quotEquiv (R := R)).symm.toRingHom =
        RingHom.id _ := by
      ext x
      simp
    rw [this]
    exact Spec.map_id _
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (quotEquiv (R := R)).symm.toRingHom.comp (quotEquiv (R := R)).toRingHom =
        RingHom.id _ := by
      ext x
      simp
    rw [this]
    exact Spec.map_id _

theorem specIso_hom_thick :
    (specIso (R := R)).hom ≫ thick R (maximalIdeal R) 0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) := by
  simp only [specIso, thick]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem isPullback_fibre {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫
        i.inv)
      (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        (specIso (R := R)).hom)
      X.hom (thick R (maximalIdeal R) 0) := by
  refine IsPullback.of_iso
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R (ResidueField R) P)).flip
    (Iso.refl _) i.symm specIso (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [hi]
  · simp [specIso_hom_thick]

theorem exists_model (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    ∃ (P : Type) (_ : CommRing P) (_ : Algebra R P) (i : X.left ≅ Spec (CommRingCat.of P)),
      X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
  obtain ⟨g, hg⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  let _ : Algebra R Γ(X.left, ⊤) := g.hom.toAlgebra
  refine ⟨Γ(X.left, ⊤), inferInstance, g.hom.toAlgebra, X.left.isoSpec, ?_⟩
  have : CommRingCat.ofHom (algebraMap R Γ(X.left, ⊤)) = g := rfl
  erw [this, hg]
  simp

theorem map_left_eq {P Q : Type} [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (φ : Q →ₐ[R] P)
    (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)))
    (hj : Y.hom = j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)))
    (hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv) :
    ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left =
      (isPullback_fibre X i hi).isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
        (isPullback_fibre Y j hj).isoPullback.hom := by
  have e1 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := Q)).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := P)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have e2 : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R (ResidueField R)) φ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := ResidueField R) (B := Q))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := ResidueField R) (B := P))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp
  apply pullback.hom_ext
  · have h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫
        pullback.fst Y.hom (thick R (maximalIdeal R) 0) =
        pullback.fst X.hom (thick R (maximalIdeal R) 0) ≫ f.left := pullback.lift_fst _ _ _
    rw [h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst,
      reassoc_of% e1, ← (isPullback_fibre X i hi).isoPullback_inv_fst, hf]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · have h0 : ((Over.pullback (thick R (maximalIdeal R) 0)).map f).left ≫
        pullback.snd Y.hom (thick R (maximalIdeal R) 0) =
        pullback.snd X.hom (thick R (maximalIdeal R) 0) := pullback.lift_snd _ _ _
    rw [h0, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd,
      reassoc_of% e2, ← (isPullback_fibre X i hi).isoPullback_inv_snd]

theorem finite_of_model {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    Module.Finite R P := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
  have h' : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
    rw [h]
    infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h')

theorem flat_of_model {P : Type} [CommRing P] [Algebra R P]
    (X : Over (Spec (CommRingCat.of R))) (hX : Flat X.hom)
    (i : X.left ≅ Spec (CommRingCat.of P))
    (hi : X.hom = i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    Module.Flat R P := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
  have h' : Flat (Spec.map (CommRingCat.ofHom (algebraMap R P))) := by
    rw [h]
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h')

end Model

theorem exists_algHom_model :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y), ∃ (P Q : Type) (_ : CommRing P) (_ : CommRing Q) (_ : Algebra R P) (_ : Algebra R Q) (φ : Q →ₐ[R] P) (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q)) (i₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj X).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] P))) (j₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj Y).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] Q))), Module.Finite R P ∧ Module.Finite R Q ∧ (Flat X.hom → Module.Flat R P) ∧ f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv ∧ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map f).left = i₀.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) ≫ j₀.inv := by
  intro R _ _ X Y _ _ f
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom
  obtain ⟨P, _, _, i, hi⟩ := exists_model X
  obtain ⟨Q, _, _, j, hj⟩ := exists_model Y
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.inv ≫ f.left ≫ j.hom)
  have hcomm : CommRingCat.ofHom (algebraMap R Q) ≫ ψ = CommRingCat.ofHom (algebraMap R P) := by
    apply Spec.map_injective
    have hw : f.left ≫ Y.hom = X.hom := Over.w f
    rw [Spec.map_comp, hψ]
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap R P)) = i.inv ≫ X.hom := by simp [hi]
    have h2 : j.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)) = Y.hom := hj.symm
    rw [h1, ← hw]
    simp only [Category.assoc, h2]
  let φ : Q →ₐ[R] P :=
    { ψ.hom with
      commutes' := fun r => by
        have := congrArg (fun g => g.hom r) hcomm
        simpa using this }
  have hφ : CommRingCat.ofHom φ.toRingHom = ψ := rfl
  have hf : f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv := by
    rw [hφ, hψ]
    simp
  refine ⟨P, Q, inferInstance, inferInstance, inferInstance, inferInstance, φ, i, j,
    (isPullback_fibre X i hi).isoPullback.symm, (isPullback_fibre Y j hj).isoPullback.symm,
    finite_of_model X i hi, finite_of_model Y j hj, fun h => flat_of_model X h i hi, hf, ?_⟩
  exact map_left_eq f φ i j hi hj hf

end GlobalTheory.CompanionTheory.FinFlatModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeLocalizationStatement
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_lattice_localization : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → ∀ v, locAt v (glued T) = locAt v (frame (T v)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodProjExistsStatementHolds
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem goodProjExistsStatement_holds : ReciprocityTheory.ChartRestriction.G.Geo.GoodProjExistsStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists

end GlobalTheory.CompanionTheory.Ar.Link
end

