import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0089

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtIffOfSpecializes
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem ringHom_eq_of_spMap {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B} (h : spMap a = spMap b) : a = b := by
  have h1 := Spec.map_injective h
  have h2 := congrArg CommRingCat.Hom.hom h1
  simpa using h2

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (s : Sp B ⟶ Sp A) : ∃ a : A →+* B, s = spMap a := ⟨(Spec.preimage s).hom, by simp [spMap]⟩

private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have key : ∀ (z : T ⟶ (Over.pullback f).obj G) (z₀ : (Over.map f).obj T ⟶ G),
      z₀.left = z.left ≫ pullback.fst G.hom f → z = (Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map z₀ := by
    intro z z₀ hz
    ext
    apply pullback.hom_ext
    · simp only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp, hz, Over.homMk_left]
      erw [pullback.lift_fst_assoc, Category.id_comp]
    · simp only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Over.homMk_left]
      erw [pullback.lift_snd]
      exact Over.w z
  rw [key x x₀ hx, key y y₀ hy, ← MonObj.comp_mul, ← Functor.map_mul]
  simp
  erw [pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]

theorem exists_common_pullback {Y : Scheme.{0}} {G : Over Y} [GrpObj G] {κ κ' : Type} [Field κ] [Field κ'] {s : Sp κ ⟶ Y}
    {s' : Sp κ' ⟶ Y} (hs : s (closedPoint κ) = s' (closedPoint κ')) {G₀ : Over (Sp κ)} [GrpObj G₀] {φ : G₀.left ⟶ G.left}
    {G₀' : Over (Sp κ')} [GrpObj G₀'] {φ' : G₀'.left ⟶ G.left} (hφ : IsGrpPullback G₀ G s φ)
    (hφ' : IsGrpPullback G₀' G s' φ') :
    ∃ (K : Type) (_ : Field K) (b : κ →+* K) (b' : κ' →+* K) (GK : Over (Sp K)) (_ : GrpObj GK) (ψ : GK.left ⟶ G₀.left)
      (ψ' : GK.left ⟶ G₀'.left), spMap b ≫ s = spMap b' ≫ s' ∧ IsGrpPullback GK G₀ (spMap b) ψ ∧
      IsGrpPullback GK G₀' (spMap b') ψ' ∧ ψ ≫ φ = ψ' ≫ φ' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := s') _ _ hs
  obtain ⟨K, _, ⟨p⟩⟩ : ∃ (K : Type) (_ : Field K), Nonempty (Sp K ⟶ pullback s s') :=
    ⟨_, inferInstance, ⟨(pullback s s').fromSpecResidueField z⟩⟩
  obtain ⟨b, hb⟩ := exists_spMap (p ≫ pullback.fst s s')
  obtain ⟨b', hb'⟩ := exists_spMap (p ≫ pullback.snd s s')
  have e : spMap b ≫ s = spMap b' ≫ s' := by
    rw [← hb, ← hb', Category.assoc, Category.assoc, pullback.condition]
  have hψ := isGrpPullback_pullback_fst (spMap b) G₀
  set ψ := pullback.fst G₀.hom (spMap b)
  set GK := (Over.pullback (spMap b)).obj G₀
  have w0 : (ψ ≫ φ) ≫ G.hom = (GK.hom ≫ spMap b') ≫ s' := by
    simp only [Category.assoc]
    rw [hφ.1.w, ← Category.assoc ψ, hψ.1.w, Category.assoc, e]
  refine ⟨K, inferInstance, b, b', GK, inferInstance, ψ, hφ'.1.lift (ψ ≫ φ) (GK.hom ≫ spMap b') w0, e, hψ, ?_,
    (hφ'.1.lift_fst _ _ _).symm⟩
  have n := hψ.comp hφ
  rw [e, ← hφ'.1.lift_fst (ψ ≫ φ) (GK.hom ≫ spMap b') w0] at n
  exact IsGrpPullback.cancel hφ' n (hφ'.1.lift_snd _ _ _)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {G : Over M.Z} [GrpObj G]
  {I T : Type} {f : I → (G ⟶ G)} {gγ : T → (Over.mk M.pt ⟶ G)} {ζ : oˣ} {L : ℕ}

theorem RkAt.unique {w : M.Z} {r r' : ℕ} (h : RkAt G w r) (h' : RkAt G w r') : r = r' := by
  obtain ⟨X, _, _, _, κ, _, s, G₀, _, φ, tι, hs, hφ, ht, rfl⟩ := h
  obtain ⟨X', _, _, _, κ', _, s', G₀', _, φ', tι', hs', hφ', ht', rfl⟩ := h'
  obtain ⟨K, _, b, b', GK, _, ψ, ψ', -, hψ, hψ', -⟩ := exists_common_pullback (hs.trans hs'.symm) hφ hφ'
  obtain ⟨e, -⟩ := IsTorPart.exists_equiv (ht.pull hψ) (ht'.pull hψ')
  exact e.toIntLinearEquiv.finrank_eq

theorem LatAt.transfer {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : I → X →+ X}
    {c : T → X →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w) {κ' : Type} [Field κ'] {s' : Sp κ' ⟶ M.Z}
    (hs' : s' (closedPoint κ') = w) {a' : o →+* κ'} (ha' : s' ≫ M.s = spMap a') {G₀' : Over (Sp κ')} [GrpObj G₀']
    {φ' : G₀'.left ⟶ G.left} (hφ' : IsGrpPullback G₀' G s' φ') {X' : Type} [AddCommGroup X'] [Module.Free ℤ X']
    [Module.Finite ℤ X'] {t' : splitTorus (Sp κ') X' ⟶ G₀'} (ht' : IsTorPart t') :
    ∃ (e : X' ≃+ X) (K : Type) (_ : Field K) (b : κ' →+* K) (GK : Over (Sp K)) (_ : GrpObj GK) (ψ : GK.left ⟶ G₀'.left)
      (hψ : IsGrpPullback GK G₀' (spMap b) ψ),
      Compat f gγ ζ L m c (spMap b ≫ s') (b.comp a') (ψ ≫ φ') (torusMap _ e.toAddMonoidHom ≫ pullTorus hψ t') := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hc⟩ := h
  obtain ⟨K, _, b, b', GK, _, ψ, ψ', e1, hψ, hψ', e2⟩ := exists_common_pullback (hs.trans hs'.symm) hφ hφ'
  obtain ⟨e, he⟩ := IsTorPart.exists_equiv (ht'.pull hψ') (ht.pull hψ)
  have hab : b.comp a = b'.comp a' := by
    apply ringHom_eq_of_spMap
    rw [← spMap_comp', ← spMap_comp', ← ha, ← ha', reassoc_of% e1]
  refine ⟨e, K, inferInstance, b', GK, inferInstance, ψ', hψ', ?_⟩
  have hc2 := hc.pull b hψ
  rw [he, e1, hab, e2] at hc2
  exact hc2

theorem Compat.unique [IsSeparated G.hom] (hL : 0 < L) {X : Type} [AddCommGroup X] {m m' : I → X →+ X}
    {c c' : T → X →+ ZMod L} {K : Type} [Field K] {s : Sp K ⟶ M.Z} {a : o →+* K} (hζ : IsPrimitiveRoot (a ζ) L)
    {G₀ : Over (Sp K)} [GrpObj G₀] {φ : G₀.left ⟶ G.left} (hφ : IsGrpPullback G₀ G s φ) {t : splitTorus (Sp K) X ⟶ G₀}
    (ht : IsTorPart t) (h : Compat f gγ ζ L m c s a φ t) (h' : Compat f gγ ζ L m' c' s a φ t) : m = m' ∧ c = c' := by
  obtain ⟨hm, hc⟩ := h
  obtain ⟨hm', hc'⟩ := h'
  constructor
  · funext e
    apply ht.cancel
    apply hom_ext_of_pullback hφ
    rw [← hm e, ← hm' e]
  · funext tt
    obtain ⟨z, hz, hv⟩ := hc tt
    obtain ⟨z', hz', hv'⟩ := hc' tt
    have hzz : z = z' := by
      have := ht.mono
      apply (cancel_mono t).1
      apply hom_ext_of_pullback hφ
      exact ValAt.unique hv hv'
    subst hzz
    ext χ
    have h3 := congrArg Units.val (GlobalTheory.ZH.TorusPerp.unitOn_injective ((hz χ).symm.trans (hz' χ)))
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h3
    haveI : NeZero L := ⟨hL.ne'⟩
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

theorem LatAt.unique [IsSeparated G.hom] (hL : 0 < L) (hζ : ∀ (κ : Type) [Field κ] (a : o →+* κ), IsPrimitiveRoot (a ζ) L)
    {X X' : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X']
    [Module.Finite ℤ X'] {m : I → X →+ X} {c : T → X →+ ZMod L} {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {w : M.Z}
    (h : LatAt f gγ ζ L m c w) (h' : LatAt f gγ ζ L m' c' w) :
    ∃ θ : X ≃+ X', (∀ e x, θ (m e x) = m' e (θ x)) ∧ ∀ t x, c' t (θ x) = c t x := by
  obtain ⟨κ', _, s', a', G₀', _, φ', tι', hs', ha', hφ', ht', hc'⟩ := h'
  obtain ⟨e, K, _, b, GK, _, ψ, hψ, hc⟩ := h.transfer hs' ha' hφ' ht'
  have hc2 := (hc'.pull b hψ).equiv e (m' := fun i => (e : X' →+ X).comp ((m' i).comp (e.symm : X →+ X')))
    (c' := fun t => (c' t).comp (e.symm : X →+ X')) (fun i x => by simp) (fun t x => by simp)
  obtain ⟨h1, h2⟩ := Compat.unique hL (hζ K (b.comp a')) (hψ.comp hφ') ((ht'.pull hψ).equiv e) hc hc2
  subst h1 h2
  refine ⟨e.symm, fun i x => ?_, fun t x => ?_⟩ <;> simp

theorem LatAt.equiv {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {m : I → X →+ X} {c : T → X →+ ZMod L}
    {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w)
    (e : X ≃+ X') (hm : ∀ i x, e (m i x) = m' i (e x)) (hc : ∀ t x, c' t (e x) = c t x) : LatAt f gγ ζ L m' c' w := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hcc⟩ := h
  exact ⟨κ, _, s, a, G₀, _, φ, _, hs, ha, hφ, ht.equiv e, hcc.equiv e hm hc⟩

private theorem ratModel_isLocallyNoetherian {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o]
    (M : RatModel o Ω) : IsLocallyNoetherian M.Z := by
  have := M.lft
  constructor
  intro U
  have h1 := HasRingHomProperty.appLE @LocallyOfFiniteType M.s this ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  have : IsNoetherianRing Γ(Sp o, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  letI := (M.s.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp o, ⊤) Γ(M.Z, U.1) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp o, ⊤) Γ(M.Z, U.1)

theorem latAt_iff_of_specializes [IsNoetherianRing o] [IsCommMonObj G] (hG : IsSemiAbelian G) (hL : 0 < L) (hζ : ζ ^ L = 1)
    (hu : IsUnit (L : o)) (hf : ∀ e, IsMonHom (f e)) (hγ : ∀ t, gγ t ^ L = 1) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) {w w' : M.Z} (hw : w ⤳ w') {r : ℕ}
    (hr : RkAt G w r) (hr' : RkAt G w' r) (hext : ∀ t, ExtNear (gγ t) w') :
    LatAt f gγ ζ L m c w ↔ LatAt f gγ ζ L m c w' := by
  by_cases hww : w = w'
  · subst hww
    exact Iff.rfl
  have := ratModel_isLocallyNoetherian M
  obtain ⟨V, _, _, _, ξ, G₁, _, _, φ₁, X₁, _, _, _, j, GK, _, ψ, hψ, hξ', hξ, hφ₁, hj, hjt⟩ :=
    GlobalTheory.T.exists_trait_spreading_torusPart_of_specialisation M.Z G hG w w' hw hww
  have := hj
  obtain ⟨a, ha⟩ := exists_spMap (ξ ≫ M.s)
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ξ G G₁ φ₁ hφ₁ hG
  have hgen : IsGrpPullback GK G (spMap (algebraMap V (FractionRing V)) ≫ ξ) (ψ ≫ φ₁) := hψ.comp hφ₁
  have hrX : r = Module.finrank ℤ X₁ :=
    RkAt.unique hr ⟨X₁, _, inferInstance, inferInstance, FractionRing V, inferInstance, _, GK, inferInstance, _, _, hξ,
      hgen, hjt, rfl⟩
  obtain ⟨X₀, _, _, _, κ₀, _, s₀, G₀, _, φ₀, t₀, hs₀, hφ₀, ht₀, hrk₀⟩ := hr'
  have hGc := isGrpPullback_pullback_fst (spMap (IsLocalRing.residue V)) G₁
  have hcl : (spMap (IsLocalRing.residue V) ≫ ξ) (closedPoint (IsLocalRing.ResidueField V)) = w' :=
    (congrArg (fun x => ξ x) (GtDescent.spMap_cpt (IsLocalRing.residue V))).trans hξ'
  obtain ⟨K, _, b₀, b₁, GK', _, ψ₀, ψ₁, -, hψ₀, hψ₁, -⟩ := exists_common_pullback (hs₀.trans hcl.symm) hφ₀ (hGc.comp hφ₁)
  have hψc : IsGrpPullback GK' G₁ (spMap (b₁.comp (IsLocalRing.residue V)))
      (ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V))) := by
    rw [← spMap_comp']
    exact hψ₁.comp hGc
  have ht0 : IsTorPart (pullTorus hψc j) :=
    GlobalTheory.T.splitTorusPart_generic_fibre_closed_fibre_dvr V G₁ hG₁ X₁ j hj GK ψ hψ hjt K (b₁.comp (IsLocalRing.residue V)) inferInstance GK' _ hψc X₀ _
      (ht₀.pull hψ₀) (hrk₀.trans hrX)
  have hsc : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) (closedPoint K) = w' :=
    (congrArg (fun x => ξ x) (GtDescent.spMap_cpt (b₁.comp (IsLocalRing.residue V)))).trans hξ'
  have ha_gen : (spMap (algebraMap V (FractionRing V)) ≫ ξ) ≫ M.s = spMap ((algebraMap V (FractionRing V)).comp a) := by
    rw [Category.assoc, ha, spMap_comp']
  have ha_cl : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) ≫ M.s = spMap ((b₁.comp (IsLocalRing.residue V)).comp a) := by
    rw [Category.assoc, ha, spMap_comp']
  have hextV : ∀ t, ExtNear (gγ t) (ξ (closedPoint V)) := by
    rw [hξ']
    exact hext
  constructor
  · intro h
    obtain ⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩ := h.transfer hξ ha_gen hgen hjt
    have hψ₂' : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (algebraMap V (FractionRing V)))) (ψ₂ ≫ ψ) := by
      rw [← spMap_comp']
      exact hψ₂.comp hψ
    have hinj : Function.Injective (b₂.comp (algebraMap V (FractionRing V))) :=
      b₂.injective.comp (IsFractionRing.injective V (FractionRing V))
    have hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j) := by
      refine GlobalTheory.T.torusCompat_of_compat_over_field o Ω M G hG I T f gγ ζ L hL hζ X m c V ξ a G₁ φ₁ hφ₁ _ hextV K₂ _ hinj GK₂ _ hψ₂' ?_
      rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψ hψ₂' (spMap_comp' _ _).symm rfl, ← spMap_comp']
      simpa only [Category.assoc, RingHom.comp_assoc] using hc
    have hc2 := hcV.pull (b₁.comp (IsLocalRing.residue V)) hψc
    rw [pullTorus_torusMap_comp] at hc2
    exact ⟨K, _, _, _, GK', _, _, _, hsc, ha_cl, hψc.comp hφ₁, ht0.equiv e, hc2⟩
  · intro h
    obtain ⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩ := h.transfer hsc ha_cl (hψc.comp hφ₁) ht0
    have hψ₃ : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (b₁.comp (IsLocalRing.residue V))))
        (ψ₂ ≫ ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V))) := by
      rw [← spMap_comp']
      exact hψ₂.comp hψc
    have hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j) := by
      refine GlobalTheory.T.torusCompat_of_compat_closedPoint o Ω M G hG I T f gγ ζ L hL hζ hu hf hγ X m c V ξ a G₁ φ₁ hφ₁ _ inferInstance hextV GK ψ hψ
        ?_ K₂ _ inferInstance GK₂ _ hψ₃ ?_ ?_
      · rw [pullTorus_torusMap_comp]
        exact hjt.equiv e
      · rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl]
        exact (ht0.pull hψ₂).equiv e
      · rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl, ← spMap_comp']
        simpa only [Category.assoc, RingHom.comp_assoc] using hc
    have hc3 := hcV.pull (algebraMap V (FractionRing V)) hψ
    rw [pullTorus_torusMap_comp] at hc3
    exact ⟨FractionRing V, _, _, _, GK, _, _, _, hξ, ha_gen, hgen, hjt.equiv e, hc3⟩

end GlobalTheory.Poinc.FibLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMultiplicationStable
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TorusRM

namespace GlobalTheory.TorusRM

open GlobalTheory.CechPic

theorem exists_obj_of_polarised_torus : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (𝔠 : FracId F) (r : Fin (Module.finrank ℚ F) → ℝ) (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)),
    (∀ i, 0 < r i) → DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin (Module.finrank ℚ F) → ℂ)) = ⊤ →
    (∀ (a : 𝓞 F), ∀ w ∈ Λ, (fun i ↦ (e i (a : F) : ℂ) * w i) ∈ Λ) →
    (∀ c ∈ 𝔠.elt, ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e i c * r i : ℝ) : ℂ) * l i * starRingEnd ℂ (l' i)).im = n) →
    (∀ w : Fin (Module.finrank ℚ F) → ℂ, (∀ c ∈ 𝔠.elt, ∀ l ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e i c * r i : ℝ) : ℂ) * w i * starRingEnd ℂ (l i)).im = n) → w ∈ Λ) →
    ∀ c : 𝔠.elt, IsTotPos (c : F) →
    ∃ (X : Obj F 𝔠 (Sp ℂ)) (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)),
      (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧
      (∀ (a : 𝓞 F) w, u.ex (fun i ↦ (e i (a : F) : ℂ) * w i) = u.ex w ≫ X.rm.act a) ∧
      ∃ χ, u.IsAH (Matrix.diagonal fun i ↦ ((2 * (e i (c : F) * r i) : ℝ) : ℂ)) χ := by
  intro F _ _ _ e 𝔠 r Λ hr hdisc hfull hstab hint hdual c hc
  let Hc : F → Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ :=
    fun x ↦ Matrix.diagonal fun i ↦ ((e i x * r i : ℝ) : ℂ)
  have form : ∀ x (z w : Fin (Module.finrank ℚ F) → ℂ),
      z ⬝ᵥ (Hc x).mulVec (star w) = ∑ i, ((e i x * r i : ℝ) : ℂ) * z i * starRingEnd ℂ (w i) := by
    intro x z w
    simp only [Hc, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.star_def]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have herm : ∀ x, (Hc x).IsHermitian := fun x ↦ by
    simp only [Hc, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  have pos : ∀ x : F, IsTotPos x → ∀ z : Fin (Module.finrank ℚ F) → ℂ, z ≠ 0 →
      0 < (z ⬝ᵥ (Hc x).mulVec (star z)).re := by
    intro x hx z hz
    rw [form, Complex.re_sum]
    have h1 : ∀ i, (((e i x * r i : ℝ) : ℂ) * z i * starRingEnd ℂ (z i)).re = (e i x * r i) * Complex.normSq (z i) := by
      intro i
      rw [_root_.mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp_rw [h1]
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    exact Finset.sum_pos' (fun i _ ↦ mul_nonneg (mul_pos (hx _) (hr i)).le (Complex.normSq_nonneg _))
      ⟨j, Finset.mem_univ _, mul_pos (mul_pos (hx _) (hr j)) (Complex.normSq_pos.2 hj)⟩
  have integ : ∀ x ∈ 𝔠.elt, ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ (Hc x).mulVec (star l')).im = n :=
    fun x hx l hl l' hl' ↦ by rw [form]; exact hint x hx l hl l' hl'
  obtain ⟨A, _, ab, dim, L₀, u₀, χ₀, hL₀, hΛ₀, hAH₀⟩ :=
    GlobalTheory.T.riemann_theorem_nonprincipal_polarised_torus _ Λ (Hc c) hdisc hfull (herm c) (pos c hc) (integ c c.2)
  haveI := ab.comm
  have hproj : IsProjOver A.hom :=
    GlobalTheory.ProjSpace.isProjOver_of_relAmple (GlobalTheory.T.rel_ample_of_appell_humbert _ A ab L₀ u₀ (Hc c) χ₀ hL₀ hAH₀)
  let ρ : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ) :=
    (Algebra.lmul ℂ (Fin (Module.finrank ℚ F) → ℂ)).toRingHom.comp
      (Pi.ringHom fun i ↦ (Complex.ofRealHom.comp (e i)).comp (algebraMap (𝓞 F) F))
  have hρ : ∀ a w, ρ a w = fun i ↦ (e i (a : F) : ℂ) * w i := fun a w ↦ rfl
  obtain ⟨rm, hrm⟩ := GlobalTheory.TorusAction.exists_oAct_of_map_lattice _ A ab L₀ u₀ (𝓞 F) ρ fun a z hz ↦ by
    rw [hΛ₀] at hz ⊢
    rw [hρ]
    exact hstab a z hz
  have hb := fun x : 𝔠.elt ↦ GlobalTheory.T.exists_appell_humbert_factor _ A ab L₀ u₀ (Hc c) χ₀ hL₀ hAH₀ (Hc x) (herm x)
    (fun l hl l' hl' ↦ integ x x.2 l ((hΛ₀ l).1 hl) l' ((hΛ₀ l').1 hl'))
  choose M u χ hM hex hf using hb
  have memΛ : ∀ x z, z ∈ (u x).Λ ↔ z ∈ Λ := fun x z ↦ by
    rw [← (u x).ker, hex x, u₀.ker, hΛ₀]
  have hΘ : ∀ x, ∃ t : LB.Gen (Theta A (M x)), t.IsGen :=
    fun x ↦ exists_gen_theta_of_isAbelianScheme ℂ A ab (M x) (hM x)
  have hlam : ∀ x, (abelian₂ A (M x)).IsLB := fun x ↦ LB.isLB_linComb (hM x) _ _
  obtain ⟨u', χ', hex', hf'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag _ A ab (M c) (u c) (Hc c) (χ c) (hM c) (hf c)
  have hsmul : ∀ (a : 𝓞 F) (x : 𝔠.elt),
      LBIso (abelian₂ A (M (a • x))) ((abelian₂ A (M x)).pull (lift (fst A A) (snd A A ≫ rm.act a)).left) :=
    fun a x ↦ GlobalTheory.T.appell_humbert_hom_compatible _ A ab hproj (M x) (M (a • x)) (u x) (u (a • x)) (Hc x) (Hc (a • x))
        (χ x) (χ _) (rm.act a) (ρ a) (hM x) (hM _) ((hex _).trans (hex x).symm) (hf x) (hf _) (rm.hom a)
        (fun z ↦ by rw [hex x]; exact hrm a z)
        (fun z w ↦ by
          rw [form, form]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hcoe : algebraMap (𝓞 F) F a = (a : F) := rfl
          simp only [hρ, Submodule.coe_smul, Algebra.smul_def, hcoe, map_mul, Complex.ofReal_mul, Complex.conj_ofReal]
          ring)
        (fun z w ↦ by
          rw [form, form, hρ, hρ]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [map_mul, Complex.conj_ofReal]
          ring)
  have hc0 : (c : F) ≠ 0 := fun h ↦ by
    have := hc (e ⟨0, Module.finrank_pos⟩)
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  have hact0 : rm.act 0 = 1 := by
    have h := rm.add 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hmul : ∀ x : 𝔠.elt, (x : F) ≠ 0 → ∃ a₀ : 𝓞 F, IsTotPos ((a₀ • x : 𝔠.elt) : F) := by
    intro x hx
    obtain ⟨k, hk, hint'⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x : F))).exists_integral_multiple
    refine ⟨⟨(k * k : ℤ) • (x : F), ?_⟩, fun τ ↦ ?_⟩
    · rw [mul_smul]
      exact hint'.smul k
    · have h1 : τ (x : F) ≠ 0 := (map_ne_zero τ).2 hx
      have h2 : (k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
      have h3 : τ (((k * k : ℤ) • (x : F)) * (x : F)) = ((k : ℝ) * τ x) ^ 2 := by
        simp only [zsmul_eq_mul, map_mul, map_intCast, Int.cast_mul]
        ring
      change 0 < τ (((k * k : ℤ) • (x : F)) * (x : F))
      rw [h3]
      positivity
  have hker : ∀ (x : 𝔠.elt) (T : Over (Sp ℂ)) (y : T ⟶ A),
      HasGen ((abelian₂ A (M x)).pull (lift (fst A T) (snd A T ≫ y)).left) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • x) → y ≫ rm.act a = 1 := by
    intro x T y hy a ha
    by_cases hx : (x : F) = 0
    · obtain ⟨b, hb⟩ := ha c
      have hb' : (a : F) * c = (b : F) * x := by
        have := congrArg (fun y : 𝔠.elt ↦ (y : F)) hb
        simpa [Submodule.coe_smul, Algebra.smul_def] using this
      rw [hx, mul_zero] at hb'
      have ha0 : a = 0 := by
        rcases mul_eq_zero.1 hb' with h | h
        · exact_mod_cast h
        · exact absurd h hc0
      rw [ha0, hact0, MonObj.comp_one]
    · obtain ⟨a₀, ha₀⟩ := hmul x hx
      refine GlobalTheory.T.line_bundle_endo_factor_pullback _ A ab (M x) (u x) (Hc x) (χ x) (rm.act a) (hM x) (hf x)
        (M (a₀ • x)) (u (a₀ • x)) (Hc (a₀ • x : 𝔠.elt)) (χ (a₀ • x)) (rm.act a₀) (hM _)
        (isAH_of_isFactorAH (hf _) (pos _ ha₀)) (rm.hom a₀) (hsmul a₀ x) (fun w hw ↦ ?_) T y hy
      rw [hex x, ← hrm a w, u₀.ker, hΛ₀]
      refine hdual _ fun d hd l hl ↦ ?_
      obtain ⟨b, hb⟩ := ha ⟨d, hd⟩
      have hb' : (a : F) * d = (b : F) * x := by
        have := congrArg (fun y : 𝔠.elt ↦ (y : F)) hb
        simpa [Submodule.coe_smul, Algebra.smul_def] using this
      obtain ⟨n, hn⟩ := hw (ρ b l) ((memΛ x _).2 (by rw [hρ]; exact hstab b l hl))
      refine ⟨n, ?_⟩
      rw [← hn, form]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi := congrArg (fun y ↦ ((e i y : ℝ) : ℂ)) hb'
      simp only [map_mul, Complex.ofReal_mul] at hi
      simp only [hρ, map_mul, Complex.ofReal_mul, Complex.conj_ofReal]
      linear_combination (↑(r i) * w i * (starRingEnd ℂ) (l i)) * hi
  let X : Obj F 𝔠 (Sp ℂ) :=
    { A := A
      ab := ab
      dim := dim
      rm := rm
      P := fun x ↦ abelian₂ A (M x)
      isLB := hlam
      rig₁ := fun x ↦ (cls_eq_zero_iff (pull_isLB (hlam x) _)).1 (by
        rw [Elliptic.cls_pull_lam (hM x), lam_one_left])
      rig₂ := fun x ↦ (cls_eq_zero_iff (pull_isLB (hlam x) _)).1 (by
        rw [Elliptic.cls_pull_lam (hM x), lam_one_right])
      symm := fun x ↦ (cls_eq_iff (hlam x) (pull_isLB (hlam x) _)).1 (by
        have h₁ : cls _ (hlam x) = lam (cls (M x) (hM x)) (fst A A) (snd A A) := cls_cube_two (hM x) _ _ (hlam x)
        rw [Elliptic.cls_pull_lam (hM x), h₁, lam_comm])
      add := fun x x' ↦ GlobalTheory.T.hermitian_forms_add_of_factor_product _ A ab hproj (M x) (M x') (M (x + x')) (u x) (u x') (u (x + x'))
        (Hc x) (Hc x') (Hc (x + x')) (χ x) (χ x') (χ (x + x')) (hM x) (hM x') (hM _)
        ((hex x').trans (hex x).symm) ((hex _).trans (hex x).symm) (hf x) (hf x') (hf _) (by
          simp only [Hc, Submodule.coe_add, map_add, Matrix.diagonal_add]
          congr 1
          funext i
          push_cast
          ring)
      smul := hsmul
      pos := fun x hx ↦ EighthPowerFactor.relAmple_diag_lam ab (hM x) (hΘ x)
        (GlobalTheory.T.rel_ample_of_appell_humbert _ A ab (M x) (u x) (Hc x) (χ x) (hM x) (isAH_of_isFactorAH (hf x) (pos x hx)))
      ker := hker }
  refine ⟨X, u', fun w ↦ ?_, fun a w ↦ ?_, χ', ?_⟩
  · rw [← u'.ker, hex', ← memΛ c, (u c).ker]
  · change u'.ex (ρ a w) = u'.ex w ≫ rm.act a
    rw [hex', hex c]
    exact hrm a w
  · have hm : (2 : ℂ) • Hc c = Matrix.diagonal fun i ↦ ((2 * (e i (c : F) * r i) : ℝ) : ℂ) := by
      simp only [Hc, ← Matrix.diagonal_smul]
      congr 1
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [← hm]
    refine isAH_of_isFactorAH hf' fun z hz ↦ ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have h2 : ∀ s : ℂ, ((2 : ℂ) * s).re = 2 * s.re := fun s ↦ by simp [Complex.mul_re]
    rw [h2]
    exact mul_pos two_pos (pos c hc z hz)

end GlobalTheory.TorusRM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LevelSecDesc

theorem levelSections_descend : ∀ (O : Type) [Ring O] (La : Type) [AddCommGroup La] [Module O La] (N : ℕ) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (act : OActN O A) (act₀ : OActN O A₀) (eta : La → (𝟙_ (Over X) ⟶ A)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsGrpPullback A A₀ π φ → GlobalTheory.ZM.IsGaloisCover Ga ν φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ a y, (eta y).left ≫ ν a = ρ a ≫ (eta y).left) → (∀ x y, eta (x + y) = eta x * eta y) → (∀ (c : O) x, eta (c • x) = eta x ≫ act.act c) → (∀ x, eta (N • x) = 1) → ∃ eta₀ : La → (𝟙_ (Over Y) ⟶ A₀), (∀ x y, eta₀ (x + y) = eta₀ x * eta₀ y) ∧ (∀ (c : O) x, eta₀ (c • x) = eta₀ x ≫ act₀.act c) ∧ (∀ x, eta₀ (N • x) = 1) ∧ ∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left := by
  intro O _ La _ _ N X Y π Ga _ ρ A _ _ A₀ _ _ φ ν act act₀ eta hπ gp hφ hact heq hadd hlin htor
  have := hπ.etale
  have := hπ.onto
  have : Epi π := Flat.epi_of_flat_of_surjective π
  have desc : ∀ y, ∃ e : 𝟙_ (Over Y) ⟶ A₀, (eta y).left ≫ φ = π ≫ e.left := fun y => by
    obtain ⟨g, hg, -⟩ := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hπ).1 A₀.left ((eta y).left ≫ φ) fun a => by
      rw [← Category.assoc, ← heq a y, Category.assoc, hφ.inv a]
    exact GlobalTheory.ObjDesc.exists_sec gp (eta y) g hg
  choose eta₀ heta using desc
  have hse : ∀ y, GlobalTheory.ObjPull.secPull gp (eta₀ y) = eta y := fun y => GlobalTheory.ObjDesc.secPull_eq gp (heta y)
  refine ⟨eta₀, fun x y => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_mul, hse, hse, hse, hadd]),
    fun c x => ?_, fun x => GlobalTheory.ObjDesc.secPull_injective gp (by rw [map_one, hse, htor]), heta⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi π, ← heta, hlin, Over.comp_left, Over.comp_left, Category.assoc, hact c, ← Category.assoc,
    heta, Category.assoc]

end GlobalTheory.LevelSecDesc

end
end

