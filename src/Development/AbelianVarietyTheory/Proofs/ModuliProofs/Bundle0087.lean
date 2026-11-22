import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_det_ne_zero_of_common_ker {K J : Type} [Field K] {g : ℕ} (φ : J → (Fin g → K) →ₗ[K] K)
    (h : ∀ w, (∀ i, φ i w = 0) → w = 0) :
    ∃ c : Fin g → J, (Matrix.of fun a b => φ (c b) (Pi.single a 1)).det ≠ 0 := by
  classical
  let ψ : J → Module.Dual K (Fin g → K) := φ
  have hspan : Submodule.span K (Set.range ψ) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hco : (Submodule.span K (Set.range ψ)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      exact (Submodule.mem_bot K).2 (h w fun i => hw _ (Submodule.subset_span ⟨i, rfl⟩))
    have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span K (Set.range ψ))
    rw [hco, finrank_bot, add_zero] at hdim
    rw [hdim, Subspace.dual_finrank_eq]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range ψ)
  let B : Module.Basis b K (Module.Dual K (Fin g → K)) :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hspan]))
  let D : Module.Basis (Fin g) K (Module.Dual K (Fin g → K)) := (Pi.basisFun K (Fin g)).dualBasis
  let e : b ≃ Fin g := B.indexEquiv D
  have hex : ∀ k : Fin g, ∃ j, ψ j = ((e.symm k : b) : Module.Dual K (Fin g → K)) := fun k => hbsub (e.symm k).2
  choose c hc using hex
  refine ⟨c, ?_⟩
  have hM : (Matrix.of fun a k => φ (c k) (Pi.single a 1)) = D.toMatrix (B.reindex e) := by
    ext a k
    rw [Matrix.of_apply]
    change ψ (c k) (Pi.single a 1) = _
    rw [hc k]
    simp only [Module.Basis.toMatrix_apply, D, Module.Basis.dualBasis_repr,
      Module.Basis.reindex_apply, B, Module.Basis.mk_apply, Pi.basisFun_apply]
  rw [hM]
  intro h0
  have hone := congrArg Matrix.det (D.toMatrix_mul_toMatrix_flip (B.reindex e))
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hone
  exact zero_ne_one hone

theorem top_le_preimage_finset_inf {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {κ : Type} (s : Finset κ) (W : κ → X.Opens)
    (h : ∀ i ∈ s, ⊤ ≤ x ⁻¹ᵁ W i) : ⊤ ≤ x ⁻¹ᵁ (s.inf W) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ p _
    simp
  | @insert a s ha ih =>
    intro h p hp
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self a s) hp, ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hp⟩

theorem fderiv_fn_resG {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    {X : Scheme.{0}} (m : A₀.left ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  have key : ∀ (y : Sp ℂ ⟶ X), ⊤ ≤ y ⁻¹ᵁ W' → valAt' y W' (resG X h f) = valAt' y W f := by
    intro y hy
    have hy2 : ⊤ ≤ y ⁻¹ᵁ W := hy.trans (fun q hq => h hq)
    unfold valAt'
    rw [dif_pos hy, dif_pos hy2]
    unfold valAt
    congr 1
    rw [← Scheme.Hom.map_appLE y hy (homOfLE h).op]
    rfl
  have hopen : IsOpen (dom u m W') := by
    exact (u.hol (m ⁻¹ᵁ W') 0).1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hopen.mem_nhds hz] with z' hz'
  exact key _ hz'

theorem exists_fibre_coords : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z, ∃ (W : X.Opens) (t : Fin P₀.g → Γ(X, W)), z ∈ dom u m W ∧ (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)).det ≠ 0 := by
  intro P₀ u Hm χ hG R _ x₀ X p m hsm hpb z
  let J : Type := {Wf : (W : X.Opens) × Γ(X, W) // z ∈ dom u m Wf.1}
  let φ : J → (Fin P₀.g → ℂ) →ₗ[ℂ] ℂ := fun j => (fderiv ℂ (fn u m j.1.1 j.1.2) z).toLinearMap
  have hker : ∀ w, (∀ j, φ j w = 0) → w = 0 := by
    intro w hw
    have hδ : PtDer ((u.ex z).left ≫ m) (fun _ _ => (0 : ℂ)) :=
      ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
    obtain ⟨w₀, _, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hsm hpb z (fun _ _ => 0) hδ (fun _ => rfl)
    have e1 : w = w₀ := huniq w (fun W f hzW => (hw ⟨⟨W, f⟩, hzW⟩).symm)
    have e2 : (0 : Fin P₀.g → ℂ) = w₀ := huniq 0 (fun W f _ => (ContinuousLinearMap.map_zero _).symm)
    exact e1.trans e2.symm
  obtain ⟨c, hc⟩ := exists_det_ne_zero_of_common_ker φ hker
  have hzW : z ∈ dom u m (Finset.univ.inf fun b => (c b).1.1) :=
    top_le_preimage_finset_inf ((u.ex z).left ≫ m) Finset.univ (fun b => (c b).1.1) (fun b _ => (c b).2)
  refine ⟨Finset.univ.inf fun b => (c b).1.1,
    fun b => resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2, hzW, ?_⟩
  have hE : (Matrix.of fun a b => fderiv ℂ (fn u m (Finset.univ.inf fun b => (c b).1.1)
      (resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2)) z (Pi.single a 1)) =
      Matrix.of fun a b => φ (c b) (Pi.single a 1) := by
    ext a b
    simp only [Matrix.of_apply]
    rw [fderiv_fn_resG u m (Finset.inf_le (Finset.mem_univ b)) (c b).1.2 hzW]
    rfl
  rw [hE]
  exact hc

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSchemeLatticeTorsionHomPrimitiveRoot
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsRootParam

open Polynomial in

abbrev CycRing (n : ℕ) : Type := AdjoinRoot (cyclotomic n ℤ)

open Polynomial in
theorem root_pow (n : ℕ) : AdjoinRoot.root (cyclotomic n ℤ) ^ n = 1 := by
  have h := (AdjoinRoot.mk_eq_zero (f := cyclotomic n ℤ)).mpr (cyclotomic.dvd_X_pow_sub_one n ℤ)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact sub_eq_zero.mp h

open Polynomial in

def cycUnit {n : ℕ} (hn : 0 < n) : (CycRing n)ˣ :=
  Units.ofPowEqOne (AdjoinRoot.root (cyclotomic n ℤ)) n (root_pow n) hn.ne'

open Polynomial in
theorem cycUnit_val {n : ℕ} (hn : 0 < n) : (cycUnit hn : CycRing n) = AdjoinRoot.root (cyclotomic n ℤ) := rfl

theorem cycUnit_pow {n : ℕ} (hn : 0 < n) : cycUnit hn ^ n = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, cycUnit_val, root_pow, Units.val_one]

open Polynomial in
theorem isPrimitiveRoot_map {n : ℕ} (hn : 0 < n) {K : Type} [Field K] (hK : (n : K) ≠ 0) (β : CycRing n →+* K) :
    IsPrimitiveRoot (Units.map β.toMonoidHom (cycUnit hn)) n := by
  have : NeZero (n : K) := ⟨hK⟩
  have hr : (cyclotomic n K).IsRoot (β (AdjoinRoot.root (cyclotomic n ℤ))) := by
    have h := congrArg β (AdjoinRoot.eval₂_root (cyclotomic n ℤ))
    rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int (β.comp (AdjoinRoot.of _)) (Int.castRingHom K),
      ← Polynomial.eval_map, Polynomial.map_cyclotomic_int] at h
    exact h
  rw [← IsPrimitiveRoot.coe_units_iff]
  have hv : ((Units.map β.toMonoidHom (cycUnit hn) : Kˣ) : K) = β (AdjoinRoot.root (cyclotomic n ℤ)) := by
    simp [cycUnit_val]
  rw [hv]
  exact (Polynomial.isRoot_cyclotomic_iff).mp hr

open Polynomial in
theorem exists_map_eq {n : ℕ} (hn : 0 < n) {K : Type} [Field K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) :
    ∃ β : CycRing n →+* K, Units.map β.toMonoidHom (cycUnit hn) = ζ := by
  have h : (cyclotomic n ℤ).eval₂ (Int.castRingHom K) (ζ : K) = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
    exact (IsPrimitiveRoot.coe_units_iff.mpr hζ).isRoot_cyclotomic hn
  refine ⟨AdjoinRoot.lift (Int.castRingHom K) (ζ : K) h, Units.ext ?_⟩
  simp [cycUnit_val]

open Polynomial in
theorem isFinite_cyc (n : ℕ) : IsFinite (spMap (algebraMap ℤ (CycRing n))) := by
  have hf : Module.Finite ℤ (CycRing n) := (AdjoinRoot.powerBasis' (cyclotomic.monic n ℤ)).finite
  dsimp only [spMap]
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr hf

theorem isUnit_natCast_of_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {n : ℕ} (h : IsUnit (n : Γ(Y, ⊤))) :
    IsUnit (n : Γ(X, ⊤)) := by
  have h' := h.map f.appTop.hom
  rwa [map_natCast] at h'

theorem natCast_ne_zero_of_isUnit {K : Type} [Field K] {n : ℕ} (h : IsUnit (n : Γ(Sp K, ⊤))) : (n : K) ≠ 0 := by
  have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast] at h'
  exact h'.ne_zero

theorem isUnit_natCast_basicOpen (S : Scheme.{0}) (n : ℕ) :
    IsUnit (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) := by
  have h : IsUnit (n : Γ(S, S.basicOpen (n : Γ(S, ⊤)))) := by
    have h0 := S.toRingedSpace.isUnit_res_basicOpen (n : Γ(S, ⊤))
    rwa [map_natCast] at h0
  have e : (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) =
      (S.basicOpen (n : Γ(S, ⊤))).topIso.inv.hom (n : Γ(S, S.basicOpen (n : Γ(S, ⊤)))) :=
    (map_natCast _ n).symm
  rw [e]
  exact h.map _

theorem range_subset_basicOpen {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ} (hK : (n : K) ≠ 0) :
    Set.range x ⊆ Set.range (S.basicOpen (n : Γ(S, ⊤))).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hK' : IsUnit (n : Γ(Sp K, ⊤)) := by
    have h1 := (Ne.isUnit hK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at h1
  have hu : IsUnit (x.app ⊤ (n : Γ(S, ⊤))) := by
    rw [map_natCast]
    have h1 := hK'.map ((Sp K).presheaf.map (homOfLE (le_top : x ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
    rwa [map_natCast] at h1
  have h := Scheme.preimage_basicOpen x (n : Γ(S, ⊤))
  rw [(Sp K).basicOpen_of_isUnit hu] at h
  show y ∈ x ⁻¹ᵁ S.basicOpen (n : Γ(S, ⊤))
  rw [h]
  trivial

theorem unitOn_inj {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := by
  intro a b h
  apply Units.ext
  have h1 := congrArg (fun u : Γ(Sp k, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (u : Γ(Sp k, ⊤))) h
  simpa [unitOn] using h1

private theorem exists_lift_of_range_subset_closure_image_finite {W U S : Scheme.{0}} (q : W ⟶ U) [IsFinite q] (f : U ⟶ S) [IsOpenImmersion f]
    {C : Set W} (hC : IsClosed C) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ U)
    (hx : Set.range (x ≫ f) ⊆ closure ((q ≫ f) '' C)) : ∃ w : Sp K ⟶ W, w ≫ q = x ∧ Set.range w ⊆ C := by
  let pt : Sp K := IsLocalRing.closedPoint K
  obtain ⟨c, hcC, hc⟩ : ∃ c ∈ C, q c = x pt := by
    have h1 : (x ≫ f) pt ∈ closure ((q ≫ f) '' C) := hx ⟨pt, rfl⟩
    have e : (q ≫ f) '' C = f '' (q '' C) := by
      ext y
      simp
    rw [e] at h1
    have h2 : x pt ∈ closure (q '' C) := by
      rw [f.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
      simpa [Scheme.Hom.comp_apply] using h1
    rw [(q.isClosedMap C hC).closure_eq] at h2
    exact h2
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback c pt hc
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  have hS : IsClosed ((pullback.fst q x) ⁻¹' C) := hC.preimage (pullback.fst q x).continuous
  obtain ⟨z', hz'C, hz'⟩ := hS.exists_closed_singleton ⟨z, by simpa [Set.mem_preimage, hz1] using hcC⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z' hz' ≫ pullback.fst q x, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  · rintro _ ⟨a, rfl⟩
    simpa [Scheme.Hom.comp_apply] using hz'C

private theorem lift_lemma' {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ} (hK : (n : K) ≠ 0) :
    ∃ xU : Sp K ⟶ (S.basicOpen (n : Γ(S, ⊤)) : Scheme.{0}), xU ≫ (S.basicOpen (n : Γ(S, ⊤))).ι = x :=
  ⟨_, IsOpenImmersion.lift_fac _ x (range_subset_basicOpen x hK)⟩

set_option maxHeartbeats 1000000 in
private theorem main_lemma_3 : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  intro S G _ _ n La _ _ _ hG hn
  have hU : IsUnit (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) := isUnit_natCast_basicOpen S n
  have hGU : IsAbelianScheme ((Over.pullback (S.basicOpen (n : Γ(S, ⊤))).ι).obj G) :=
    Out.TLinPf.isAb_pullback _ G hG
  have hP := isGrpPullback_pullback G (S.basicOpen (n : Γ(S, ⊤))).ι
  obtain ⟨Z₀, et₀, hfin, -, hadd₀, hpow₀, huniv₀⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom _ ((Over.pullback (S.basicOpen (n : Γ(S, ⊤))).ι).obj G) n La hGU hU
  have hcyc := isFinite_cyc n
  have hp1 : IsFinite (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n)))) :=
    by infer_instance
  let ZU : Over (S.basicOpen (n : Γ(S, ⊤)) : Scheme.{0}) :=
    Over.mk (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n))) ≫ Z₀.hom)
  let r : ZU ⟶ Z₀ := Over.homMk (pullback.fst _ _)
  have hWu : IsUnit (n : Γ(ZU.left, ⊤)) := isUnit_natCast_of_hom ZU.hom hU
  refine ⟨Over.mk (ZU.hom ≫ (S.basicOpen (n : Γ(S, ⊤))).ι), fun a => GlobalTheory.ObjPull.pushEquiv hP ZU (r ≫ et₀ a),
    Units.map (GlobalTheory.LevCover.fnOn (pullback.snd (specZIsTerminal.from Z₀.left)
      (spMap (algebraMap ℤ (CycRing n))))).toMonoidHom (cycUnit hn), hWu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a'
    dsimp only
    rw [hadd₀, comp_mul, map_mul]
  · intro a
    dsimp only
    rw [← map_pow, ← comp_pow, hpow₀]
    simp
  · rw [← map_pow, cycUnit_pow, map_one]
  · intro K _ h ζ hζ
    obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (h ≫ pullback.snd _ _)
    rw [GlobalTheory.LevCover.map_fnOn _ h β hβ] at hζ
    rw [← unitOn_inj hζ]
    exact isPrimitiveRoot_map hn (natCast_ne_zero_of_isUnit (isUnit_natCast_of_hom h hWu)) β
  · intro K _ x et' ζ hK hadd hpow hζ
    obtain ⟨xU, hxU⟩ := lift_lemma' (S := S) (K := K) (n := n) x hK
    let e : Over.mk ((Over.mk xU).hom ≫ (S.basicOpen (n : Γ(S, ⊤))).ι) ⟶ Over.mk x :=
      Over.homMk (𝟙 _) (by simpa using hxU.symm)
    obtain ⟨h₀, hh₀, -⟩ := huniv₀ (Over.mk xU) (fun a => (GlobalTheory.ObjPull.pushEquiv hP _).symm (e ≫ et' a))
      (fun a a' => by rw [hadd, comp_mul, map_mul])
      (fun a => by rw [← map_pow, ← comp_pow, hpow]; simp)
    obtain ⟨β, hβ⟩ := exists_map_eq hn hζ
    let hW : Sp K ⟶ ZU.left := pullback.lift h₀.left (spMap β) (specZIsTerminal.hom_ext _ _)
    have hW1 : hW ≫ pullback.fst _ _ = h₀.left := pullback.lift_fst _ _ _
    have hW2 : hW ≫ pullback.snd _ _ = spMap β := pullback.lift_snd _ _ _
    refine ⟨Over.homMk hW ?_, ?_, ?_⟩
    · show hW ≫ (pullback.fst _ _ ≫ Z₀.hom) ≫ _ = x
      rw [← Category.assoc, ← Category.assoc, hW1, Over.w h₀]
      exact hxU
    · intro a
      apply Over.OverMorphism.ext
      have h1 := GlobalTheory.ObjPull.pushEquiv_symm_left hP _ (e ≫ et' a)
      rw [← hh₀ a] at h1
      have h2 : (e ≫ et' a).left = (et' a).left := by simp [e]
      show hW ≫ (GlobalTheory.ObjPull.pushEquiv hP ZU (r ≫ et₀ a)).left = (et' a).left
      rw [GlobalTheory.ObjPull.pushEquiv_left, ← h2, ← h1, Over.comp_left, Over.comp_left, ← hW1]
      simp only [Category.assoc]
      rfl
    · show Units.map hW.appTop.hom.toMonoidHom _ = _
      rw [GlobalTheory.LevCover.map_fnOn _ hW β hW2, hβ]
  · intro C hC K _ _ x hK hcl
    obtain ⟨xU, hxU⟩ := lift_lemma' (S := S) (K := K) (n := n) x hK
    have : IsFinite Z₀.hom := hfin
    have : IsFinite ZU.hom := by
      show IsFinite (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n))) ≫ Z₀.hom)
      infer_instance
    obtain ⟨w, hw, hwC⟩ := exists_lift_of_range_subset_closure_image_finite ZU.hom (S.basicOpen (n : Γ(S, ⊤))).ι hC xU
      (by rw [hxU]; exact hcl)
    refine ⟨Over.homMk w ?_, hwC⟩
    show w ≫ ZU.hom ≫ _ = x
    rw [← Category.assoc, hw, hxU]

end GlobalTheory.TorsRootParam

namespace GlobalTheory

open TorsRootParam in

theorem exists_latticeTorsionHom_primitiveRoot_param : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  exact main_lemma_3

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOActDescendOfEtaleIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

theorem exists_oAct_descend_of_etale_isogeny :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (a : OAct O A), IsAbelianScheme A → IsAbelianScheme B → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A) (c : O), x ≫ ψ = 1 → (x ≫ a.act c) ≫ ψ = 1) → ∃ b : OAct O B, ∀ c, a.act c ≫ ψ = ψ ≫ b.act c := by
  intro O _ S _ A B _ _ _ _ ψ a hA hB hψ hf he hs hker
  have hsep : IsSeparated B.hom := by
    have := hB.proper
    infer_instance
  have key : ∀ c : O, ∃ g' : B ⟶ B, IsMonHom g' ∧ ψ ≫ g' = a.act c ≫ ψ ∧
      ∀ g'' : B ⟶ B, ψ ≫ g'' = a.act c ≫ ψ → g'' = g' := by
    intro c
    have := a.hom c
    refine GlobalTheory.T.exists_unique_factor_through_etale_isogeny_reduced S A B B ψ (a.act c ≫ ψ) hA hB hsep hψ hf he hs inferInstance ?_
    intro k _ _ t x hx
    rw [← Category.assoc]
    exact hker k t x c hx
  choose f hf1 hf2 hf3 using key
  refine ⟨⟨f, hf1, ?_, ?_, ?_⟩, fun c => (hf2 c).symm⟩
  · refine (hf3 1 _ ?_).symm
    rw [a.one, Category.id_comp, Category.comp_id]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [← Category.assoc, hf2, Category.assoc, hf2, a.mul, Category.assoc]
  · intro x y
    refine (hf3 _ _ ?_).symm
    rw [MonObj.comp_mul, hf2, hf2, a.add]
    exact (map_mul (IsMonHom.monoidHom ψ A) _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothDescentOfTameQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_smooth_descent_of_tame_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (s : X ⟶ Sp R) (τ : Γ →* Aut G.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (G.hom ≫ s) → Smooth G.hom → (∀ g, (τ g).hom ≫ G.hom = G.hom ≫ (ρ g).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst G.hom x ≫ (τ g).hom = pullback.fst G.hom x) → ∃ (G' : Over X') (φ : G.left ⟶ G'.left), IsPullback φ G.hom G'.hom π ∧ Smooth G'.hom ∧ ∀ g, (τ g).hom ≫ φ = φ := by
  intro Γ _ _ R _ X X' _ ρ π G s τ hπ hfin hqp hsm hτ hstab hfib
  have hsepG : G.left.IsSeparated := by
    obtain ⟨N, i, hi, -, hcomp⟩ := hqp
    haveI := isProper_str R N
    haveI : IsSeparated (G.hom ≫ s) := by rw [← hcomp]; infer_instance
    constructor
    rw [show terminal.from G.left = (G.hom ≫ s) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨Y', φ, hφ⟩ := exists_quotient_of_finite_group Γ G.left τ (fun y => by
    obtain ⟨V, hV, hF, -⟩ := exists_isAffineOpen_le_of_isQProjOver R G.left (G.hom ≫ s) hqp
      (Set.range fun g => (τ g).hom y) ⊤ (Set.finite_range _) (fun _ _ => trivial)
    exact ⟨V, hV, fun g => hF ⟨g, rfl⟩⟩)
  obtain ⟨p', hp', -⟩ := quotient_existsUnique_comp_eq Γ G.left Y' τ φ hφ X' (G.hom ≫ π)
    (fun g => by rw [← Category.assoc, hτ g, Category.assoc, hπ.2.1 g])
  obtain ⟨hpb, hflat, hlft⟩ := GlobalTheory.T.isPullback_flat_of_tame_alt Γ X X' G.left Y' ρ τ π φ G.hom p' hπ hφ hp' hτ hfin
    inferInstance inferInstance hstab hfib
  have hsurj : Surjective π := (quotient_isIntegral_surjective_orbits Γ X X' ρ π hπ).2.1
  haveI : LocallyOfFinitePresentation p' := inferInstance
  exact ⟨Over.mk p', φ, hpb,
    smooth_of_isPullback_of_surjective_of_flat X X' G.left Y' π φ G.hom p' hpb hsurj hflat
      inferInstance hsm, fun g => hφ.2.1 g⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPull

theorem lbIso_pull {X Y Y' : Scheme.{0}} {A : LB Y} {L : LB X} {φ : Y ⟶ X} (H : LBIso A (L.pull φ)) (h : Y' ⟶ Y)
    {F : Y' ⟶ X} (e : F = h ≫ φ) : LBIso (A.pull h) (L.pull F) :=
  H.chartPull (chartPullPull A h h rfl)
    (chartPullSame L (fun _ : PUnit => F) (fun _ : PUnit => φ) (fun _ => 1) h fun _ => e)

theorem isPEL_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g k J a bas o _ b ρ S S' s s' f t t' τ hs ⟨ψ, hψ, hψL, hpt, hact⟩ ⟨φ, hφ, hφL, hφa, hgeom⟩
  obtain ⟨τ', ⟨m⟩⟩ : ∃ τ' : SAB H S', Nonempty (SABMap τ' τ f) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f τ
    exact ⟨_, ⟨m⟩⟩
  have hL : LBIso τ'.PP.L (τ.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : IsGrpPullback τ'.G t.A f (m.cm.F ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨τ', e, he, ?_, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · exact (hL.trans τ'.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (lbIso_pull hφL m.cm.F rfl)).trans
      τ'.PP.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) (lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (τ'.act.act (a j)).left ≫ m.cm.F = m.cm.F ≫ (τ.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom K (x ≫ f) β (by rw [Category.assoc, hs, hx])
    refine ⟨fun σ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c y => ?_)
      (fun n y y' c hc => ?_) I, hI, fun i => ?_⟩
    · rw [GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ,
        GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ]
      exact hdet σ
    · apply Over.OverMorphism.ext
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' τ.G τ'.G f m.cm.F τ.PP.L τ'.PP.L τ.PP.isLB τ'.PP.isLB m.cart hL
        (Over.mk x) n y y' _ _ _ rfl rfl).2 hc
    · apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = (x ≫ f) ≫ (t.pt i).left :=
          congrArg (fun z => z.left) (hA i)
        have h₂ := GlobalTheory.ObjPull.pushEquiv_symm_left m.cart (Over.mk x) (I.ev k (bas (Pi.single i 1)))
        show (((GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)).symm (I.ev k (bas (Pi.single i 1)))).left ≫ e.hom.left) ≫ ψ =
          (x ≫ (t'.pt i).left) ≫ ψ
        rw [Category.assoc, heF, Category.assoc, hpt]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ.hom.left) h₂).trans (h₁.trans (Category.assoc _ _ _)))
      · rw [Over.w, Over.w]

end GlobalTheory.PELPull
end

