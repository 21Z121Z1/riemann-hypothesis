import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBOfKeyViaField
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyDesc

open GlobalTheory.KeyCancel

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMapR_algebraMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    Chart.dualMapR f (algebraMap A _ a) = algebraMap B _ (f a) := by
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMapR_eps {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Chart.dualMapR f DualNumber.eps = DualNumber.eps := by
  ext <;> simp [Chart.dualMapR]

theorem keyPB_of_keyVia_field : ∀ (R k K : Type) [CommRing R] [Field k] [Field K] (α : R →+* k) (β : k →+* K)
    (y : KeyIn R) (z : KeyIn k) (x : KeyIn K) (φ : x.P.A.left ⟶ z.P.A.left) (w₀ : LB.Iso x.P.L (z.P.L.pull φ))
    (ψ : z.P.A.left ⟶ y.P.A.left) (w₁ : LB.Iso x.P.L (y.P.L.pull (φ ≫ ψ))), KeyVia x z β φ w₀ →
    KeyVia x y (β.comp α) (φ ≫ ψ) w₁ → IsGrpPullback z.P.A y.P.A (spMap α) ψ → LBIso z.P.L (y.P.L.pull ψ) →
    KeyPB z y α := by
  intro R k K _ _ _ α β y z x φ w₀ ψ w₁ ⟨he₀, hg₀, F₀, hc₀, hw₀, hr₀, hs₀, hF₀, hFe₀, hv₀⟩
    ⟨he₁, hg₁, F₁, hc₁, hw₁, hr₁, hs₁, hF₁, hFe₁, hv₁⟩ hψ ⟨u, hu⟩
  have he : eSec z.P.A ≫ ψ = spMap α ≫ eSec y.P.A := PolBaseChange.eSec_comm hψ
  obtain ⟨w, g, m⟩ := KeyPow.exists_rescale y.P.isLB z.P.isLB ((isGen_iff u).1 hu) (p := z.P.A.hom)
    (Over.w η[z.P.A]) he z.rig_gen y.rig_gen
  have g₀ := (isGen_iff w₀).1 hw₀
  obtain ⟨w₂, T⟩ := exists_comp z.P.isLB w w₀ g g₀ y.P.isLB x.P.isLB
  have r₀ := (maps_iff w₀ _ (fun _ => eSec z.P.A) _ x.rig z.rig (spMap β) _ (rigPull_le φ (spMap β) he₀ z.P.L)
    (fun _ => rfl)).1 hr₀
  have r₂ := T.pmaps_comp z.P.isLB (fun _ => he₀) m r₀
  rw [← spMap_comp] at r₂
  obtain rfl : w₂ = w₁ := rigidified_iso_unique globalFns_holds x.P y.P.isLB (φ ≫ ψ) w₂ w₁
    ((isGen_iff _).2 (T.pgen_comp z.P.isLB g g₀)) hw₁ x.rig _
    ((maps_iff w₂ _ (fun _ => eSec y.P.A) _ x.rig y.rig (spMap (β.comp α)) _
      (rigPull_le (φ ≫ ψ) (spMap (β.comp α)) he₁ y.P.L) (fun _ => rfl)).2 r₂) hr₁
  have := z.P.isAb.smooth
  have := y.P.isAb.proper
  have : IsSchemeTheoreticallyDominant (spMap β) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom β) β.injective
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hc₀.1.flip
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hc₀.1.flip inferInstance
  obtain rfl : F₀ = Chart.dualMapR β := dualNumber_ringHom_ext
    (fun a => (hF₀ a).trans (dualMapR_algebraMap β a).symm) (hFe₀.trans (dualMapR_eps β).symm)
  obtain rfl : F₁ = (Chart.dualMapR β).comp (Chart.dualMapR α) := dualNumber_ringHom_ext
    (fun a => by rw [hF₁, RingHom.comp_apply, RingHom.comp_apply, dualMapR_algebraMap, dualMapR_algebraMap])
    (by rw [hFe₁, RingHom.comp_apply, dualMapR_eps, dualMapR_eps])
  refine ⟨ψ, he, w, hg₀.symm.trans hg₁, Chart.dualMapR α, hψ, (isGen_iff w).2 g,
    (maps_iff w _ (fun _ => eSec y.P.A) _ z.rig y.rig (spMap α) _ (rigPull_le ψ (spMap α) he y.P.L)
      (fun _ => rfl)).2 m, fun j i hle => φ.app_injective _ (fn_ext fun q hq => ?_), dualMapR_algebraMap α,
    dualMapR_eps α, fun i => ?_⟩
  · have hq' : φ ((𝟙 x.P.A.left : _ ⟶ _) q) ∈ (y.P.L.pull ψ).U j ⊓ z.P.L.U i := hq
    obtain ⟨l, hl⟩ := exists_chart x.P.isLB q
    have a := (appLE_eq_iff_stalk w₀ z.th x.th).1 hs₀ _ (𝟙 _) q i l hq'.2 hl
    have b := (appLE_eq_iff_stalk w₂ y.th x.th).1 hs₁ _ (𝟙 _) q (j PUnit.unit) l ((mem_pull (F := ψ)).1 hq'.1) hl
    rw [T _ (𝟙 _) q (j PUnit.unit) i l (mem_pull.1 hq'.1) hq'.2 hl, Units.val_mul, _root_.mul_assoc, ← a,
      ← Category.assoc] at b
    refine (gs_pull (𝟙 _) φ q _ hq' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) φ q _ hq' _).symm)
    refine (gs_appLE ψ _ _ hle (𝟙 _ ≫ φ) q hq' _).trans (b.trans ?_)
    rw [gs_mul (𝟙 _ ≫ φ) q _ hq', gs_res (𝟙 _ ≫ φ) q _ hq']
    exact congrArg (· * _) (gs_unit (𝟙 _ ≫ φ) q _ hq' _).symm
  · refine Spread.tangent_ext β β.injective y.P.A.hom ?_ ?_
    · rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext fun a => (dualMapR_algebraMap α a).symm
    · have a := hv₀ (i.cast hg₀.symm)
      have b := hv₁ (i.cast hg₀.symm)
      rw [← Category.assoc, a, spMap_comp, Category.assoc, Category.assoc] at b
      exact b

end GlobalTheory.KeyDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyOnPol

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

section Generator

variable {R : Type} [CommRing R]

theorem cst_mul₀ {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a b : R) : cst q z (a * b) = cst q z a * cst q z b := by
  simp only [cst, gs_eq q z ⊤ trivial, map_mul]

theorem cst_one₀ {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 1 = 1 := by
  simp only [cst, gs_eq q z ⊤ trivial, map_one]

def toPow {X : Scheme.{0}} {L : LB X} (s : L.Sec) : LB.Sec (AbLaw.pw L ((1 : ℕ) : ℤ)) :=
  ⟨s.f, fun i j => (s.compat i j).trans (congrArg (· * _) (congrArg Units.val (zpow_one (L.g i j)).symm))⟩

def ofPow {X : Scheme.{0}} {L : LB X} (s : LB.Sec (AbLaw.pw L ((1 : ℕ) : ℤ))) : L.Sec :=
  ⟨s.f, fun i j => (s.compat i j).trans (congrArg (· * _) (congrArg Units.val (zpow_one (L.g i j))))⟩

theorem exists_generator (hS : Out.SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) :
    ∃ b : P.L.Sec, (∀ s : Sp R, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus b) ∧
      ∀ s : P.L.Sec, ∃ a : R, ∀ i, s.f i = constFn P.A.hom _ a * b.f i := by
  obtain ⟨β, hβ⟩ := KeyBasis.exists_universal_basis hS R P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  obtain ⟨b, hb⟩ := KeyBasis.exists_pw (β i₀)
  have hv : ∀ (Z : Scheme.{0}) (q : Z ⟶ P.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      sval (β i₀) q z J = gs q z (P.L.U (J q)) ((ofPow b).f (J q)) := fun Z q z J hJ =>
    (sval_of (β i₀) q z J (fun _ => J q) fun _ => by rw [Category.comp_id]).trans (hb Z q z _ (hJ q))
  have := P.isAb.smooth
  refine ⟨ofPow b, ?_, fun s => ?_⟩
  · let k := IsLocalRing.ResidueField R
    let t : Sp k ⟶ Sp R := spMap (IsLocalRing.residue R)
    let f := pullback.fst t P.A.hom
    let π := pullback.snd t P.A.hom
    have hp : IsPullback f π t P.A.hom := IsPullback.of_hasPullback _ _
    have : IsReduced (pullback t P.A.hom) := isReduced_scheme_of_smooth_of_isIntegrallyClosed k f
    obtain ⟨z, hz⟩ : ∃ z, π z ∈ Out.nonzeroLocus (ofPow b) := by
      by_contra hn
      have h0 : ∀ j, (π.app _).hom ((ofPow b).f j) = 0 := fun j => by
        refine (basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun z hz => hn ⟨z, ?_⟩)
        rw [← Scheme.preimage_basicOpen] at hz
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hz⟩
      obtain ⟨c, -, hu⟩ := hβ k t _ π f hp ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩
      have hc : ∀ c, SectionLimit.Rep π f β ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩ c := by
        intro c Z r z J hJ
        rw [su, hv Z _ z J hJ, ← gs_pull r π z _ (hJ (r ≫ π)), h0, gs_eq r z _ (hJ (r ≫ π)), map_zero, map_zero, mul_zero]
        exact (gs_eq r z _ (hJ.mem (fun _ : Fin 1 => π) r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _))
      exact zero_ne_one (congrFun ((hu (fun _ => 0) (hc _)).trans (hu (fun _ => 1) (hc _)).symm) i₀)
    have hc : P.A.hom (π z) = IsLocalRing.closedPoint R := by
      refine (congrArg (fun g => g z) hp.w.symm).trans ?_
      refine Eq.trans ?_ (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))
      exact congrArg (PrimeSpectrum.comap (IsLocalRing.residue R)) (Subsingleton.elim (α := PrimeSpectrum k) _ _)
    have ht := (IsLocalRing.closedPoint_mem_iff (R := R)
      ⟨_, P.A.hom.isOpenMap _ (Out.nonzeroLocus (ofPow b)).isOpen⟩).1 ⟨_, hz, hc⟩
    intro s
    obtain ⟨y, h₁, h₂⟩ := (congrArg (fun U => s ∈ U) ht).mpr trivial
    exact ⟨y, h₂, h₁⟩
  · obtain ⟨σ, hσ⟩ := KeyBasis.exists_powerSection_of_chartFunctions (toPow s)
    obtain ⟨c, hc, -⟩ := hβ R (𝟙 _) _ (𝟙 _) P.A.hom (IsPullback.of_vert_isIso ⟨by simp⟩) σ
    refine ⟨c i₀, (sec_eq_iff _ _ _ _).2 fun i y hy => ?_⟩
    obtain ⟨J, hJ, hi⟩ := exists_good P.L P.isLB y (fun _ : PUnit => 𝟙 P.A.left) (fun _ => i) (fun _ _ _ => rfl) fun _ => hy
    have e := hc _ (𝟙 _) y J hJ
    rw [su, Category.id_comp, Category.id_comp, hv _ _ y J hJ, hi PUnit.unit,
      sval_of σ (𝟙 _) y J (fun _ => i) (fun _ => by rw [Category.comp_id]; exact hi PUnit.unit), hσ _ _ y i hy] at e
    exact e

end Generator

section Units

variable {R : Type} [CommRing R] {X : Scheme.{0}} {L : LB X}

def scale (p : X ⟶ Sp R) (a : R) (s : L.Sec) : L.Sec :=
  ⟨fun i => constFn p _ a * s.f i, fun i j => fn_ext fun y hy => by
    rw [gs_res _ y _ hy, gs_mul _ y _ hy.1, gs_mul _ y _ hy, gs_res _ y _ hy, gs_mul _ y _ hy.2, gs_constFn p _ _ y hy.1,
      gs_constFn p _ _ y hy.2, gs_unit _ y _ hy, gs_compat s (𝟙 X) y hy.1 hy.2, mul_left_comm]⟩

theorem isUnit_cst {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) (a : Rˣ) : IsUnit (cst q z (a : R)) :=
  IsUnit.of_mul_eq_one (cst q z (a⁻¹ : Rˣ)) (by rw [← cst_mul₀, Units.mul_inv, cst_one₀])

theorem mem_nonzeroLocus_of_unit (p : X ⟶ Sp R) (a : Rˣ) {s t : L.Sec} (h : ∀ i, t.f i = constFn p _ (a : R) * s.f i)
    {y : X} (hy : y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus t := by
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hy
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  rw [(sec_eq_iff _ _ _ _).1 h k y hk]
  exact (isUnit_cst p y a).mul u

theorem exists_unit (hS : Out.SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R))
    (s t : P.L.Sec) (hs : ∀ y : Sp R, ∃ z : P.A.left, P.A.hom z = y ∧ z ∈ Out.nonzeroLocus s)
    (ht : ∀ y : Sp R, ∃ z : P.A.left, P.A.hom z = y ∧ z ∈ Out.nonzeroLocus t) :
    ∃ a : Rˣ, ∀ i, t.f i = constFn P.A.hom _ (a : R) * s.f i := by
  obtain ⟨b, -, hb⟩ := exists_generator hS P
  have key : ∀ s : P.L.Sec, (∀ y : Sp R, ∃ z : P.A.left, P.A.hom z = y ∧ z ∈ Out.nonzeroLocus s) →
      ∃ a : Rˣ, ∀ i, ∀ y ∈ P.L.U i, gs (𝟙 _) y _ (s.f i) = cst P.A.hom y (a : R) * gs (𝟙 _) y _ (b.f i) := fun s hs => by
    obtain ⟨a, ha⟩ := hb s
    have ha' := (sec_eq_iff _ _ _ _).1 ha
    obtain ⟨z, hz, hz'⟩ := hs (IsLocalRing.closedPoint R)
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    rw [ha' k z hk] at u
    have hu : IsUnit a := by
      by_contra hn
      exact cst_not_isUnit P.A.hom z hz ((IsLocalRing.mem_maximalIdeal a).2 hn) (isUnit_of_mul_isUnit_left u)
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, ha'⟩
  obtain ⟨a, ha⟩ := key s hs
  obtain ⟨c, hc⟩ := key t ht
  refine ⟨c * a⁻¹, (sec_eq_iff _ _ _ _).2 fun i y hy => ?_⟩
  rw [ha i y hy, hc i y hy, ← _root_.mul_assoc, ← cst_mul₀, ← Units.val_mul, inv_mul_cancel_right]

end Units

open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem main : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], (∀ P : Out.PolAV (Sp R), 1 ≤ P.g → ∃ x : KeyIn R, x.P = P) ∧ ∀ (x : KeyIn R) (rig' hr' th' hth' v' hv'), ∃ (a : Rˣ) (t : x.P.L.Sec) (ht : _), (∀ i, t.f i = constFn x.P.A.hom _ (a : R) * x.th.f i) ∧ KeyPB ⟨x.P, x.g_pos, rig', hr', th', hth', v', hv'⟩ ⟨x.P, x.g_pos, x.rig, x.rig_gen, t, ht, v', hv'⟩ (RingHom.id R) := by
  intro hL R _ _ _
  refine ⟨fun P hg => ?_, fun x rig' hr' th' hth' v' hv' => ?_⟩
  · obtain ⟨rig, hr⟩ := P.rigid
    obtain ⟨th, hth, -⟩ := exists_generator hL.secBaseChange P
    obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis P.A P.smoothDim
    exact ⟨⟨P, hg, rig, hr, th, hth, v, hv⟩, rfl⟩
  · have e : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    have e' : spMap (RingHom.id (DualNumber R)) = 𝟙 (Sp (DualNumber R)) := Spec.map_id _
    have : IsMonHom (Iso.refl x.P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    have h : IsGrpPullback x.P.A x.P.A (spMap (RingHom.id R)) (𝟙 _) :=
      (isGrpPullback_of_iso (Iso.refl x.P.A)).congr e.symm rfl
    have he : eSec x.P.A ≫ 𝟙 _ = spMap (RingHom.id R) ≫ eSec x.P.A := PolBaseChange.eSec_comm h
    have := x.P.isAb.comm
    obtain ⟨w, hw, hm⟩ := KeyPow.exists_rescale x.P.isLB x.P.isLB (isoPullId_pgen (idIso_isGen x.P.isLB) rfl)
      (p := x.P.A.hom) (Over.w η[x.P.A]) he hr' x.rig_gen
    obtain ⟨s, hs⟩ := sec_pull_down hw x.P.isLB x.P.isLB x.th
    obtain ⟨a, ha⟩ := exists_unit hL.secBaseChange x.P s th'
      (SectionBaseChange.fibre_nonzero_of_pull x.P.isLB hs h.1 x.th_ne) hth'
    refine ⟨a, scale x.P.A.hom a x.th, fun y => ?_, fun _ => rfl, 𝟙 _, he, w, rfl, RingHom.id _, h, (isGen_iff _).2 hw,
      (maps_iff w _ (fun _ => eSec x.P.A) _ rig' x.rig _ _ (rigPull_le _ _ he x.P.L) (fun _ => rfl)).2 hm,
      KeyPow.appLE_eq_of_stalk w _ th' fun z j k hj hk => ?_, fun _ => rfl, rfl,
      fun i => by rw [e']; exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
    · obtain ⟨z, hz, hz'⟩ := x.th_ne y
      exact ⟨z, hz, mem_nonzeroLocus_of_unit x.P.A.hom a (fun _ => rfl) hz'⟩
    · have e₁ := hs _ (𝟙 _) z j k hj hk
      rw [Category.id_comp] at e₁ ⊢
      rw [(sec_eq_iff x.P.A.hom (scale x.P.A.hom a x.th) x.th a).1 (fun _ => rfl) j z hj, e₁,
        (sec_eq_iff _ _ _ _).1 ha k z hk, mul_left_comm]

end GlobalTheory.KeyOnPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalAtScale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq

theorem normalAt_scale :
    ∀ (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv th' hth' v' hv') (a : ℂ) (N : Matrix (Fin P.g) (Fin P.g) ℂ), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (N i) v (v' i)) → a ≠ 0 ∧ N.det ≠ 0 ∧ ∀ (τ M : Matrix (Fin P.g) (Fin P.g) ℂ) (α β : Fin P.g → ℂ) (c : ℂ), NormalAt ⟨P, hg, rig, hr, th, hth, v, hv⟩ τ M α β c → NormalAt ⟨P, hg, rig, hr, th', hth', v', hv'⟩ τ (N * M) α β (a * c) := by
  intro P hg rig hr th hth v hv th' hth' v' hv' a N ha hN
  haveI := P.isAb.comm
  obtain ⟨-, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ P.A P.g v hv.1
  refine ⟨?_, ((bas N v' hv hN).1 hv').ne_zero, ?_⟩
  · rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint ℂ)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  · rintro τ M α β c ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨u, h₁, h₂, h₃, h₄, ?_, ?_⟩
    · intro i z hz
      have e := h₅ i z hz
      refine ((congrArg (valAt' _ _) (ha i)).trans (valAt'_mul _ _ _ _)).trans ?_
      rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
      refine (congrArg (a * ·) e).trans ?_
      beta_reduce
      simp only [_root_.mul_assoc]
    · intro i
      have h1 := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 h₆ (hN i)
      have e : ∑ j, N i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ • (N * M) i := by
        simp only [smul_comm (N i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
        rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
        rfl
      rwa [e] at h1

end GlobalTheory.KeyEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeIsoThetaProductBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudeIso_thetaProduct_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ u (m N : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin N → RR x m) (b' : Fin N → RR x' m) (ξ : Fin 4 → Pt x) (ξ' : Fin 4 → Pt x') (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (q : (Fin 4 → Fin N) → R), KeyVia x' x f φ u → (∀ k, SecVia x' x φ u (b' k) (b k)) → (∀ r, (ξ' r).left ≫ φ = spMap f ≫ (ξ r).left) → w.IsGen → (∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) J, Good x.P.L z J → ∏ r, gs (ρ ≫ (alMap x al r (ξ r)).left) z (x.P.L.U (J (ρ ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (ρ ≫ (alMap x al r (ξ r)).left))) = (val w ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (q I')) * ∏ c, gs (ρ ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (ρ ≫ (Out.powPr x.P.A c).left))) ((b (I' c)).f (J (ρ ≫ (Out.powPr x.P.A c).left)))) → ∃ w' : LB.Gen (LB.LinComb x'.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x' al r (ξ' r)).left) (fun c => (Out.powPr x'.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (Out.powObj x'.P.A 4).left) (z : Z) J, Good x'.P.L z J → ∏ r, gs (ρ ≫ (alMap x' al r (ξ' r)).left) z (x'.P.L.U (J (ρ ≫ (alMap x' al r (ξ' r)).left))) (x'.th.f (J (ρ ≫ (alMap x' al r (ξ' r)).left))) = (val w' ρ z J).val * ∑ I' : Fin 4 → Fin N, gs ρ z ⊤ (cst (Out.powObj x'.P.A 4).hom ⊤ (f (q I'))) * ∏ c, gs (ρ ≫ (Out.powPr x'.P.A c).left) z (x'.P.L.U (J (ρ ≫ (Out.powPr x'.P.A c).left))) ((b' (I' c)).f (J (ρ ≫ (Out.powPr x'.P.A c).left))) := by
  first | exact @GlobalTheory.KeyRow.main | exact GlobalTheory.KeyRow.main | (intros; apply GlobalTheory.KeyRow.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFrame_value_independent_normalForm : ThetaUnifAV → Key.Chi.InversionStatement → ∀ (x : KeyIn ℂ) (t t' : ℂ), (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t' = M.det ^ 4 / c ^ 8) → t = t' := by
  first | exact @GlobalTheory.NormalUnique.thetaFrame_value_unique | exact GlobalTheory.NormalUnique.thetaFrame_value_unique | (intros; apply GlobalTheory.NormalUnique.thetaFrame_value_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyValUnit

theorem valUnit : ∀ κ : Rule, Funct κ → UnitSp κ → ValUnit κ := by
  intro κ hF hU S V K _ _ _ _ _ _ _ _ _ g y x hx
  have := RingHom.ker_isPrime g
  let S₀ := S ⧸ RingHom.ker g
  let K₀ := FractionRing S₀
  let g₀ : S₀ →+* V := RingHom.kerLift g
  let f₀ : S₀ →+* K := (algebraMap V K).comp g₀
  have hf₀ : Function.Injective f₀ := (IsFractionRing.injective V K).comp (RingHom.kerLift_injective g)
  let j : K₀ →+* K := IsFractionRing.lift hf₀
  have hj : j.comp (algebraMap S₀ K₀) = (algebraMap V K).comp g₀ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hf₀ a
  have : CharZero K₀ := j.charZero
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker g))
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y₀ (algebraMap S₀ K₀)
  have e : j.comp ((algebraMap S₀ K₀).comp (Ideal.Quotient.mk (RingHom.ker g))) = (algebraMap V K).comp g := by
    rw [← RingHom.comp_assoc, hj]
    exact RingHom.ext fun a => congrArg (algebraMap V K) (RingHom.kerLift_mk g a)
  have hxj : KeyPB x x₀ j := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y x₀ x _ _
    (GlobalTheory.keyPB_trans _ _ _ y y₀ x₀ _ _ hy₀ hx₀) (e.symm ▸ hx)
  have hval := hF K₀ K j x₀ x hxj
  obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyGenInt.isIntegral_value κ hU S₀ K₀ y₀ x₀ hx₀
  have h₁' : IsIntegral V (κ K x : K) := hval ▸ h₁.map_of_comp_eq g₀ j hj.symm
  have h₂' : IsIntegral V ((κ K x : K)⁻¹) := by
    rw [hval, ← map_inv₀]
    exact h₂.map_of_comp_eq g₀ j hj.symm
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₁'
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₂'
  have hab : a * b = 1 := IsFractionRing.injective V K (by
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ (κ K x).ne_zero])
  exact ⟨Units.mkOfMulEqOne a b hab, ha.symm⟩

end GlobalTheory.KeyValUnit
end

