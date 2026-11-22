import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0004
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RelAmpleQProj

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out TopologicalSpace

variable {Y : Scheme.{0}} {L M G : LB Y}

def secPwOne (σ : G.Sec) : (pw G 1).Sec where
  f := σ.f
  compat i j := by
    have h := σ.compat i j
    rw [← zpow_one (G.g i j)] at h
    exact h

theorem exists_sec_tw_locus [CompactSpace Y] [QuasiSeparatedSpace Y] (hM : M.IsLB) (hG : G.IsLB) (σ : G.Sec)
    (V : Y.Opens) (hV : V = nonzeroLocus σ) (r : (M.pull V.ι).Sec) :
    ∃ (k : ℕ) (u : (tw M G (k : ℤ)).Sec), V.ι ⁻¹ᵁ nonzeroLocus u = nonzeroLocus r := by
  obtain ⟨s, ⟨hs, hr⟩, -⟩ := existsUnique_secOn_of_pull M V r
  obtain ⟨k, H⟩ := exists_tw_extend_pow_mul Y G M 1 (secPwOne σ) V 0 hG hM hV inferInstance inferInstance
    (SecOn.twZeroEquiv hM hG V (GlobalTheory.LB.mkSec s hs))
  rw [show (0 : ℤ) + k * 1 = k by ring] at H
  obtain ⟨a, ha⟩ := H
  refine ⟨k, SecOn.topEquiv _ a, ?_⟩
  ext z
  obtain ⟨p, hp⟩ := exists_chart hM (V.ι z)
  obtain ⟨l, hl⟩ := exists_chart hG (V.ι z)
  have hzV : V.ι z ∈ V := z.2
  have hz : V.ι z ∈ V ⊓ (M.U p ⊓ G.U l) := ⟨hzV, hp, hl⟩
  have hz' : V.ι z ∈ M.U p ⊓ G.U l := ⟨hp, hl⟩
  have hzp : z ∈ (M.pull V.ι).U (fun _ => p) := mem_pull.2 hp
  have e := congrArg (gs V.ι z _) (ha p l)
  rw [SecOn.twCoord_twZeroEquiv, gs_res _ z _ hz, gs_mul _ z _ hz, gs_pow _ z _ hz, gs_res _ z _ hz] at e
  have e₁ : gs V.ι z _ ((SecOn.topEquiv _ a).f (p, l)) = gs V.ι z _ (SecOn.twCoord a p l) :=
    gs_res V.ι z _ hz' _
  have e₂ : gs (𝟙 _) z _ (r.f fun _ => p) = gs V.ι z _ (s p) := by
    rw [← hr, gs_appLE V.ι _ _ _ (𝟙 _) z hzp, Category.id_comp]
  have hσ : IsUnit (gs V.ι z (V ⊓ (M.U p ⊓ G.U l)) (rs Y (inf_le_right.trans inf_le_right) (σ.f l))) := by
    rw [gs_res _ z _ hz]
    exact (mem_nonzeroLocus_iff_pull σ V.ι z hl).1 (hV.le hzV)
  refine (mem_nonzeroLocus_iff_pull (SecOn.topEquiv _ a) V.ι z (k := (p, l)) hz').trans
    (Iff.trans ?_ (mem_nonzeroLocus_iff_isUnit r hzp).symm)
  rw [e₂]
  refine (iff_of_eq (congrArg IsUnit (e₁.trans e))).trans ?_
  rw [IsUnit.mul_iff]
  exact and_iff_right (hσ.pow k)

theorem exists_sec_pow_tw {m k c e : ℕ} (he : 1 ≤ e) (h : c * m = k + e) (u : (tw (lbPow L m) G (k : ℤ)).Sec)
    (σ : G.Sec) : ∃ w : (lbPow (tw L G (c : ℤ)) m).Sec, nonzeroLocus w = nonzeroLocus u ⊓ nonzeroLocus σ := by
  have le : ∀ J : PUnit → L.ι × G.ι, powChart (tw L G (c : ℤ)) J ≤
      powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2 := fun J y hy =>
    ⟨mem_powChart.2 (mem_powChart.1 hy).1, (mem_powChart.1 hy).2⟩
  let F : ∀ J : PUnit → L.ι × G.ι, Γ(Y, powChart (tw L G (c : ℤ)) J) := fun J =>
    resG Y (le J) (show Γ(Y, powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2) from
      u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
      resG Y ((le J).trans inf_le_right) (σ.f (J PUnit.unit).2) ^ e
  have hF : ∀ (y : Y) (J : PUnit → L.ι × G.ι), y ∈ powChart (tw L G (c : ℤ)) J → gs (𝟙 Y) y _ (F J) =
      gs (𝟙 Y) y _ (u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
        gs (𝟙 Y) y _ (σ.f (J PUnit.unit).2) ^ e := fun y J hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨powSecOfGerm (L := tw L G (c : ℤ)) m F fun y J J' hJ hJ' => ?_, ?_⟩
  · have e₁ := gs_compat u (𝟙 Y) y (j := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
      (j' := (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2)) (le J hJ) (le J' hJ')
    have e₂ := TwistGen.gm_tw_g (lbPow L m) G k y (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2) (le J hJ) (le J' hJ')
    have e₃ := gm_lbPow_g (L := L) m (𝟙 Y) y (fun _ => (J PUnit.unit).1) (fun _ => (J' PUnit.unit).1)
      (le J hJ).1 (le J' hJ').1
    have e₄ := TwistGen.gm_tw_g L G c y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.1 hJ) (mem_powChart.1 hJ')
    have e₅ := gs_compat σ (𝟙 Y) y (le J hJ).2 (le J' hJ').2
    dsimp only at e₂
    rw [e₃] at e₂
    refine (hF y J hJ).trans (Eq.trans ?_ (congrArg₂ (fun a b => a ^ m * b) e₄ (hF y J' hJ')).symm)
    rw [e₅]
    refine (congrArg (· * _) (e₁.trans (congrArg (· * _) e₂))).trans ?_
    simp only [Units.val_pow_eq_pow_val]
    rw [mul_pow, mul_pow, ← pow_mul, h]
    ring
  · refine nonzeroLocus_pow_eq_of _ _ (fun y hy => ?_) fun y J hJ => ?_
    · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
      exact ⟨fun _ => (p.1 PUnit.unit, p.2), mem_powChart.2 ⟨mem_powChart.1 hp.1, hp.2⟩⟩
    · refine (iff_of_eq (congrArg IsUnit (hF y J hJ))).trans ?_
      rw [IsUnit.mul_iff, isUnit_pow_iff (by omega)]
      exact and_congr (mem_nonzeroLocus_iff_isUnit u (k := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
        (le J hJ)).symm (mem_nonzeroLocus_iff_isUnit σ (le J hJ).2).symm

theorem exists_isAmpleLB_tw [CompactSpace Y] [QuasiSeparatedSpace Y] (hL : L.IsLB) (hG : G.IsLB)
    (h : ∀ y : Y, ∃ (σ : G.Sec) (V : Y.Opens), V = nonzeroLocus σ ∧ y ∈ V ∧ IsAmpleLB (L.pull V.ι)) :
    ∃ c : ℕ, IsAmpleLB (tw L G (c : ℤ)) := by
  have loc : ∀ y : Y, ∃ (m k : ℕ) (u : (tw (lbPow L m) G (k : ℤ)).Sec) (σ : G.Sec), 1 ≤ m ∧
      y ∈ nonzeroLocus u ⊓ nonzeroLocus σ ∧ IsAffineOpen (nonzeroLocus u ⊓ nonzeroLocus σ) := fun y => by
    obtain ⟨σ, V, hV, hy, hA⟩ := h y
    obtain ⟨m, hm, τ, hτ, ha⟩ := hA.exists_affine ⟨y, hy⟩
    obtain ⟨r, hr⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL m) V.ι)
      (isLB_lbPow hA.isLB m) (lbIso_lbPow_pull hL V.ι m).symm τ
    obtain ⟨k, u, hu⟩ := exists_sec_tw_locus (isLB_lbPow hL m) hG σ V hV r
    have e := hu.trans hr
    refine ⟨m, k, u, σ, hm, ⟨e.ge hτ, hV.le hy⟩, ?_⟩
    have h₁ := ha.image_of_isOpenImmersion V.ι
    rwa [← e, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm, hV] at h₁
  choose m k u σ hm hy ha using loc
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun y => nonzeroLocus (u y) ⊓ nonzeroLocus (σ y)) hy
  refine ⟨T.sup k + 1, isLB_tw hL hG _, inferInstance, fun x => ?_⟩
  obtain ⟨y, hx⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ x))
  have h₁ : k y ≤ T.sup k := Finset.le_sup y.2
  have h₂ : T.sup k + 1 ≤ (T.sup k + 1) * m y := Nat.le_mul_of_pos_right _ (hm y)
  obtain ⟨w, hw⟩ := exists_sec_pow_tw (c := T.sup k + 1) (e := (T.sup k + 1) * m y - k y) (by omega) (by omega)
    (u y) (σ y)
  exact ⟨m y, hm y, w, hw.ge hx, hw ▸ ha y⟩

theorem isProper_morphismRestrict {S : Scheme.{0}} (A : Over S) {B : LB A.left} (h : RelAmple A B) {U : S.Opens}
    (hU : IsAffineOpen U) : IsProper (A.hom ∣_ U) := by
  obtain ⟨N, -, K, s, H⟩ := h U hU
  have h₁ := isProper_of_veryAmpleBy
    ((ProjSpace.veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom s).2 H)
  exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).1 h₁

theorem isProper_and_exists_isAmpleLB {S : Scheme.{0}} (A : Over S) {B : LB A.left} (hB : B.IsLB)
    (h : RelAmple A B) {H : LB S} (hH : IsAmpleLB H) : IsProper A.hom ∧ ∃ N : LB A.left, IsAmpleLB N := by
  obtain ⟨n, -, c, s, hs, ha⟩ := hH.exists_cover
  have hp : IsProper A.hom := IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) _ hs
    fun i => isProper_morphismRestrict A h (ha i)
  have := hH.compactSpace
  have := hH.quasiSeparatedSpace
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  obtain ⟨d, hd⟩ := exists_isAmpleLB_tw hB (LB.isLB_pull (isLB_lbPow hH.isLB n) A.hom) fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ (A.hom y)))
    exact ⟨secPull (s i) A.hom, _, (nonzeroLocus_secPull _ _).symm, hi, isAmpleLB_of_relAmple A hB h _ (ha i)⟩
  exact ⟨hp, _, hd⟩

theorem isQProjOver_of_relAmple : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  rintro K _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem isQProjOver_of_isPullback_spMap {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') {Y Y' : Scheme.{0}}
    {s : Y ⟶ Sp R} {p : Y' ⟶ Y} {s' : Y' ⟶ Sp R'} (sq : IsPullback p s' s (spMap j)) (h : IsQProjOver s) :
    IsQProjOver s' := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have P := ProjSpace.isPullback_baseChange N j
  have w : (p ≫ i) ≫ PSpace.str R N = s' ≫ spMap j := by rw [Category.assoc]; exact sq.w
  have Q : IsPullback p (P.lift (p ≫ i) s' w) i (ProjSpace.baseChange N j) :=
    IsPullback.of_bot (by rw [P.lift_snd]; exact sq) (P.lift_fst _ _ w).symm P
  exact ⟨N, P.lift (p ≫ i) s' w, MorphismProperty.of_isPullback (P := @IsImmersion) Q hi,
    MorphismProperty.of_isPullback (P := @QuasiCompact) Q hq, P.lift_snd _ _ w⟩

theorem isQProjOver_comp_spMap_of_finiteType {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}
    (hj : j.FiniteType) {Y : Scheme.{0}} {s' : Y ⟶ Sp R'} (h : IsQProjOver s') : IsQProjOver (s' ≫ spMap j) := by
  obtain ⟨N, i, _, _, rfl⟩ := h
  have := isProper_str R' N
  have : LocallyOfFiniteType (spMap j) := HasRingHomProperty.Spec_iff.2 hj
  exact ((isAmple_projective_O_one R' N).pull_of_isImmersion i).isQProjOver _

theorem isQProjOver_baseChange_and_finite_restrict :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (j : R →+* R') (Y : Scheme.{0}) (s : Y ⟶ Sp R),
      (IsQProjOver s → IsQProjOver (pullback.snd s (spMap j))) ∧
        ∀ s' : Y ⟶ Sp R', j.Finite → IsQProjOver s' → IsQProjOver (s' ≫ spMap j) :=
  fun _ _ _ _ j _ _ => ⟨fun h => isQProjOver_of_isPullback_spMap j (IsPullback.of_hasPullback _ _) h,
    fun _ hj h => isQProjOver_comp_spMap_of_finiteType hj.finiteType h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem isQProjOver_comp_of_isFinite_general {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    {s : Y ⟶ Sp R} (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have hO : IsAmpleLB (ProjSpace.O1 R N) := isAmpleLB_basic.2.2.2.2.2.2.1 R N
  have hY : IsAmpleLB ((ProjSpace.O1 R N).pull i) := hO.pull_of_isImmersion i
  have hX : IsAmpleLB (((ProjSpace.O1 R N).pull i).pull f) := hY.pull_of_isFinite f
  have := isProper_str R N
  have : LocallyOfFiniteType (f ≫ i ≫ PSpace.str R N) := inferInstance
  exact hX.isQProjOver _

theorem isQProjOver_comp_of_isFinite_noetherian :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) (s : Y ⟶ Sp R),
      IsFinite f → IsQProjOver s → IsQProjOver (f ≫ s) := by
  intro R _ _ X Y f s hf h
  exact isQProjOver_comp_of_isFinite_general f h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

theorem isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (s : X ⟶ Sp R) :
    IsQProjOver s ↔ LocallyOfFiniteType s ∧ ∃ L : LB X, IsAmpleLB L := by
  constructor
  · rintro ⟨N, i, hi, hq, rfl⟩
    haveI := hi
    haveI := hq
    haveI : IsProper (PSpace.str R N) :=
      ((isProjOver_iff_isProper_and_exists_isAmpleLB (PSpace.str R N)).1
        ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩).1
    exact ⟨inferInstance, _, IsAmpleLB.pull_of_isImmersion (isAmpleLB_basic.2.2.2.2.2.2.1 R N) i⟩
  · rintro ⟨hs, L, hL⟩
    haveI := hs
    exact hL.isQProjOver s

theorem isQProjOver_comp_of_isAffineHom (f : Y ⟶ X) [IsAffineHom f] [LocallyOfFiniteType f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  haveI := hs
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (f ≫ s)).2 ⟨inferInstance, L.pull f, ?_⟩
  exact isAmpleLB_basic.2.2.1 f inferInstance hL

theorem isQProjOver_comp_of_isFinite (f : Y ⟶ X) [IsFinite f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := isQProjOver_comp_of_isAffineHom f h

theorem isQProjOver_of_isPullback {R' : Type} [CommRing R'] {b : R →+* R'} {s : X ⟶ Sp R} {π : Y ⟶ X}
    {s' : Y ⟶ Sp R'} (H : IsPullback π s' s (spMap b)) (h : IsQProjOver s) : IsQProjOver s' := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s').2 ⟨?_, L.pull π, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H hs
  · exact hL.pull_of_isPullback H

theorem isQProjOver_finite_and_baseChange :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      (∀ (Y : Scheme.{0}) (f : Y ⟶ X), IsFinite f → IsQProjOver (f ≫ s)) ∧
        ∀ (R' : Type) [CommRing R'] (b : R →+* R'), IsQProjOver (pullback.snd s (spMap b)) := by
  intro R _ _ X s h
  refine ⟨fun Y f hf => ?_, fun R' _ b => ?_⟩
  · haveI := hf
    exact isQProjOver_comp_of_isFinite f h
  · exact isQProjOver_of_isPullback (IsPullback.of_hasPullback s (spMap b)) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TransitionUnique

open GlobalTheory.ModelCompare

theorem isDominant_fst {F : Type} [Field F] (V : ValuationSubring F) {X : Scheme.{0}} (s : X ⟶ Sp V) [Flat s] :
    IsDominant (pullback.fst s (spMap V.subtype)) := by
  refine ⟨fun x => ?_⟩
  let g : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  have hg : spMap V.subtype g ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ?_
    show Ideal.comap V.subtype ⊥ ≤ _
    rw [Ideal.comap_bot_of_injective _ V.subtype_injective]
    exact bot_le
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s hg
  refine hy.mem_closed isClosed_closure (subset_closure ?_)
  rw [Scheme.Pullback.range_fst]
  exact ⟨g, e.symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isDominant_j {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) : IsDominant Y.j := by
  have := Y.flat
  have := isDominant_fst V Y.s
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  unfold Model.j
  infer_instance

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).1

theorem map_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} [IsReduced S]
    {t : SAB H S} {r r' : S ⟶ Xo.XF c} (ν : SABMap t Y.oF.t r) (ν' : SABMap t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) : r = r' := by
  let o := objOfSABMap Y.oF ν
  let n : ObjMap o Y.oF r := objMapOfSABMap Y.oF ν
  let n' : ObjMap o Y.oF r' := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq_secPull ν h)).symm.trans h'⟩
  obtain ⟨k, -⟩ := ObjComp.objMap_comp Y.m0 n
  obtain ⟨k', -⟩ := ObjComp.objMap_comp Y.m0 n'
  refine pullback.hom_ext ((Xo.rep S _ ‹_› o).unique ⟨Category.assoc _ _ _, ⟨k⟩⟩ ⟨?_, ⟨k'⟩⟩) hr
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr, Category.assoc]

theorem isTransition_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (c : Coeff l) (c₂ : Coeff l₂) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) (Y₂ : Model Xo₂ c₂ (c₂.V W).subtype) (b : c.V W →+* c₂.V W) (π π' : Y₂.X ⟶ Y.X), c.F ≤ c₂.F → IsIncl b → IsTransition Y Y₂ b π → IsTransition Y Y₂ b π' → π = π' := by
  intro E _ _ _ H D l l₂ Xo Xo₂ c c₂ W Y Y₂ b π π' _ _ h h'
  obtain ⟨p, mu, r, h₁, h₂, -, h₃, h₄, h₅⟩ := h
  obtain ⟨p', mu', r', h₁', h₂', -, h₃', h₄', h₅'⟩ := h'
  have e : π ≫ Y.s = Y₂.s ≫ spMap b := by
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition]
  have e' : π' ≫ Y.s = Y₂.s ≫ spMap b := by
    rw [← h₁', ← h₂', Category.assoc, Category.assoc, pullback.condition]
  have := mono_spMap_subtype (c.V W)
  have hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _ := by
    rw [← cancel_mono (spMap (c.V W).subtype), Category.assoc, Category.assoc, ← ModelRelProbe.j_over Y,
      ← Category.assoc, ← Category.assoc, ← h₃, ← h₃', Category.assoc, Category.assoc, e, e']
  obtain ⟨n, hn⟩ := LevelCover.sab_comp Y₂.m mu h₃
  obtain ⟨n', hn'⟩ := LevelCover.sab_comp Y₂.m mu' h₃'
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel Y.m n r rfl
  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y.m n' r' rfl
  have := isReduced_XF Xo₂ c₂
  have hrr : r = r' := map_unique Y ν ν' hr
    (fun a => ⟨_, LevelCover.sec_cancel ν Y.m _ _ (by rw [hν, hn]; exact h₄ a),
      LevelCover.sec_cancel ν' Y.m _ _ (by rw [hν', hn']; exact h₄' a)⟩)
    (fun a => ⟨_, LevelCover.sec_cancel ν Y.m _ _ (by rw [hν, hn]; exact h₅ a),
      LevelCover.sec_cancel ν' Y.m _ _ (by rw [hν', hn']; exact h₅' a)⟩)
  have : ∀ x : Y₂.X, _root_.IsReduced (Y₂.X.presheaf.stalk x) := fun x ↦
    have := (Y₂.normal x).1
    inferInstance
  have := isReduced_of_isReduced_stalk Y₂.X
  have := projProper _ _ _ Y.proj
  have := isDominant_j Y₂
  exact ext_of_isDominant_of_isSeparated Y.s (e.trans e'.symm) Y₂.j (by rw [h₃, h₃', hrr])

end GlobalTheory.TransitionUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOut
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericLB

open Spread

private theorem lbIso_pull_iff_lbIso_pull_pull_of_eq_comp {W X Y : Scheme.{0}} {M N : LB X} (hM : M.IsLB) (hN : N.IsLB) {a : Y ⟶ X}
    (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (M.pull a') (N.pull a') ↔ LBIso ((M.pull a).pull j) ((N.pull a).pull j) := by
  have hM' := pull_isLB hM a'
  have hN' := pull_isLB hN a'
  have hMj := pull_isLB (pull_isLB hM a) j
  have hNj := pull_isLB (pull_isLB hN a) j
  constructor
  · intro h
    exact LBIso.trans hMj hM' hNj (LBIso.symm (lbIso_pull_pull hM j ha))
      (LBIso.trans hM' hN' hNj h (lbIso_pull_pull hN j ha))
  · intro h
    exact LBIso.trans hM' hMj hN' (lbIso_pull_pull hM j ha)
      (LBIso.trans hMj hNj hN' h (LBIso.symm (lbIso_pull_pull hN j ha)))

theorem exists_finset_lbIso {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {B : Scheme.{0}} (pB : B ⟶ Sp k)
    [QuasiCompact pB] [QuasiSeparated pB] {M N : LB B} (hM : M.IsLB) (hN : N.IsLB)
    (H : LBIso (M.pull (pullback.fst pB (spMap (algebraMap k A)))) (N.pull (pullback.fst pB (spMap (algebraMap k A))))) :
    ∃ s : Finset A, LBIso (M.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))))
      (N.pull (pullback.fst pB (spMap (algebraMap k (Algebra.adjoin k (s : Set A)))))) := by
  classical
  obtain ⟨j, g, hg⟩ := exists_lbIso_of_isLimit (D := bcDiagram pB A)
    (π := fun s => bcMap pB (Algebra.adjoin k (s.unop : Set A)).val)
    (w := fun {s t} f => bcMap_comp_of_eq pB _ _ _ fun _ => rfl)
    (hc := isLimitBcCone pB A) (i := Opposite.op ∅)
    (M := M.pull (pullback.fst _ _)) (N := N.pull (pullback.fst _ _))
    (hM := pull_isLB hM _) (hN := pull_isLB hN _)
    (h := (lbIso_pull_iff_lbIso_pull_pull_of_eq_comp hM hN _ (bcMap_fst pB _).symm).mp H)
  exact ⟨j.unop, (lbIso_pull_iff_lbIso_pull_pull_of_eq_comp hM hN ((bcDiagram pB A).map g) (bcMap_fst pB _).symm).mpr hg⟩

theorem exists_denom {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (s : Finset K) : ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      ∃ ψ : Algebra.adjoin R (s : Set K) →+* R', ψ.comp (algebraMap R _) = φ := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) s
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  intro R' _ φ hφ
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hunit : IsUnit (algebraMap R K (b : R)) := IsLocalization.map_units K b
  let g0 : Localization.Away (b : R) →+* K := IsLocalization.Away.lift (b : R) hunit
  have hg0 : ∀ r : R, g0 (algebraMap R _ r) = algebraMap R K r := fun r => IsLocalization.lift_eq _ r
  let g : Localization.Away (b : R) →ₐ[R] K := { g0 with commutes' := hg0 }
  have hinj : Function.Injective g := by
    change Function.Injective g0
    refine (IsLocalization.lift_injective_iff _).mpr fun x y => ?_
    exact ((IsLocalization.injective (Localization.Away (b : R))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hb0)).eq_iff).trans
      (IsFractionRing.injective R K).eq_iff.symm
  have hle : Algebra.adjoin R (s : Set K) ≤ g.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨a, ha⟩ := hb x hx
    refine ⟨IsLocalization.mk' (Localization.Away (b : R)) a ⟨(b : R), Submonoid.mem_powers _⟩, ?_⟩
    show IsLocalization.Away.lift (b : R) hunit _ = x
    unfold IsLocalization.Away.lift
    rw [IsLocalization.lift_mk'_spec]
    rw [ha, Algebra.smul_def]
  refine ⟨((IsLocalization.Away.lift (b : R) hφ).comp
    ((AlgEquiv.ofInjective g hinj).symm : g.range →ₐ[R] Localization.Away (b : R)).toRingHom).comp
    (Subalgebra.inclusion hle).toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.lift_eq _ r

end GenericLB

theorem lbIso_generic_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M N : LB B), QuasiCompact pB → QuasiSeparated pB → M.IsLB → N.IsLB → LBIso (M.pull (pullback.fst pB (spMap (algebraMap R K)))) (N.pull (pullback.fst pB (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → LBIso (M.pull (pullback.fst pB (spMap φ))) (N.pull (pullback.fst pB (spMap φ))) := by
  intro R K _ _ _ _ _ _ B pB M N hqc hqs hM hN H
  have := hqc
  have := hqs
  obtain ⟨s, hs⟩ := GenericLB.exists_finset_lbIso pB hM hN H
  obtain ⟨f, hf0, hf⟩ := GenericLB.exists_denom (R := R) s
  refine ⟨f, hf0, fun R' _ φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hf R' φ hφ
  have key : spMap φ = spMap ψ ≫ spMap (algebraMap R (Algebra.adjoin R (s : Set K))) := by
    rw [spMap_comp_ring, hψ]
  exact Spread.lbIso_pull_comp
    (pullback.lift (pullback.fst pB (spMap φ)) (pullback.snd _ _ ≫ spMap ψ)
      (by rw [pullback.condition, key, Category.assoc]))
    (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm hs

end GlobalTheory
end
end

