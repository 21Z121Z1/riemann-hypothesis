import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3645
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.BaseChangeMapRingAct
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3648
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3637

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFil
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount.LieZFil

theorem omega_sq {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) :
    D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
  rw [← D.tr_eq, ← D.nm_eq]; ring

theorem end_sq {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (h : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) (act (algebraMap (𝓞 D.F) D.O D.ω) h) =
      (D.tr : C) • act (algebraMap (𝓞 D.F) D.O D.ω) h - (D.nm : C) • h := by
  have e := congrArg (fun x => act (algebraMap (𝓞 D.F) D.O x) h) (omega_sq D)
  simp only [map_mul, map_sub, map_intCast, Module.End.mul_apply, LinearMap.sub_apply] at e
  rw [e]
  simp [Module.End.intCast_apply, Int.cast_smul_eq_zsmul]

theorem rho_part_eig {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {C H : Type*} [CommRing C] [AddCommGroup H]
    [Module C H] (act : D.O →+* Module.End C H) (ρ : C) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0) (y : H) :
    act (algebraMap (𝓞 D.F) D.O D.ω) ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) -
      ρ • ((act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - ρ) • 1) y) = 0 := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, end_sq]
  have hn : (D.nm : C) = ρ * (D.tr - ρ) := by linear_combination hρ
  rw [hn]
  module

theorem sum_mem_fil {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {C : Type} [CommRing C] [IsLocalRing C] (β : R →+* C)
    {s : Sp C ⟶ Sp R} (hs : s = spMap β) (o : GlobalTheory.UPel.HT.Obj b N s) {r : ℕ} (lam : Fin r → C)
    (c : Fin r → 𝓞 D.F) (hlam : ∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) (y : HdR o.A) :
    ∑ l, lam l • GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O (c l))
      ((GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O D.ω) -
        ((D.tr : C) - β b.ρ) • 1) y) ∈ Fil o.A := by
  set act := GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act with hact
  set u := (act (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : C) - β b.ρ) • 1) y with hu
  have hfil : ∀ (x : D.O) {h : HdR o.A}, h ∈ Fil o.A → act x h ∈ Fil o.A := fun x h hh => by
    haveI := o.act.hom x
    exact push_mem_Fil (o.act.act x) hh
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hω : act (algebraMap (𝓞 D.F) D.O D.ω) u - β b.ρ • u ∈ Fil o.A := by
    rw [hu, rho_part_eig act (β b.ρ) hρ y]; exact zero_mem _
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N C β s hs o u hω
  set c' := fun l => algebraMap (𝓞 D.F) D.O (c l)
  have h1 : ∀ l, act (c' l) u - ∑ i, act (c' l) (w i) ∈ Fil o.A := fun l => by
    rw [← map_sum, ← map_sub]; exact hfil _ hsum
  have h2 : ∀ i, ∑ l, lam l • act (c' l) (w i) ∈ Fil o.A := fun i => by
    have e : ∑ l, lam l • act (c' l) (w i) = ∑ l, lam l • (act (c' l) (w i) - β (b.t i (c l)) • w i) +
        (∑ l, lam l * β (b.t i (c l))) • w i := by
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_sub, mul_smul]; abel
    rw [e, hlam i, zero_smul, add_zero]
    exact sum_mem fun l _ => Submodule.smul_mem _ _ (hw i (c l))
  have e : ∑ l, lam l • act (c' l) u = ∑ l, lam l • (act (c' l) u - ∑ i, act (c' l) (w i)) +
      ∑ i, ∑ l, lam l • act (c' l) (w i) := by
    rw [Finset.sum_comm (f := fun i l => lam l • act (c' l) (w i)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.smul_sum, ← smul_add, sub_add_cancel]
  show ∑ l, lam l • act (c' l) u ∈ Fil o.A
  rw [e]
  exact add_mem (sum_mem fun l _ => Submodule.smul_mem _ _ (h1 l)) (sum_mem fun i _ => h2 i)

theorem dualNumber_local (k : Type) [Field k] : IsLocalRing (DualNumber k) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    by_cases h : TrivSqZeroExt.fst x = 0
    · right
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [h]
    · left
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact isUnit_iff_ne_zero.2 h

end GlobalTheory.HTCount.LieZFil

namespace GlobalTheory.HTCount

open LieZFil in
set_option maxHeartbeats 800000 in

theorem lieZ_mem_fil_and_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  intro p _ D R _ b N k _ t o₀ β ht o' m' z hz
  constructor
  · induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      exact sum_mem_fil β ht o₀ lam c hlam y'
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · have hbc := GlobalTheory.HTRealise.isBC_constMor o₀.ab
    suffices H : ∀ z ∈ lieZ o₀ β, hbc.bcMap z ∈ liftFil (epsDP k) m'.cart by
      refine ⟨hbc.bcMap z, H z hz, fun c => ?_⟩
      rw [(hbc.corr_iff.2 rfl) c]
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hE : ∀ (x : D.O) (h : HdR o₀.A), crysToDR (epsDP k) m'.cart (hbc.bcMap (crysAct o₀ x h)) =
        GlobalTheory.HTSummand.crysAct (dp0 (DualNumber k)) (𝟙 _) o'.act x (crysToDR (epsDP k) m'.cart (hbc.bcMap h)) := by
      intro x h
      haveI := o₀.act.hom x
      haveI := o'.act.hom x
      have e1 : hbc.bcMap (crysAct o₀ x h) =
          push (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.act.act x) (hbc.bcMap h) := by
        rw [← hbc.corr_iff]
        exact GrpMor.Corr.push (m := constMor o₀.A) (constMor o₀.A) (o₀.act.act x) (o₀.act.act x) (by rfl)
          (hbc.corr_iff.2 rfl)
      have e2 := crysToDR_push (epsDP k) m'.cart m'.cart (o₀.act.act x) (o'.act.act x) (m'.act x).symm (hbc.bcMap h)
      exact (congrArg (crysToDR (epsDP k) m'.cart) e1).trans e2
    have hs : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
      rw [ht]; unfold spMap; rw [← Spec.map_comp]; rfl
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, lam, c, y, ⟨y', rfl⟩, hlam, rfl⟩ := hx
      have hlam' : ∀ i, ∑ l, algebraMap k (DualNumber k) (lam l) *
          ((algebraMap k (DualNumber k)).comp β) (b.t i (c l)) = 0 := fun i => by
        simp only [RingHom.comp_apply, ← map_mul, ← map_sum, hlam i, map_zero]
      haveI : IsLocalRing (DualNumber k) := dualNumber_local k
      have key := sum_mem_fil ((algebraMap k (DualNumber k)).comp β) hs o' (fun l => algebraMap k _ (lam l)) c hlam'
        (crysToDR (epsDP k) m'.cart (hbc.bcMap y'))
      rw [liftFil, Submodule.mem_comap]
      convert key using 2
      simp only [map_sum, map_smulₛₗ, hE, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_sub, RingHom.comp_apply, map_intCast, RingHom.id_apply, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.HTCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffDualNumberGraphReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

theorem crysRed_pull_constMor_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).pull ((constMor A₀).pull c) = c := by
  rw [GrpMor.pull_pull (constMor A₀) (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀)
    (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun _ ↦ rfl) (by simp) c]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

set_option maxHeartbeats 1000000 in

theorem mem_Fil_iff_exists_graphFil_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀) :
    y ∈ Fil A₀ ↔ ∃ d ∈ graphFil A₀ f,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  constructor
  · intro hy
    obtain ⟨d, hd⟩ := exists_crys hA y (f y)
    refine ⟨d, ⟨y, hy, 0, zero_mem _, fun c ↦ by rw [hd c]; simp⟩, fun c ↦ ?_⟩
    obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TrivSqZeroExt.fst_zero]
    | add a b ha hb => simp only [map_add, ha, hb, TrivSqZeroExt.fst_add]
    | tmul a c =>
      rw [liftSemi_tmul, map_smulₛₗ, map_smul, crysRed_pull_constMor_pull, map_smul, hd c]
      simp
  · rintro ⟨d, ⟨x, hx, y', -, e⟩, hc⟩
    have : y = x := LinearMap.ext fun c ↦ by
      have h1 := hc ((constMor A₀).pull c)
      rw [crysRed_pull_constMor_pull, e c] at h1
      simpa using h1
    exact this ▸ hx

end GlobalTheory.HTRealise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFilHtObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

theorem red_pull_constMorV_pull {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀]
    (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem eq_of_liftSemi_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) (π : C →+* K)
    (Q : M' →ₛₗ[π] M) (e : M' →ₗ[C] C) (y : M →ₗ[K] K) (hQ : ∀ c, Q (P c) = c)
    (he : ∀ c, π (e (P c)) = y c) (c' : M') : y (Q c') = π (e c') := by
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, map_add, hu, hv]
  | tmul r c =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, hQ, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, he]

theorem corr_of_fst {k : Type} [Field k] {d : ℕ} (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (y : HdR A₀) (hc : ∀ c, (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom
      (e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c)) = y c) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl A₀).Corr e y :=
  eq_of_liftSemi_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) A₀ hA (GlobalTheory.FODef.sqZero k (Fin d → k))
    (GlobalTheory.FODef.constMorV k (Fin d → k) A₀)).2 _ _ e y (red_pull_constMorV_pull A₀) hc

theorem fil_iff_red_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ (GlobalTheory.HTGlue.glueFil o₀.A f), (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ _ d f _ y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, corr_of_fst o₀.A o₀.ab e y fun c => ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, hz, he⟩, hcorr⟩
    have hxy : y = x := LinearMap.ext fun c => by
      have h1 := hcorr ((GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).pull c)
      rw [red_pull_constMorV_pull, he c] at h1
      simpa using h1
    exact hxy ▸ hx

end GlobalTheory.HTGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem red_constPull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c :=
  (GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀))
    (fun r ↦ by simp [TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c).trans
    (Subtype.ext (IsMor.pullCohomologyOne_id _ _))

theorem corr_crysRedMor_iff (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) (y : HdR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y ↔
      ∀ c, y c = TrivSqZeroExt.fst (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)) := by
  constructor
  · intro H c
    have := H ((GlobalTheory.FODef.constMorV k V A₀).pull c)
    rw [red_constPull] at this
    exact this
  · intro H c'
    have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)
    obtain ⟨z, rfl⟩ := hm.2 c'
    induction z with
    | zero => simp only [map_zero]
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | tmul r c =>
      rw [liftSemi_tmul]
      have h1 := (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull.map_smulₛₗ r
        ((GlobalTheory.FODef.constMorV k V A₀).pull c)
      refine (congrArg y h1).trans ?_
      rw [red_constPull, map_smul, H c]
      have h2 := e.map_smul r ((GlobalTheory.FODef.constMorV k V A₀).pull c)
      rw [h2]
      exact (TrivSqZeroExt.fst_mul r _).symm

theorem mem_fil_iff_exists_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d f y
  constructor
  · intro hy
    obtain ⟨e, he, hc⟩ := exists_mem_glueFil o₀.A o₀.ab f hy
    refine ⟨e, he, (corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).2 fun c ↦ ?_⟩
    rw [hc c]
    simp
  · rintro ⟨e, ⟨x, hx, z, -, he⟩, hc⟩
    have hxy : y = x := LinearMap.ext fun c ↦ by
      rw [(corr_crysRedMor_iff (Fin d → k) o₀.A o₀.ab e y).1 hc c, he c]
      simp
    exact hxy ▸ hx

end GlobalTheory.HTGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianSmallSectionsKeyInequalityStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_hermitian_small_sections_key_inequality : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  first | exact @GlobalTheory.HSNefCore.key_ineq | exact GlobalTheory.HSNefCore.key_ineq | (intros; apply GlobalTheory.HSNefCore.key_ineq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenySquareCompatCompQuasiInvStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (exact GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverse
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open GlobalTheory.CechPic

theorem relAmple_diag_root_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → Out.RelAmple B (P'.pull (lift (𝟙 B) (𝟙 B)).left) := by
  intro p _ D R _ b N c Y _ s o B _ _ ψ ψ' hp hc hB hq P' hP' hiso _
  obtain ⟨e, rfl⟩ := hc
  have hu : IsUnit (((p ^ e : ℕ)) : Γ(Y, ⊤)) := by
    have h := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_natCast] at h
    rw [Nat.cast_pow]
    exact h.pow e
  have hq' : IsQuasiInv (p ^ e) ψ' ψ := ⟨hq.2.1, hq.1, hq.2.2.2, hq.2.2.1⟩
  have hfin := (isFinite_etale_surjective_of_isQuasiInv Y B o.A (p ^ e) ψ' ψ hB o.ab hu hq').1
  have := hB.proper
  have := o.ab.proper
  have hL := hP'.1
  have hD := pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left
  have a₁ := GlobalTheory.RootDiagAmple.relAmple_pull_of_isFinite ψ' hD o.ample
  refine GlobalTheory.RootDiagAmple.relAmple_of_relAmple_pow (pull_isLB hL _) (pull_isLB hD _)
    (d := p ^ e) (Nat.one_le_pow e p ((Fact.out : p.Prime).pos)) ?_ a₁
  have hpow : (Hecke.lbPow P' (p ^ e)).IsLB := LB.isLB_linComb hL _ _
  have ec := (cls_eq_iff (pull_isLB o.isLB _) hpow).2 hiso
  have ep : cls _ hpow = (p ^ e) • cls P' hL := by
    refine (cls_linComb hL (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1) hpow).trans ?_
    simp [pull_id]
  rw [cls_pull hL, cls_pull hD, cls_pull o.isLB, ← pull_comp]
  have m : ψ'.left ≫ (lift (𝟙 o.A) (𝟙 o.A)).left = (lift (𝟙 B) (𝟙 B)).left ≫ Hecke.sq2 ψ' := by
    rw [Hecke.sq2, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [m, pull_comp, ← cls_pull o.isLB _ (pull_isLB o.isLB _), ec, ep, map_nsmul]

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDual
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.AbDual GlobalTheory.CechPic
open GlobalTheory.SerreTateDef (IsPairRed polBundle)
open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin (IsPolarisation)
open GlobalTheory.BadPt (IsWeilHom)
open GlobalTheory.PerfdLat (dualBaseChange)

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.DualTower

theorem dim_eq_of_isDual {K : Type} [Field K] (A D : AV.AbVar K) (P : LB (A.X ⊗ D.X).left)
    (h : IsDual A.X D.X P) : D.dim = A.dim := by
  obtain ⟨B, _, P₀, _, hdim, hdual, _⟩ := GlobalTheory.dualAbelianScheme _ A.X A.ab
  obtain ⟨e⟩ := GlobalTheory.Published.AbelianDualCrystal.Test.dual_unique hdual h
  have hB := hdim A.dim A.smooth
  have hne : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
  exact (GlobalTheory.relDim_unique_of_iso_grp _ hne B D.X e.hom inferInstance A.dim D.dim hB D.smooth).symm

end GlobalTheory.DualTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndepOfMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaSum_zeta_exponent_indep_of_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (t₁ : Y₁ → V₁) (δ₁ : I → Y₁ → Y₁) (𝔪₁ : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : Y₁ → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (t₂ : Y₂ → V₂) (δ₂ : I → Y₂ → Y₂) (𝔪₂ : GlobalTheory.GSep.GMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : Y₂ → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  first | exact @GlobalTheory.GSep.twistSum_indep | exact GlobalTheory.GSep.twistSum_indep | (intros; apply GlobalTheory.GSep.twistSum_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickPrincipalObjectsIsoUnique
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem actPB_of_zRel : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d _ _ _ hd _ jl n o κ S t c z₁ z₂ act₁ act₂ hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂ hZ₁ hZ₂
  obtain ⟨inc₁, pr₁, hi₁, hp₁, hip₁, hpi₁, hL₁, -, hz₁⟩ := hZ₁
  obtain ⟨inc₂, pr₂, hi₂, hp₂, hip₂, hpi₂, hL₂, -, hz₂⟩ := hZ₂
  have hker : ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔
      x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1 := fun T x =>
    ⟨fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x hx),
     fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x hx)⟩
  obtain ⟨e, he, hinc, hact⟩ := GlobalTheory.T.zarhinTrick_actions_isomorphic h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ pr₂ hdS hA₁ hA₂
    hi₁ hp₁ hip₁ hpi₁ hi₂ hp₂ hip₂ hpi₂ hker
  have hLB := GlobalTheory.T.zarhinTrick_bundle_unique_of_order_linear_iso h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ e hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂
    hi₁ hp₁ hip₁ hpi₁ hL₁ hL₂ he hinc hact
  haveI := he
  refine ⟨e.hom.left, (e.hom ⊗ₘ e.hom).left, isGrpPullback_of_iso e, ⟨?_, ?_⟩, hLB, fun a => ?_, fun o => ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  · rw [Category.id_comp, ← Over.comp_left, hz₁ a, hz₂ a]
    congr 1
    have key := map_list_prod (IsMonHom.monoidHom e.hom (𝟙_ (Over S)))
      (List.ofFn fun k => c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))
    refine key.trans ?_
    rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    show (c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)) ≫ e.hom = _
    rw [Category.assoc, Category.assoc, hact, ← Category.assoc inc₁, hinc]
  · rw [← Over.comp_left, ← Over.comp_left, hact o]

end GlobalTheory.ZarhinFam
end
end

