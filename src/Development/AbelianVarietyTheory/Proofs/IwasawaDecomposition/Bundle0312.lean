import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLabelPartFinrankEqRowsPartFinrank
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamDim

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  let j : V ≃+ Tw.sub s V :=
    { toFun := fun x => ⟨Tw.mk s (x : E), x.2⟩
      invFun := fun y => ⟨Tw.out (y : Tw s E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hi : Function.Bijective (cj s) :=
    ⟨fun a b h => by simpa [cj_cj] using congrArg (cj s) h, fun z => ⟨cj s z, cj_cj s z⟩⟩
  have h := rank_eq_of_equiv_equiv (cj s) j hi (fun r m => by
    apply Subtype.ext
    show r • (m : E) = cj s (cj s r) • (m : E)
    rw [cj_cj])
  unfold Module.finrank
  rw [h]

theorem twSub_inf (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V W : Submodule ℂ E) :
    Tw.sub s (V ⊓ W) = Tw.sub s V ⊓ Tw.sub s W := by
  ext x; exact Iff.rfl

theorem finrank_comap_of_inj {M E : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup E] [Module ℂ E]
    (f : M →ₗ[ℂ] E) (hf : Function.Injective f) (S : Submodule ℂ E) :
    Module.finrank ℂ (S.comap f) = Module.finrank ℂ (S ⊓ LinearMap.range f : Submodule ℂ E) := by
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf (S.comap f)), Submodule.map_comap_eq, inf_comm]

end GlobalTheory.Mem.R3.LamDim

open GlobalTheory.Mem.R3.LamDim in
set_option maxHeartbeats 2000000 in

theorem GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Module.finrank ℂ ((R.Wp3 i p).comap (Y.mj.eW i)) = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i p
  set s := twAt D.what₂.embLL A3.A.v0 with hs

  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Y.mj.eW_norm i x
    rw [hx, norm_zero, zero_pow two_ne_zero] at h1
    have hn : (0 : ℝ) < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have h2 : ‖x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hn.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

  have hrg : LinearMap.range (Y.mj.eW i) = R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [Y.mj.eW_range i, hH.aux.levelW false i (sg0 D A3.A)]

  have hw : LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub s (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      show ((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ) •
        (show R.toRealDat.WS F.lv2 false i (sg0 D A3.A) from (R.toCx3 F).wC false i A3.fam3.base3.v0 y).1 ∈ _
      exact Submodule.smul_mem (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) _
        (show R.toRealDat.WS F.lv2 false i (sg0 D A3.A) from (R.toCx3 F).wC false i A3.fam3.base3.v0 y).2
    · intro x hx
      have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
          Submodule.comap (Tw.mkL s (R.HW i (sg0 D A3.A)).H) (LinearMap.range ((R.toCx3 F).w0C false i)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
      exact hle hx
  have hD := hH.prim.dimParts i p
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have key := CxData.finrank_Ep (R.toCx3 F) F.cr false (hR.wf false) (hR.what₂ false).1 (hR.rowHyp false).h3
    (hR.partsE false) p
  have key2 : Module.finrank D.what₂.LL ((s0Of R F).Ep p) =
      Module.finrank ℂ ((R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) := key
  rw [key2, ← hD, finrank_comap_of_inj _ hinj, hrg, hw]
  show _ = Module.finrank ℂ (Tw.sub s (R.Wp3 i p) ⊓ Tw.sub s (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) : Submodule ℂ _)
  rw [← twSub_inf, finrank_twSub]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators

theorem theta_eq_zero_of_orth {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {F : Type} [AddCommGroup F] [Module K F]
    {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {j : F →ₛₗ[σ] V} {r : Representation K G F} {ρ : G → V →ₗ[ℂ] V} {gE : Representation ℂ G E} {Θ : V →ₗ[ℂ] E}
    (H : Hyp σ j r ρ gE Θ)
    (hRZ : Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint Θ)).comap j : Set F)) =
      LinearMap.range (LinearMap.adjoint Θ))
    (e a : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e)
    (hfix : ∀ y ∈ LinearMap.range Θ, opV σ (fun g => gE g) a y = y) (f : F) (hea : opF r e f = opF r a f)
    (horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint Θ)).comap j ⊓ LinearMap.range (opF r e) : Submodule K F),
      ⟪j z, j f⟫_ℂ = 0) : Θ (j f) = 0 := by
  have h1 : Θ (j (opF r e f)) = Θ (j f) := by
    rw [hea, j_opF H.jr, theta_opV H.sp H.jr H.eq, hfix _ ⟨_, rfl⟩]
  have h2 : j (opF r e f) ∈ LinearMap.range (opV σ ρ e) := ⟨j f, (j_opF H.jr e f).symm⟩
  obtain ⟨u', hu', hθ⟩ := H.dn e he h2
  have hu'' : u' ∈ Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
      LinearMap.range (opF r e) : Submodule K F) : Set F)) := by
    rw [H.ratLev hRZ e he]
    exact hu'
  have h3 : ⟪u', j f⟫_ℂ = 0 := by
    have hle : Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
        LinearMap.range (opF r e) : Submodule K F) : Set F)) ≤ (Submodule.span ℂ {j f})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact horth z hz
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu'')
  obtain ⟨⟨w, rfl⟩, -⟩ := hu'
  have h4 : Θ (LinearMap.adjoint Θ w - j f) = 0 := by
    rw [map_sub, hθ, h1, sub_self]
  have h5 : ⟪LinearMap.adjoint Θ w, LinearMap.adjoint Θ w - j f⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h4, inner_zero_right]
  rw [inner_sub_right, h3, sub_zero, inner_self_eq_zero] at h5
  rw [← h1, ← hθ, h5, map_zero]

theorem opF_lvlIdem_fix {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (H : Subgroup G) (ψ : H →* Kˣ) (v : V)
    (hv : ∀ a : H, ρ a.1 v = ((ψ a : Kˣ) : K) • v) : opF ρ (lvlIdem H ψ) v = v := by
  classical
  rw [opF_eq_lift]
  unfold lvlIdem
  rw [map_sum, LinearMap.sum_apply]
  have : ∀ h : H, MonoidAlgebra.lift K (V →ₗ[K] V) G ρ
      (MonoidAlgebra.single (h : G) ((Nat.card H : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K))) v = (Nat.card H : K)⁻¹ • v := by
    intro h
    rw [MonoidAlgebra.lift_single, LinearMap.smul_apply, hv, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, mul_one]
  rw [Finset.sum_congr rfl fun h _ => this h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_smul]

end GlobalTheory.Mem.ThOrth

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators

set_option maxHeartbeats 4000000 in

theorem thG_eq_zero_of_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y _Z hP hH i t x hx
  have hok := hH.ok
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hP.char hH.aux.ex
  have hM := hc.models
  have hCore : GlobalTheory.Hk3.Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hRZ : (R.toCx3 F).RatZ := (complex_data_conditions_base_level_of_primitive_links hok hH.sep hP.char hH.prim).ratZ
  have H := Formalism.IndefR.CxPass.lift_hypotheses_of_unitary hok hK F.cv (fun _ _ _ _ => rfl) hJ hH.prim.gUnit.2 hH.prim.gEquiv.2 i t
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 := ⟨hok.ok2.conj, hok.ok2.irr, hok.ok2.lifts i t⟩

  have hopE : opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) := by
    let mA : ((R.HW i (sg0 D A3.A)).H →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H) →+
        (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H →ₗ[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) :=
      { toFun := Tw.map (twAt D.what₂.embLL A3.A.v0), map_zero' := LinearMap.ext fun _ => rfl,
        map_add' := fun _ _ => LinearMap.ext fun _ => rfl }
    rw [show Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) = mA (GlobalTheory.Hk3.eH R.toRealDat i) from rfl]
    unfold opV GlobalTheory.Hk3.eH
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => LinearMap.ext fun y => ?_
    show cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y)
    rw [Formalism.IndefR.Links.emb_eq D.what₂.embLL A3.A.v0, cj_cj]
    rfl
  have hθ : ∀ (u : (R.toCx3 F).FLC i t),
      Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
        cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) :=
    fun u => rfl
  have hfix : ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t),
      opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) y = y := by
    rintro _ ⟨u, rfl⟩
    rw [hopE]
    change Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i
      (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u))) =
      (R.toCx3 F).θ' i t u
    rw [hθ, map_smul, hL.2.2.2, ← hθ]
    rfl

  set ℓ := A3.A.fam.lvlA F.P0 F.ψ0 with hℓ
  set f0 := liftForm A3.A F.P0 F.ψ0 i t x with hf0
  have hf0l : f0 = GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ x := rfl
  have hlev : f0 ∈ lvlForms (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ := by
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm]
    exact ⟨x, hf0l.symm⟩
  have hfix0 : opF (A3.A.fam.L i t).r (lvlIdem ℓ.P ℓ.ψ) f0 = f0 := by
    exact opF_lvlIdem_fix (A3.A.fam.L i t).r ℓ.P ℓ.ψ f0 hlev
  have hea : opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ) f0 = opF (A3.A.fam.L i t).r (idemOf A3.A.X) f0 := by
    rw [goodAt, opF_mul, LinearMap.comp_apply, hfix0]
    rfl
  have horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ⊓
      LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _),
      ⟪(R.toCx3 F).jL i t z, (R.toCx3 F).jL i t f0⟫_ℂ = 0 := by
    intro z hz
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) ℓ _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq]
      rfl
    have hz' : z ∈ LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := hZeq ▸ hz
    obtain ⟨c, rfl⟩ := hz'
    rw [← GlobalTheory.Mem.LiftForms.lvlForm_lE hB c]
    refine (hJ i t _ _).trans ?_
    have h0 : Formalism.DivisionValues.hform ((A3.A.fam.L i t).S.lvlH (A3.A.fam.L i t).r ℓ.P ℓ.ψ)
        ((A3.A.fam.L i t).lE ℓ ((R.toCx3 F).Zl i t) *ᵥ c) x = 0 := hx c
    show A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _) = 0
    rw [CSDForm.csumForm_apply, hf0l, GlobalTheory.Mem.LiftForms.csum_lvlForm, h0, mul_zero, map_zero]
  have key := theta_eq_zero_of_orth H (hRZ.2 i t) (goodAt ℓ.X ℓ.P ℓ.ψ) (idemOf A3.A.X)
    (opF_goodAt_idem _ _ hok.ok2.irr _ _) hfix f0 hea horth
  have h2 := congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) key
  rw [hθ, hP.phs i, map_one, one_smul] at h2
  exact h2

end GlobalTheory.Mem.ThOrth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecomposition
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Pointwise

namespace GlobalTheory.LocEmbDec

theorem exists_dec_of_isLocEmb : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (ι ι₂ : Ω →ₐ[K] Kbar v), IsLocEmb A v ι → IsLocEmb A v ι₂ → ∃ σ ∈ Dec (F := K) A, ∀ z, ι₂ z = ι (σ z) := by
  intro K Ω _ _ _ _ _ A v ι ι₂ hι hι₂
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  set e : Ω ≃ₐ[K] ι.fieldRange := AlgEquiv.ofInjectiveField ι with he
  haveI : Normal K ι.fieldRange := Normal.of_algEquiv e
  have hr : (ι₂.comp (e.symm : ι.fieldRange →ₐ[K] Ω)).fieldRange = ι.fieldRange :=
    AlgHom.fieldRange_of_normal _
  have hmem : ∀ z, ι₂ z ∈ ι.fieldRange := fun z => by
    rw [← hr]; exact ⟨e z, by simp⟩
  let f : Ω →ₐ[K] ι.fieldRange := ι₂.codRestrict ι.fieldRange.toSubalgebra hmem
  let σ0 : Ω →ₐ[K] Ω := (e.symm : ι.fieldRange →ₐ[K] Ω).comp f
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective σ0 (Algebra.IsAlgebraic.algHom_bijective σ0)
  have key : ∀ z, ι (σ z) = ι₂ z := fun z => by
    have h1 : ((e (σ z) : ι.fieldRange) : Kbar v) = ι (σ z) := rfl
    rw [← h1]
    show ((e (e.symm (f z)) : ι.fieldRange) : Kbar v) = ι₂ z
    rw [AlgEquiv.apply_symm_apply]; rfl
  refine ⟨σ, ?_, fun z => (key z).symm⟩
  show σ • A = A
  have hA : ∀ x, σ x ∈ A ↔ x ∈ A := fun x => by rw [hι, key, ← hι₂]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hA]
  show σ (σ⁻¹ y) ∈ A ↔ y ∈ A
  rw [← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl

end GlobalTheory.LocEmbDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionNorm

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem isEquiv_valued :
    (valuation (w.adicCompletion E)).IsEquiv
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))

theorem exists_unit_valued_eq :
    ∃ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h : Valued.v ((π : E) : w.adicCompletion E) = WithZero.exp (-1) := by
    rw [w.valuedAdicCompletion_eq_valuation']; exact hπ
  have h0 : ((π : E) : w.adicCompletion E) ≠ 0 := by
    intro h'; rw [h', map_zero] at h; exact WithZero.zero_ne_coe h
  exact ⟨Units.mk0 _ h0, h⟩

theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) : a ≤ WithZero.exp (-1) := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem valued_eq_exp (x : (w.adicCompletion E)ˣ) :
    Valued.v (x : w.adicCompletion E) = WithZero.exp (-ord (w.adicCompletion E) x) := by
  have he := isEquiv_valued w
  obtain ⟨ϖ, hϖ⟩ := exists_unit_valued_eq w
  have hϖ1 : Valued.v (ϖ : w.adicCompletion E) < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hu : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) = uniformizer (w.adicCompletion E) := by
    apply le_antisymm
    · exact le_uniformizer_iff.2 (he.lt_one_iff_lt_one.2 hϖ1)
    · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer (w.adicCompletion E))
      rw [← hy]
      have hy1 : Valued.v y < 1 := he.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
      exact (he y ϖ).2 (hϖ ▸ le_exp_neg_one_of_lt_one hy1)
  have hord : ord (w.adicCompletion E) ϖ = 1 := SmGL.ord_eq_one hu
  let o : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]
  set n := ord (w.adicCompletion E) x
  set u := x * ϖ ^ (-n)
  have hou : o u = 1 := by
    rw [map_mul, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hord, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    show Multiplicative.ofAdd n * Multiplicative.ofAdd (-n) = 1
    rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]
  have hu1 : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 :=
    SmGL.ord_eq_zero_iff.1 (ofAdd_eq_one.1 hou)
  have hv1 : Valued.v (u : w.adicCompletion E) = 1 := he.eq_one_iff_eq_one.1 hu1
  have hx : x = u * ϖ ^ n := by simp [u]
  rw [hx, Units.val_mul, map_mul, hv1, one_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul,
    smul_eq_mul, mul_neg_one]

theorem normV_eq_absNorm : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem norm_eq_zpow (x : (w.adicCompletion E)ˣ) :
    ‖(x : w.adicCompletion E)‖ = ((normV w : ℕ) : ℝ) ^ (-ord (w.adicCompletion E) x) := by
  have key : ∀ (a : ℤ) (h : WithZero.exp a ≠ 0), (WithZero.unzero h).toAdd = a := fun a h => rfl
  rw [FinitePlace.norm_def, valued_eq_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -ord (w.adicCompletion E) x)), key]
  simp [normV_eq_absNorm]

theorem one_lt_normV : 1 < normV w := by
  have := one_lt_resCard (w.adicCompletion E)
  rwa [GlobalTheory.LocLanglands.resCard_eq_normV] at this

theorem valuation_le_iff_norm_le (x y : w.adicCompletion E) :
    valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) y ↔ ‖x‖ ≤ ‖y‖ := by
  have h1 : (1 : NNReal) < (Ideal.absNorm w.asIdeal : NNReal) := by
    rw [← normV_eq_absNorm]; exact_mod_cast one_lt_normV w
  rw [isEquiv_valued w x y, FinitePlace.norm_def, FinitePlace.norm_def, NNReal.coe_le_coe]
  exact (WithZeroMulInt.toNNReal_strictMono h1).le_iff_le.symm

theorem range_map_eq_KO (m : ℕ) :
    (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype).range = KO (w.adicCompletion E) (Fin m) := by
  have he := isEquiv_valued w
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  let e := RingEquiv.subringCongr hO
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨GeneralLinearGroup.map e.symm.toRingHom h, ?_⟩
    ext i j; rfl
  · rintro ⟨h, rfl⟩
    refine ⟨GeneralLinearGroup.map e.toRingHom h, ?_⟩
    ext i j; rfl

end GlobalTheory.CompletionNorm

open GlobalTheory.CompletionNorm in

theorem GlobalTheory.CompletionNorm.norm_nabs_valuation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (∀ x : (w.adicCompletion E)ˣ, ‖(x : w.adicCompletion E)‖ = nabs (w.adicCompletion E) x ∧ ‖(x : w.adicCompletion E)‖ = ((normV w : ℕ) : ℝ) ^ (-ord (w.adicCompletion E) x) ∧ Valued.v (x : w.adicCompletion E) = WithZero.exp (-ord (w.adicCompletion E) x)) ∧ (∀ x y : w.adicCompletion E, valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) y ↔ ‖x‖ ≤ ‖y‖) ∧ ∀ m : ℕ, (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype).range = KO (w.adicCompletion E) (Fin m) := by
  intro E _ _ w
  refine ⟨fun x => ⟨?_, norm_eq_zpow w x, valued_eq_exp w x⟩, valuation_le_iff_norm_le w, range_map_eq_KO w⟩
  rw [norm_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LocLanglands.resCard_eq_normV]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ExtValueGroup

theorem add_le_max {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K)
    (hO : ∀ x, x ∈ O ↔ w x ≤ 1) (x y : K) : w (x + y) ≤ max (w x) (w y) := by
  have key : ∀ x y : K, w x ≤ w y → w (x + y) ≤ w y := by
    intro x y h
    by_cases hy : y = 0
    · subst hy; simpa using h
    have hp : 0 < w y := w.pos hy
    have h1 : x / y ∈ O := by rw [hO, map_div₀, div_le_one hp]; exact h
    have h2 : x / y + 1 ∈ O := O.add_mem _ _ h1 O.one_mem
    rw [hO, div_add_one hy, map_div₀, div_le_one hp] at h2
    exact h2
  rcases le_total (w x) (w y) with h | h
  · exact (key x y h).trans (le_max_right _ _)
  · rw [add_comm]; exact (key y x h).trans (le_max_left _ _)

theorem sum_lt {K ι : Type} [Field K] (w : AbsoluteValue K ℝ)
    (hw : ∀ x y, w (x + y) ≤ max (w x) (w y)) (f : ι → K) (c : ℝ) (hc : 0 < c) (s : Finset ι)
    (h : ∀ j ∈ s, w (f j) < c) : w (∑ j ∈ s, f j) < c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hw _ _).trans_lt (max_lt (h a (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem exists_eq_of_sum_eq_zero {K ι : Type} [Field K] (w : AbsoluteValue K ℝ)
    (hw : ∀ x y, w (x + y) ≤ max (w x) (w y)) (f : ι → K) (s : Finset ι) (hs : s.Nonempty)
    (hf : ∀ j ∈ s, f j ≠ 0) (h0 : ∑ j ∈ s, f j = 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ w (f i) = w (f j) := by
  classical
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => w (f j)) hs
  by_contra hc
  push Not at hc
  have h1 : w (∑ j ∈ s.erase i, f j) < w (f i) := by
    refine sum_lt w hw f _ (w.pos (hf i hi)) _ fun j hj => ?_
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.1 hj
    exact lt_of_le_of_ne (hmax j hjs) (hc j hjs i hi hji)
  rw [← Finset.add_sum_erase s f hi] at h0
  have h2 : ∑ j ∈ s.erase i, f j = - f i := by linear_combination h0
  rw [h2, w.map_neg] at h1
  exact lt_irrefl _ h1

theorem log_adicAbv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0) :
    ∃ z : ℤ, Real.log (NumberField.HeightOneSpectrum.adicAbv F v a) =
      (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : v.valuation F a ≠ 0 := by simpa using ha
  rw [NumberField.HeightOneSpectrum.adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  refine ⟨Multiplicative.toAdd (WithZero.unzero h0), ?_⟩
  push_cast
  rw [Real.log_zpow]

theorem log_w_rat (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
    (α : AlgebraicClosure F) (hα : α ≠ 0) :
    ∃ (m : ℕ) (z : ℤ), 0 < m ∧
      (m : ℝ) * Real.log (e.w α) = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  obtain ⟨p, hp, hp0⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := F) α)
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hp0
  have hc : ∀ j ∈ p.support, p.coeff j ≠ 0 := fun j hj => Polynomial.mem_support_iff.1 hj
  have hne : ∀ j ∈ p.support, algebraMap F (AlgebraicClosure F) (p.coeff j) ≠ 0 := fun j hj => by
    simpa using hc j hj
  obtain ⟨i, hi, j, hj, hij, h⟩ := exists_eq_of_sum_eq_zero e.w (add_le_max e.w e.O e.mem_O) _ p.support
    (Polynomial.support_nonempty.2 hp) (fun j hj => mul_ne_zero (hne j hj) (pow_ne_zero _ hα)) hp0
  obtain ⟨zi, hzi⟩ := log_adicAbv v _ (hc i hi)
  obtain ⟨zj, hzj⟩ := log_adicAbv v _ (hc j hj)
  have hl := congrArg Real.log h
  rw [map_mul, map_mul, map_pow, map_pow,
    Real.log_mul (e.w.pos (hne i hi)).ne' (pow_pos (e.w.pos hα) _).ne',
    Real.log_mul (e.w.pos (hne j hj)).ne' (pow_pos (e.w.pos hα) _).ne',
    Real.log_pow, Real.log_pow, e.w_alg, e.w_alg, hzi, hzj] at hl
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, zi - zj, by omega, ?_⟩
    rw [Nat.cast_sub hlt.le]; push_cast; linear_combination -hl
  · refine ⟨i - j, zj - zi, by omega, ?_⟩
    rw [Nat.cast_sub hlt.le]; push_cast; linear_combination hl

end GlobalTheory.ExtValueGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelGroupFaceLevelIffFlagGroupStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_group_face_level_iff_flag_group : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_red_R → ∀ (b : Bool) (t : T) (κ : GA D D.sp.X'), κ ∈ GfC D.sp.X' → ((κ ∈ levS _ R.βX (datXP R t (R.levR F b)) ↔ ∃ hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q, (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P) ∧ ∀ (hq : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hp : (R.B.R t).act_tie.red ⟨_, hq⟩ ∈ (F.lvl b).P), levChi _ R.βX (datXP R t (R.levR F b)) κ = ((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hq⟩ : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hp⟩ : D.what₂.LLˣ) : D.what₂.LL)) := by
  first | exact @GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff | exact GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff | (intros; apply GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff <;> assumption)
end

