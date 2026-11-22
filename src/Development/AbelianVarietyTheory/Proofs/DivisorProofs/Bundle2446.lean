import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialEvaluationsOfMemKernelSymmetricPair
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KerAxes

theorem triv_of_local_evc {S : Scheme.{0}} {G T : Over S} [GrpObj G] (hG : IsAbelianScheme G)
    {P : LB (G ⊗ G).left} (hP : P.IsLB) (h2 : Triv (ev P (𝟙 G) (1 : G ⟶ G))) (x : T ⟶ G)
    (hloc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over S) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ x) g = 0) :
    Triv (ev P (snd G T ≫ x) (fst G T)) := by
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (snd G T ≫ x) (fst G T))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (G ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (snd G T ≫ x) (fst G T)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd G T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hG T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, lift_snd_assoc, Category.id_comp, lift_fst]
    exact evc_one_right hP h2 x
  · intro p
    obtain ⟨V, hV, hz⟩ := hloc p
    refine ⟨V, hV, ?_⟩
    let U := (snd G T).left ⁻¹ᵁ V
    let Y : Over S := Over.mk (U.ι ≫ (G ⊗ T).hom)
    let i : Y ⟶ G ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, ← Category.assoc]
    exact hz Y _ _ (fun z ↦ z.2)

theorem triv_of_memKL_pair : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a b : T ⟶ G), GlobalTheory.MemKL (G ⊗ G) P (lift a b) → (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (snd G T ≫ b) (fst G T)).left).Gen, t.IsGen) := by
  intro R _ _ G _ hG P hP h1 h2 hs T a b hx
  have hs' : (swap P).IsLB := pull_isLB hP _
  have h1' : Triv (ev P (1 : G ⟶ G) (𝟙 G)) := h1
  have h2' : Triv (ev P (𝟙 G) (1 : G ⟶ G)) := h2
  have add1 := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hG hG hP h1' h2')
  have add2 := (isAdditive_iff hs').1 (CubeNoeth.isAdditive_swap_of_triv_axes hG hG hP h1' h2')
  have symm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP v u = evc hP u v := by
    intro Y u v
    have e := congrArg (CechPic.pull (lift v u).left) ((cls_eq_iff hP hs').2 hs)
    exact e.trans (evc_swap hP hs' v u)
  have loc : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∀ (Y : Over (Sp R)) (t : Y ⟶ T) (g : Y ⟶ G),
      (∀ z, t.left z ∈ V) → evc hP (t ≫ a) g = 0 ∧ evc hP (t ≫ b) g = 0 := by
    intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    refine ⟨V, hV, fun Y t g ht ↦ ?_⟩
    have mk : ∀ u v : Y ⟶ G, evc hP ((t ≫ a) * u) ((t ≫ b) * v) = evc hP u v := by
      intro u v
      have e := pull_mul_eq hP hTV t ht (lift u v)
      have q : (t ≫ lift a b) * lift u v = lift ((t ≫ a) * u) ((t ≫ b) * v) := by
        ext <;> simp [MonObj.mul_comp]
      rw [q] at e
      exact e
    have e0 := mk 1 1
    rw [_root_.mul_one, _root_.mul_one, evc_one_left hP h1'] at e0
    constructor
    · have e1 := mk 1 g
      rw [_root_.mul_one, evc_one_left hP h1'] at e1
      have s := add2 Y (t ≫ b) g (t ≫ a)
      rw [evc_swap hP hs', evc_swap hP hs', evc_swap hP hs'] at s
      rw [s, e0, zero_add] at e1
      exact e1
    · have e3 := mk g 1
      rw [_root_.mul_one, evc_one_right hP h2'] at e3
      have s := add1 Y (t ≫ a) g (t ≫ b)
      rw [s, e0, zero_add] at e3
      rw [symm]
      exact e3
  refine ⟨triv_of_local_evc hG hP h2' a fun p ↦ ?_, triv_of_local_evc hG hP h2' b fun p ↦ ?_⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).1⟩
  · obtain ⟨V, hV, h⟩ := loc p
    exact ⟨V, hV, fun Y t g ht ↦ (h Y t g ht).2⟩

end GlobalTheory.KerAxes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadings
section
set_option autoImplicit false

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

namespace GlobalTheory.Unframe

theorem lUnif_moveR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) (hw : ∀ i σ, w i σ ∈ Subgroup.center G) (hU : R.LUnif) :
    (moveR R w).LUnif := by
  intro i σ
  obtain ⟨h1, h2, h3⟩ := hU i σ
  have hl : ∀ x, (R.FW i).ρ (w i σ)⁻¹ ((R.FW i).ρ (w i σ) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hr : ∀ x, (R.FW i).ρ (w i σ) ((R.FW i).ρ (w i σ)⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hc : ∀ g x, (R.FW i).ρ (w i σ) ((R.FW i).ρ g x) = (R.FW i).ρ g ((R.FW i).ρ (w i σ) x) := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.1 (hw i σ) g, map_mul, Module.End.mul_apply]
  refine ⟨fun n b hb => ?_, ?_, fun g x => ?_⟩
  · have hinj : Function.Injective ((R.FW i).ρ (w i σ)) := Function.LeftInverse.injective hl
    exact h1 n (fun k => (R.FW i).ρ (w i σ) (b k)) (hb.map' _ (LinearMap.ker_eq_bot.2 hinj))
  · refine top_le_iff.1 (h2 ▸ Submodule.span_mono ?_)
    rintro _ ⟨x, rfl⟩
    exact ⟨(R.FW i).ρ (w i σ)⁻¹ x, congrArg ((R.FW i).j σ) (hr x)⟩
  · have h := h3 g ((R.FW i).ρ (w i σ) x)
    rw [← hc] at h
    exact h

end GlobalTheory.Unframe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleDescendsOnTripleOverlaps
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
namespace GlobalTheory.LBDescent.CocycleTensor

theorem appLE_congr_hom {A B : Scheme.{0}} {g₁ g₂ : A ⟶ B} (hg : g₁ = g₂) (U : B.Opens) (W : A.Opens)
    (e₁ : W ≤ g₁ ⁻¹ᵁ U) (e₂ : W ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U W e₁ = g₂.appLE U W e₂ := by
  subst hg; rfl

theorem germ_appLE_gm {A B : Scheme.{0}} (g : A ⟶ B) {U U' : B.Opens} (W : A.Opens) (e : W ≤ g ⁻¹ᵁ U)
    (hUU' : U ≤ U') (w : A) (hw : w ∈ W) (a : Γ(B, U')ˣ) :
    (A.presheaf.germ W w hw).hom ((g.appLE U W e).hom (res hUU' a).val) = (gm g w U' a).val :=
  (TopCat.Presheaf.germ_res_apply A.presheaf (homOfLE e) w hw ((g.app U).hom (res hUU' a).val)).trans
    ((gm_val g w U (e hw) (res hUU' a)).symm.trans (congrArg Units.val (gm_res g w hUU' (e hw) a)))

set_option maxHeartbeats 1600000 in
theorem cocycle_tensor_of_pointwise : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V V₀ : Y.Opens), IsAffineOpen V₀ →
    ∀ (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
      (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∀ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      (∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b) →
      Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) *
          Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) := by
  intro X Y f _ V V₀ hV₀ h hle c hc e he
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hcond : ∀ z : ↥(pullback f f), f ((pullback.fst f f) z) = f ((pullback.snd f f) z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hq : ∀ w : ↥(Triple f), (pullback.snd f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w) = (pullback.fst f f) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) w) := fun w => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have h1 : (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) ≤ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := fun z hz => by
    show f ((pullback.fst f f) z) ∈ V₀
    rw [hcond]; exact hz
  have hleG : ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ≤ (pullback.fst (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) := fun w hw => by
    show f ((pullback.snd f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w)) ∈ V₀
    rw [hq]; exact hw
  have hp1 : pr13 f ≫ (pullback.fst f f) = (pullback.fst (pullback.snd f f) (pullback.fst f f)) ≫ (pullback.fst f f) := pullback.lift_fst _ _ _
  have hp2 : pr13 f ≫ (pullback.snd f f) = (pullback.snd (pullback.snd f f) (pullback.fst f f)) ≫ (pullback.snd f f) := pullback.lift_snd _ _ _
  have h13 : ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ≤ pr13 f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := fun w hw => by
    show f ((pullback.fst f f) (pr13 f w)) ∈ V₀
    have e13 : (pullback.fst f f) (pr13 f w) = (pullback.fst f f) ((pullback.fst (pullback.snd f f) (pullback.fst f f)) w) :=
      (Scheme.Hom.comp_apply _ _ w).symm.trans ((congrArg (fun g => g w) hp1).trans (Scheme.Hom.comp_apply _ _ w))
    rw [e13]
    exact h1 (hleG hw)
  have h2 : (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) ≤ (pullback.fst f f) ⁻¹ᵁ f ⁻¹ᵁ V := h1.trans hle
  have hP := Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback (pullback.snd f f) (pullback.fst f f)) inferInstance
    (hV₀.preimage f) ((hV₀.preimage f).preimage (pullback.fst f f)) le_rfl hleG
  have e1 : ∀ s : Γ(X, f ⁻¹ᵁ V₀), e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom s) = 1 ⊗ₜ s := fun s => by
    rw [e.symm_apply_eq, he, map_one, _root_.one_mul]
  have e2 : ∀ s : Γ(X, f ⁻¹ᵁ V₀), e.symm (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom s) = s ⊗ₜ 1 := fun s => by
    rw [e.symm_apply_eq, he, map_one, _root_.mul_one]
  let m₁ : Γ(pullback f f, (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ⟶ CommRingCat.of ((Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) :=
    CommRingCat.ofHom ((Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))).toRingHom.comp (e.symm.toRingHom.comp ((pullback f f).presheaf.map (homOfLE h).op).hom))
  let m₂ : Γ(pullback f f, (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) ⟶ CommRingCat.of ((Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) :=
    CommRingCat.ofHom ((Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))).toRingHom.comp e.symm.toRingHom)
  have cond : (pullback.snd f f).app (f ⁻¹ᵁ V₀) ≫ m₁ = (pullback.fst f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) le_rfl ≫ m₂ := by
    ext s
    show (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom s)) = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) le_rfl).hom s))
    rw [Scheme.Hom.appLE_eq_app, e1, e2]
    simp
  let Ψ := hP.desc m₁ m₂ cond
  have hΨ1 : ∀ y, Ψ.hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom y) = m₁.hom y := fun y =>
    congrArg (fun k => k.hom y) (hP.inl_desc m₁ m₂ cond)
  have hΨ2 : ∀ y, Ψ.hom (((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom y) = m₂.hom y := fun y =>
    congrArg (fun k => k.hom y) (hP.inr_desc m₁ m₂ cond)
  have ka : ∀ a : Γ(X, f ⁻¹ᵁ V₀), ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a) =
      ((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a) := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom a) ((Scheme.Hom.appLE_comp_appLE (pr13 f) (pullback.fst f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) le_rfl h13).trans
      ((appLE_congr_hom hp1 (f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) _ _).trans (Scheme.Hom.appLE_comp_appLE (pullback.fst (pullback.snd f f) (pullback.fst f f)) (pullback.fst f f) (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h1 hleG).symm))
  have kb : ∀ b : Γ(X, f ⁻¹ᵁ V₀), ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b) =
      ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b) := fun b => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom b) ((Scheme.Hom.appLE_comp_appLE (pr13 f) (pullback.snd f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h h13).trans
      ((appLE_congr_hom hp2 (f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) _ _).trans (Scheme.Hom.appLE_comp_appLE (pullback.snd (pullback.snd f f) (pullback.fst f f)) (pullback.snd f f) (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h le_rfl).symm))
  have ra : ∀ a : Γ(X, f ⁻¹ᵁ V₀), ((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a) =
      ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a := fun a => by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun k => k.hom a) (Scheme.Hom.appLE_map (pullback.fst f f) h1 (homOfLE h).op)
  have hΨ3 : ∀ t, Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (e t)) = (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      rw [he, map_mul, map_mul, ka, kb, hΨ1, hΨ2]
      show (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback.fst f f).appLE (f ⁻¹ᵁ V₀) ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) h1).hom a))) *
        (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) h).hom b)) = _
      rw [ra, e1, e2]
      simp
  have hABC : ((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val * ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val =
      ((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val := by
    apply TopCat.Presheaf.section_ext (Triple f).sheaf ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀))
    intro w hw
    have hw1 : (pullback.fst (pullback.snd f f) (pullback.fst f f)) w ∈ (pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀) := hleG hw
    have hw13 : pr13 f w ∈ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) := h13 hw
    have key := congrArg Units.val (hc w (hle (h1 hw1)))
    show ((Triple f).presheaf.germ ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) w hw).hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val * ((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val) =
      ((Triple f).presheaf.germ ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) w hw).hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val)
    rw [Scheme.Hom.app_eq_appLE]
    refine (RingHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (germ_appLE_gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) _ hleG h2 w hw c) (germ_appLE_gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) _ _ hle w hw c)).trans
      ((Units.val_mul _ _).symm.trans (key.trans (germ_appLE_gm (pr13 f) _ h13 hle w hw c).symm))
  have hA : (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pullback.fst (pullback.snd f f) (pullback.fst f f)).appLE ((pullback.snd f f) ⁻¹ᵁ (f ⁻¹ᵁ V₀)) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) hleG).hom (res h2 c).val) := by
    have hres : ((pullback f f).presheaf.map (homOfLE h).op).hom (res h2 c).val = (res hle c).val := by
      show ((pullback f f).presheaf.map (homOfLE h).op).hom (((pullback f f).presheaf.map (homOfLE h2).op).hom c.val) =
        ((pullback f f).presheaf.map (homOfLE hle).op).hom c.val
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    exact (congrArg (fun y => (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (e.symm y)) hres).symm.trans (hΨ1 _).symm
  have hB : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pullback.snd (pullback.snd f f) (pullback.fst f f)).app (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)).hom (res hle c).val) := (hΨ2 _).symm
  have hC : (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀))) (e.symm (res hle c).val) = Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom (res hle c).val) := by
    exact (hΨ3 (e.symm (res hle c).val)).symm.trans (congrArg (fun y => Ψ.hom (((pr13 f).appLE (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀) ((pullback.snd (pullback.snd f f) (pullback.fst f f)) ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀)) h13).hom y)) (e.apply_symm_apply _))
  exact (congrArg₂ (· * ·) hA hB).trans ((map_mul Ψ.hom _ _).symm.trans ((congrArg Ψ.hom hABC).trans hC.symm))

end GlobalTheory.LBDescent.CocycleTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqOfGermsPinchingSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem unit_eq_of_germs_glues : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), i' ≫ p = p' ≫ i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (V : X.Opens) (u v : Γ(X, V)ˣ), (∀ x' : X', p x' ∈ V → gm p x' V u = gm p x' V v) → (∀ z : Z, i z ∈ V → gm i z V u = gm i z V v) → u = v := by
  intro X X' Z Z' p i i' p' hc hG V u v hp hi
  have ep : (p.app V).hom u.val = (p.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext X'.sheaf (p ⁻¹ᵁ V)
    intro x hx
    have h := congrArg Units.val (hp x hx)
    rwa [gm_val _ x V hx, gm_val _ x V hx] at h
  have ei : (i.app V).hom u.val = (i.app V).hom v.val := by
    apply TopCat.Presheaf.section_ext Z.sheaf (i ⁻¹ᵁ V)
    intro z hz
    have h := congrArg Units.val (hi z hz)
    rwa [gm_val _ z V hz, gm_val _ z V hz] at h
  have key : ∀ (f g : Z' ⟶ X) (_ : f = g) (O : Z'.Opens) (e : O ≤ f ⁻¹ᵁ V) (e' : O ≤ g ⁻¹ᵁ V),
      f.appLE V O e = g.appLE V O e' := by
    intro f g hfg O e e'; subst hfg; rfl
  have hag : (i'.appLE (p ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left).hom ((p.app V).hom u.val) =
      (p'.appLE (i ⁻¹ᵁ V) (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right).hom ((i.app V).hom u.val) := by
    have e1 := Scheme.Hom.comp_appLE i' p V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left
    have e2 := Scheme.Hom.comp_appLE p' i V (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_right
    have e3 := key _ _ hc (i' ⁻¹ᵁ (p ⁻¹ᵁ V) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ V)) inf_le_left inf_le_right
    rw [e1, e2] at e3
    have := congrArg (fun f => f.hom u.val) e3
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  exact Units.ext ((hG V _ _ hag).unique ⟨rfl, rfl⟩ ⟨ep.symm, ei.symm⟩)

end GlobalTheory.PinchLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F]

def unitObj (𝔠 : FracId F) (n : ℕ) : ObjClass 𝔠 := fun R _ _ ↦ IsUnit (n : R)

def levObj (𝔠 : FracId F) (N : ℕ) : ObjClass 𝔠 := fun R _ X ↦ IsUnit (N : R) ∧ Nonempty (X.Level N)

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitOfTestPointEstimateStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_of_test_point_estimate : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → ∀ u : A, (∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ‖(φ u : ℂ_[p]) - 1‖ < 1) → u - 1 ∈ (Ideal.span {(p : A)}).radical := by
  first | exact @GlobalTheory.FlatModel.sub_one_mem_radical_of_isTest | exact GlobalTheory.FlatModel.sub_one_mem_radical_of_isTest | (intros; apply GlobalTheory.FlatModel.sub_one_mem_radical_of_isTest <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRatioOnChartOverlapStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_ratio_on_chart_overlap : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (A : Type) [CommRing A] (w : Sp A ⟶ X) (a1 : cR h x →+* A) (a2 : cR h y →+* A), IsOpenImmersion w → spMap a1 ≫ cξ h x = w → spMap a2 ≫ cξ h y = w → Set.range w = Set.range (cξ h x) ∩ Set.range (cξ h y) → ∀ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical → (∀ (χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A)), χ1.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap (cR h y) _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (cu h y : Localization.Away (p : cR h y)) = χ1 (cu h x : Localization.Away (p : cR h x))) → ∃ u' : Γ(X, Uc h x ⊓ Uc h y)ˣ, RatioProp h x y u' := by
  first | exact @GlobalTheory.UnitGlueTransport.ratioProp_of_chart | exact GlobalTheory.UnitGlueTransport.ratioProp_of_chart | (intros; apply GlobalTheory.UnitGlueTransport.ratioProp_of_chart <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulArrowVacuaProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitVacuum_eq_smul_arrowVacua_product : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ (fun _ => True) : Set _) = orderingsOnSpW G i j →
      ∀ f, IsVacO W.ψ W.θ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (fun τ => -W.cart (.grid (i + 1) (j + 1)) τ) (frSum AV AV₁).cart
        (G.Λ (.grid (i + 1) (j + 1))) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacA ρ i j := by
  first | exact @GlobalTheory.TopFlip.VacRouteBig.vac_eq_smul_vacA | exact GlobalTheory.TopFlip.VacRouteBig.vac_eq_smul_vacA | (intros; apply GlobalTheory.TopFlip.VacRouteBig.vac_eq_smul_vacA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevel
section
set_option autoImplicit false

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.UnramCover

theorem unramPts_deep : Hypotheses2 → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T →
    InR D j → Y.Good e o → UnramPts Y.d.Xo₂ Y.d.c₂ (badPrimes T.Q.H Y.d.l₂) := by
  intro hP D T j Y e o hL hj hY
  have hLaws := GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hL hj hY
  obtain ⟨-, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hL.pins j hj
  have h6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  exact GlobalTheory.T.unramified_points_good_level hP _ T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ (by omega)
    (Or.inr (Or.inr ⟨by omega, hLaws.line⟩)) hLaws.good

end GlobalTheory.UnramCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_bound_holds : WtN := by
  first | exact @GlobalTheory.CovTop.WtShape.wtN | exact GlobalTheory.CovTop.WtShape.wtN | (intros; apply GlobalTheory.CovTop.WtShape.wtN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionKernelEqBaseOnRealUnitaryPointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_kernel_eq_base_on_realUnitaryPoints : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ u ∈ GinfC (Vc D i), ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ω (u, 1) f = R.ωP i A.μ0 (u, 1) f := by
  first | exact @GlobalTheory.RealTwistKer.weil_kernel_real | exact GlobalTheory.RealTwistKer.weil_kernel_real | (intros; apply GlobalTheory.RealTwistKer.weil_kernel_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiDescentDvrTraceLocalisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

theorem zariski_descent_heart : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  have hA : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := GlobalTheory.T.exists_normal_finiteType_subring_in_valuationSubring
  have hB : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K) (V : ValuationSubring L) [IsDiscreteValuationRing V] (R : Subring K) [IsIntegrallyClosed R], (∀ a, c a ∈ R) → R ≤ (V.comap φ).toSubring → ∀ t : Finset L, (∀ x ∈ t, x ∈ V ∧ ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ (V.comap φ).nonunits) → ∀ r : R, (r : K) ∈ (V.comap φ).nonunits → r ∈ p := GlobalTheory.T.height_le_one_of_goingDown_zariski
  have hC : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) → ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) → ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := GlobalTheory.T.exists_div_of_center_height_le_one'
  have hD : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := GlobalTheory.T.essFiniteType_of_localization_finiteType_complex
  intro K L _ _ φ c hfin V _ hc t ht htV
  obtain ⟨R, hcR, hft, hRE, hnoeth, hic, hfr, htR⟩ := hA K L φ c hfin V hc t ht htV
  have hB' := hB K L φ c V R hcR hRE t (fun x hx => ⟨(ht x hx).1, htR x hx⟩) htV
  have hC' := hC K R (V.comap φ) hRE hB'
  exact hD K c R hcR (V.comap φ) hc hRE hft hC'
end GlobalTheory
end

