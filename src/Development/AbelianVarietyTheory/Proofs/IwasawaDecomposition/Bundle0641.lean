import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsUniqueSecIsFnAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConsta
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.ArcThetaFib

theorem val_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    (res h u).val = (X.presheaf.map (homOfLE h).op).hom u.val := rfl

theorem val_linComb {X Y : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) (e : Y ⟶ X)
    (jM : PUnit → M.ι) (jL : PUnit → L.ι) :
    ((LB.linCombIso w (K := PUnit) (fun _ => e) (fun _ => 1)).s (jM, jL)).val =
      (Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ => e) jM PUnit.unit))
        (inf_le_right.trans (LB.wchart_le L (fun _ => e) jL PUnit.unit)) :
          LB.wchart M (fun _ => e) jM ⊓ LB.wchart L (fun _ => e) jL ≤
            e ⁻¹ᵁ ((LB.div M L).U (jM PUnit.unit, jL PUnit.unit)))).op).hom
        ((e.app _).hom (w.s (jM PUnit.unit, jL PUnit.unit)).val) := by
  show Units.val (∏ _k : PUnit, (res _ (pullU e _ (w.s (jM _k, jL _k)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  rfl

theorem val_rigPullOf {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (F : G'.left ⟶ G.left) (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (j : PUnit → PUnit → L.ι) :
    ((rigPullOf F f he L r).s j).val = ((𝟙_ (Over S')).left.presheaf.map (homOfLE (rigPull_le F f he L j)).op).hom
      ((f.app _).hom (r.s (fun _ => j PUnit.unit PUnit.unit)).val) := rfl

theorem maps_val {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (F : G'.left ⟶ G.left) (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left)
    (r : LB.Gen (L.pull (eSec G))) (L' : LB G'.left) (w : LB.Iso L' (L.pull F)) (a : LB.Gen (L'.pull (eSec G')))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) a (rigPullOf F f he L r))
    (t : Sp ℂ ⟶ (𝟙_ (Over S')).left) (j : L.ι) (i : L'.ι) (hj : ⊤ ≤ (t ≫ eSec G' ≫ F) ⁻¹ᵁ L.U j)
    (hi : ⊤ ≤ (t ≫ eSec G') ⁻¹ᵁ L'.U i) :
    valAt' (t ≫ f) ((L.pull (eSec G)).U (fun _ => j)) (r.s (fun _ => j)).val =
      valAt' (t ≫ eSec G') ((LB.div (L.pull F) L').U (fun _ => j, i)) (w.s (fun _ => j, i)).val *
        valAt' t ((L'.pull (eSec G')).U (fun _ => i)) (a.s (fun _ => i)).val := by
  have hB : ⊤ ≤ t ⁻¹ᵁ ((L.pull F).pull (eSec G')).U (fun _ _ => j) :=
    fun q hq => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => hj hq
  have hA : ⊤ ≤ t ⁻¹ᵁ (L'.pull (eSec G')).U (fun _ => i) := fun q hq => Set.mem_iInter.2 fun _ => hi hq
  have hBA : ⊤ ≤ t ⁻¹ᵁ (((L.pull F).pull (eSec G')).U (fun _ _ => j) ⊓ (L'.pull (eSec G')).U (fun _ => i)) :=
    fun q hq => ⟨hB hq, hA hq⟩
  have e := congrArg (fun v => valAt' t _ (Units.val v)) (h (fun _ _ => j, fun _ => i))
  dsimp only at e
  rw [val_res, GlobalTheory.ThetaFn.valAt'_res t _ hBA, val_rigPullOf] at e
  erw [GlobalTheory.ThetaFn.valAt'_res t _ hB] at e
  erw [GlobalTheory.ThetaFn.valAt'_app] at e
  rw [Units.val_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul] at e
  erw [val_linComb, GlobalTheory.ThetaFn.valAt'_res t _ hBA] at e
  refine e.trans ?_
  congr 1
  rw [val_res]; exact GlobalTheory.ThetaFn.valAt'_res t _ hBA _

theorem maps_val' {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (F : G'.left ⟶ G.left) (f : S' ⟶ S)
    (he : eSec G' ≫ F = f ≫ eSec G) (L : LB G.left)
    (r : LB.Gen (L.pull (eSec G))) (L' : LB G'.left) (w : LB.Iso L' (L.pull F)) (a : LB.Gen (L'.pull (eSec G')))
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) a (rigPullOf F f he L r))
    (t : Sp ℂ ⟶ S') (j : L.ι) (i : L'.ι) (hj : ⊤ ≤ (t ≫ eSec G' ≫ F) ⁻¹ᵁ L.U j)
    (hi : ⊤ ≤ (t ≫ eSec G') ⁻¹ᵁ L'.U i) :
    valAt' (t ≫ f) ((L.pull (eSec G)).U (fun _ => j)) (r.s (fun _ => j)).val =
      valAt' (t ≫ eSec G') ((LB.div (L.pull F) L').U (fun _ => j, i)) (w.s (fun _ => j, i)).val *
        valAt' t ((L'.pull (eSec G')).U (fun _ => i)) (a.s (fun _ => i)).val :=
  maps_val F f he L r L' w a h t j i hj hi

set_option maxHeartbeats 1600000 in

theorem const_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∀ (w : ℂ), Ha.T < w.im → ∀ (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → ∀ K : ℂ, (∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (K * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z)) → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → c₀ = K := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hGE hty hPI hχ hgen hM w hw w₀ w₁ h₀ h₁ K hK yF hyF1 hyF2 hz x φ hkey u c₀ hrig hfib hfn
  obtain ⟨he, wx, hg, hpb, hwgen, hrigx, hfun, -⟩ := hkey
  have hP := Ha.period w hw
  have hw1 : φ ≫ Y.t.G.hom = (x.P.A.hom ≫ yF) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    rw [hpb.1.w, Category.assoc]; rfl
  obtain ⟨Φ, hΦ1, hΦ2⟩ : ∃ Φ : x.P.A.left ⟶ Y.oF.t.G.left, Φ ≫ Y.m.φ = φ ∧ Φ ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF :=
    ⟨_, Y.m.cart.1.lift_fst _ _ hw1, Y.m.cart.1.lift_snd _ _ hw1⟩
  have hfib' : ∀ z, ∃ ψ : Sp ℂ ⟶ Y.oF.t.G.left, ψ ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left ∧
      ψ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ ∧ (u.ex z).left ≫ φ = ψ ≫ Y.m.φ := hfib
  choose ψ hψ1 hψ2 hψ3 using hfib'
  have hexA : ∀ z, (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := fun z => Over.w (u.ex z)
  have hψF : ∀ z, ψ z ≫ Y.oF.t.G.hom = yF := fun z => by
    apply pullback.hom_ext
    · rw [Category.assoc, ← Y.m0.toSABMap.cart.1.w, ← Category.assoc, hψ1 z, hyF1]
      exact Over.w (Fu.ex Ha.i (Ha.Pw w) z)
    · rw [Category.assoc, hψ2 z, hyF2]
  have hψ : ∀ z, ψ z = (u.ex z).left ≫ Φ := fun z => by
    apply Y.m.cart.1.hom_ext
    · rw [Category.assoc]; exact (hψ3 z).symm.trans (by rw [hΦ1])
    · rw [hψF z, Category.assoc, hΦ2, ← Category.assoc, hexA z]; exact (Category.id_comp yF).symm
  have hu0' : (u.ex 0).left = eSec x.P.A := by
    rw [(u.ker 0).2 u.Λ.zero_mem]
    change (toUnit _ ≫ η[x.P.A]).left = η[x.P.A].left
    rw [toUnit_unit, Category.id_comp]
  obtain ⟨hsym, hpos⟩ := Θ.pos w hw
  obtain ⟨hd, v₀, hv₀⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g Θ.c₁ Θ.c₂ Θ.half₁ Θ.half₂).1 _ hsym hpos
  have hθd : Differentiable ℂ (fun v => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v)) :=
    hd.comp (LinearMap.toContinuousLinearMap (Matrix.mulVecLin Θ.h)).differentiable
  have hθ : ∃ v, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec v) ≠ 0 := by
    refine ⟨∑ k, v₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)), ?_⟩
    have : Θ.h.mulVec (∑ k, v₀ k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = v₀ := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' v₀).symm
    rwa [this]
  obtain ⟨fr, hfr⟩ := Θ.frame w hw
  have hKf := hK fr hfr
  let pt : Sp ℂ := IsLocalRing.closedPoint ℂ
  have top_iff : ∀ {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens), ⊤ ≤ f ⁻¹ᵁ U ↔ f pt ∈ U := fun f U =>
    ⟨fun h => h (x := pt) trivial, fun h q _ => (Subsingleton.elim (α := PrimeSpectrum ℂ) pt q) ▸ h⟩
  have exch : ∀ {X : Scheme.{0}} {L : LB X}, L.IsLB → ∀ y : X, ∃ i, y ∈ L.U i := fun hL y =>
    TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, _ by rw [hL.cover]; trivial)
  set y₀ := (u.ex 0).left pt with hy₀
  obtain ⟨i, hi⟩ := exch x.P.isLB y₀
  obtain ⟨j, hj⟩ := exch Y.t.PP.isLB (φ y₀)
  obtain ⟨k, hk⟩ := exch Y.oF.t.PP.isLB (Φ y₀)
  obtain ⟨j₀, hj₀⟩ := exch Xo.univ.t.PP.isLB (Y.m0.toSABMap.φ (Φ y₀))
  let Ω : x.P.A.left.Opens := Φ ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) ⊓ Φ ⁻¹ᵁ ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) ⊓ ((LB.div (Y.t.PP.L.pull φ) x.P.L).U (fun _ => j, i)) ⊓ (Φ ≫ Y.m0.toSABMap.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U j₀
  have hΦφ : ∀ y, Y.m.φ (Φ y) = φ y := fun y => by rw [← hΦ1]; rfl
  have hy₀Ω : y₀ ∈ Ω := by
    refine ⟨⟨⟨⟨Set.mem_iInter.2 fun _ => hj₀, hk⟩, ⟨Set.mem_iInter.2 fun _ => ?_, hk⟩⟩, ⟨Set.mem_iInter.2 fun _ => hj, hi⟩⟩, hj₀⟩
    show Y.m.φ (Φ y₀) ∈ Y.t.PP.L.U j
    rw [hΦφ]; exact hj
  let N : Set (Fin g → ℂ) := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ Ω}
  have hN : N ∈ nhds (0 : Fin g → ℂ) := ((u.hol Ω 1).1).mem_nhds ((top_iff _ _).2 hy₀Ω)
  have hle : (Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) := by
    intro y hy
    refine ⟨?_, Set.mem_iInter.1 hy.1 PUnit.unit⟩
    show (φ ≫ Y.t.G.hom) y ∈ M.U
    rw [hpb.1.w]
    exact hz (x := x.P.A.hom y) trivial
  have key : ∀ z ∈ N, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) *
      (c₀ * (valAt' ((u.ex z).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val *
        valAt' (u.ex z).left ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val * u.fr i z) -
       K * (valAt' ((u.ex z).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ z)) = 0 := by
    intro z hzN
    have hz0 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (Φ ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k))) := fun q hq => (hzN hq).1.1.1
    have hz1 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (Φ ⁻¹ᵁ ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k))) := fun q hq => (hzN hq).1.1.2
    have hDx : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((LB.div (Y.t.PP.L.pull φ) x.P.L).U (fun _ => j, i)) := fun q hq => (hzN hq).1.2
    have hUi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i := fun q hq => (hzN hq).1.2.2
    have e : valAt' ((u.ex z).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val *
        valAt' ((u.ex z).left ≫ φ) (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) (M.θ j) =
        valAt' ((u.ex z).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * (K * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z) := by
      have := hKf z (ψ z) j k j₀ (hψ1 z) (hψ2 z) (by rw [hψ z]; exact hz1) (by rw [hψ z]; exact hz0)
      rw [hψ z, Category.assoc, hΦ1] at this
      exact this
    have a2 := GlobalTheory.ThetaFn.valAt'_appLE' (u.ex z).left φ hle hDx (M.θ j)
    rw [hfun (fun _ => j) i hle, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul] at a2
    dsimp only at a2
    have r2 := GlobalTheory.ThetaFn.valAt'_res (u.ex z).left (inf_le_right : ((LB.div (Y.t.PP.L.pull φ) x.P.L).U (fun _ => j, i)) ≤ x.P.L.U i) hDx (x.th.f i)
    rw [hfn i z hUi] at r2
    erw [r2] at a2
    linear_combination valAt' ((u.ex z).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val * a2 + e
  have hη : eSec Y.oF.t.G ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w η[Y.oF.t.G]
  have hψ0 : (u.ex 0).left ≫ Φ = yF ≫ eSec Y.oF.t.G := by
    apply Y.m.cart.1.hom_ext
    · refine ((Category.assoc _ _ _).trans (congrArg _ hΦ1)).trans ?_
      refine (congrArg (· ≫ φ) hu0').trans (he.trans ?_)
      refine Eq.trans ?_ (congrArg (yF ≫ ·) Y.m.cm.e_comm.symm |>.trans (Category.assoc _ _ _).symm)
      rw [Y.m.base, Category.assoc]
      rfl
    · refine ((Category.assoc _ _ _).trans ((congrArg _ hΦ2).trans (((Category.assoc _ _ _).symm).trans
        ((congrArg (· ≫ yF) (hexA 0)).trans (Category.id_comp yF))))).trans ?_
      exact ((Category.comp_id yF).symm.trans (congrArg (yF ≫ ·) hη.symm)).trans (Category.assoc _ _ _).symm
  have memE : ∀ U : x.P.A.left.Opens, y₀ ∈ U → ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ U := fun U h => by
    rw [← hu0']; exact (top_iff _ _).2 h
  have R1 : u.fr i 0 = valAt' (𝟙 (Sp ℂ)) ((x.P.L.pull (eSec x.P.A)).U (fun _ => i)) (x.rig.s (fun _ => i)).val := by
    refine hrig (fun _ => i) fun q hq => Set.mem_iInter.2 fun _ => ?_
    exact memE _ hi hq
  have R2 := maps_val' φ (yF ≫ Y.j) he Y.t.PP.L Y.t.PP.rig x.P.L wx x.rig hrigx (𝟙 _) j i
    (fun q hq => memE (φ ⁻¹ᵁ Y.t.PP.L.U j) hj hq) (fun q hq => memE _ hi hq)
  rw [Category.id_comp, Category.id_comp] at R2
  have R3 := maps_val' Y.m.φ Y.m.cm.e Y.m.cm.e_comm Y.t.PP.L Y.t.PP.rig Y.oF.t.PP.L w₁ Y.oF.t.PP.rig h₁.2 yF j k
    (by rw [← Category.assoc, ← hψ0, Category.assoc, hΦ1]; exact (top_iff _ _).2 hj)
    (by rw [← hψ0]; exact (top_iff _ _).2 hk)
  rw [Y.m.base] at R3
  have R4 := maps_val' Y.m0.toSABMap.φ Y.m0.cm.e Y.m0.cm.e_comm Xo.univ.t.PP.L Xo.univ.t.PP.rig Y.oF.t.PP.L w₀
    Y.oF.t.PP.rig h₀.2 yF j₀ k
    (by rw [← Category.assoc, ← hψ0]; exact (top_iff _ _).2 hj₀)
    (by rw [← hψ0]; exact (top_iff _ _).2 hk)
  rw [Y.m0.base, hyF1] at R4
  have h5 : ⊤ ≤ (Fu.ex Ha.i (Ha.Pw w) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j₀ := by
    rw [← hψ1 0, hψ 0]; exact (top_iff _ _).2 hj₀
  have R5 := hfr.2.2.2.1 j₀ h5
  have hF : valAt' ((u.ex 0).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val *
      valAt' (u.ex 0).left ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val * u.fr i 0 =
      valAt' ((u.ex 0).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ 0 := by
    rw [hψ0, R5, R1, hu0', R4]
    rw [show valAt' (eSec x.P.A) ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val =
      valAt' (eSec x.P.A) ((LB.div (Y.t.PP.L.pull φ) x.P.L).U (fun _ => j, i)) (wx.s (fun _ => j, i)).val from rfl]
    have R3' : valAt' (yF ≫ Y.j) ((Y.t.PP.L.pull (eSec Y.t.G)).U (fun _ => j)) (Y.t.PP.rig.s (fun _ => j)).val = _ := R3
    linear_combination valAt' (yF ≫ eSec Y.oF.t.G) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val * (R3' - R2)
  have hne : valAt' ((u.ex 0).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ 0 ≠ 0 :=
    mul_ne_zero (GlobalTheory.AbelianLetters.valAt'_unit_ne_zero ((u.ex 0).left ≫ Φ)
      ((top_iff ((u.ex 0).left ≫ Φ) _).2 hy₀Ω.1.1.2) _) (hfr.2.1 j₀ 0 h5)
  have cont : ∀ (U : x.P.A.left.Opens) (f : Γ(x.P.A.left, U)), (∀ z ∈ N, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) →
      ContinuousAt (fun z => valAt' (u.ex z).left U f) 0 := fun U f hU =>
    ((u.hol U f).2.differentiableAt (Filter.mem_of_superset hN hU)).continuousAt
  have cΦ : ∀ (U : Y.oF.t.G.left.Opens) (f : Γ(Y.oF.t.G.left, U)), (∀ z ∈ N, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (Φ ⁻¹ᵁ U)) →
      ContinuousAt (fun z => valAt' ((u.ex z).left ≫ Φ) U f) 0 := fun U f hU =>
    (cont _ ((Φ.app U).hom f) hU).congr (Filter.Eventually.of_forall fun z => GlobalTheory.ThetaFn.valAt'_app _ Φ U f)
  have c0 := cΦ ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val (fun z hz q hq => (hz hq).1.1.1)
  have c1 := cΦ ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val (fun z hz q hq => (hz hq).1.1.2)
  have cW := cont ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val (fun z hz q hq => (hz hq).1.2)
  have cu : ContinuousAt (u.fr i) 0 :=
    ((u.fr_hol i).differentiableAt (Filter.mem_of_superset hN fun z hz q hq => (hz hq).1.2.2)).continuousAt
  have cf : ContinuousAt (fr j₀) 0 := by
    refine ((hfr.1 j₀).differentiableAt (Filter.mem_of_superset hN fun z (hz : z ∈ N) => ?_)).continuousAt
    show ⊤ ≤ (Fu.ex Ha.i (Ha.Pw w) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j₀
    rw [← hψ1 z, hψ z]
    exact fun q hq => (hz hq).2
  have hlim := GlobalTheory.ArcQ.AnFrEx.eq_zero_of_mul_eventually (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z))
    (fun z => c₀ * (valAt' ((u.ex z).left ≫ Φ) ((LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k)) (w₀.s (fun _ => j₀, k)).val *
        valAt' (u.ex z).left ((Y.t.PP.L.pull φ).U (fun _ => j) ⊓ x.P.L.U i) (wx.s (fun _ => j, i)).val * u.fr i z) -
       K * (valAt' ((u.ex z).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ z)) hθd hθ
    ((continuousAt_const.mul ((c0.mul cW).mul cu)).sub (continuousAt_const.mul (c1.mul cf)))
    (by filter_upwards [hN] with z hz using key z hz)
  beta_reduce at hlim
  rw [hF] at hlim
  have h2 : (c₀ - K) * (valAt' ((u.ex 0).left ≫ Φ) ((LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k)) (w₁.s (fun _ => j, k)).val * fr j₀ 0) = 0 := by
    linear_combination hlim
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)

end GlobalTheory.ArcThetaFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionUniformisationEqRestrictCharacters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ToricTorsionCompare

theorem units_of_pow_eq_one : ∀ (K : Type) [Field K] (O : ValuationSubring K) (X : Type) [AddCommGroup X] (k : ℕ), 1 ≤ k →
    ∀ (τ : Multiplicative X →* Kˣ), τ ^ k = 1 → ∃ τO : Multiplicative X →* Oˣ, ∀ x, ((τO x : O) : K) = (τ x : K) := by
  intro K _ O X _ k hk τ hτ
  have hpow : ∀ x, (τ x : K) ^ k = 1 := fun x => by
    have := congrArg (fun f => ((f x : Kˣ) : K)) hτ
    simpa [MonoidHom.pow_apply] using this
  have mem : ∀ x, (τ x : K) ∈ O := fun x => by
    rcases O.mem_or_inv_mem (τ x : K) with h | h
    · exact h
    · have h1 : (τ x : K) ^ (k - 1) * (τ x : K) = 1 := by rw [← pow_succ, Nat.sub_add_cancel hk, hpow]
      have h2 : ((τ x : K)⁻¹) ^ (k - 1) = τ x := by rw [inv_pow, inv_eq_of_mul_eq_one_right h1]
      rw [← h2]; exact O.pow_mem h _
  have vi : ∀ x, (τ x : K) * (τ x⁻¹ : K) = 1 := fun x => by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  let f : Multiplicative X → Oˣ := fun x =>
    ⟨⟨τ x, mem x⟩, ⟨τ x⁻¹, mem x⁻¹⟩, Subtype.ext (vi x), Subtype.ext ((mul_comm _ _).trans (vi x))⟩
  exact ⟨MonoidHom.mk' f (fun x y => Units.ext (Subtype.ext (by simp [f]))), fun x => rfl⟩

theorem toric_torsion_eq_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') [CharZero R] [CharZero W], AdmBase R (maximalIdeal R) → AdmBase W (maximalIdeal W) →
    ∀ (g : R →+* W) (m : SABMap t' t (spMap g))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    α.comp ψ = β.comp g → n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
      (O : ValuationSubring F) (φ : W →+* O), IsLocalHom φ →
      (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' _ _ hR hW g m V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ
    hα hb hc hd he hf F _ _ _ _ O φ hφ hφW hgF k hk τ τ' q q' v v' hτ'k hττ' hqy hq hq'y hq' hv hv'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.T.exists_toric_torsion_sections_uniformisation E H R t P hR k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.T.exists_toric_torsion_sections_uniformisation E H W t' P' hW k hk1
  obtain ⟨fR, hfR, -⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H R t P hR F k hk1
  obtain ⟨fW, hfW, -⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H W t' P' hW F k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {G : Type} [CommGroup G] (f : Multiplicative P'.D.toPre.X →* G), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  have hv0 : v = (s F _ τ hτk).left :=
    ((hfR q v).1 hv).trans ((hfR q _).1 (s4 F _ τ hτk q rfl hqy hq)).symm
  have hv0' : v' = (s' F _ τ' hτ'k).left :=
    ((hfW q' v').1 hv').trans ((hfW q' _).1 (s4' F _ τ' hτ'k q' rfl hq'y hq')).symm

  obtain ⟨τO, hτO⟩ := units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl

  let bW : ResidueField W →+* Ω := Ideal.Quotient.lift (maximalIdeal W) β hβ
  obtain ⟨Ω', _, _, σ, κ₀, hσκ⟩ : ∃ (Ω' : Type) (_ : Field Ω') (_ : IsAlgClosed Ω') (σ : Ω →+* Ω')
      (κ₀ : ResidueField O →+* Ω'), σ.comp bW = κ₀.comp (ResidueField.map φ) := by
    letI := bW.toAlgebra
    letI := (ResidueField.map φ).toAlgebra
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (ResidueField W) Ω (ResidueField O))
    letI := Ideal.Quotient.field M
    let q0 : TensorProduct (ResidueField W) Ω (ResidueField O) →+* AlgebraicClosure (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M) :=
      (algebraMap (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M) _).comp (Ideal.Quotient.mk M)
    refine ⟨AlgebraicClosure (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M), inferInstance, inferInstance,
      q0.comp Algebra.TensorProduct.includeLeftRingHom, q0.comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    exact congrArg q0.comp Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  let κ : O →+* Ω' := κ₀.comp (residue O)
  have hκ : σ.comp β = κ.comp φ := by
    ext w
    have := congrArg (fun f => f (residue W w)) hσκ
    change σ (bW (residue W w)) = κ₀ (ResidueField.map φ (residue W w)) at this
    rw [ResidueField.map_residue] at this
    exact this
  have hκloc : IsLocalHom κ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : residue O a = 0 := (residue_eq_zero_iff a).2 ((mem_maximalIdeal a).2 hna)
    have h0 : κ a = 0 := by simp only [κ, RingHom.comp_apply, this, map_zero]
    rw [h0] at ha; exact not_isUnit_zero ha

  obtain ⟨U, hU, hUloc⟩ := IsLocalRing.exists_factor_valuationRing (σ.comp α)
  let u : V →+* U := (σ.comp α).codRestrict U.toSubring hU
  have hwu : U.subtype.comp u = σ.comp α := rfl
  let τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ := (Units.map κ.toMonoidHom).comp τO
  have h'' : τ'' ^ k = 1 := by
    rw [show τ'' ^ k = (Units.map κ.toMonoidHom).comp (τO ^ k) by ext x; simp [τ'']]
    rw [hτOk]; ext; simp
  obtain ⟨τU, hτU⟩ := units_of_pow_eq_one Ω' U _ k hk1 τ'' h''
  have hτUk : τU ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Ω'ˣ) : Ω')) h''
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτU, this]; rfl
  let zU : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of U)).inv.hom.toMonoidHom).comp τU)
  have hzU : ∀ χ, GlobalTheory.UU.chV zU χ = unitOn (τU (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, zU, MulEquiv.apply_symm_apply]; rfl
  have hkU : IsUnit (k : U) := by simpa using hk.map (u.comp ψ)
  let τRU := τU.comp ρm
  have hτRU : τRU ^ k = 1 := by
    exact powc τU hτUk
  have hG1 := GlobalTheory.T.toricTorsionSection_eq_pushed_trait_point_local E H R t P k s s1 s2 s3 _ ρ V ψ tV mV j t₀ m₀ h₀ m₀' hc hd U u hUloc hkU τU τRU hτRU hτUk
    (fun χ => rfl) zU hzU
  have hG2 := GlobalTheory.T.toricTorsionSection_eq_pulled_trait_point_field E H W t' P' k s' s3' R t g m V ψ tV mV Ω α β hβ tΩ n n' j hb hf Ω' σ (κ.comp φ) hκ.symm
    U u U.subtype hwu τU τ'' h'' (fun χ => (hτU χ).symm) zU hzU
  let τRΩ := τ''.comp ρm
  have hτRΩ : τRΩ ^ k = 1 := by
    exact powc τ'' h''
  have hgU : (κ.comp φ).comp g = U.subtype.comp (u.comp ψ) := by
    ext r
    have := congrArg (fun f => σ f) (RingHom.congr_fun he r)
    have h2 := RingHom.congr_fun hκ (g r)
    simp only [RingHom.comp_apply] at this h2 ⊢
    rw [← h2, ← this]; rfl
  have h8 : (s Ω' ((κ.comp φ).comp g) τRΩ hτRΩ).left = spMap U.subtype ≫ (s U (u.comp ψ) τRU hτRU).left :=
    s2 U Ω' _ _ U.subtype τRU hτRU τRΩ hτRΩ hgU (fun χ => (hτU (ρm χ)).symm)

  let τOR := τO.comp ρm
  have hτOR : τOR ^ k = 1 := by
    exact powc τO hτOk
  obtain ⟨e, he'⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk (spMap φ)) (spMap (φ.comp g)) (spMap_comp g φ)
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hxy : s O (φ.comp g) τOR hτOR = e (s' O φ τO hτOk) := by
    refine GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) t.G t.semi.smooth O (spMap (φ.comp g)) k hkO _ _ ?_ Ω' κ hκloc ?_
    · rw [s1, ← map_pow, s1', map_one]
    · rw [he', ← Category.assoc, ← s2' O Ω' φ (κ.comp φ) κ τO hτOk τ'' h'' rfl (fun χ => rfl), hG2,
        ← s2 O Ω' (φ.comp g) ((κ.comp φ).comp g) κ τOR hτOR τRΩ hτRΩ rfl (fun χ => rfl), h8, hG1]
  have hOR : (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) = O.subtype.comp (φ.comp g) := by
    ext r; simp [hgF, hφW]
  have hOW : (algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W)) = O.subtype.comp φ := by
    ext w; simp [hφW]
  rw [hv0, hv0', s2 O F _ _ O.subtype τOR hτOR τ hτk hOR (fun χ => by simp [τOR, hτ, hτO]),
    s2' O F _ _ O.subtype τO hτOk τ' hτ'k hOW (fun χ => by simp [hτO]), hxy, he', Category.assoc]

end GlobalTheory.ToricTorsionCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionFlatLocallyQuasiFiniteStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_flat_locallyQuasiFinite : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 → Flat (torsion G q).hom ∧ LocallyQuasiFinite (torsion G q).hom := by
  first | exact @GlobalTheory.FibreFlatGen.flat_and_locallyQuasiFinite_torsion | exact GlobalTheory.FibreFlatGen.flat_and_locallyQuasiFinite_torsion | (intros; apply GlobalTheory.FibreFlatGen.flat_and_locallyQuasiFinite_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChartLevelsDeterminantMapsValuesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_levels_determinant_maps_values : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∃ dt : ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        Formalism.MainNotions.G.CmpJ.DetTie (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev,
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) β cl, ∃ r : (w.D Z).what₂.LL, (w.D Z).what₂.embLL r =
        (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).tw β).ch
          (((Formalism.MainNotions.G.CmpJ.AgreeLv.formsInTw tt.forms u ((w.D Z).what₂.muAt v) hμ j hj (dt j hj)).K β).y cl) : ℂ) := by
  first | exact @GlobalTheory.Mem.Top.KerTwDet.detTie_vals | exact GlobalTheory.Mem.Top.KerTwDet.detTie_vals | (intros; apply GlobalTheory.Mem.Top.KerTwDet.detTie_vals <;> assumption)
end

