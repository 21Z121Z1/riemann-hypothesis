import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0009

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CharOf
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (x : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ x) = T (cmp i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp

private theorem adj_rT {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (r : ℝ)
    (T : Module.End ℂ (Sm E a)) (hT : ∀ X φ, lie E a X (T φ) = T (lie E a X φ)) (X : GlobalTheory.CuspRep.Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) : smAdj Ξ r X (T.rTensor _ x) = T.rTensor _ (smAdj Ξ r X x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v =>
    simp only [smAdj, adj_apply, smA_apply, smB_apply, map_sub, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hT,
      LinearMap.map_smul_of_tower]

private theorem cocl_app {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (r : ℝ)
    {n : ℕ} (e : Fin n → Herm E a)
    (T : Module.End ℂ (Sm E a)) (hT : ∀ X φ, lie E a X (T φ) = T (lie E a X φ)) :
    ∀ {q : ℕ} (ω : Co Ξ q), Coclosed (smAdj Ξ r) e ω → Coclosed (smAdj Ξ r) e (app T ω)
  | 0, _, _ => trivial
  | _ + 1, ω, h => by
    have h' : del (smAdj Ξ r) e ω = 0 := h
    show del (smAdj Ξ r) e (app T ω) = 0
    refine AlternatingMap.ext fun X => ?_
    have h2 := congrArg (fun η => T.rTensor (Fin Ξ.d → ℂ) (η X)) h'
    simp only [del_apply, map_sum, AlternatingMap.zero_apply, map_zero] at h2
    simp only [del_apply, app_apply, adj_rT Ξ r T hT, AlternatingMap.zero_apply, h2]

theorem UpperTheory.V.Cj.H.charOf :
    UpperTheory.V.Cj.H.CharOf := by
  intro E _ _ _ a ha n e he Ξ r m hm q ω h1 h2 h3 h4 X i t u
  have hL := (sqLie E a r).2
  obtain ⟨-, -, c3, c4⟩ := capSm E a Ξ t u
  have hx := wigSm E a Ξ (sqSub E a r) hL t (m t) (hm t) u q ω h1 h2 h4
  have hv : Val (sqSub E a r) (app (cap t u - ((m t).map (u + ·)).prod • 1) ω) := fun Y j => by
    rw [app_apply, cmp_rT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ (c4 _ hL _ (h4 Y j)) (Submodule.smul_mem _ _ (h4 Y j))
  have hc := cocl_app Ξ r e (cap t u - ((m t).map (u + ·)).prod • 1) (fun Y φ => by
    have := LinearMap.congr_fun (c3 Y).eq φ
    simp only [Module.End.mul_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, this]) ω h3
  have h0 := (sqOrth E a ha n e he Ξ r q).1 _ hv hc hx
  have h5 := congrArg (fun η : Co Ξ q => cmp i (η X)) h0
  simp only [app_apply, cmp_rT, AlternatingMap.zero_apply, map_zero, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h5
  exact sub_eq_zero.1 h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PerLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.perLim :
    UpperTheory.V.Cj.H.PerLim := by
  intro E _ _ _ a U Ξ q ω hω h0 hl
  have hc := (coneConvex E a).1
  have hn : (cone E a).Nonempty := ⟨_, hOne_mem_cone⟩
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have key : ∀ k, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (ω k) w.1 ∧ (∀ γ, (geo ho U Ξ).act q γ w = w) ∧
      (geo ho U Ξ).dOm q w = 0 := fun k => by
    have hv : ∀ X, LeftInv (ω k X) ∧ RightInv U (ω k X) := fun X => (levelVal E a U Ξ _).1 ((hω k).val X)
    obtain ⟨w, hw, hw0⟩ := corrFwd E a U Ξ q (ω k) (hω k).equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, hw0 s⟩⟩
    have hw' : Corr U Ξ (ω k) w'.1 := hw
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [h0 k] at h
    exact ⟨w', hw', fun γ => (corrInv E a ho U Ξ q _ _ hw').1 (fun X => (hv X).1) γ,
      (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)⟩
  choose w hw hi hd0 using key
  obtain ⟨c, hz, hlim⟩ := zigLim _ _ _ _ (geo ho U Ξ) hc hn q 0 (fun k _ => w k)
    (fun k => ⟨fun γ _ _ => (hi k γ).symm, fun x hx => by simp [hd, hx, Finset.sum_range_succ]⟩)
    (fun k _ _ => hd0 k) (fun _ _ => corrLim E a ho U Ξ q ω w hw hl)
  exact ⟨c, fun k => ⟨ho, w k, hw k, hz k⟩, fun x hx => hlim x (by omega)⟩
end

