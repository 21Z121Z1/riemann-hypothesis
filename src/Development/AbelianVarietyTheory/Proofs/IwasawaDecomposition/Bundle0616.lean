import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendOfIntegralAtDvr
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenExt
open GlobalTheory.FlagMod

theorem generic_le {X : Scheme.{0}} {G W : X.Opens} (hG : IsAffineOpen G) [IsDomain Γ(X, G)]
    (hW : W ≤ G) (hne : ∃ x, x ∈ W) :
    ⊤ ≤ (spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G))) ≫ tau hG) ⁻¹ᵁ W := by
  intro y _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, hq⟩ := hG.range_fromSpec.ge (hW hx)
  have hq' : q ∈ (tau hG ⁻¹ᵁ W : (Sp Γ(X, G)).Opens) := by
    show hG.fromSpec q ∈ W
    rw [hq]; exact hx
  have hsp : (spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G)))) y ⤳ q := by
    refine (PrimeSpectrum.le_iff_specializes (R := Γ(X, G)) ((spMap (algebraMap Γ(X, G) (FractionRing Γ(X, G)))) y) q).1 ?_
    show Ideal.comap _ y.asIdeal ≤ q.asIdeal
    rw [@Ideal.eq_bot_of_prime _ _ y.asIdeal y.2]
    exact Ideal.comap_bot_le_of_injective _ (IsFractionRing.injective Γ(X, G) (FractionRing Γ(X, G)))
  exact hsp.mem_open (tau hG ⁻¹ᵁ W).isOpen hq'

theorem extend_of_integral_at_dvr : ∀ (X : Scheme.{0}) (G W₀ : X.Opens) (hle : W₀ ≤ G), IsAffineOpen G → IsDomain Γ(X, G) → IsNoetherianRing Γ(X, G) → IsIntegrallyClosed Γ(X, G) → Countable Γ(X, G) → (∃ x, x ∈ W₀) → Function.Injective (resG X hle) ∧ ∀ f₀ : Γ(X, W₀), (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ X), Countable R → ⊤ ≤ z ⁻¹ᵁ G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∃ f : Γ(X, G), resG X hle f = f₀ := by
  intro X G W₀ hle hG hD hN hI hC hne
  let K := FractionRing Γ(X, G)
  let η : Sp K ⟶ X := spMap (algebraMap Γ(X, G) K) ≫ tau hG
  have hηG : ⊤ ≤ η ⁻¹ᵁ G := le_preimage_comp _ (tau_le hG le_rfl)
  have key : ∀ (W : X.Opens) (hW : W ≤ G) (h : ⊤ ≤ η ⁻¹ᵁ W) (a : Γ(X, G)),
      ev η W h (resG X hW a) = algebraMap Γ(X, G) K a := by
    intro W hW h a
    rw [ev_res η hW h hηG, ev_spMap_tau hG]
  have hW₀ : ⊤ ≤ η ⁻¹ᵁ W₀ := generic_le hG hle hne
  refine ⟨fun a b e => IsFractionRing.injective Γ(X, G) K (by rw [← key W₀ hle hW₀, ← key W₀ hle hW₀, e]), ?_⟩
  intro f₀ hf
  have hKc : Countable K := by
    have hs : Function.Surjective (fun p : Γ(X, G) × nonZeroDivisors Γ(X, G) => IsLocalization.mk' K p.1 p.2) :=
      fun x => by
        obtain ⟨p, e⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Γ(X, G)) x
        exact ⟨p, e⟩
    exact hs.countable
  have hint : _root_.IsIntegral Γ(X, G) (ev η W₀ hW₀ f₀) := by
    apply GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring Γ(X, G) K
    intro V hV hBV
    let ι : Γ(X, G) →+* V := (algebraMap Γ(X, G) K).codRestrict V.toSubring hBV
    have hz : ⊤ ≤ (spMap ι ≫ tau hG) ⁻¹ᵁ G := le_preimage_comp _ (tau_le hG le_rfl)
    have hc : (algebraMap V K).comp ι = algebraMap Γ(X, G) K := RingHom.ext fun _ => rfl
    have he : spMap (algebraMap V K) ≫ spMap ι ≫ tau hG = η := by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    have h' : ⊤ ≤ (spMap (algebraMap V K) ≫ spMap ι ≫ tau hG) ⁻¹ᵁ W₀ := by rw [he]; exact hW₀
    obtain ⟨v, hv⟩ := hf V K (spMap ι ≫ tau hG) inferInstance hz h'
    rw [ev_congr he W₀ h' hW₀] at hv
    rw [← hv]
    exact v.2
  obtain ⟨f, hf'⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).1 hint
  refine ⟨f, ext_ev_loc fun p hp => ?_⟩
  obtain ⟨s, hsle, hps⟩ := hG.exists_basicOpen_le ⟨p, hp⟩ (hle hp)
  have hN : ⊤ ≤ η ⁻¹ᵁ X.basicOpen s := generic_le hG (X.basicOpen_le s) ⟨p, hps⟩
  have inj : Function.Injective (ev η (X.basicOpen s) hN) := by
    haveI := hG.isLocalization_basicOpen s
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, e⟩ := IsLocalization.surj (Submonoid.powers s) x
    have h1 : algebraMap Γ(X, G) K a = 0 := by
      rw [← key _ (X.basicOpen_le s) hN a]
      change ev η _ hN (algebraMap Γ(X, G) Γ(X, X.basicOpen s) a) = 0
      rw [← e, map_mul, hx, zero_mul]
    have ha : a = 0 := IsFractionRing.injective Γ(X, G) K (by rw [h1, map_zero])
    have hu : IsUnit (algebraMap Γ(X, G) Γ(X, X.basicOpen s) m) := IsLocalization.map_units _ m
    rw [ha, map_zero] at e
    exact hu.mul_left_eq_zero.1 e
  have hres : resG X hsle (resG X hle f) = resG X hsle f₀ := by
    apply inj
    rw [ev_res η hsle hN hW₀, ev_res η hsle hN hW₀, key W₀ hle hW₀, hf']
  refine ⟨X.basicOpen s, hps, fun S _ z hz hzN => ?_⟩
  rw [← ev_res z hsle hzN hz, ← ev_res z hsle hzN hz (f₀), hres]

end GlobalTheory.GenExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagTorusAlgebraicallyClosed
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ShFam.Horiz

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem carries_of_frameCast (C : FlagCpt Z e) {k : Type} [Field k] {φ : c.F →+* k} {x x' : Sp k ⟶ Z.X} (h : x = x')
    {p : Sp k ⟶ C.Y.X} {g : EigFrame Z φ x} (hc : C.Carries p (frameCast h g)) : C.Carries p g := by
  subst h
  exact hc

theorem y0_specializes (C : FlagCpt Z e) (s₀ : Sp C.Y.Fn) {w : C.Y.X} {ξ : Xo.XF c} (h : C.π w = Z.jQ ξ) :
    (letI := (constF e C.Y).toAlgebra; GlobalTheory.AllWt.ptF C.y0) s₀ ⤳ ξ := by
  letI := (constF e C.Y).toAlgebra
  have := Z.jQ_open
  have h1 : Z.jQ (GlobalTheory.AllWt.ptF C.y0 s₀) = C.π (genericPt C.Y s₀) := by
    have h2 := congrArg (fun f => f s₀) C.y0_x
    simpa only [Scheme.Hom.comp_apply] using h2
  have h2 : genericPt C.Y s₀ ⤳ genericPoint C.Y.X := by
    have h3 : genericPt C.Y s₀ ∈ Set.range (C.Y.X.fromSpecStalk (genericPoint C.Y.X)) := ⟨s₀, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h3
  have h3 : genericPoint C.Y.X ⤳ w := (genericPoint_spec C.Y.X).specializes trivial
  have h4 := (h2.trans h3).map C.π.continuous
  rw [← h1, h] at h4
  exact Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 h4

theorem mem_comp_of_over (C : FlagCpt Z e) {w w' : C.Y.X} {ξ ξ' : Xo.XF c} (h : C.π w = Z.jQ ξ) (h' : C.π w' = Z.jQ ξ')
    (W : Comp Xo c) (hξ : ξ ∈ W.1) : ξ' ∈ W.1 := by
  letI := (constF e C.Y).toAlgebra
  let s₀ : Sp C.Y.Fn := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.Y.Fn)
  let w₀ := GlobalTheory.AllWt.ptF C.y0 s₀
  let W₀ : Comp Xo c := ⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩
  have hc : IsClosed W₀.1 := isClosed_of_mem_irreducibleComponents _ W₀.2
  have h0 : w₀ ∈ W₀.1 := mem_irreducibleComponent
  have h1 : ξ ∈ W₀.1 := (y0_specializes C s₀ h).mem_closed hc h0
  have h2 : ξ' ∈ W₀.1 := (y0_specializes C s₀ h').mem_closed hc h0
  by_cases hne : W₀ = W
  · rw [← hne]; exact h2
  · exact absurd hξ (Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c W₀ W hne) h1)

theorem carriedC_flagTor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → FnAlgClosed Xo c → ∀ k (y : (U.X k).dom), CarriedC (Φ.C k) (U.un k y) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e σ N U Φ hσ hU hF k y
  have hne : ∀ k, (U.X k).dom.Nonempty := fun k => ReciprocityTheory.ChartRestriction.G.PullbackSections.noBase_dom_nonempty (U.X k)
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ N U hσ hU hne hF
  let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have claim : ∀ i (w : (Φ.C i).Y.X) (ξ : Xo.XF c), (Φ.C i).π w = Z.jQ ξ → ξ ∈ (q i).1 := by
    intro i w ξ h
    obtain ⟨x₀, hx₀⟩ := hne i
    obtain ⟨w₁, hw₁⟩ := Φ.label i ⟨x₀, hx₀⟩ s
    rw [Scheme.Hom.comp_apply] at hw₁
    exact mem_comp_of_over (Φ.C i) hw₁ h (q i) (hq i ⟨x₀, hx₀⟩ s)
  let P := U.un k y
  let a := cxOf Z P
  obtain ⟨⟨i, p⟩, ⟨hp, hc⟩, -⟩ := Φ.lifts ℂ σ a.1.1 a.1.2 a.2
  have hs : GlobalTheory.AllWt.ptF (S := CAt σ) P s ∈ (q i).1 := by
    have hp' : p ≫ (Φ.C i).π = GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ := hp
    have h1 : (p ≫ (Φ.C i).π) s = (GlobalTheory.AllWt.ptF (S := CAt σ) P ≫ Z.jQ) s := congrArg (fun f => f s) hp'
    exact claim i (p s) _ (((Scheme.Hom.comp_apply _ _ _).symm.trans h1).trans (Scheme.Hom.comp_apply _ _ _))
  obtain rfl : i = k := by
    by_contra hik
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c (q i) (q k) (fun h => hik (q.injective h))) hs (hq k y s)
  letI := σ.toAlgebra
  unfold CarriedC Carried
  exact ⟨p, hp, carries_of_frameCast (Φ.C i) (Category.assoc _ _ _).symm hc⟩

end GlobalTheory.ShFam.Horiz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqOmegaRatio
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FramePairGram

theorem coef_conj_eq_coOm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin (r - j) => coef X x x' (conjEmb τ.1) b i) =
      (((coOm X hj x τ)⁻¹ * coOm X hj x' τ)ᵀ).submatrix Fin.rev Fin.rev := by
  have hd0 : IsUnit (mat (x0F X) τ).det := (det_x0F X τ).isUnit
  have hd : IsUnit (mat x τ).det := (hx τ).1.isUnit
  have hf : IsUnit (frameCo X hj x τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ hd0).mul hd
  have hN : (frameCo X hj x τ)⁻¹ * frameCo X hj x' τ =
      reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
    simp only [frameCo, inv_reindex]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hd0, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd0]
  have h12 : (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₁₂ = 0 := by
    ext a c
    simp only [toBlocks₁₂, of_apply, reindex_apply, submatrix_apply, Matrix.zero_apply]
    apply PointWell.block_of_moeb_eq X hj hp hx hx' τ h
    · rw [idx_symm_inl, hp]; omega
    · rw [idx_symm_inr, hp]; exact c.2
  have hO : (coOm X hj x τ)⁻¹ * coOm X hj x' τ =
      (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₂₂ := by
    have e : frameCo X hj x' τ = frameCo X hj x τ * reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
      rw [← hN, mul_nonsing_inv_cancel_left _ _ hf]
    have e2 : coOm X hj x' τ = coOm X hj x τ * (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)).toBlocks₂₂ := by
      rw [coOm, coOm, e]
      conv_lhs => rw [← fromBlocks_toBlocks (frameCo X hj x τ),
        ← fromBlocks_toBlocks (reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ)), fromBlocks_multiply,
        toBlocks_fromBlocks₂₂]
      rw [h12, Matrix.mul_zero, zero_add]
    rw [e2, ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_coOm X hj hp hx τ), Matrix.one_mul]
  have cc : conjEmb (conjEmb τ.1) = τ.1 := RingHom.ext fun a => by simp [conjEmb]
  have hcc : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [cc]; exact τ.2
  have hc : conjEmb τ.1 ∉ X.Ψ := fun hc => ((X.cmType τ.1).mp τ.2) hc
  have hs : (⟨conjEmb (conjEmb τ.1), hcc⟩ : X.Ψ) = τ := Subtype.ext cc
  rw [hO]
  ext b i
  have hb := b.2
  have hi := i.2
  have hl : X.p0 - 1 - (i : ℕ) < r ∧ X.p0 - 1 - (b : ℕ) < r := by omega
  simp only [of_apply, submatrix_apply, transpose_apply, coef, dif_neg hc, dif_pos hcc, ent, dif_pos hl, hs,
    toBlocks₂₂, reindex_apply]
  refine congrArg₂ _ (Fin.ext ?_) (Fin.ext ?_) <;> simp [idx_symm_inr, Fin.val_rev, hp] <;> omega

end GlobalTheory.FramePairGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqWeightRatio
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePairGram

theorem coef_eq_coW_change {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom) (hx' : x' ∈ X.dom) (τ : X.Ψ)
    (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) :
    (Matrix.of fun b i : Fin j => coef X x x' τ.1 b i) = (coW X hj x' τ)⁻¹ * coW X hj x τ := by
  have hd' : IsUnit (mat x' τ).det := (hx' τ).1.isUnit
  have hN : frameCo X hj x τ = frameCo X hj x' τ * reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) := by
    simp only [frameCo, reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd']
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hW : coW X hj x τ = coW X hj x' τ * (reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ)).toBlocks₁₁ := by
    unfold coW
    rw [h, hN, moeb_zero]
    generalize frameCo X hj x' τ = g at *
    generalize reindex (idx hj) (idx hj) ((mat x' τ)⁻¹ * mat x τ) = N
    have e11 : (g * N).toBlocks₁₁ = g.toBlocks₁₁ * N.toBlocks₁₁ + g.toBlocks₁₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁]
    have e21 : (g * N).toBlocks₂₁ = g.toBlocks₂₁ * N.toBlocks₁₁ + g.toBlocks₂₂ * N.toBlocks₂₁ := by
      conv_lhs => rw [← fromBlocks_toBlocks g, ← fromBlocks_toBlocks N]
      rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    rw [e11, e21]
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hu']
    abel
  rw [hW, ← Matrix.mul_assoc, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 ((isUnit_iff_isUnit_det _).2 (isUnit_coW X hj hp hx' τ))), Matrix.one_mul]
  ext b i
  have hb : X.p0 + (b : ℕ) < r := by have := b.2; have := X.p0_le; omega
  have hi : X.p0 + (i : ℕ) < r := by have := i.2; have := X.p0_le; omega
  have eb : (idx hj).symm (Sum.inl b) = ⟨X.p0 + b, hb⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (b : ℕ) = X.p0 + b; omega)
  have ei : (idx hj).symm (Sum.inl i) = ⟨X.p0 + i, hi⟩ := Fin.ext (by rw [idx_symm_inl]; show r - j + (i : ℕ) = X.p0 + i; omega)
  simp only [of_apply, coef, dif_pos τ.2, ent, dif_pos (And.intro hb hi), Subtype.coe_eta, toBlocks₁₁, reindex_apply,
    submatrix_apply, eb, ei]

end GlobalTheory.FramePairGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramePointCombinationMatrix
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.FramePairGram

attribute [local instance] Over.cartesianMonoidalCategory

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
  {t : SAB H X} {t' : SAB H X'} {S : Type} [CommRing S] {f : X' ⟶ X}

theorem left_pushE_symm_congr (m : SABMap t' t f) {q q' : Sp S ⟶ X'} (e : q = q') {x₀ x₀' : Sp S ⟶ X}
    (hq : q ≫ f = x₀) (hq' : q' ≫ f = x₀') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x₀ v)
    (hv' : IsTanAtG t x₀' v) :
    (tv ((pushE m q hq).symm (tanOf hv))).left = (tv ((pushE m q' hq').symm (tanOf hv'))).left := by
  subst e
  subst hq
  subst hq'
  rfl

end Generic

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem ptF_eq_of_x_eq {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y.x = y'.x) :
    GlobalTheory.AllWt.ptF y = GlobalTheory.AllWt.ptF y' :=
  pullback.hom_ext ((ptF_fst y).trans (h.trans (ptF_fst y').symm)) ((ptF_snd y).trans (ptF_snd y').symm)

theorem ofFrPt_v_eq {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y.x = y'.x)
    {x : Sp S ⟶ Z.X} (hx : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ genι Z = x) {x' : Sp S ⟶ Z.X}
    (hx' : GlobalTheory.AllWt.ptF y' ≫ Z.jQ ≫ genι Z = x') (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (hv : IsTanAtG Xo.univ.t y'.x (y.u τ i)) :
    (EigFrame.ofFrPt Z y hx).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := by
  show (tv (pushE Z.m (GlobalTheory.AllWt.ptF y) hx
      ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y) (ptF_fst y)).symm (tanOf (t := Xo.univ.t) (y.tan τ i))))).left =
    (tv (pushE Z.m (GlobalTheory.AllWt.ptF y') hx'
      ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y') (ptF_fst y')).symm (tanOf hv)))).left
  rw [left_pushE, left_pushE,
    left_pushE_symm_congr Z.m0.toSABMap (ptF_eq_of_x_eq h) (ptF_fst y) (ptF_fst y') (y.tan τ i) hv]

theorem isComb_ofFrPt {S : Type} [CommRing S] [Algebra c.F S] (y' : FrPt Xo c S) {x' : Sp S ⟶ Z.X}
    (hx' : GlobalTheory.AllWt.ptF y' ≫ Z.jQ ≫ genι Z = x') (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → S)
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAtG Xo.univ.t y'.x w)
    (hc : IsCombAtG Xo.univ.t y'.x (y'.u τ) a w) :
    IsCombAtG Z.t x' ((EigFrame.ofFrPt Z y' hx').v τ) a (tv (lieEquiv Z y' hx' (tanOf hv))).left := by
  have e := (isComb_iff (t := Xo.univ.t) (x := y'.x) (fun b => tanOf (t := Xo.univ.t) (y'.tan τ b)) a (tanOf hv)).1 hc
  refine (isComb_iff (t := Z.t) (x := x') (fun b => lieEquiv Z y' hx' (tanOf (t := Xo.univ.t) (y'.tan τ b))) a
    (lieEquiv Z y' hx' (tanOf hv))).2 ?_
  rw [e, map_sum]
  simp only [map_smul]

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

theorem gram_transport (x : OddPrimesWithRootsOfUnity Z) {σ : c.F →+* ℂ} {p q : CxPts (genStr Z) σ} (e : p = q)
    (F : EigFrame Z σ (p.1 ≫ genι Z)) (G : EigFrame Z σ (q.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (q.1 ≫ genι Z) (G.v τ) (fun a => T a i) (F.v τ i)) :
    x.gram p F τ = Tᴴ * x.gram q G τ * T := by
  subst e
  exact x.gram_change G F τ T h

theorem gram_of_comb (x : OddPrimesWithRootsOfUnity Z) {σ : c.F →+* ℂ} (y y' : FrPt Xo c (CAt σ)) (h : y.x = y'.x) (τ : E →+* ℂ)
    (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hK : ∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) :
    x.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * x.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  refine gram_transport x (cxPt_congr h) _ _ τ K fun i => ?_
  have hv : IsTanAtG Xo.univ.t y'.x (y.u τ i) := h ▸ y.tan τ i
  have hx' : GlobalTheory.AllWt.ptF (S := CAt σ) y' ≫ Z.jQ ≫ genι Z = (cxPt Z y').1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = (cxPt Z y).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have e1 : (cxFrame Z y).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := ofFrPt_v_eq h hx hx' τ i hv
  rw [e1]
  exact isComb_ofFrPt (S := CAt σ) y' hx' τ (fun b => (K b i : CAt σ)) hv (hK i)

end Main

end GlobalTheory.FramePairGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm

namespace GlobalTheory.LineNorm.Add

theorem presents_tens {X Z : Scheme.{0}} [IsIntegral Z] {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (j : Z ⟶ X)
    {D E : CartierDiv Z} {r : (A.pull j).ι → Z.functionFieldˣ} {s : (B.pull j).ι → Z.functionFieldˣ}
    (hr : Presents D (A.pull j) r) (hs : Presents E (B.pull j) s) :
    Presents (D + E) ((CechPic.tens A B).pull j)
      fun i => r (fun _ => (i PUnit.unit).1) * s fun _ => (i PUnit.unit).2 := by
  have cA {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (A.pull j).U fun _ => (i PUnit.unit).1 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1
  have cB {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (B.pull j).U fun _ => (i PUnit.unit).2 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2
  refine ⟨LB.isLB_pull (CechPic.isLB_tens hA hB) j, fun i i' h => ?_,
    fun i x hx => (hr.isEqn _ x (cA hx)).add (hs.isEqn _ x (cB hx))⟩
  have lA := inf_le_inf (cA (i := i)) (cA (i := i'))
  have lB := inf_le_inf (cB (i := i)) (cB (i := i'))
  rw [Units.val_mul, Units.val_mul, hr.isRatSec _ _ (lA h), hs.isRatSec _ _ (lB h), mul_mul_mul_comm,
    ← fnOf_resG lA h, ← fnOf_resG lB h, ← map_mul,
    InducedPull.val_pull_g _ j i i' (InducedPull.inf_le _ j i i')]
  congr 2
  refine Eq.trans ?_ (map_mul _ _ _).symm
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (congrArg _ (InducedPull.val_pull_g A j _ _ (InducedPull.inf_le A j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le A j (fun _ => (i PUnit.unit).1)
      fun _ => (i' PUnit.unit).1) (homOfLE lA).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (A.g (i PUnit.unit).1 (i' PUnit.unit).1).val
  · refine (congrArg _ (InducedPull.val_pull_g B j _ _ (InducedPull.inf_le B j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le B j (fun _ => (i PUnit.unit).2)
      fun _ => (i' PUnit.unit).2) (homOfLE lB).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (B.g (i PUnit.unit).2 (i' PUnit.unit).2).val

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def GivenBy (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) (M : GlobalTheory.TrueGeo.Model Y) (L : LB M.X) (m : ℕ) : Prop :=
  ∃ r : (L.pull M.j).ι → Y.Fnˣ, L.IsLB ∧ Presents (m • Δ) (L.pull M.j) r ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) →
      (m : ℝ) * φ v e y = Real.log (e.w (valAt y.1 (((t (below y.1))⁻¹ ^ m * r i : Y.Fnˣ) : Y.Fn)))

variable {Δ Δ' : Y.Dv} {t t' : Y.X → Y.Fnˣ} {φ φ' : PtFn Y}

theorem GivenBy.pull {M N : GlobalTheory.TrueGeo.Model Y} {L : LB M.X} {m : ℕ} (h : GivenBy Δ t φ M L m) (π : N.X ⟶ M.X)
    (hj : N.j ≫ π = M.j) : GivenBy Δ t φ N (L.pull π) m := by
  obtain ⟨MX, Mp, Mar, Mj, Mpb⟩ := M
  dsimp only at π hj L
  subst hj
  obtain ⟨r, hL, hr, h⟩ := h
  refine ⟨fun i => r fun _ => i PUnit.unit PUnit.unit, LB.isLB_pull hL π,
    InducedPull.presents_pull_pull hL π N.j hr, fun v e y yt i hy hi => ?_⟩
  exact h v e y (yt ≫ π) (fun _ => i PUnit.unit PUnit.unit)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) hy).trans (Category.assoc _ _ _)))
    fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit

theorem unitAt_quot {M : GlobalTheory.TrueGeo.Model Y} {L : LB M.X} {m : ℕ} (ht : ∀ y, Δ.IsEqn y (t y))
    {r : (L.pull M.j).ι → Y.Fnˣ} (hr : Presents (m • Δ) (L.pull M.j) r)
    {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y} {yt : Sp e.O ⟶ M.X} {i : (L.pull M.j).ι}
    (h : spMap e.O.subtype ≫ yt = y.1 ≫ M.j) (hi : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit)) :
    UnitAt (below y.1) (((t (below y.1))⁻¹ ^ m * r i : Y.Fnˣ) : Y.Fn) := by
  have h₂ : below y.1 ∈ (L.pull M.j).U i := OfModel.le_chart M L e y yt h hi trivial
  have := ((ht (below y.1)).nsmul m).iff_unitAt.1 (hr.isEqn _ _ h₂)
  rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this

theorem GivenBy.pow {M : GlobalTheory.TrueGeo.Model Y} {L : LB M.X} {m : ℕ} (ht : ∀ y, Δ.IsEqn y (t y))
    (h : GivenBy Δ t φ M L m) (n : ℕ) : GivenBy Δ t φ M (lbPow L n) (m * n) := by
  obtain ⟨r, hL, hr, h⟩ := h
  have hr' := InducedPow.presents_pow L M.j n hL hr
  refine ⟨fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ n, LB.isLB_linComb hL _ _, ?_,
    fun v e y yt i hy hi => ?_⟩
  · rw [mul_nsmul]; exact hr'
  have hi' : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit PUnit.unit) := fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
  have h₁ := h v e y yt (fun _ => i PUnit.unit PUnit.unit) hy hi'
  have hu := (unitAt_quot (i := fun _ => i PUnit.unit PUnit.unit) ht hr hy hi').regAt
  rw [pow_mul, ← mul_pow, Units.val_pow_eq_pow_val, SmallSec.valAt_pow hu, map_pow, Real.log_pow, ← h₁]
  push_cast
  ring

theorem GivenBy.tens {M : GlobalTheory.TrueGeo.Model Y} {L L' : LB M.X} {m : ℕ} (ht : ∀ y, Δ.IsEqn y (t y))
    (ht' : ∀ y, Δ'.IsEqn y (t' y)) (h : GivenBy Δ t φ M L m) (h' : GivenBy Δ' t' φ' M L' m) :
    GivenBy (Δ + Δ') (fun y => t y * t' y) (fun v e y => φ v e y + φ' v e y) M (CechPic.tens L L') m := by
  obtain ⟨r, hL, hr, h⟩ := h
  obtain ⟨r', hL', hr', h'⟩ := h'
  refine ⟨fun i => r (fun _ => (i PUnit.unit).1) * r' fun _ => (i PUnit.unit).2, CechPic.isLB_tens hL hL', ?_,
    fun v e y yt i hy hi => ?_⟩
  · rw [nsmul_add]; exact presents_tens hL hL' M.j hr hr'
  have hi₁ : ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit).1 := fun x hx => (hi hx).1
  have hi₂ : ⊤ ≤ yt ⁻¹ᵁ L'.U (i PUnit.unit).2 := fun x hx => (hi hx).2
  have h₁ := h v e y yt (fun _ => (i PUnit.unit).1) hy hi₁
  have h₂ := h' v e y yt (fun _ => (i PUnit.unit).2) hy hi₂
  have u₁ := unitAt_quot (i := fun _ => (i PUnit.unit).1) ht hr hy hi₁
  have u₂ := unitAt_quot (i := fun _ => (i PUnit.unit).2) ht' hr' hy hi₂
  rw [mul_inv, mul_pow, mul_mul_mul_comm, Units.val_mul, SmallSec.valAt_mul u₁.regAt u₂.regAt, map_mul,
    Real.log_mul (e.w.pos (SmallSec.valAt_ne_zero u₁)).ne' (e.w.pos (SmallSec.valAt_ne_zero u₂)).ne', ← h₁, ← h₂,
    mul_add]

theorem fromModel_add (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ Δ' : Y.Dv) (t t' : Y.X → Y.Fnˣ)
    (φ φ' : PtFn Y) (ht : ∀ y, Δ.IsEqn y (t y)) (ht' : ∀ y, Δ'.IsEqn y (t' y)) (h : FromModel Y Δ t φ)
    (h' : FromModel Y Δ' t' φ') :
    FromModel Y (Δ + Δ') (fun y => t y * t' y) (fun v e y => φ v e y + φ' v e y) := by
  obtain ⟨M, L, m, h⟩ := h
  obtain ⟨M', L', m', h'⟩ := h'
  obtain ⟨N, π, π', -, -, -, hj, hj', -⟩ := ModelDom.exists_normal_dominating F Y M M'
  have a := (GivenBy.pull (m := m) h π hj).pow ht m'
  have b := (GivenBy.pull (m := m') h' π' hj').pow ht' m
  rw [mul_comm] at b
  exact ⟨N, _, m * m', a.tens ht ht' b⟩

end GlobalTheory.LineNorm.Add
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tanEv_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (v : Sp (DualNumber k) ⟶ t.G.left) (hv : IsTanAtG t x v) (k' : Type) [CommRing k'] (φ : k →+* k') (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) (s : Γ(GlobalTheory.LieVB.omega t.G, V)), tanEv t hv' h' s = φ (tanEv t hv h s) := by
  first | exact @GlobalTheory.LocM.tanEv_baseChange | exact GlobalTheory.LocM.tanEv_baseChange | (intros; apply GlobalTheory.LocM.tanEv_baseChange <;> assumption)
end

