import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.BcExAll
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.FramedBaseChange

theorem bcEx_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ σ : c.F →+* ℂ, BCEx Xo c σ :=
  fun E _ _ _ H Dw l Xo c σ p y ψ =>
    exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R (CAt σ) ψ y

end GlobalTheory.FramedBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComponentEqOfMatchedLatticesMarkings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem index_eq_of_marked_isometry {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (hr : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H Dw.p Dw.q ty) (k k' : Fin F.n) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La)
    (hEF : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b)
    (hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F.t k' a + l.M • x)
    (hA : ∀ a, ∃ x, gam (F.t k a) = F.t k' a + l.A • x) : k = k' := by
  obtain ⟨-, P', hP'⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di k') g ty
    (by rw [(F.sig k').1, (F.sig k').2]; exact hty)
  have hP := GlobalTheory.ClassUniq.isPeriod_comp_isometry gam hEF hP'
  set P := P'.comp gam.toLinearMap.toAddMonoidHom with hPdef
  refine F.disj k k' P P' hP hP' ?_
  exact (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g ty
    hr hσ hty (F.Di k) (F.Di k')
    (F.t k) (F.t k') P P' (F.u k P) (F.u k' P') (F.ex k P) (F.ex k' P')
    ⟨F.over_σ k P hP, hP, ⟨F.ex_add k P hP, F.ex_onto k P hP, GlobalTheory.ClassUniq.isHolTo_ex F k P hP,
      (F.ex_diff k P hP).1, (F.ex_diff k P hP).2⟩, F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP,
      F.ex_eta k P hP, F.ex_etaA k P hP⟩
    ⟨F.over_σ k' P' hP', hP', ⟨F.ex_add k' P' hP', F.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F k' P' hP',
      (F.ex_diff k' P' hP').1, (F.ex_diff k' P' hP').2⟩, F.ex_ker k' P' hP', F.ex_lin k' P' hP',
      F.ex_weil k' P' hP', F.ex_eta k' P' hP', F.ex_etaA k' P' hP'⟩).2
    ⟨gam, LinearEquiv.refl ℂ _, hEF, hM, hA, fun a => rfl⟩

theorem UW.ik_injective {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (W : UW U) :
    Function.Injective W.ik := by
  obtain ⟨hr, hX, -, hfib, -⟩ := hU
  obtain ⟨g, e, F, ik, φ, hEF, hP⟩ := W
  intro k k' hk
  change ik k = ik k' at hk
  obtain ⟨x, hx⟩ := CompInj.dom_nonempty (U.X k)
  obtain ⟨x₀, hx₀⟩ := CompInj.dom_nonempty (U.X k')
  obtain ⟨P, -, hper, hpt, hder, -⟩ := hP k ⟨x, hx⟩
  obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
  have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2.1⟩ : _ ∧ _ ∧ _)
  have hEF' := hEF k'
  generalize φ k' = ψ at hP₀ hP' hEF'
  clear hP hEF φ
  generalize ik k' = n at *
  subst hk
  obtain ⟨x', hx', hPx⟩ := CompInj.exists_frame hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1 (F.sig _).2
    ψ hEF' x₀ hx₀ P₀ hP₀ hper₀ P hper
  obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
  obtain rfl : P = P' := by
    ext a j
    rw [hPx, hP']
  have hbor := CompInj.frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
  obtain ⟨ga, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
  exact (congrArg Sigma.fst h).symm

theorem comp_eq_of_matched : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (W : UW U) (k k' : U.Comp), SameSp (U.X k) (U.X k') → ∀ ga : GL (Fin r) E, IsUn (U.X k) ga → mapL ga (U.X k).Λ = (U.X k').Λ → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ (U.X k').Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ W.mark k a = W.mark k' a + l.M • u) → k = k' := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 hA W k k' hS ga hun hΛ hm
  apply W.ik_injective hσ hU h1
  have hinj : Function.Injective
      ((Matrix.toLin' (ga : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) := by
    intro u v huv
    have h : (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = (ga : Matrix (Fin r) (Fin r) E) *ᵥ v := huv
    have h2 := congrArg (fun w => ((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using h2
  let ψ : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ :=
    (Submodule.equivMapOfInjective _ hinj (U.X k).Λ).trans (LinearEquiv.ofEq _ _ hΛ)
  let gam : (W.F.Di (W.ik k)).La ≃ₗ[𝓞 E] (W.F.Di (W.ik k')).La := (W.φ k).trans (ψ.trans (W.φ k').symm)
  have hgam : ∀ a, (W.φ k' (gam a) : Fin r → E) = (ga : Matrix (Fin r) (Fin r) E) *ᵥ (W.φ k a : Fin r → E) := by
    intro a
    change (W.φ k' ((W.φ k').symm (ψ (W.φ k a))) : Fin r → E) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine index_eq_of_marked_isometry W.F (hU.1 ▸ h1) hσ
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw W.g W.e) _ _ gam (fun a b => ?_) (fun a ha => ?_) fun a => ?_
  · have h := W.isom k' (gam a) (gam b)
    rw [hgam, hgam, ← hS.gm, ← hS.xi, hun, ← W.isom k a b] at h
    exact_mod_cast h
  · obtain ⟨w, hw, h⟩ := hm a ha
    refine ⟨(W.φ k').symm ⟨w, hw⟩, (W.φ k').injective (Subtype.ext ?_)⟩
    rw [hgam, map_add, map_nsmul, LinearEquiv.apply_symm_apply]
    exact h
  · exact ⟨gam (W.F.t _ a) - W.F.t _ a, by rw [hA, one_smul, add_sub_cancel]⟩

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PushforwardPreservesHarmonicPolynomialsAndLatticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (h : Matrix (Fin n) (Fin n) E), IsUnitaryM h → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), pushLet c h P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ∧ ∀ Λ : GenLat E n, (Λ.Unimod → (actLat h Λ).Unimod) ∧ Moves h Λ.La (actLat h Λ).La ∧ ccT h * h = 1 ∧ ∀ P ∈ harmL (Dw := Dw) c Λ a, pushLet c h P ∈ harmL (Dw := Dw) c (actLat h Λ) a := by
  first | exact @GlobalTheory.PushKeeps.push_keeps | exact GlobalTheory.PushKeeps.push_keeps | (intros; apply GlobalTheory.PushKeeps.push_keeps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RatioMemRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.ConstRatio

theorem ratio_mem_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Type) [Field T] [IsAlgClosed T] [Algebra c.F T]
    (u u' : FrPt Xo c T → T)
    (hu : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u y) = u z)
    (hu' : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u' y) = u' z)
    (z : T) (h : ∀ y, u' y = z * u y) (y : FrPt Xo c T) (hy : u y ≠ 0) :
    z ∈ Set.range (algebraMap c.F T) := by
  refine GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv z fun σ => ?_
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T T σ.toAlgHom y
  have h1 := hu _ _ _ hy'
  have h2 := hu' _ _ _ hy'
  rw [h y, h y', map_mul, ← h1] at h2
  have hne : σ.toAlgHom (u y) ≠ 0 := by
    simpa using hy
  exact mul_right_cancel₀ hne h2

theorem exists_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (J : Type) (u u' : J → ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u j S y) = u j T z)) → (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' j S y) = u' j T z)) → ∀ z : ℂ, IsMu z → (∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u' j ℂ _ s.toAlgebra y = z * @u j ℂ _ s.toAlgebra y) → ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧ ∀ j (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u' j S y = algebraMap c.F S z₀ * u j S y := by
  intro E _ _ _ H Dw l Xo c s J u u' hu hu' z hz h
  have key : ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧
      ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra),
        @u' j ℂ _ s.toAlgebra y = s z₀ * @u j ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u j ℂ _ s.toAlgebra y = 0
    · refine ⟨1, ⟨1, one_pos, one_pow 1⟩, fun j y => ?_⟩
      rw [h j y, h0 j y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨j, y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u j ℂ _ s.toAlgebra) (@u' j ℂ _ s.toAlgebra)
        (@hu j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@hu' j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z (h j) y hy
      have hz₀' : s z₀ = z := hz₀
      obtain ⟨m, hm, hzm⟩ := hz
      refine ⟨z₀, ⟨m, hm, s.injective ?_⟩, fun j y => ?_⟩
      · rw [map_pow, hz₀', hzm, map_one]
      · rw [hz₀', h j y]
  obtain ⟨z₀, hk, hz₀⟩ := key
  refine ⟨z₀, hk, fun j => ?_⟩
  refine GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s (u' j) (fun S _ _ y => algebraMap c.F S z₀ * u j S y) (hu' j) ?_ ?_
  · intro S T _ _ _ _ φ y y' hyy
    rw [map_mul, φ.commutes, hu j S T φ y y' hyy]
  · intro y
    exact hz₀ j y

end GlobalTheory.ConstRatio
end

