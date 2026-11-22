import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0091
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
section
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem algebraic_laws : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrChartF Xo c ∧ BorChartF Xo c ∧ EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ WtField Xo c ∧ IntDiagUnit Xo c ∧ UnitIndep Xo c ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S], IsReduced S → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y := by
  intro hB E _ _ _ H Dw l Xo c

  have hTest := GlobalTheory.T.framedPoint_reduced_from_testRing hB E H Dw l Xo c
  have hCov := GlobalTheory.T.chartCoverF_of_sectionBaseChange hB E H Dw l Xo c
  have hLat := GlobalTheory.T.integralLattice_structure_unique E H Dw l Xo c
  have hFr : FrChartF Xo c := frChartF_of hCov
  have hBor : BorChartF Xo c := borChartF_of_cover hCov
  refine ⟨hFr, hBor, evalWD_fr hFr, wtField_of_borChart hBor, intDiagUnit_of hLat,
    unitIndep_of_charts hBor hLat, ?_⟩

  intro S _ _ hS a n f hf t y y' hy
  obtain ⟨hnat, hwt⟩ := hf
  exact wtAll_of_borChart hBor (ex Dw a n) hnat hwt S t y y' (hTest S y) (hTest S y') hy

end GlobalTheory.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
section
namespace GlobalTheory.IntegralFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem intAll : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Formalism.L2.PjFree.IntAll Xo c := by
  intro hI hA hB hT E _ _ _ H Dw l Xo c hpq hg
  exact Formalism.L2.PjFree.intAll_of' (GlobalTheory.T.intFrExt_of_good_level hI hA hB hT E H Dw l Xo c hpq hg)
    (fun S S' _ _ _ _ φ y => GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c S S' φ y)
    (fun S _ x _ v hv _ w A N w' hw hw' => GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw')
    (GlobalTheory.T.integralFrame_change_integral_invertible_matrix hB E H Dw l Xo c)

end GlobalTheory.IntegralFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralAlgebraicFramedPointExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem integralAlgebraicFramedPoint_exists : PartI → N1ab → N1c → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrNe Xo c (Formalism.L2.PjFree.algCls Xo c) :=
  fun hP hab hc hB hT E _ _ _ H Dw l Xo c hpq hg =>
    intFrNe_of (GlobalTheory.T.algebraicPoints_moduli_every_place hc E H Dw l Xo c hpq) (GlobalTheory.T.intFrExt_of_good_level hP hab hB hT E H Dw l Xo c hpq hg)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ClassUniq

lemma isHolTo_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) :
    IsHolTo Set.univ (fun z => (F.ex k P z).left) := by
  have h1 := (F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  unfold IsHolTo at h1 ⊢
  intro U f
  obtain ⟨ho, hd⟩ := h1 U f
  have hj : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := continuous_const.prodMk continuous_id
  have hjd : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  have hset : {b | b ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (fun z => (F.ex k P z).left) b ⁻¹ᵁ U} =
      (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) ⁻¹'
        {b | b ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) ∧
          ⊤ ≤ (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (F.ex k P bz.2).left) b ⁻¹ᵁ U} := by
    ext z
    simp
  rw [hset]
  refine ⟨ho.preimage hj, ?_⟩
  have h2 := hd.comp hjd.differentiableOn (fun z hz => hz)
  rw [Function.comp_def] at h2
  dsimp only at h2 ⊢
  exact h2

lemma isPeriod_comp_isometry {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (gam : D.La ≃ₗ[𝓞 E] D'.La) (hg : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P') :
    IsPeriod D ty (P'.comp gam.toLinearMap.toAddMonoidHom) := by
  unfold IsPeriod at hP ⊢
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hrange : (P'.comp gam.toLinearMap.toAddMonoidHom).range = P'.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨gam a, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨gam.symm b, by simp⟩
  have hr2 : Set.range (P'.comp gam.toLinearMap.toAddMonoidHom) = Set.range P' := by
    rw [← AddMonoidHom.coe_range, ← AddMonoidHom.coe_range, hrange]
  refine ⟨?_, ?_, ?_, ?_, Hm, hH, hpos, ?_⟩
  · intro a x i
    show P' (gam (a • x)) i = (ty i) (a : E) * P' (gam x) i
    rw [map_smul]
    exact hlin a (gam x) i
  · intro a b hab
    exact gam.injective (hinj hab)
  · rw [hrange]
    exact hdisc
  · rw [hr2]
    exact hspan
  · intro x y
    have h := him (gam x) (gam y)
    rw [hg] at h
    exact h

theorem eq_of_matched : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (k k' : Fin F.n) (γ : GL (Fin r) E), 1 ≤ Dw.p + Dw.q → σ' (baseKA l).ρ = H.rt0 → IsTypeFn H Dw.p Dw.q ty → ModelBase M → (M.X k').Gm = (M.X k).Gm → (M.X k').ξ0 = (M.X k).ξ0 → (∀ u v, herm (M.X k).Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm (M.X k).Gm u v) → (∀ v, v ∈ (M.X k).Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ (M.X k').Λ) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ (M.X k').Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k (F.t k a) : Fin r → E) = (M.φ k' (F.t k' a) : Fin r → E) + l.M • w) → (∀ a, ∃ w ∈ (M.X k').Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k (F.t k a) : Fin r → E) = (M.φ k' (F.t k' a) : Fin r → E) + l.A • w) → k = k' := by
  intro hT hL E _ _ _ H Dw l Xo σ' g ty F r M k k' γ hpq hρ hty hMB hGm hξ hunit hΛ hcM hcA
  have hmem : ∀ a : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((M.φ k a : (M.X k).Λ) : Fin r → E) ∈ (M.X k').Λ :=
    fun a => (hΛ _).1 (M.φ k a).2
  let gmap : (F.Di k).La →ₗ[𝓞 E] (F.Di k').La :=
    (M.φ k').symm.toLinearMap ∘ₗ LinearMap.codRestrict (M.X k').Λ
      (((Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) ∘ₗ
        (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) (fun a => hmem a)
  have hgmap : ∀ a, ((M.φ k' (gmap a) : (M.X k').Λ) : Fin r → E) =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
    intro a
    simp only [gmap, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have hinv : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (γ : Matrix (Fin r) (Fin r) E) = 1 :=
    Units.inv_mul γ
  have hinv' : (γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 :=
    Units.mul_inv γ
  have hinj : Function.Injective gmap := by
    intro a b hab
    have h1 := congrArg (fun x => ((M.φ k' x : (M.X k').Λ) : Fin r → E)) hab
    simp only [hgmap] at h1
    have h2 := congrArg (fun v => ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2
    exact (M.φ k).injective (Subtype.ext h2)
  have hsurj : Function.Surjective gmap := by
    intro b
    have hAv : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((M.φ k' b : (M.X k').Λ) : Fin r → E)) = ((M.φ k' b : (M.X k').Λ) : Fin r → E) := by
      rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    have hvmem : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((M.φ k' b : (M.X k').Λ) : Fin r → E) ∈ (M.X k).Λ := by
      rw [hΛ, hAv]
      exact (M.φ k' b).2
    refine ⟨(M.φ k).symm ⟨_, hvmem⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgmap, LinearEquiv.apply_symm_apply]
    exact hAv
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La := LinearEquiv.ofBijective gmap ⟨hinj, hsurj⟩
  have hgam : ∀ a, ((M.φ k' (gam a) : (M.X k').Λ) : Fin r → E) =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := fun a => hgmap a
  have hiso : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b := by
    intro a b
    have h1 := hMB.ef k' (gam a) (gam b)
    have h2 := hMB.ef k a b
    rw [hgam, hgam, hGm, hξ, hunit] at h1
    exact_mod_cast h1.trans h2.symm
  have hcM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ x, gam (F.t k a) = F.t k' a + l.M • x := by
    intro a ha
    obtain ⟨w, hw, hweq⟩ := hcM a ha
    refine ⟨(M.φ k').symm ⟨w, hw⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgam, hweq]
    simp
  have hcA' : ∀ a, ∃ x, gam (F.t k a) = F.t k' a + l.A • x := by
    intro a
    obtain ⟨w, hw, hweq⟩ := hcA a
    refine ⟨(M.φ k').symm ⟨w, hw⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgam, hweq]
    simp
  have htyk' : IsTypeFn H (F.Di k').p (F.Di k').q ty := by
    rw [(F.sig k').1, (F.sig k').2]
    exact hty
  obtain ⟨P', hP'⟩ := (GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di k') g ty htyk').2
  have hP := isPeriod_comp_isometry gam hiso hP'
  have key := GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hT hL E H Dw l Xo σ' g ty hpq hρ hty
    (F.Di k) (F.Di k') (F.t k) (F.t k') (P'.comp gam.toLinearMap.toAddMonoidHom) P'
    (F.u k (P'.comp gam.toLinearMap.toAddMonoidHom)) (F.u k' P')
    (F.ex k (P'.comp gam.toLinearMap.toAddMonoidHom)) (F.ex k' P')
    ⟨F.over_σ k _ hP, hP, ⟨F.ex_add k _ hP, F.ex_onto k _ hP, isHolTo_ex F k _ hP, (F.ex_diff k _ hP).1,
      (F.ex_diff k _ hP).2⟩, F.ex_ker k _ hP, F.ex_lin k _ hP, F.ex_weil k _ hP, F.ex_eta k _ hP,
      F.ex_etaA k _ hP⟩
    ⟨F.over_σ k' _ hP', hP', ⟨F.ex_add k' _ hP', F.ex_onto k' _ hP', isHolTo_ex F k' _ hP',
      (F.ex_diff k' _ hP').1, (F.ex_diff k' _ hP').2⟩, F.ex_ker k' _ hP', F.ex_lin k' _ hP',
      F.ex_weil k' _ hP', F.ex_eta k' _ hP', F.ex_etaA k' _ hP'⟩
  have hu := key.2 ⟨gam, LinearEquiv.refl ℂ _, hiso, hcM', hcA', fun a => rfl⟩
  exact F.disj k k' _ _ hP hP' hu

end GlobalTheory.ClassUniq
end

