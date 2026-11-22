import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0112
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSecOfMoveInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.OfPositiveTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.PublishedTheorems.ThetaCharacteristics.ThetaCharZero
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteUnitaryClassesOfDualEqSmul
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLawsOfSignature
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore.Model

open NumberField IsDedekindDomain Module Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem det_eq_one_of_half (l : Level H) (Di : Datum H) {r : ℕ} (X : Data E r) (φ : Di.La ≃ₗ[𝓞 E] X.Λ)
    (ef : ∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (γ : GL (Fin r) E) (hU : IsUStab X.Gm X.Λ γ)
    (hh : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Di.La), ∃ b : Di.La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (φ a : Fin r → E) = (φ a : Fin r → E) + (l.M : ℕ) • (φ b : Fin r → E)) :
    (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  let g : (Fin r → E) ≃ₗ[𝓞 E] (Fin r → E) :=
    (Matrix.toLin'OfInv (M := (γ : Matrix (Fin r) (Fin r) E)) (M' := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))
      (Units.mul_inv γ) (Units.inv_mul γ)).symm.restrictScalars (𝓞 E)
  have hg : ∀ v, g v = (γ : Matrix (Fin r) (Fin r) E) *ᵥ v := fun v => rfl
  have hmap : X.Λ.map (g : (Fin r → E) →ₗ[𝓞 E] (Fin r → E)) = X.Λ := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hU.2 w).1 hw
    · intro hv
      refine ⟨g.symm v, (hU.2 _).2 ?_, g.apply_symm_apply v⟩
      rw [← hg, g.apply_symm_apply]; exact hv
  let f : Di.La ≃ₗ[𝓞 E] Di.La := φ.trans ((g.ofSubmodules X.Λ X.Λ hmap).trans φ.symm)
  have hf : ∀ a, (φ (f a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := fun a => by
    simp only [f, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Di l f
    (fun a b => by
      have : ((Di.EF (f a) (f b) : ℤ) : ℚ) = ((Di.EF a b : ℤ) : ℚ) := by rw [ef, ef, hf, hf, hU.1]
      exact_mod_cast this)
    (fun a ha => by
      obtain ⟨b, hb⟩ := hh a ha
      refine ⟨b, φ.injective (Subtype.ext ?_)⟩
      rw [hf, hb, map_add, map_nsmul]; rfl)
  refine GlobalTheory.CongruenceDet.det_eq_one E r l.M X.Gm X.Λ γ X.Gm_det X.Λ_fg X.Λ_span l.three_le hU fun v hv => ?_
  obtain ⟨a, ha⟩ := φ.surjective ⟨v, hv⟩
  obtain ⟨e, he⟩ := hfull a
  have hv' : (φ a : Fin r → E) = v := congrArg Subtype.val ha
  refine ⟨φ e, (φ e).2, ?_⟩
  rw [← hv', ← hf, he, map_add, map_nsmul]; rfl

theorem exists_unf (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E)
    (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hσ : GoodEmb c σ) (hξ : cc ξ₀ = -ξ₀) (hneg : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0)
    (hφ : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) :
    ∃ U : Formalism.L2.PjFree.Unf Xo c σ r, Formalism.L2.PjFree.IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧
      (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) l.M) ∧
      ∀ k, ∀ γ ∈ (U.X k).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  classical
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => relab c σ (e j).1) hpq hσ ((GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat E H l c σ hσ).2.2.2 Dw _ e)
  obtain ⟨M, hM, hX, hG⟩ := GlobalTheory.T.exists_flagDomainModels_of_familyUniformisation GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F r ξ₀ Gm φ hξ hneg hφ
  obtain ⟨un, hun⟩ := GlobalTheory.T.exists_framedPoints_all_normalisations_familyUnif hB hT E H Dw l Xo c σ _ e F r M hσ hM hX
  refine ⟨GlobalTheory.FrameUnif.unfOf e F M un, GlobalTheory.T.familyUniformisation_isComplexUniformisation hB E H Dw l Xo c σ _ e F r M un hσ hM hX hun, hM.chi, hG,
    fun k γ hU hv => (hM.gam k γ).2 ⟨hU, fun a _ => ?_, fun a => ?_⟩, fun k γ hγ => ?_⟩
  · obtain ⟨u, hu, h⟩ := hv _ (M.φ k a).2
    obtain ⟨b, hb⟩ := (M.φ k).surjective ⟨u, hu⟩
    exact ⟨b, by rw [hb]; exact h⟩
  · obtain ⟨u, hu, h⟩ := hv _ (M.φ k a).2
    obtain ⟨b, hb⟩ := (M.φ k).surjective ⟨u, hu⟩
    refine ⟨l.M • b, ?_⟩
    rw [hA, one_smul, map_nsmul, hb]
    exact h
  · obtain ⟨h1, h2, -⟩ := (hM.gam k γ).1 hγ
    exact det_eq_one_of_half l (F.Di k) (M.X k) (M.φ k) (hM.ef k) γ h1 h2

set_option maxHeartbeats 1000000 in

theorem exists_laws (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hF : FnAlgClosed Xo c) (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) :
    ∃ U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q), Laws U (Real.sqrt H.d) := by
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hn : ∀ τ : E →+* ℂ, ‖τ (H.rt : E)‖ = Real.sqrt H.d := fun τ => by
    have : ‖τ (H.rt : E)‖ ^ 2 = H.d := by rw [← norm_pow, ← map_pow, hsq]; simp
    rw [← this, Real.sqrt_sq (norm_nonneg _)]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
    have him : z.im ≠ 0 := by
      intro h
      rw [h] at h1
      nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hτ₀ := key (τ₀ (H.rt : E)) (by rw [← map_pow, hsq]; simp)
    apply τ₀.injective
    unfold cc
    rw [IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hτ₀.1]
  have hne : (H.rt : E) ≠ 0 := fun h => by
    rw [h] at hsq
    have : (H.d : E) = 0 := by simpa using hsq
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  obtain ⟨ξ₀, hc0, hne0, him, hx⟩ : ∃ ξ₀ : E, cc ξ₀ = -ξ₀ ∧ ξ₀ ≠ 0 ∧
      (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) ∧ ∀ τ : E →+* ℂ, ‖τ ξ₀‖ = Real.sqrt H.d := by
    rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
    · exact ⟨H.rt, hcc, hne, fun τ hτ => by rw [hτ]; exact h, hn⟩
    · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_, fun τ => by rw [map_neg, norm_neg, hn]⟩
      · unfold cc at hcc ⊢
        rw [map_neg, hcc]
      · rw [map_neg, hτ, Complex.neg_im]; linarith
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hc0 ⊢
    rw [map_neg, hc0]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne0) (Dw.p + Dw.q) rfl
  have hU : ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), GoodEmb c σ →
      Formalism.L2.PjFree.IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧
      (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k, GlobalTheory.Dict.HasPrinc (U.X k) l.M) ∧
      ∀ k, ∀ γ ∈ (U.X k).Γ, (γ : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) E).det = 1 := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, hU⟩ := exists_unf Dw l Xo c σ _ ξ₀ Gm φ hpq hA hσ hc0 him hφ
      exact ⟨U, fun _ => hU⟩
    · exact ⟨{ Comp := PEmpty, X := fun k => k.elim, un := fun k => k.elim }, fun h => absurd h hσ⟩
  choose U hU using hU
  refine ⟨fun σ => (U σ).toPj, hpq, hA, hg, fun σ hσ => (hU σ hσ).1, hF,
    fun σ hσ k τ => ?_, fun σ hσ a n _ k γ _ => (hU σ hσ).2.1 k _ γ, fun σ hσ => (hU σ hσ).2.2.2.2, ?_, h1⟩
  · exact (congrArg (fun z => ‖τ z‖) ((hU σ hσ).2.2.1 k).2).trans (hx τ)
  · intro σ hσ a n hD ha hn P hP
    have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional E H Dw l Xo c _ U hpq hA
      (fun s hs => (hU s hs).1) σ hσ
      (fun k k' => ⟨((hU σ hσ).2.2.1 k).1.trans ((hU σ hσ).2.2.1 k').1.symm,
        ((hU σ hσ).2.2.1 k).2.trans ((hU σ hσ).2.2.1 k').2.symm⟩)
      (hU σ hσ).2.2.2.1 a n hD (fun τ _ h0 => ha τ _ (by omega)) hn (fun k γ _ => (hU σ hσ).2.1 k _ γ)
    exact key ⟨hP.1, hP.2⟩

theorem exists_laws_of_signature (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) (p q : ℕ) (hpq : 1 ≤ p + q) :
    ∃ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q)),
      Dw.p = p ∧ Dw.q = q ∧ Nonempty (Comp Xo c) ∧ Laws U (Real.sqrt H.d) := by
  obtain ⟨D, hp, hq, -⟩ := GlobalTheory.CompRat.exists_splitLat_of_signature E H p q h1
  have h : 1 ≤ D.p + D.q := by omega
  obtain ⟨l, hA, hg, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx _ H 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ D l h
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c₀ h
  obtain ⟨hZ, -⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c h
  obtain ⟨U, hU⟩ := exists_laws D l Xo c h hA hg (hc c le_rfl) h1
  exact ⟨D, l, Xo, c, U, hp, hq, hZ, hU⟩

theorem exists_laws_cyclotomic (p q : ℕ) (hpq : 1 ≤ p + q) :
    ∃ (Dw : Datum GlobalTheory.CM.CyclotomicTwentyEight.host) (l : Level GlobalTheory.CM.CyclotomicTwentyEight.host) (Xo : Moduli Dw l) (c : Coeff l)
      (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q)) (x : ℝ),
      Dw.p = p ∧ Dw.q = q ∧ Nonempty (Comp Xo c) ∧ Laws U x := by
  obtain ⟨D, l, Xo, c, U, h⟩ := exists_laws_of_signature GlobalTheory.CM.CyclotomicTwentyEight.exists_datum p q hpq
  exact ⟨D, l, Xo, c, U, _, h⟩

theorem archEx_of_definite {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (h : Laws U x) (hq : Dw.q = 0) : ArchEx U x := fun Z τ => by
  have hp : 1 ≤ Dw.p := by have := h.pos; omega
  obtain ⟨s⟩ := GlobalTheory.FlatLine.Definite.nonempty_flatSec U x hq hp h.good h.unf h.geo Z τ
  exact ⟨.ofConst s⟩

section Steps

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem hasPts (h : Laws U x) (Z : Comp Xo c) : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z

theorem htValAt_nonempty (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io)
    (hy : y₀.IsAlg) : (htValAt la y₀).Nonempty := by
  obtain ⟨p, hp, ha, k, y, h⟩ := (GlobalTheory.CompHt.exists_isHTFrameCp_and_nonempty E H Dw l Xo c).1 T io y₀ hy
  exact ⟨_, p, hp, ha, k, y, h, rfl⟩

theorem htValOn_nonempty (h : Laws U x) (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) : (htValOn Z la).Nonempty := by
  obtain ⟨_, ⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := (hasPts h Z).2 la
  obtain ⟨w, hw⟩ := htValAt_nonempty la y hy.1
  exact ⟨w, T, io, e, y, ho, hy, hw⟩

theorem finConst_of (h₁ : HTConst U x) (h₂ : HTShift Xo c) : FinConst U x := fun Z τ s la => by
  obtain ⟨ρ, hρ⟩ := h₁ Z τ s la
  obtain ⟨κ, hκ⟩ := h₂ τ la
  refine ⟨ρ - κ, ?_⟩
  rintro _ ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := htValAt_nonempty la y hy.1
  have h3 := (hρ w ⟨T, io, e, y, ho, hy, hw⟩).symm.trans (hκ T io e y ho hy.1 w hw _ s.sig_mem)
  show nval T.V e (evI y s.sig) = _
  by_cases h0 : evI y s.sig = 0
  · rw [h0, nval_zero, EReal.top_add_coe] at h3
    exact absurd h3 (EReal.coe_ne_top ρ)
  · rw [nval_of_ne h0] at h3 ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h3
    rw [EReal.coe_eq_coe_iff, h3]; ring

theorem flatDegree_of (h : Laws U x) {om : ℝ} (h₁ : ArchEx U x) (h₂ : FinConst U x) (h₃ : FrameDeg U x om) :
    FlatDegree U x om := fun Z τ => by
  constructor
  · obtain ⟨s⟩ := h₁ Z τ
    choose ρ hρ using h₂ Z τ s
    let t : ConstSec U x Z (flatWt Dw τ) 0 :=
      { s with
        rho_vw := ρ
        val_fin := fun w => image_eq_singleton_iff.2 ⟨(hasPts h Z).2 w, fun v hv => by simpa using hρ w v hv⟩
        finite_rho := (h₃ Z τ s ρ hρ).1 }
    exact ⟨t.relat _ (by simpa using finite_flDefect_vw τ)⟩
  · intro s
    have h4 := (h₃ Z τ (.ofConst s.toFrame) s.toFrame.rho_vw fun la w hw => by
      exact (s.toFrame.val_eq hw).trans (by simp)).2
    rw [s.deg_eq_toFrame, neg_neg, flatDegVal, ← h4]
    rfl

end Steps

theorem exists_laws_record (D : Formalism.BasicNotions.D7) (p q : ℕ) (hpq : 1 ≤ p + q) :
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField (hostOfRecord D) ∧
    ∃ (Dw : Datum (hostOfRecord D)) (l : Level (hostOfRecord D)) (Xo : Moduli Dw l) (c : Coeff l)
      (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q)),
      Dw.p = p ∧ Dw.q = q ∧ Nonempty (Comp Xo c) ∧ Laws U (Real.sqrt (hostOfRecord D).d) :=
  ⟨GlobalTheory.FlatRow.isHostField D _ rfl,
    exists_laws_of_signature (GlobalTheory.RankOneDatum.exists_datum_of_rt D _ rfl rfl) p q hpq⟩

end GlobalTheory.FlatCore.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsPullOfMoveInv
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevPullModel

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LevPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pull_zero (d : DeltaDat Xo c 0) : Pull d 0 0 := fun _ _ _ _ _ _ y₂ y _ =>
  (evalAt_zero _ _ y₂).trans (evalAt_zero _ _ y).symm

theorem pull_one (d : DeltaDat Xo c 0) : Pull d 1 1 := fun k _ _ _ _ _ y₂ y _ =>
  (GlobalTheory.RawSpan.evR_one_field k y₂).trans (GlobalTheory.RawSpan.evR_one_field k y).symm

theorem pull_add {d : DeltaDat Xo c 0} {f f' : Rul Xo c} {g g' : Rul d.Xo₂ d.c₂} (h : Pull d f g) (h' : Pull d f' g') :
    Pull d (f + f') (g + g') := fun k _ _ _ _ hk y₂ y ho =>
  (evalAt_add _ _ g g' y₂).trans ((congrArg₂ (· + ·) (h k hk y₂ y ho) (h' k hk y₂ y ho)).trans (evalAt_add _ _ f f' y).symm)

theorem pull_mul {d : DeltaDat Xo c 0} {f f' : Rul Xo c} {g g' : Rul d.Xo₂ d.c₂} (h : Pull d f g) (h' : Pull d f' g') :
    Pull d (f * f') (g * g') := fun k _ _ _ _ hk y₂ y ho =>
  (evalAt_mul _ _ g g' y₂).trans ((congrArg₂ (· * ·) (h k hk y₂ y ho) (h' k hk y₂ y ho)).trans (evalAt_mul _ _ f f' y).symm)

theorem pull_smul {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g) (a : c.F) :
    Pull d (a • f) (d.eF a • g) := fun k _ _ _ _ hk y₂ y ho =>
  (evalAt_smul _ _ (d.eF a) g y₂).trans
    ((congrArg₂ (· * ·) (hk a) (h k hk y₂ y ho)).trans (evalAt_smul _ _ a f y).symm)

theorem pull_inj {d : DeltaDat Xo c 0} (hd : d.IsLev) {f f' : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g)
    (h' : Pull d f' g) (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k) :
    evR Xo c f y = evR Xo c f' y := by
  let _ : Algebra d.c₂.F k := ((algebraMap c.F k).comp d.eF.symm.toRingEquiv.toRingHom).toAlgebra
  have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a =>
    congrArg (algebraMap c.F k) (d.eF.symm_apply_apply a)
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  exact (h k hk y₂ y hy).symm.trans (h' k hk y₂ y hy)

theorem not_pull_zero_one {d : DeltaDat Xo c 0} (hd : d.IsLev) (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k]
    (y : FrPt Xo c k) : ¬ Pull d 0 1 := fun h => by
  have e := pull_inj hd h (pull_one d) k y
  rw [GlobalTheory.RawSpan.evR_one_field k y] at e
  exact zero_ne_one ((evalAt_zero _ _ y).symm.trans e)

theorem pull_id (nab : NabV Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    Pull (GlobalTheory.RawSpan.idCover nab 0) f f := by
  intro k _ _ i₁ i₂ hk y₂ y ho
  have e : i₂ = i₁ := Algebra.algebra_ext _ _ fun a => hk a
  subst e
  have hb := @GlobalTheory.FrameLift.frBor_lift E _ _ _ H Dw l Xo k _ c 0 (GlobalTheory.RawSpan.idCover nab 0) GlobalTheory.firstFiveLaws.1.globalFns
    i₂ i₂ 1 y y y y₂ (@GlobalTheory.RawSpan.frOver_self E _ _ _ H Dw l Xo c nab 0 k _ i₂ y) ho
    ((CategoryTheory.Category.comp_id _).symm.trans ho.1) (@GlobalTheory.ShFam.Descent.frBor_one E _ _ _ H Dw l Xo c k _ i₂ y)
  have := @GlobalTheory.ThetaSumDescent.evR_frBor E _ _ _ H Dw l Xo c n a f hf k _ i₂ 1 y y₂ hb
  refine this.trans ?_
  simp [wchar]

theorem exists_pull_of_moveInv (d : DeltaDat Xo c 0) (hd : d.IsLev) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (g : Rul d.Xo₂ d.c₂) (hg : g ∈ sec d.Xo₂ d.c₂ a n) (hi : GlobalTheory.ThetaSumDescent.MoveInv d g) :
    ∃ f ∈ sec Xo c a n, Pull d f g := by
  obtain ⟨f, hf, h⟩ := GlobalTheory.ThetaSumDescent.exists_sec_of_moveInv d hd g hg hi
  exact ⟨f, hf, fun k _ _ _ _ hk y₂ y ho => (h k hk y y₂ ho).symm⟩

theorem fibConst_of_moveInv (d : DeltaDat Xo c 0) (hd : d.IsLev) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (g : Rul d.Xo₂ d.c₂) (hg : g ∈ sec d.Xo₂ d.c₂ a n) (hi : GlobalTheory.ThetaSumDescent.MoveInv d g) : FibConst d g := by
  obtain ⟨f, -, h⟩ := exists_pull_of_moveInv d hd g hg hi
  exact h.fibConst

theorem intAt_zero : IntAt Xo c 0 := by
  rintro la _ ⟨y, rfl⟩
  rw [vAtV_zero]; exact le_top

theorem intAt_add {f g : Rul Xo c} (hf : IntAt Xo c f) (hg : IntAt Xo c g) : IntAt Xo c (f + g) := by
  rintro la _ ⟨y, rfl⟩
  exact (le_min (hf la _ ⟨y, rfl⟩) (hg la _ ⟨y, rfl⟩)).trans (vAtV_add y f g)

theorem intAt_mul {f g : Rul Xo c} (hf : IntAt Xo c f) (hg : IntAt Xo c g) : IntAt Xo c (f * g) := by
  rintro la _ ⟨y, rfl⟩
  rw [vAtV_mul]
  exact add_nonneg (hf la _ ⟨y, rfl⟩) (hg la _ ⟨y, rfl⟩)

theorem laQ_eq : LaQ Dw l = LevQ Dw l := rfl

theorem exists_isLift : ∃ lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La, IsLift lift := by
  have := Dw.proj
  choose lift h using fun γ : Gam Dw l =>
    Module.projective_lifting_property (Submodule.mkQ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
      (γ.toLinearMap ∘ₗ Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact ⟨lift, h⟩

theorem congMod_iff (h h' : Dw.La →ₗ[𝓞 E] Dw.La) :
    CongMod l.Mb h h' ↔ ∀ a, (Submodule.Quotient.mk (h a) : LaQ Dw l) = Submodule.Quotient.mk (h' a) :=
  forall_congr' fun _ => (Submodule.Quotient.eq _).symm

theorem lift_mk {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ : Gam Dw l) (a : Dw.La) :
    (Submodule.Quotient.mk (lift γ a) : LaQ Dw l) = γ (Submodule.Quotient.mk a) := LinearMap.congr_fun (h γ) a

theorem lift_unique {lift lift' : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (h' : IsLift lift') (γ : Gam Dw l) :
    CongMod l.Mb (lift γ) (lift' γ) := (congMod_iff _ _).2 fun a => (lift_mk h γ a).trans (lift_mk h' γ a).symm

theorem lift_mul {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ γ' : Gam Dw l) :
    CongMod l.Mb (lift (γ * γ')) (lift γ ∘ₗ lift γ') := (congMod_iff _ _).2 fun a => by
  rw [lift_mk h, LinearMap.comp_apply, lift_mk h, lift_mk h]; rfl

theorem eq_of_congMod {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) {γ γ' : Gam Dw l}
    (e : CongMod l.Mb (lift γ) (lift γ')) : γ = γ' := by
  ext q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact (lift_mk h γ a).symm.trans (((congMod_iff _ _).1 e a).trans (lift_mk h γ' a))

theorem mb_ne_bot : l.Mb ≠ ⊥ := fun h => by
  have e := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at e
  have := l.three_le
  omega

theorem finite_laQ : Finite (LaQ Dw l) := by
  have := Dw.fin
  have : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ mb_ne_bot
  have : Module.Finite (𝓞 E ⧸ l.Mb) (LaQ Dw l) := Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  exact Module.finite_of_finite (𝓞 E ⧸ l.Mb)

theorem finite_gam : Finite (Gam Dw l) := by
  have := finite_laQ (Dw := Dw) (l := l)
  exact Finite.of_injective (fun γ : Gam Dw l => (γ : LaQ Dw l → LaQ Dw l)) DFunLike.coe_injective

theorem mb_ne_top : l.Mb ≠ ⊤ := fun h => by
  have e := l.prod
  rw [h, Ideal.map_top, Ideal.top_mul, eq_comm, Ideal.span_singleton_eq_top] at e
  have h1 := (e.map (Algebra.norm ℤ))
  have h2 : Algebra.norm ℤ ((l.M : 𝓞 E)) = (l.M : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
    rw [← Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 E) (l.M : ℤ)]; simp
  rw [h2, isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne', Int.isUnit_iff] at h1
  have := l.three_le
  omega

theorem nontrivial_laQ (hr : 1 ≤ Dw.p + Dw.q) : Nontrivial (LaQ Dw l) := by
  have := Dw.fin
  have := Dw.proj
  rw [Submodule.Quotient.nontrivial_iff]
  intro h
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul l.Mb (⊤ : Submodule (𝓞 E) Dw.La)
    Module.Finite.fg_top h.ge
  have hne : r ≠ 0 := by
    rintro rfl
    exact mb_ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using l.Mb.neg_mem hr1))
  have : Nontrivial Dw.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [Dw.rank]; omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : Dw.La)
  exact hx ((smul_eq_zero.1 (hr0 x trivial)).resolve_left hne)

theorem nontrivial_gam (hr : 1 ≤ Dw.p + Dw.q) : Nontrivial (Gam Dw l) := by
  have := nontrivial_laQ (l := l) hr
  refine ⟨LinearEquiv.neg _, 1, fun h => ?_⟩
  obtain ⟨q, hq⟩ := exists_ne (0 : LaQ Dw l)
  have h2 : -q = q := LinearEquiv.congr_fun h q
  have hM : (l.M : 𝓞 E) • q = 0 := by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Submodule.smul_mem_smul ?_ trivial
    have e : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left e
  obtain ⟨m, hm⟩ := l.odd
  have h3 : (2 : 𝓞 E) • q = 0 := by rw [two_smul]; nth_rewrite 1 [← h2]; exact neg_add_cancel q
  rw [hm] at hM
  push_cast at hM
  rw [add_smul, one_smul, mul_comm, mul_smul, h3, smul_zero, zero_add] at hM
  exact hq hM

end GlobalTheory.LevPullModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.P22
section
namespace GlobalTheory.CovTop

structure Hypotheses₂ : Prop where
  p1 : GlobalTheory.Published.ToroidalCompactification
  p2 : GlobalTheory.Published.VolGe
  p3 : GlobalTheory.Published.VolNef
  p4 : GlobalTheory.Published.ArCalc
  p5 : GlobalTheory.Published.AbelianDeRham
  p6 : GlobalTheory.Published.TamagawaSpecialUnitary
  p8 : GlobalTheory.Published.RayClassFieldSt
  p12 : GlobalTheory.Published.SemistableReductionSt
  p13 : GlobalTheory.Published.StrongApproxSU
  p14 : GlobalTheory.Published.GreenSeriesSt
  p16 : GlobalTheory.Published.MumfordProportionality
  p18 : GlobalTheory.Published.FinitenessOfHermitianClasses
  p19 : GlobalTheory.Published.LandherrSt
  p20 : GlobalTheory.Published.HasseNormSt
  p22 : GlobalTheory.Published.SemiAbelianHomExtension
  p23 : GlobalTheory.Published.InducedSimpleLowestAlcove
  p25 : GlobalTheory.Published.principalPolarisationOneSection
  p26 : GlobalTheory.Published.AbMulNSt

end GlobalTheory.CovTop
end

