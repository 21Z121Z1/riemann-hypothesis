import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalHeckeMatrixIntermediateLattice
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsOrthonormalisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalHeckeMatrixIntermediateLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localHeckeMatrix_intermediateLattice : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k n : ℕ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D)
    (Λ M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
    (T C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)),
    IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    (∀ x, s (π (finPart D x)) = e * x) → (∀ a, π (finPart D (s a)) = a) →
    (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    (∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) =
      algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) x) →
    Λ.FG → Submodule.span D.host.E (Λ : Set (Fin n → D.host.E)) = ⊤ →
    P.asIdeal • Λ ≤ M → M ≤ Λ → M.toAddSubgroup.relIndex Λ.toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    t ≠ 0 →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) ↔
      ∀ i, ((t • T.1) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    (∀ y : Fin n → GlobalTheory.SplitPlace.RF D, finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
      ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) →
    ∃ Z : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), (∀ i j, Z.1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      (∀ i j, π (finPart D (incA D (ϖ : D.host.E))) * (Z⁻¹).1 i j ∈ Formalism.UG.Ov D.host.F v) ∧
      Valued.v Z.1.det = Valued.v (π (finPart D (incA D (ϖ : D.host.E)))) ^ k ∧
      ∀ y : Fin n → GlobalTheory.SplitPlace.RF D, (finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin n → D.host.E)) ↔
        ∀ i, (((Z⁻¹).1 * (t • T.1)) *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v) := by
  first | exact @GlobalTheory.HeckeLocMatrix.exists_local_matrix | exact GlobalTheory.HeckeLocMatrix.exists_local_matrix | (intros; apply GlobalTheory.HeckeLocMatrix.exists_local_matrix <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
section
set_option autoImplicit false

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

namespace GlobalTheory.HeckeEx

theorem spMap_epsMul_comp (a b : ℂ) {Y : Scheme.{0}} (v : Sp (DualNumber ℂ) ⟶ Y) :
    spMap (epsMul a) ≫ spMap (epsMul b) ≫ v = spMap (epsMul (b * a)) ≫ v := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply RingHom.ext
  intro x
  ext <;> simp [epsMul] <;> ring

theorem exists_lift_deriv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') {p : ℕ} (hp : p.Prime)
    {y y'' : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy'' : y'' = F.u j P') (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hI : IsHkIsog p y y'' C ψ ψp) :
    ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ b, ∃ a, gam a = (p ^ 2) • b) ∧
      ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) := by
  subst hy hy''
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := GlobalTheory.T.heckeIsogeny_lifts_to_lattice_map_scaling_forms _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  refine ⟨gam, h, h1, h2, h3, fun w v hvs hd => ?_⟩
  have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
    pullback.lift_fst _ _ _
  have d0 : IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
    refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
      (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
    · convert ExpChain.isHolTo_ex F i P hP using 2 with z
      exact hfst z
    · convert hd using 2 with z
      exact hfst z
  have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
  have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left := fun z => by
    rw [← Category.assoc, hI.2.2.1, h4]
    exact pullback.lift_fst _ _ _
  simp only [e1] at d1
  exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1

set_option maxHeartbeats 1000000 in

theorem exists_similitude_tri_of_hkPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z → ∃ (gam : (U.X k).Λ →ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (p : ℚ) ^ 2 * Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ w : (U.X k').Λ, ∃ v, gam v = (p ^ 2) • w) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ m < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) m = p * ∑ j ∈ Finset.range (Dw.mult τ), A τ m j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (m : Fin (Dw.mult τ)), A τ m m = Formalism.L2.PjFree.toC (t (some ⟨τ, m⟩) : CAt σ) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ hU P p i k k' x x' C z t hA hK hH hB
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨Pm, hP, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨Pm', hP', per', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hH
  have hpp : p.Prime := hA.2.2.1
  have hC : ∀ a ∈ C, a ^ p ^ 2 = 1 := fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha
  obtain ⟨gam, h, hiso, hh, honto, hder⟩ := exists_lift_deriv F (ik k) (ik k') Pm Pm' per per' hpp hPx
    (hB.1.trans hPx') C ψ ψp hC hI
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hcol : ∀ τ m, h.toLinearMap (Pi.single (e.symm ⟨τ, m⟩) 1) =
      (∑ j, ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ m
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL τ m
    have d2 := hder (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm' per' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ m)
      (z.u τ m)).1 (hPx' ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
      have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
        apply RingHom.ext
        intro a
        ext <;> simp [epsMul]
      rw [e0]
      first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
    have e3 : spMap (epsMul (p : ℂ)) ≫ z.u τ m = wv ≫ ψ ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm' per'
    show h (Pi.single (e.symm ⟨τ, m⟩) 1) = _
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (smul_smul (p : ℂ) (Formalism.L2.PjFree.toC (cf τ m j)) (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))
  refine ⟨(φ k').toLinearMap ∘ₗ gam ∘ₗ (φ k).symm.toLinearMap,
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun w => ?_, fun τ i j hji => ?_,
    fun τ m hm v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
    push_cast
    ring
  · obtain ⟨a, ha⟩ := honto ((φ k').symm w)
    refine ⟨φ k a, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [ha, map_nsmul, LinearEquiv.apply_symm_apply]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨m, hm⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range, Finset.mul_sum]
    refine (GlobalTheory.LevelCusp.apply_of_cols e h.toLinearMap
      (fun τ i j => (p : ℂ) * Formalism.L2.PjFree.toC (cf τ i j)) hcol (Pm v) τ ⟨m, hm⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dif_pos ⟨hm, j.2⟩, _root_.mul_assoc]
  · beta_reduce
    rw [dif_pos ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryMatchingFramesAtNonconjugatePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.FrameMatch

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem frGL_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (y z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    frGL (β * intGL F E n y) z = frGL β (y * z * y⁻¹) := by
  show MulAut.conj (β * intGL F E n y) (intGL F E n z) = MulAut.conj β (intGL F E n (y * z * y⁻¹))
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  group

theorem St_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    St (β * intGL F E n y) = St β := by
  ext x
  show x ∈ (frGL (β * intGL F E n y)).range ↔ x ∈ (frGL β).range
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨y * z * y⁻¹, (frGL_mul_intGL β y z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨y⁻¹ * z * y, ?_⟩
    rw [frGL_mul_intGL]
    congr 1
    group

theorem redFn_mul_intGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E))
    (PP : Pl E) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    redFn (β * intGL F E n y) PP x =
      (Formalism.UG.bc (resS F PP) y)⁻¹ * redFn β PP x * Formalism.UG.bc (resS F PP) y := by
  by_cases hx : x ∈ St β
  · obtain ⟨z, rfl⟩ := MonoidHom.mem_range.1 hx
    have h1 : frGL β z = frGL (β * intGL F E n y) (y⁻¹ * z * y) := by
      rw [frGL_mul_intGL]
      congr 1
      group
    conv_lhs => rw [h1]
    rw [redFn_frGL, redFn_frGL]
    rw [map_mul, map_mul, map_inv]
  · have hx' : x ∉ St (β * intGL F E n y) := by rwa [St_mul_intGL]
    simp only [redFn, ext1, dif_neg hx, dif_neg hx', mul_one, inv_mul_cancel]

theorem frGL_mul (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    frGL β y * β = β * intGL F E n y := by
  simp only [frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_intGL_of_isFrame {β₁ β₂ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : IsFrame β₁ Λ) (h₂ : IsFrame β₂ Λ) : ∃ m : GL (Fin n) (Formalism.L2.Herm.intAf F E), β₂ = β₁ * intGL F E n m := by
  classical

  have key : ∀ {γ δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}, IsFrame γ Λ → IsFrame δ Λ → ∀ i j,
      ((γ⁻¹ * δ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j ∈
        Formalism.L2.Herm.intAf F E := by
    intro γ δ hγ hδ i j
    set v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F :=
      (δ : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec (Pi.single j 1) with hv
    have hvL : v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
      rw [hδ v]
      intro k
      rw [hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rcases eq_or_ne k j with hk | hk
      · subst hk
        simp only [Pi.single_eq_same]
        exact Subring.one_mem _
      · simp only [Pi.single_eq_of_ne hk]
        exact Subring.zero_mem _
    have hi := (hγ v).1 hvL i
    rw [hv, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, ← Units.val_mul] at hi
    simpa [Matrix.transpose_apply] using hi
  let M : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, key h₁ h₂ i j⟩
  let N : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) := fun i j => ⟨_, key h₂ h₁ i j⟩
  have hM : M.map (Formalism.L2.Herm.intAf F E).subtype =
      ((β₁⁻¹ * β₂ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    ext i j
    rfl
  have hN : N.map (Formalism.L2.Herm.intAf F E).subtype =
      ((β₂⁻¹ * β₁ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    ext i j
    rfl
  have hinj : Function.Injective
      (fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) => A.map (Formalism.L2.Herm.intAf F E).subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hone : (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map (Formalism.L2.Herm.intAf F E).subtype = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hMN : M * N = 1 := hinj (by
    simp only [Matrix.map_mul, hM, hN, hone, ← Units.val_mul]
    rw [show β₁⁻¹ * β₂ * (β₂⁻¹ * β₁) = 1 by group, Units.val_one])
  have hNM : N * M = 1 := hinj (by
    simp only [Matrix.map_mul, hM, hN, hone, ← Units.val_mul]
    rw [show β₂⁻¹ * β₁ * (β₁⁻¹ * β₂) = 1 by group, Units.val_one])
  refine ⟨⟨M, N, hMN, hNM⟩, ?_⟩
  have hm : intGL F E n ⟨M, N, hMN, hNM⟩ = β₁⁻¹ * β₂ := by
    ext1
    rw [← hM]
    exact Formalism.UG.P.bc_coe _ _
  rw [hm]
  group

end General

set_option maxHeartbeats 1000000 in

theorem frames_match : ∀ {D : D7} (V : HSp D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∀ β₁ β₂ : GL (Fin V.rank) (EAf D), IsFrame β₁ (Formalism.L2.Herm.crdLat V V.L0) → IsFrame β₂ (Formalism.L2.Herm.crdLat V V.L0) → ∃ u ∈ GfC V, IsFrame (finE V u * β₁) (Formalism.L2.Herm.crdLat V V.L0) ∧ ∀ PP ∈ Pg, ∀ x, redFn (finE V u * β₁) PP x = redFn β₂ PP x := by
  classical
  intro D V Pg hPg β₁ β₂ h₁ h₂
  obtain ⟨m, hm⟩ := exists_intGL_of_isFrame h₁ h₂

  obtain ⟨β₀, ⟨c, h₀⟩, -⟩ := GlobalTheory.StdFrames.exists_frame_std V
  have hB : IsBaseFrame V β₁ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ c) := ⟨h₁, h₀.2⟩

  have hloc : ∀ PP, ∃ κ : GA D V, κ ∈ GfC V ∧ finE V κ ∈ St β₁ ∧
      (PP ∈ Pg → redFn β₁ PP (finE V κ) = Formalism.UG.bc (resS D.host.F PP) m) ∧
      ∀ P', P' ≠ PP → (PP ∈ Pg → ¬ IsConjPl (D := D) PP P') → redFn β₁ P' (finE V κ) = 1 := by
    intro PP
    by_cases hPP : PP ∈ Pg
    · obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (hPg PP hPP PP hPP)
      obtain ⟨κ, -, k1, k2, k3, k4⟩ :=
        GlobalTheory.ParahoricLift.exists_local_lift hB he (Formalism.UG.bc (resS D.host.F PP) m)
      exact ⟨κ, k1, k2, fun _ => k3, fun P' hP' hc => k4 P' hP' (hc hPP)⟩
    · refine ⟨1, Subgroup.one_mem _, ?_, fun h => absurd h hPP, fun P' _ _ => ?_⟩
      · rw [map_one]
        exact Subgroup.one_mem _
      · rw [map_one]
        exact blockDiagonalExtendByOnePrimeField_one (St β₁) (redAt β₁ P')
  choose κ hκG hκS hκR hκO using hloc
  have hprod := GlobalTheory.ParahoricLift.redFn_list_prod V β₁ (Pg.toList.map κ) (by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact hκS b)

  have hred : ∀ PP ∈ Pg, redFn β₁ PP (finE V (Pg.toList.map κ).prod) = Formalism.UG.bc (resS D.host.F PP) m := by
    intro PP hPP
    have hs := GlobalTheory.ParahoricLift.prod_map_single (Finset.nodup_toList Pg) (Finset.mem_toList.2 hPP)
      (fun b => redFn β₁ PP (finE V (κ b)))
      (fun b hb => hκO b PP (Ne.symm hb) (fun hbP => hPg b hbP PP hPP))
    rw [hprod.2 PP, List.map_map]
    exact hs.trans (hκR PP hPP)
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 hprod.1
  refine ⟨(Pg.toList.map κ).prod, (GfC V).list_prod_mem (by
    intro g hg
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hg
    exact hκG b), GlobalTheory.StabLatInv.isFrame_mul_of_mem_St β₁ _ _ h₁ hprod.1, ?_⟩
  intro PP hPP x
  have hz' : Formalism.UG.bc (resS D.host.F PP) z = Formalism.UG.bc (resS D.host.F PP) m := by
    rw [← redFn_frGL β₁ PP z, hz]
    exact hred PP hPP
  rw [← hz, frGL_mul, hm, redFn_mul_intGL, redFn_mul_intGL, hz']

end GlobalTheory.FrameMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormsOfBoundedAdelicFunctionNormBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.BddForms

theorem fg_of_mem_lats {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    (Lv : SW.Level X) {L : Lt E r} (hL : L ∈ Lv.lats) : L.FG := by
  obtain ⟨-, s, hcop, hs, -⟩ := hL
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hcop
    have hle := Ideal.mul_le_left (I := Lv.𝔪) (J := conjI Lv.𝔪)
    rw [hcop] at hle
    exact Lv.proper (top_le_iff.1 hle)
  let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := s • LinearMap.id
  have hinj : Function.Injective f := fun v w h => smul_right_injective _ hs0 h
  have hle : L.map f ≤ X.Λ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hs v hv
  have : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
  exact Submodule.fg_of_fg_map_injective f hinj (isNoetherian_submodule.1 this _ hle)

theorem zpow_mul_rpow_sq (t : ℝ) (ht : 0 < t) (l : ℤ) : t ^ l * (t ^ 2) ^ (-(l : ℝ) / 2) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
    Real.rpow_intCast]
  exact mul_inv_cancel₀ (zpow_ne_zero _ ht.ne')

theorem diag_ne_zero {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  obtain ⟨hdet, hlow⟩ := hb τ
  have htri : (mat b τ).BlockTriangular id := fun a c hca => hlow a c hca
  rw [Matrix.det_of_isUpperTriangular htri, Finset.prod_ne_zero_iff] at hdet
  exact hdet i (Finset.mem_univ _)

theorem exists_isSB_ne (n g : ℕ) : ∃ φ : TF n g, SW.IsSB φ ∧ φ ≠ 0 := by
  have key : ∀ x y : Matrix (Fin n) (Fin g) ℚ, SW.IntM y → (SW.IntM (x + y) ↔ SW.IntM x) := by
    intro x y hy
    constructor
    · intro h k i
      simpa using (h k i).sub (hy k i)
    · intro h k i
      simpa using (h k i).add (hy k i)
  have h0 : SW.IntM (0 : Matrix (Fin n) (Fin g) ℚ) := fun k i => by
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℚ))
  refine ⟨fun x => if SW.IntM x then 1 else 0, ⟨1, one_pos, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases h : SW.IntM x
    · simpa using h
    · simp [h] at hx
  · intro x y hy
    simp only [Nat.cast_one, one_smul, key x y hy]
  · intro h
    have := congrFun h 0
    simp [h0] at this

end GlobalTheory.AdSpan.BddForms

namespace GlobalTheory.AdSpan.BddForms

theorem pnorm_le_of_bdd : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  intro D S T C om hW Lv hn M hw hM hMm B hB f' _hbase c c' z φ hz _hγ _hk v₀ μ _hvac _hμ ep cf hepcf gL hgL F
    _hFd hFb hFφ hφb
  obtain ⟨K, hKφ⟩ := hφb
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hmv : ∀ a, C.IsB (C.mvB a B) := fun a => ((hJ B hB).2.2.2.2.2 a).1
  have hdom : ∀ a, C.xB (C.mvB a B) ∈ C.X.dom := fun a => (hJ _ (hmv a)).2.1
  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := exists_isSB_ne S.rank C.g

  have hz1 : ∀ a ∈ GinfC T, ‖z a‖ = 1 := by
    intro a ha
    obtain ⟨c0, hc0, hc0'⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hW 1 (one_mem _) a ha B hB
    have e1 : om (1, a) (C.Th (C.xB B) φ₀) = z a • C.Th (C.xB (C.mvB a B)) φ₀ := hz a ha φ₀ hφ₀
    have e2 := hc0' φ₀ hφ₀
    have : z a = c0 := RealChar.smul_cancel (RealChar.th_ne C (hdom a) hφ₀ hφ₀ne) (e1.symm.trans e2)
    rw [this, hc0]

  have hstdFG : (stdL D.host.E S.rank).FG := Submodule.fg_span (Set.finite_range _)
  have hec : ∀ L ∈ Lv.lats, ‖ep 1 * cf (gL L)‖ = 1 := by
    intro L hL
    obtain ⟨h1, h2, h3⟩ := hgL L hL
    obtain ⟨e1, e2, -⟩ := hepcf 1 (stdL _ _) (gL L) L (one_mem _) (Red.trivAt_one _ _) hstdFG
      (by rw [Red.fmtC_one]; exact Red.isMov_one _) h1 h2 (fg_of_mem_lats Lv hL) h3
    rw [norm_mul, e1, e2, one_mul]

  have hFa : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, ‖F L (C.xB (C.mvB a B))‖ ≤ K := by
    intro L hL a ha
    have h := hKφ (gL L * a)
    rw [hFφ L hL a ha, norm_mul, norm_mul, hz1 a ha, hec L hL, one_mul, one_mul] at h
    exact h
  refine ⟨K, fun L hL x hx => ?_⟩
  obtain ⟨hON, hbB, hxe, hdm, -⟩ := hob x hx
  obtain ⟨a, ha, hax⟩ := (GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved D S T C B hB).2.1 (o x) hON
  have hox : o x ∈ C.X.dom := hax ▸ hdom a
  have hFo : ‖F L (o x)‖ ≤ K := hax ▸ hFa L hL a ha
  set la := wtOf C.X C.hr c c' S.rank with hla
  have hval : F L x = bchar la (b x) * F L (o x) := by
    have := hFb L hL (o x) hox (b x) hbB
    rw [← hxe] at this
    exact this
  have hprod : ‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2) = 1 := by
    unfold bchar
    simp_rw [norm_prod, norm_zpow]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    exact zpow_mul_rpow_sq _ (norm_pos_iff.2 (diag_ne_zero hbB τ i)) _
  simp only [Data.pnorm]
  simp only [← hdm]
  rw [hval, norm_mul]
  calc ‖bchar la (b x)‖ * ‖F L (o x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)
      = ‖F L (o x)‖ * (‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)) := by ring
    _ = ‖F L (o x)‖ := by rw [hprod, mul_one]
    _ ≤ K := hFo

end GlobalTheory.AdSpan.BddForms
end

