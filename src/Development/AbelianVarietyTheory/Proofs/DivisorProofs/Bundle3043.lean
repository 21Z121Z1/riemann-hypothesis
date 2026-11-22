import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  first | (exact @GlobalTheory.AV.lam_symm_nat_add) | (exact GlobalTheory.AV.lam_symm_nat_add) | (intros; apply GlobalTheory.AV.lam_symm_nat_add  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPointStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  first | exact @GlobalTheory.ChernCalc.frame_eventually_near | exact GlobalTheory.ChernCalc.frame_eventually_near | (intros; apply GlobalTheory.ChernCalc.frame_eventually_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFullFlagFrameChangeDiagonalUnitsStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedFullFlag_frame_change_diagonal_units : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m) (B : Mat m X.Fn),
    B ∈ E.S (genericPoint X.X) → ∀ (z : X.X) (A A' : Mat m X.Fn), A ∈ E.S z → A' ∈ E.S z → ∀ x : Root m,
      UnitAt z ((A' * A⁻¹) x.1 x.2 x.2) ∧ (B * A⁻¹) x.1 x.2 x.2 = (B * A'⁻¹) x.1 x.2 x.2 * (A' * A⁻¹) x.1 x.2 x.2 := by
  first | exact @GlobalTheory.FlagChange.diag_unitAt_and_mul | exact GlobalTheory.FlagChange.diag_unitAt_and_mul | (intros; apply GlobalTheory.FlagChange.diag_unitAt_and_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleDescendsAlongIsogenyTorsorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_lineBundle_descends_along_isogeny_torsor : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B N : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] [GrpObj N] (P : LB (A ⊗ B).left) (i : N ⟶ A) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → P.IsLB → IsAdditive P → Triv (ev P (𝟙 A) (1 : A ⟶ B)) → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback (fst A N) (fst A N * (snd A N ≫ i)) q q → Triv (ev P (fst N B ≫ i) (snd N B)) → ∃ P₀ : LB (A' ⊗ B).left, P₀.IsLB ∧ LBIso (ev P₀ (fst A B ≫ q) (snd A B)) P := by
  first | exact @GlobalTheory.PoincareDescent.descend_torsor | exact GlobalTheory.PoincareDescent.descend_torsor | (intros; apply GlobalTheory.PoincareDescent.descend_torsor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveFinsumOrdLogEqLocalLengths
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.AffineCurveSum

theorem length_quot_eq {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (p : Submonoid B)
    [IsLocalization p S] (b : B) :
    Module.length S (S ⧸ Ideal.span {algebraMap B S b}) =
      Module.length (Localization p) (LocalizedModule p (B ⧸ Ideal.span {b})) := by
  let e := IsLocalization.algEquiv p (Localization p) S
  let : Algebra (Localization p) S := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower B (Localization p) S := .of_algebraMap_eq fun x => (e.commutes x).symm
  have h : Submodule.localized' S p (Algebra.linearMap B S) (Ideal.span {b}) =
      Ideal.span {algebraMap B S b} := by
    rw [Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]
  rw [← h, ← Module.length_eq_of_surjective (S := Localization p) (R := S) e.surjective]
  exact (((IsLocalizedModule.iso p (Submodule.toLocalizedQuotient' S p (Algebra.linearMap B S)
    (Ideal.span {b}))).extendScalarsOfIsLocalization p (Localization p)).length_eq).symm

theorem finsum_ord_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsAffine Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ b : Γ(Y, ⊤), b ≠ 0 → ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ m : MaximalSpectrum Γ(Y, ⊤), ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl (Γ(Y, ⊤) ⧸ Ideal.span {b}))).toNat : ℝ) * Real.log (Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal)) := by
  intro k _ Y _ _ _ q hq b hb
  have hU := isAffineOpen_top Y
  have hd : ringKrullDim Γ(Y, ⊤) = 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    have := (Scheme.homeoOfIso Y.isoSpec).isHomeomorph.topologicalKrullDim_eq
    exact this.symm.trans (hq.dim_eq.trans (by simp))
  have hc (z : Y) : (Order.coheight z : WithBot ℕ∞) =
      (hU.primeIdealOf ⟨z, trivial⟩).asIdeal.height := by
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨z, trivial⟩ : (⊤ : Y.Opens))
    have := hU.isLocalization_stalk ⟨z, trivial⟩
    exact (ringKrullDim_stalk_eq_coheight z).symm.trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height _ _)
  have hK : Ring.KrullDimLE 1 Γ(Y, ⊤) := Ring.krullDimLE_iff.2 (by simp [hd])
  have hmax (P : PrimeSpectrum Γ(Y, ⊤)) : P.asIdeal.height = 1 ↔ P.asIdeal.IsMaximal := by
    constructor
    · intro h
      refine Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hK _ (fun h0 => ?_) P.isPrime
      rw [h0, Ideal.height_bot] at h
      exact zero_ne_one h
    · intro h
      have h1 : P.asIdeal.height ≤ 1 := by
        have := (Ideal.height_le_ringKrullDim_of_ne_top h.ne_top).trans_eq hd
        exact_mod_cast this
      refine le_antisymm h1 (Order.one_le_iff_ne_zero.2 fun h0 => ?_)
      have h2 : P.asIdeal = ⊥ := by
        simpa [IsDomain.minimalPrimes_eq_singleton_bot] using Ideal.height_eq_zero_iff.1 h0
      have h3 : IsField Γ(Y, ⊤) := Ring.isField_iff_maximal_bot.2 (h2 ▸ h)
      rw [ringKrullDim_eq_zero_of_isField h3] at hd
      exact zero_ne_one hd
  let i : MaximalSpectrum Γ(Y, ⊤) → Y := fun m => hU.fromSpec m.toPrimeSpectrum
  have hi : Function.Injective i :=
    hU.fromSpec.isOpenEmbedding.injective.comp (MaximalSpectrum.toPrimeSpectrum_injective)
  have hp (m) : hU.primeIdealOf ⟨i m, trivial⟩ = m.toPrimeSpectrum :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  rw [← finsum_mem_univ, ← finsum_mem_inter_support_eq' _ (Set.range i) Set.univ ?_, finsum_mem_range hi]
  · refine finsum_congr fun m => ?_
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨i m, trivial⟩ : (⊤ : Y.Opens))
    have hl : IsLocalization.AtPrime (Y.presheaf.stalk (i m)) m.asIdeal := by
      have := hU.isLocalization_stalk ⟨i m, trivial⟩
      convert this
      exact congrArg PrimeSpectrum.asIdeal (hp m).symm
    have h1 : Order.coheight (i m) = 1 := by
      have := hc (i m)
      rw [hp, (hmax _).2 m.isMaximal] at this
      exact_mod_cast this
    have hb' : algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (i m)) b ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective _ m.asIdeal.primeCompl_le_nonZeroDivisors)).2 hb
    have h2 := ord_algebraMap h1 hb'
    rw [length_quot_eq m.asIdeal.primeCompl] at h2
    have h3 : algebraMap Γ(Y, ⊤) Y.functionField b =
        algebraMap _ Y.functionField (algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (i m)) b) :=
      (algebraMap_germ (Opens.mem_top (i m)) b).symm
    have h4 : Nat.card (Y.residueField (i m)) = Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal) :=
      Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m.asIdeal
        (Y.presheaf.stalk (i m))).symm.toEquiv
    rw [h3, h2, h4, Int.cast_natCast]
  · intro z hz
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have h1 : Order.coheight z = 1 := by
      by_contra h
      exact hz (by simp [Scheme.ord_eq_zero_of_coheight_neq_one h])
    have h2 := hc z
    rw [h1] at h2
    exact ⟨⟨_, (hmax (hU.primeIdealOf ⟨z, trivial⟩)).1 (by exact_mod_cast h2.symm)⟩,
      hU.fromSpec_primeIdealOf ⟨z, trivial⟩⟩

end GlobalTheory.AffineCurveSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveSumComplexPointsLogEqRingHo
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AffCurveSum

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] [IsAffine Y] {q : Y ⟶ Sp k}

def evTop (y : Σ σ : k →+* ℂ, CxPts q σ) : Γ(Y, ⊤) →+* ℂ := evHom (y := y.2) mem_ptsIn_top

theorem evTop_apply (y : Σ σ : k →+* ℂ, CxPts q σ) (b : Γ(Y, ⊤)) :
    evTop y b = ev q y.1 ⊤ b y.2 := (ev_eq mem_ptsIn_top b).symm

theorem evTop_bijective : Function.Bijective (evTop (q := q)) := by
  constructor
  · rintro ⟨σ, y⟩ ⟨σ', y'⟩ h
    have hσ : σ = σ' := RingHom.ext fun a => by
      have := congrArg (fun φ : Γ(Y, ⊤) →+* ℂ => φ (algX q ⊤ a)) h
      simp only [evTop_apply, ev_algX mem_ptsIn_top] at this
      exact this
    subst hσ
    have hy : y = y' := Subtype.ext (Points.ext_of_valR (isAffineOpen_top Y)
      (mem_ptsIn_top : y ∈ ptsIn q σ ⊤) (mem_ptsIn_top : y' ∈ ptsIn q σ ⊤) fun f => by
        have := congrArg (fun φ : Γ(Y, ⊤) →+* ℂ => φ f) h
        simp only [evTop_apply] at this
        exact this)
    rw [hy]
  · intro τ
    refine ⟨⟨τ.comp (algX q ⊤), ofHom (p := q) (σ := τ.comp (algX q ⊤)) (isAffineOpen_top Y) τ
      (fun _ => rfl)⟩, ?_⟩
    ext f
    rw [evTop_apply]
    exact ev_ofHom (p := q) (σ := τ.comp (algX q ⊤)) (isAffineOpen_top Y) τ (fun _ => rfl) f

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsAffine Y] (q : Y ⟶ Sp k),
    IsArithVar q 0 → ∀ b : Γ(Y, ⊤), ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ,
      Real.log ‖ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y‖ =
        ∑ᶠ τ : Γ(Y, ⊤) →+* ℂ, Real.log ‖τ b‖ := by
  intro k _ Y _ _ q hq b
  have := hq.finite_emb
  have (σ : k →+* ℂ) := ArchDimZero.finite_cxPts hq σ
  let := Fintype.ofFinite (k →+* ℂ)
  let (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  let e := Equiv.ofBijective _ (evTop_bijective (q := q))
  have : Finite (Γ(Y, ⊤) →+* ℂ) := .of_equiv _ e
  let := Fintype.ofFinite (Γ(Y, ⊤) →+* ℂ)
  have hv (σ : k →+* ℂ) (y : CxPts q σ) :
      ratVal (algebraMap Γ(Y, ⊤) Y.functionField b) y = evTop ⟨σ, y⟩ b := by
    exact (ratVal_fnOf mem_ptsIn_top _ b).trans (evTop_apply ⟨σ, y⟩ b).symm
  simp only [hv, finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_sigma (fun x : (Σ σ : k →+* ℂ, CxPts q σ) => Real.log ‖evTop x b‖)]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.AffCurveSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStepStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraisation_of_proper_modification_noetherian_step : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → ∀ (W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) → ∀ K : W.IdealSheafData, (∀ x, x ∉ K.support → x ∈ U) → Alg (π ≫ f) I → (∀ k : ℕ, Alg ((K ^ k).subschemeι ≫ f) I) → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_modification | exact GlobalTheory.FormalAlg.alg_of_modification | (intros; apply GlobalTheory.FormalAlg.alg_of_modification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleCubicalLineBundleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_ample_cubical_lineBundle_abelianVariety : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∃ L : LB B.left, GlobalTheory.SS.AmpleCub B L := by
  first | exact @GlobalTheory.SS.exists_ampleCub_of_isAbelianScheme | exact GlobalTheory.SS.exists_ampleCub_of_isAbelianScheme | (intros; apply GlobalTheory.SS.exists_ampleCub_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalRealDual
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.RiemFormKer.smul_mem_lattice : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : u.Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ u.Λ := by
  intro F _ _ _ 𝔠 X c hc u e hu h χ hAH x hx a ha
  obtain ⟨U0, hU0⟩ := GlobalTheory.T.product_abelian_uniformization X.A X.ab (X.diag c) _ u
  have hAb2 := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  obtain ⟨U, H, χ', hUex, hF⟩ := GlobalTheory.T.exists_appell_humbert_line_bundle (X.A ⊗ X.A) hAb2 _ _ U0 (X.P c) (X.isLB c)
  have hex : ∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y) := fun x y => by rw [hUex]; exact hU0 x y
  have hb := GlobalTheory.T.torus_real_mult_appell_humbert F 𝔠 X c hc u e hu h χ hAH U H χ' hex hF
  have hχ := GlobalTheory.T.product_torus_factor_appell_humbert X.A (X.diag c) _ u (X.P c) (X.isLB c) (X.rig₂ c) U H χ' hex hF
    (fun z w => by rw [hb]; simp [hermForm])
  obtain ⟨u', hu'ex, hu'ch, hu'fr⟩ := GlobalTheory.T.translated_uniformization_pullback X.A (X.diag c) _ u (X.P c) U hex x
  have hgen : HasGen ((X.P c).pull (lift (𝟙 X.A) (toUnit X.A ≫ u.ex x)).left) := by
    refine GlobalTheory.T.theta_nonvanishing_bundle_generated X.A X.ab (GlobalTheory.T.totally_positive_polarization_projective F 𝔠 X c hc) _ (LB.isLB_pull (X.isLB c) _) _ u'
      (fun z => Complex.exp (Real.pi * hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) z x / 2)) ?_
      (fun z => Complex.exp_ne_zero _) ?_
    · simp only [hermForm, dotProduct]
      fun_prop
    · intro l hl i z hz
      have hlu : l ∈ u.Λ := by rw [← u.ker, ← hu'ex]; exact (u'.ker l).2 hl
      have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
      have hm : Fin.append l (0 : Fin (Module.finrank ℚ F) → ℂ) ∈ U.Λ := by
        rw [← U.ker, hex, (u.ker l).2 hlu, ← h0, ← hex]
        have hz0 : Fin.append (0 : Fin (Module.finrank ℚ F) → ℂ) (0 : Fin (Module.finrank ℚ F) → ℂ) = 0 := by
          funext k
          refine Fin.addCases (fun k => ?_) (fun k => ?_) k
          · simp only [Fin.append_left, Pi.zero_apply]
          · simp only [Fin.append_right, Pi.zero_apply]
        rw [hz0]
        exact (U.ker 0).2 U.Λ.zero_mem
      have hz' : ⊤ ≤ (U.ex (Fin.append z x)).left ⁻¹ᵁ (X.P c).U (i PUnit.unit) := (hu'ch i z).1 hz
      have happ : Fin.append z x + Fin.append l 0 = Fin.append (z + l) x := by
        funext k
        refine Fin.addCases (fun k => ?_) (fun k => ?_) k
        · simp only [Pi.add_apply, Fin.append_left]
        · simp only [Pi.add_apply, Fin.append_right, Pi.zero_apply, add_zero]
      have e1 : hermForm H (Fin.append z x) (Fin.append l 0) =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l / 2 := by
        rw [hb]; simp [hermForm]
      have e2 : hermForm H (Fin.append l 0) (Fin.append l 0) = 0 := by
        rw [hb]; simp [hermForm]
      have hf : U.fr (i PUnit.unit) (Fin.append z x) = Complex.exp (Real.pi *
          (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l / 2)) * U.fr (i PUnit.unit) (Fin.append (z + l) x) := by
        have h3 := hF.2.2 ⟨_, hm⟩ (i PUnit.unit) (Fin.append z x) hz'
        rw [hχ ⟨_, hm⟩ l rfl, _root_.one_mul] at h3
        dsimp only at h3
        rw [h3, happ]
        congr 2
        rw [show (Fin.append z x ⬝ᵥ H.mulVec (star (Fin.append l 0))) = hermForm H (Fin.append z x) (Fin.append l 0) from rfl,
          show (Fin.append l 0 ⬝ᵥ H.mulVec (star (Fin.append l 0))) = hermForm H (Fin.append l 0) (Fin.append l 0) from rfl,
          e1, e2]
        ring
      obtain ⟨n, hn⟩ := hx ⟨l, hlu⟩
      have hs : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l = ∑ j, (h j : ℂ) * (x j * starRingEnd ℂ (l j)) := by
        simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hsw : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) l x =
          starRingEnd ℂ (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l) := by
        simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def, map_sum, map_mul,
          Complex.conj_conj, Complex.conj_ofReal]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hadd : hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) (z + l) x =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) z x + hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) l x := by
        simp only [hermForm, add_dotProduct]
      have hc : starRingEnd ℂ (hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l) =
          hermForm (Matrix.diagonal fun j ↦ (h j : ℂ)) x l - 4 * n * Complex.I := by
        rw [hs]
        apply Complex.ext
        · simp
        · simp only [Complex.conj_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im]
          rw [hn]
          simp
          ring
      rw [hu'fr, hu'fr, hf]
      beta_reduce
      rw [← _root_.mul_assoc, ← Complex.exp_add]
      congr 1
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-n, ?_⟩
      rw [hadd, hsw, hc]
      push_cast
      ring
  have hgen2 : HasGen ((X.P c).pull (lift (fst X.A (𝟙_ (Over (Sp ℂ)))) (snd X.A (𝟙_ (Over (Sp ℂ))) ≫ u.ex x)).left) := by
    obtain ⟨t, ht⟩ := hgen
    have hm : lift (fst X.A (𝟙_ (Over (Sp ℂ)))) (snd X.A (𝟙_ (Over (Sp ℂ))) ≫ u.ex x) =
        fst X.A (𝟙_ (Over (Sp ℂ))) ≫ lift (𝟙 X.A) (toUnit X.A ≫ u.ex x) := by
      ext
      · simp
      · have hs : snd X.A (𝟙_ (Over (Sp ℂ))) = fst X.A (𝟙_ (Over (Sp ℂ))) ≫ toUnit X.A := toUnit_unique _ _
        simp [hs]
    rw [hm, Over.comp_left]
    exact ⟨LB.pullGen _ (fun _ : PUnit => _) (fun _ => 1) t (fst X.A _).left, DVR.pullGen_isGen _ _ _ t ht _⟩
  have h1 := X.ker c (𝟙_ _) (u.ex x) hgen2 a ha
  rw [← u.ker, hu a x]
  exact h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFrameLogDerivativeQuasiPeriodicStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_frame_log_derivative_quasi_periodic : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → L.IsLB → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH H χ → ∀ v : Fin g → ℂ, (∀ i, DifferentiableOn ℂ (fun z => fderiv ℂ (u.fr i) z v / u.fr i z) (pre u.ex (L.U i))) ∧ (∀ i j, IsReg u.ex (L.U i ⊓ L.U j) ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z)) ∧ ∀ i (l : u.Λ), ∀ z ∈ pre u.ex (L.U i), fderiv ℂ (u.fr i) (z + l) v / u.fr i (z + l) = fderiv ℂ (u.fr i) z v / u.fr i z - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  first | exact @GlobalTheory.CechPer.LogDer.main | exact GlobalTheory.CechPer.LogDer.main | (intros; apply GlobalTheory.CechPer.LogDer.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximateGermMemCartierIdealModMaxPow
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.FibreCorr

theorem nonUnitAt_of_isHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z}
    (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {x' : M.Z} {h : Ω} (hh : NonUnitAt M₁ (π x') h) : NonUnitAt M x' h := by
  obtain ⟨hO, h0⟩ := hh
  refine ⟨mem_O_of_isHom hπ hO, ?_⟩
  rcases h0 with h0 | hinv
  · exact Or.inl h0
  · right
    intro hinv'
    obtain ⟨V, g, hzV, rfl⟩ := hO
    have hV : (V : Set M₁.Z).Nonempty := ⟨_, hzV⟩
    have hnu : ¬ IsUnit (⟨valF M₁.pt V g, RatModel.valF_mem_O hzV g⟩ : M₁.O (π x')) := by
      rw [RatModel.isUnit_O_iff]
      exact fun H => hinv H.2
    rw [RatModel.isUnit_valF_iff hzV g] at hnu
    have hx : x' ∈ π ⁻¹ᵁ V := hzV
    have happ := hπ.valF_app hV g
    simp only [AlgHom.id_apply] at happ
    have hnu' : ¬ IsUnit (⟨valF M.pt (π ⁻¹ᵁ V) ((π.app V).hom g), RatModel.valF_mem_O hx _⟩ : M.O x') := by
      rw [RatModel.isUnit_valF_iff hx]
      intro hb
      apply hnu
      have : x' ∈ π ⁻¹ᵁ M₁.Z.basicOpen g := by
        rw [Scheme.preimage_basicOpen]; exact hb
      exact this
    apply hnu'
    rw [RatModel.isUnit_O_iff]
    refine ⟨?_, ?_⟩
    · show valF M.pt _ _ ≠ 0
      rw [happ]
      intro h0
      have : valF M₁.pt V g = 0 := h0
      rw [this, inv_zero] at hinv
      exact hinv (zero_mem _)
    · simpa only [happ] using hinv'

end GlobalTheory.FibreCorr

theorem GlobalTheory.FibreCorr.locbound : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → ∀ (z : M₁.Z) (x' : M.Z), π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∀ F ∈ GlobalTheory.FibreCorr.approxIdeal hπ U D z n, ∃ a b : M.O x', (F : Ω) = a * f' + b ∧ b ∈ maximalIdeal (M.O x') ^ e := by
  intro o Ω _ _ _ _ M₁ M π hπ hN U D hU z x' hx hc f' hf e
  obtain ⟨i, hi, rfl⟩ := hf
  have hne : valF M.pt (D.U i) (D.f i) ≠ 0 := by
    intro h0
    haveI : Nontrivial Γ(M.Z, D.U i) := RingHom.domain_nontrivial (M.Z.presheaf.germ (D.U i) x' hi).hom
    have hreg := D.regular i (D.U i) le_rfl
    have h00 : D.f i = 0 := by
      apply RatModel.valF_injective M ⟨x', hi⟩
      rw [h0]
      unfold valF
      split_ifs <;> simp
    rw [h00, map_zero] at hreg
    exact zero_notMem_nonZeroDivisors hreg
  obtain ⟨C, hC⟩ := GlobalTheory.T.izumi_bound_mod_principal_ideal o Ω M hN U hU x' hc _ (RatModel.valF_mem_O hi (D.f i)) hne
  refine ⟨C e, fun n hn F hF => ?_⟩
  have hF' := approxIdeal_antitone U D z hn hF
  have hFO : (F : Ω) ∈ M.O x' := mem_O_of_isHom hπ (hx ▸ F.2)
  obtain ⟨a, b, hab, hb⟩ := hC e ⟨F, hFO⟩ (by
    intro p _ y hy
    obtain ⟨hyx, hyU⟩ := hy
    have hz : π (y (cPt p)) = z := by rw [hyx, hx]
    rcases hF' p y hz hyU _ ⟨i, hyx ▸ hi, rfl⟩ with h1 | ⟨h, hh, hle⟩
    · exact Or.inl h1
    · refine Or.inr ⟨h, nonUnitAt_of_isHom hπ (x' := x') (by rw [hx]; exact hh), hle⟩)
  refine ⟨a, b, hab, ?_⟩
  have hsp : Ideal.span {c : M.O x' | ¬ IsUnit c} = maximalIdeal (M.O x') := Ideal.span_eq (maximalIdeal (M.O x'))
  rwa [hsp] at hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableOfProjArithAmbient
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem archIntegrable_of_isAmb : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) →
    ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro H k _ Y _ q hq e he M N r hr σ
  rcases isEmpty_or_nonempty (CxPts q σ) with h0 | ⟨⟨y⟩⟩
  · exact ⟨MeasureTheory.Integrable.of_isEmpty, MeasureTheory.Integrable.of_isEmpty⟩
  · have hc : CharZero Γ(Y, ⊤) :=
      RingHom.charZero (S := ℂ) ((Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp y.1.appTop.hom)
    exact H k Y q e ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 hc, he⟩ M N r hr σ

end GlobalTheory.MixHt
end

