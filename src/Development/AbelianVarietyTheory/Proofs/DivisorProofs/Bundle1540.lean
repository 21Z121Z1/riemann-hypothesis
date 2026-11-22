import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSelfDualLatticeBoundedMajorantLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqZeroOfAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegOfRankPullbackIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false
noncomputable section
open scoped GlobalTheory.ProjSpace
namespace GlobalTheory.CxLine

section Iso

variable {X Y : Scheme.{0}} (e : Y ≅ X)

def pullEquiv : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackId X).symm ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id.symm ≪≫
      (Scheme.Modules.pullbackComp e.inv e.hom).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId Y)

def pushPullIso (G : X.Modules) :
    G ≅ (Scheme.Modules.pushforward e.hom).obj ((Scheme.Modules.pullback e.hom).obj G) :=
  (pullEquiv e).unitIso.app G ≪≫
    ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).rightAdjointUniq
      (pullEquiv e).toAdjunction).symm.app ((Scheme.Modules.pullback e.hom).obj G)

variable {k : Type} [Field k] [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]

theorem degOfRank_pullback_iso
    (hf : ∀ r : k, e.hom.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r)
    (G : X.Modules) (r : ℕ) :
    degOfRank k ((Scheme.Modules.pullback e.hom).obj G) r = degOfRank k G r := by
  have h₁ : chi k G = chi k ((Scheme.Modules.pullback e.hom).obj G) :=
    (chi_congr k (pushPullIso e G)).trans (chi_pushforward_of_isClosedImmersion hf _)
  have h₂ : chi k (structureModule X) = chi k (structureModule Y) :=
    (chi_congr k (asIso (unitToPush e.hom))).trans (chi_pushforward_of_isClosedImmersion hf _)
  rw [degOfRank, degOfRank, h₁, h₂]

end Iso

end GlobalTheory.CxLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DimCover

theorem exists_trdeg_eq_and_dim_eq {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [IsProper f]
    [Flat f] : ∃ d : ℕ, Algebra.trdeg ℤ (X.residueField (genericPoint X)) = d ∧
      topologicalKrullDim X = (d + 1 : ℕ) := by
  obtain ⟨A, _, _, _, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq f (genericPoint X)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  rw [hA] at hd
  have h₁ := topologicalKrullDim_preimage_genericPoint_eq f hd
  have H := IsPullback.of_hasPullback f (spMap (algebraMap ℤ ℚ))
  have := IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  obtain ⟨e₁, r₁⟩ := isEmbedding_and_range_eq_of_isPullback f H
  have hr₁ : Set.range (spMap (algebraMap ℤ ℚ)) = {genericPoint (Spec (.of ℤ))} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap ℤ ℚ) x.asIdeal = ⊥
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)
  rw [hr₁] at r₁
  refine ⟨d, ?_, IntModel.topologicalKrullDim_eq_succ Int.not_isField H
    ((topologicalKrullDim_eq_of_isEmbedding e₁ r₁).symm.trans h₁)⟩
  have hb : Function.Bijective (IsLocalRing.residue X.functionField) :=
    ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
  have e := ((RingEquiv.ofBijective _ hb).toIntAlgEquiv).trdeg_eq
  exact e.symm.trans
    ((congrArg (@Algebra.trdeg ℤ X.functionField _ _) (Subsingleton.elim _ _)).trans hd)

theorem charZero_residueField {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp ℤ) [Flat f] :
    CharZero (X.residueField (genericPoint X)) := by
  have := (flat_int_iff_charZero f).1 inferInstance
  have : CharZero X.functionField :=
    ((X.presheaf.germ ⊤ (genericPoint X) trivial).hom.charZero_iff
      (germ_injective_of_isIntegral X _ _)).1 this
  exact ((IsLocalRing.residue X.functionField).charZero_iff (RingHom.injective _)).1 this

theorem topologicalKrullDim_eq (k : Type) [CommRing k] (Y Z : Scheme.{0}) [IsIntegral Y]
    [IsIntegral Z] (p : Y ⟶ Sp k) (q : Z ⟶ Sp k) (D : ℕ) (h : IsArithVar p D) (hq : IsProjOver q)
    (hf : Flat (q ≫ spMap (Int.castRingHom k))) (g : Z ⟶ Y) (_ : g ≫ p = q)
    (hη : g (genericPoint Z) = genericPoint Y) (hd : g.residueDegree (genericPoint Z) ≠ 0) :
    topologicalKrullDim Z = (D + 1 : ℕ) := by
  have := h.finite
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 this
  have := CommonModel.isProper_of_isProjOver hq
  have := CommonModel.isProper_of_isProjOver h.isProjOver
  have := h.flat
  obtain ⟨a, ha, ha'⟩ := exists_trdeg_eq_and_dim_eq (p ≫ spMap (Int.castRingHom k))
  obtain ⟨b, hb, hb'⟩ := exists_trdeg_eq_and_dim_eq (q ≫ spMap (Int.castRingHom k))
  rw [← hη] at ha
  let := (g.residueFieldMap (genericPoint Z)).hom.toAlgebra
  have : Module.Finite (Y.residueField (g (genericPoint Z))) (Z.residueField (genericPoint Z)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hd)
  have : CharZero (Y.residueField (g (genericPoint Z))) :=
    hη ▸ charZero_residueField (p ≫ spMap (Int.castRingHom k))
  have e := trdeg_eq_of_isAlgebraic_top ℤ (Y.residueField (g (genericPoint Z)))
    (Z.residueField (genericPoint Z))
  obtain rfl : b = a := by exact_mod_cast hb.symm.trans (e.trans ha)
  rw [hb', ← ha', h.dim_eq]

end GlobalTheory.DimCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSelfDualLatticeBoundedMajorantLeStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_selfDualLattice_bounded_majorant_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε R : ℝ), x ∈ X.dom → 0 < ε → 0 ≤ R → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({v | v ∈ X.L' ∧ ∑ τ, X.maj x τ (Data.emb τ.1 v) ≤ R}.encard : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt (R / ε)) ^ (2 * fdeg E * r)) := by
  first | exact @GlobalTheory.LatCount.encard_le | exact GlobalTheory.LatCount.encard_le | (intros; apply GlobalTheory.LatCount.encard_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnifTangent

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem eq_of_values {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x x' : Sp ℂ ⟶ X} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : ∀ f, valAt' x U f = valAt' x' U f) : x = x' := by
  refine (AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x h).symm.trans
    (Eq.trans ?_ (AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x' h'))
  congr 2
  ext1
  refine RingHom.ext fun f => ?_
  have := e f
  rw [valAt', valAt', dif_pos h, dif_pos h'] at this
  exact this

theorem fderiv_eq_zero_of_origin {w : Fin g → ℂ}
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0)
    (z : Fin g → ℂ) (U : A.left.Opens) (f : Γ(A.left, U)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) :
    fderiv ℂ (fun z => valAt' (u.ex z).left U f) z w = 0 := by
  let τ : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A
  have hτ : ∀ v, u.ex v ≫ τ = u.ex (z + v) := fun v => by
    rw [u.ex_add, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (τ.left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, hτ, add_zero]
    exact h
  have e : (fun v => valAt' (u.ex v).left (τ.left ⁻¹ᵁ U) ((τ.left.app U).hom f)) =
      fun v => valAt' (u.ex (z + v)).left U f := funext fun v => by
    rw [valAt'_comp, ← Over.comp_left, hτ]
  have := hw _ ((τ.left.app U).hom f) h0
  rw [e, fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), add_zero] at this
  exact this

theorem eq_zero_of_fderiv_eq_zero (w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) : w = 0 := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := A.left)
    (x := (u.ex 0).left (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hx
  haveI := u.discrete
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set u.Λ))
  have hO0 : (0 : Fin g → ℂ) ∈ O := by
    have : (0 : u.Λ) ∈ Subtype.val ⁻¹' O := hOe ▸ rfl
    exact this
  have hc : Continuous fun t : ℂ => t • w := by fun_prop
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 ((((u.hol U 0).1).inter hO).preimage hc) 0
    (by simpa only [Set.mem_preimage, zero_smul] using ⟨h0, hO0⟩)
  have ht : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hd : ∀ f, ∀ t ∈ Metric.ball (0 : ℂ) ε, HasDerivAt (fun t : ℂ => valAt' (u.ex (t • w)).left U f) 0 t := by
    intro f t ht
    have h1 := ((u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds (hB ht).1)).hasFDerivAt
    have h2 := h1.comp_hasDerivAt t ((hasDerivAt_id t).smul_const w)
    rw [one_smul, fderiv_eq_zero_of_origin u hw _ U f (hB ht).1] at h2
    exact h2
  have he : u.ex (((ε / 2 : ℝ) : ℂ) • w) = u.ex ((0 : ℂ) • w) := by
    refine Over.OverMorphism.ext (eq_of_values hU (hB ht).1 (hB (Metric.mem_ball_self hε)).1 fun f => ?_)
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) ε).isPreconnected
      (fun t ht => (hd f t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hd f t ht).deriv) ht
      (Metric.mem_ball_self hε)
  rw [zero_smul, (u.ker 0).2 (zero_mem _), u.ker] at he
  have h3 : (⟨_, he⟩ : u.Λ) ∈ ({0} : Set u.Λ) := hOe ▸ (hB ht).2
  exact (smul_eq_zero.1 (congrArg Subtype.val h3)).resolve_left (Complex.ofReal_ne_zero.2 (by positivity))

theorem tangent_bijection (hs : SmoothOfRelativeDimension g A.hom) :
    (∀ v : epsR ℂ ⟶ A, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v : epsR ℂ ⟶ A, IsTangent v ∧ u.IsDiff w v :=
  TangentOrigin.tangent_bijection_of_values valAt'_rules A L g u
    (exists_coord_adapted (HolChart.exists_holomorphic_chart valAt'_rules existsUnique_point_of_ringHom
      exists_holomorphic_section_of_etale) A L g u hs (eq_zero_of_fderiv_eq_zero u))

theorem riemannData_tangent : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y),
    (∀ v : epsR ℂ ⟶ d.B, IsTangent v → ∃! w, d.u.IsDiff w v) ∧
      (∀ w, ∃! v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff w v) := fun _ P _ d =>
  tangent_bijection d.u
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback d.isPull.1 P.smoothDim)

end GlobalTheory.UnifTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvREqOfReadsSmul
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

theorem frBor_genDiag {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (s' : LB.Sec (PPx y.x)) (hs' : GlobalTheory.Frames.SecGen y.x s') (a : Sˣ)
    (h : ∀ i, s'.f i = scal y.x (a : S) i * y.s.f i) :
    FrBor (GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.genDiag Dw a) y { y with s := s', gen := hs' } := by
  refine ⟨rfl, fun τ i => ⟨(1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) i, Matrix.one_apply_eq i,
    fun j hij => Matrix.one_apply_ne hij.ne, (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y y).1.2.1 τ i⟩,
    𝟙 _, Category.id_comp _, Category.id_comp _, fun i hi => ?_⟩
  refine Eq.trans ?_ (h i).symm
  exact congrArg (fun m => CommRingCat.Hom.hom m (scal y.x (a : S) i * y.s.f i))
    ((Gx y.x).presheaf.map_id (Opposite.op ((PPx y.x).U i)))

set_option maxHeartbeats 1000000 in

theorem evR_eq_of_reads_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → (∀ z, (A'.ex z).left = (A.ex z).left) → (∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A'.fr j z = A.fr j z) → ∀ (θ : (Fin g → ℂ) → ℂ) (t : ℂ), A.Reads 1 y.s θ → A'.Reads 1 y'.s (t • θ) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evR Xo c f y' = t ^ n * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' _ _ _ hex hfr θ t hR hR' a n f hf
  have hx : y'.x = y.x := (Over.w (A'.ex 0)).symm.trans
    ((congrArg (· ≫ Xo.univ.t.G.hom) (hex 0)).trans (Over.w (A.ex 0)))
  have hu : y'.u = y.u := funext fun τ => funext fun i =>
    GlobalTheory.PointUnif.deriv_unique (by simpa only [hex] using A'.der ⟨τ, i⟩) (A.der ⟨τ, i⟩)
  obtain ⟨x', ho', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hu
  subst hx hu
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have V := GlobalTheory.sec_values_complex_fibre hT E H Dw l Xo y.x
  have key : ∀ i (pt : Sp ℂ ⟶ Gx y.x), pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 _ →
      valAt' pt ((PPx y.x).U i) (s'.f i) = t * valAt' pt ((PPx y.x).U i) (y.s.f i) := by
    intro i pt hp
    by_cases hi : ⊤ ≤ pt ⁻¹ᵁ (PPx y.x).U i
    · have hw : (pt ≫ Formalism.L2.PjFree.gxFst y.x) ≫ Xo.univ.t.G.hom = y.x := by
        have h1 := Over.w (CartesianMonoidalCategory.snd (Over.mk y.x) Xo.univ.t.G)
        have h2 := Over.w (CartesianMonoidalCategory.fst (Over.mk y.x) Xo.univ.t.G)
        refine (Category.assoc _ _ _).trans ((congrArg (pt ≫ ·) (h1.trans h2.symm)).trans ?_)
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.x) hp).trans (Category.id_comp _))
      obtain ⟨z, hz⟩ := A.ex_onto (Over.homMk (pt ≫ Formalism.L2.PjFree.gxFst y.x) hw)
      have hz' : pt ≫ Formalism.L2.PjFree.gxFst y.x = (A.ex z).left := (congrArg (·.left) hz).symm
      obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun q => congrArg i (Fin.fin_one_eq_zero q)⟩
      have hj : ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
        rw [← hz']
        exact fun q hq => Set.mem_iInter.1 (hi hq) 0
      have e1 := hR j z pt hz' hp hj
      have e2 := hR' j z pt (hz'.trans (hex z).symm) hp (by rw [hex]; exact hj)
      rw [hfr j z hj, Pi.smul_apply, smul_eq_mul, mul_assoc] at e2
      exact e2.trans (congrArg (t * ·) e1.symm)
    · rw [ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_of_not _ _ hi, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_of_not _ _ hi, mul_zero]
  have ht : t ≠ 0 := by
    obtain ⟨i, pt, hp, hv⟩ := (V s').2.1.1 gen'
    exact fun h0 => hv (by rw [key i pt hp, h0, zero_mul])
  obtain ⟨b, hb, -⟩ := y.gen s'
  have hbt : b = t := by
    obtain ⟨i, pt, hp, hv⟩ := (V y.s).2.1.1 y.gen
    refine mul_right_cancel₀ hv ?_
    rw [← key i pt hp, hb i, (V y.s).1 b i pt hp]
  subst hbt
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hw := (GlobalTheory.borDesc_and_wtField E H Dw l Xo c).2 a n f hf ℂ _ y _ (hA ℂ y) (hA ℂ _)
    (frBor_genDiag y s' gen' (Units.mk0 b ht) hb)
  refine hw.trans (congrArg (· * evR Xo c f y) ?_)
  unfold wchar
  rw [Fintype.prod_option]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.genDiag, ex]

end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalCompactSmall
section
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

namespace GlobalTheory.GLTwoHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_adicCompletionIntegers_loc (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem eventually_singleNU_mem {N : Set (FiniteAdeleRing (𝓞 E) E)} (hN : N ∈ 𝓝 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ y ∈ w.adicCompletionIntegers E, singleNU w y ∈ N := by
  classical
  let s : (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) → FiniteAdeleRing (𝓞 E) E :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) cofinite
  have hs : Continuous s :=
    (RestrictedProduct.isOpenEmbedding_structureMap isOpen_adicCompletionIntegers_loc).continuous
  have hs0 : s 0 = 0 := rfl
  have h1 : s ⁻¹' N ∈ 𝓝 (0 : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) :=
    hs.continuousAt.preimage_mem_nhds (by rw [hs0]; exact hN)
  rw [nhds_pi, Filter.mem_pi'] at h1
  obtain ⟨I, t, ht, hIt⟩ := h1
  refine Filter.mem_of_superset I.finite_toSet.compl_mem_cofinite fun w hw y hy => ?_
  have hx : s (Pi.single w ⟨y, hy⟩) = singleNU w y := by
    refine Subtype.ext (funext fun u => ?_)
    change ((Pi.single w (⟨y, hy⟩ : w.adicCompletionIntegers E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletionIntegers E) u : u.adicCompletion E) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV E u (GlobalTheory.AdelicU.singleFin w y)
    by_cases h : u = w
    · subst h
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, Pi.single_eq_same]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, Pi.single_eq_of_ne h]
      rfl
  rw [← hx]
  refine hIt fun u hu => ?_
  have hne : u ≠ w := fun e => hw (e ▸ hu : w ∈ (I : Set _))
  rw [Pi.single_eq_of_ne hne]
  exact mem_of_mem_nhds (ht u)

end GlobalTheory.GLTwoHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUnimodularRiemannFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appellHumbert_unimodular_riemannForm : ∀ (h : ℕ) (P : Out.PolAV (Sp ℂ)), P.g = h → ∃ (u : HolUnif P.A P.L h) (Hm : Matrix (Fin h) (Fin h) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ ∧ (∀ x y : u.Λ, (Ef x y : ℝ) = (hermForm Hm x y).im) ∧ Function.Bijective Ef ∧ (∀ x, Ef x x = 0) ∧ Module.Free ℤ u.Λ ∧ Module.Finite ℤ u.Λ ∧ Module.finrank ℤ u.Λ = 2 * h ∧ ∀ (n : ℕ) (x y : u.Λ) (e : ℂˣ), 0 < n → (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef x y : ℂ) / n) → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (x : Fin h → ℂ))) (u.ex ((n : ℂ)⁻¹ • (y : Fin h → ℂ))) (unitOn e) := by
  first | exact @GlobalTheory.PolUnif.exists_unif_riemannForm | exact GlobalTheory.PolUnif.exists_unif_riemannForm | (intros; apply GlobalTheory.PolUnif.exists_unif_riemannForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjRiemannData
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open Limits (pullback)
open GlobalTheory.ArchMetricCompare (cj cjPt_comp val_cj)
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem sqMap_comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} (w : φ ≫ A.hom = A'.hom ≫ f)
    (w' : ψ ≫ A'.hom = A''.hom ≫ g) (w'' : (ψ ≫ φ) ≫ A.hom = A''.hom ≫ g ≫ f) :
    sqMap w'' = sqMap w' ≫ sqMap w :=
  (pullback.map_comp ψ φ ψ φ g f w'.symm w'.symm w.symm w.symm).symm

namespace PPAS.RiemannData

variable {S : Scheme.{0}} {P : PPAS S} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

def conj : P.RiemannData (spMap (starRingEnd ℂ) ≫ y) :=
  have h := isGrpPullback_pullback d.B cj
  have hL := pull_isLB d.isLB (pullback.fst d.B.hom cj)
  { B := (Over.pullback cj).obj d.B
    φ := pullback.fst d.B.hom cj ≫ d.φ
    isPull := h.comp d.isPull
    L := d.L.pull (pullback.fst d.B.hom cj)
    isLB := hL
    pol := by
      rw [sqMap_comp d.isPull.1.w h.1.w, CechPic.pull_comp, d.pol]
      exact (pull_sqMap_lam h _).trans
        (congrArg (CechPic.lam · _ _) (CechPic.cls_pull d.isLB _ hL).symm)
    u := ConjUnif.conjPull h d.u
    H := d.H.map star
    χ := _
    isAH := ConjUnif.conjPull_isAH h d.u d.isAH }

theorem conj_H : d.conj.H = d.H.map star := rfl

theorem conj_fn (W : P.A.left.Opens) (f : Γ(P.A.left, W)) (z : Fin P.g → ℂ) :
    d.conj.fn W f z = star (d.fn W f (star z)) := by
  have e : (d.conj.u.ex z).left ≫ d.conj.φ = cj ≫ (show Sp ℂ ⟶ _ from (d.u.ex (star z)).left) ≫ d.φ :=
    ArchMetricCompare.cjPt_comp' (isGrpPullback_pullback d.B cj) _
  unfold fn
  rw [← Points.valAt'_eq_valR, ← Points.valAt'_eq_valR]
  exact (congrArg (valAt' · W f) e).trans (val_cj _ _ _)

theorem conj_cov (W : P.A.left.Opens) (f : Γ(P.A.left, W)) (h : ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W) :
    d.conj.cov W f = star (d.cov W f) := by
  have D := (d.differentiableAt_fn f h).hasFDerivAt.star_star
  rw [star_zero] at D
  have e : d.conj.fn W f = star ∘ d.fn W f ∘ star := funext (d.conj_fn W f)
  funext a
  unfold cov
  rw [e, D.fderiv]
  simp

end PPAS.RiemannData

theorem PPAS.exists_conj_riemannData : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y), ∃ d' : P.RiemannData (spMap (starRingEnd ℂ) ≫ y), d'.H = d.H.map star ∧ ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ⊤ ≤ (y ≫ LieVB.unitSec P.A) ⁻¹ᵁ W → d'.cov W f = star (d.cov W f) :=
  fun _ _ _ d => ⟨d.conj, d.conj_H, d.conj_cov⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevelStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (M : ℕ) (X0 : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)), 3 ≤ M → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ X : Data E r, X.Gm = X0.Gm ∧ X.Ψ = X0.Ψ ∧ X.p0 = X0.p0 ∧ X.Λ = Λ ∧ ∀ γ, γ ∈ X.Γ ↔ IsUStab X0.Gm Λ γ ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y := by
  first | exact @GlobalTheory.PrincData.exists_princ_data | exact GlobalTheory.PrincData.exists_princ_data | (intros; apply GlobalTheory.PrincData.exists_princ_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralElementCharPolyNonsplitStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_element_char_poly_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  first | exact @GlobalTheory.ExInertUnit.exists_integral_unitary_charpoly | exact GlobalTheory.ExInertUnit.exists_integral_unitary_charpoly | (intros; apply GlobalTheory.ExInertUnit.exists_integral_unitary_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistNonvanishingRationalPointStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_twist_nonvanishing_rationalPoint : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (a : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ s : LB.Sec (twistLB P.A P.L 2 c), (lift (𝟙 (Over.mk t)) a).left p ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus | exact GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus | (intros; apply GlobalTheory.TwistFibre.exists_sec_twist_mem_nonzeroLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterPhaseTypeCmStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_heckeCharacter_phase_type_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  first | exact @GlobalTheory.WeilTypeChar.exists_weil_char | exact GlobalTheory.WeilTypeChar.exists_weil_char | (intros; apply GlobalTheory.WeilTypeChar.exists_weil_char <;> assumption)
end

