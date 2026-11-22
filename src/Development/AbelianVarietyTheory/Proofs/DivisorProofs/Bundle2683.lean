import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2568
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2553
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorInOrderStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_denominator_in_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ orderC c := by
  first | exact @GlobalTheory.ConductorMult.exists_natMul_mem_orderC | exact GlobalTheory.ConductorMult.exists_natMul_mem_orderC | (intros; apply GlobalTheory.ConductorMult.exists_natMul_mem_orderC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CFxi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem c_xp (F : Factor D D') (y : D'.X) : D.c (F.xp y) = D'.c y ≫ F.pr := by
  have h : D.c (F.xp y) ≫ F.inc = D'.c y ≫ F.pr ≫ F.inc := by
    rw [← F.c_xi, F.xi_xp, F.o.c_lin, F.pr_inc]
  have h2 := congrArg (· ≫ F.pr) h
  simp only [Category.assoc, F.inc_pr, Category.comp_id] at h2
  exact h2

theorem c_fxi (F : Factor D D') (y : D.X) : D'.c (F.f • F.xi y) = D.c y ≫ F.inc ≫ F.o.onB.act F.f := by
  rw [F.o.c_lin, F.c_xi, Category.assoc]

end GlobalTheory.MumFam.FactorAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrameStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrying_section_integral_frame : GlobalTheory.RefSum.RefW → (Covers fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → MultC := by
  first | exact @GlobalTheory.CovMult.multC_of_refW | exact GlobalTheory.CovMult.multC_of_refW | (intros; apply GlobalTheory.CovMult.multC_of_refW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorMultCharacterize
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.MultEff

open CartierDiv

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_one (z : X) : Scheme.ord (1 : X.functionField) z = 0 := (unitAt_one z).ord_eq_zero

theorem mult_zero (z : X) : (0 : CartierDiv X).mult z = 0 := by
  rw [(isEqn_zero z).mult_eq, Units.val_one, ord_one]

theorem mult_neg (D : CartierDiv X) (z : X) : (-D).mult z = - D.mult z := by
  have h := mult_add D (-D) z
  rw [add_neg_cancel, mult_zero] at h
  omega

theorem ord_inv (u : X.functionFieldˣ) (z : X) :
    Scheme.ord ((u⁻¹ : X.functionFieldˣ) : X.functionField) z = - Scheme.ord (u : X.functionField) z := by
  have h := Scheme.ord_mul (x := z) u.ne_zero (u⁻¹).ne_zero
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, ord_one] at h
  omega

theorem IsEqn.of_specializes {D : CartierDiv X} {x z : X} {g : X.functionFieldˣ} (h : D.IsEqn x g)
    (hz : z ⤳ x) : D.IsEqn z g := by
  obtain ⟨U, hU, hg⟩ := h.exists_nhds
  exact hg z (hz.mem_open U.isOpen hU)

variable [GlobalTheory.IsNormalScheme X]

theorem regAt_iff_ord (x : X) (u : X.functionFieldˣ) :
    RegAt x (u : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (u : X.functionField) z := by
  rw [← regularAt_zero_iff, GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X (0 : CartierDiv X) x u]
  simp only [mult_zero, add_zero]

theorem unitAt_of_ord (x : X) (u : X.functionFieldˣ)
    (h : ∀ z, z ⤳ x → Scheme.ord (u : X.functionField) z = 0) : UnitAt x (u : X.functionField) := by
  rw [unitAt_iff u.ne_zero, ← Units.val_inv_eq_inv_val, regAt_iff_ord, regAt_iff_ord]
  exact ⟨fun z hz => (h z hz).ge, fun z hz => by rw [ord_inv, h z hz, neg_zero]⟩

theorem eff_supp_eq_of_mult : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X), (D.Eff ↔ ∀ z, 0 ≤ D.mult z) ∧ (∀ x, x ∈ D.supp ↔ ∃ z, z ⤳ x ∧ D.mult z ≠ 0) ∧ (∀ E : CartierDiv X, (∀ z, D.mult z = E.mult z) → D = E) ∧ ∀ (x : X) (g : X.functionFieldˣ), (∀ z, z ⤳ x → Scheme.ord (g : X.functionField) z = D.mult z) → D.IsEqn x g := by
  intro X _ _ _ D
  have hEff : ∀ F : CartierDiv X, F.Eff ↔ ∀ z, 0 ≤ F.mult z := by
    intro F
    refine ⟨fun h z => ?_, fun h x => ?_⟩
    · have := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X F z 1).1 (h z) z (specializes_refl z)
      simpa [Units.val_one, ord_one] using this
    · have := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X F x 1).2 fun z _ => by simpa [Units.val_one, ord_one] using h z
      simpa using this
  refine ⟨hEff D, fun x => ⟨fun hx => ?_, fun ⟨z, hz, hm⟩ => ?_⟩, fun E h => ?_, fun x g h => ?_⟩
  · by_contra hne
    push_neg at hne
    obtain ⟨g, hg⟩ := D.exists_isEqn x
    refine (hg.mem_supp_iff.1 hx) (unitAt_of_ord x g fun z hz => ?_)
    rw [← (IsEqn.of_specializes hg hz).mult_eq]
    exact hne z hz
  · exact hz.mem_closed D.supp.isClosed (mem_supp_of_mult_ne_zero hm)
  · have h1 : (D - E).Eff := (hEff _).2 fun z => by
      rw [sub_eq_add_neg, mult_add, mult_neg, h z]; omega
    have h2 : (-(D - E)).Eff := (hEff _).2 fun z => by
      rw [mult_neg, sub_eq_add_neg, mult_add, mult_neg, h z]; omega
    exact sub_eq_zero.1 (h1.eq_zero h2)
  · obtain ⟨g', hg'⟩ := D.exists_isEqn x
    refine hg'.iff_unitAt.2 ?_
    have e : ((g / g' : X.functionFieldˣ) : X.functionField) = (g : X.functionField) / g' :=
      Units.val_div_eq_div_val g g'
    rw [← e]
    refine unitAt_of_ord x _ fun z hz => ?_
    have hm := (IsEqn.of_specializes hg' hz).mult_eq
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, Scheme.ord_mul g.ne_zero (inv_ne_zero g'.ne_zero),
      ← Units.val_inv_eq_inv_val, ord_inv, h z hz, hm]
    ring

end GlobalTheory.Cartier.MultEff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), ρ.Flat → ∀ (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), QuasiCompact p → QuasiSeparated p → IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (D : CartierDiv X) (D₁ : CartierDiv Y), PPull i φ θ D D₁ → LinDisj (GlobalTheory.Desc.cst p) (GlobalTheory.Desc.cst q) θ ∧ ∀ k : ℕ, {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = spanBy (GlobalTheory.Desc.cst q) (θ '' Sec D k) := by
  first | exact @GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange | exact GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange | (intros; apply GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyAwayNaturalStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_first_cohomology_away_natural : ∀ (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ d : Fin n → Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E' (θ.comp ψ) = θ (d a b E ψ)) → (∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) → d a b E ψ + d b c E ψ = d a c E ψ) → ∃ e : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → e a E' (θ.comp ψ) = θ (e a E ψ)) ∧ ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  first | exact @GlobalTheory.CechAway.cech_one_away_natural | exact GlobalTheory.CechAway.cech_one_away_natural | (intros; apply GlobalTheory.CechAway.cech_one_away_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  first | exact @GlobalTheory.CoverHyp.restrict_bijective | exact GlobalTheory.CoverHyp.restrict_bijective | (intros; apply GlobalTheory.CoverHyp.restrict_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocksStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechKodairaSpencerMatrix_eq_zero_off_conj_blocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → Θ a b = 0 := by
  first | exact @GlobalTheory.LogPole.ksMatrix_eq_zero_of_ne_conj | exact GlobalTheory.LogPole.ksMatrix_eq_zero_of_ne_conj | (intros; apply GlobalTheory.LogPole.ksMatrix_eq_zero_of_ne_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPairRestrict_baseChange_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R₀) (φ : X' ⟶ X), (Function.Bijective (extMap R₁ (pairRes φ s')).pull1 ∧ Function.Bijective (extMap R₁ (pairRes φ s')).pull2) ∧ ∀ (Y : Scheme.{0}) (ψ : X ⟶ Y), Function.Injective (extMap R₁ (cechTripleRestrictFirst φ ψ s')).pull1 := by
  first | exact @GlobalTheory.Obs.PairExt.pairRes_ext_bijective | exact GlobalTheory.Obs.PairExt.pairRes_ext_bijective | (intros; apply GlobalTheory.Obs.PairExt.pairRes_ext_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupSubsingletonOfBoundedRamification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorsRam

theorem classes_fixed {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W)
    {D : DegData W (maximalIdeal W)} {Q : PolAV (Sp (FractionRing W))} {H : Over (Sp W)} [GrpObj H] [IsCommMonObj H]
    (hH : IsSemiAbelian H) (U : Unif (maximalIdeal W) D Q H) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing W) F] {k : ℕ} (hk : 1 ≤ k) (σ : F ≃+* F)
    (hσ : σ.toRingHom.comp (algebraMap (FractionRing W) F) = algebraMap (FractionRing W) F)
    (hfixH : ∀ x : TF (R := W) F ⟶ H, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left)
    (p q : QkPt D.toPre F k) (hpq : QkExt σ.toRingHom p q) : QkPt.Equiv D.toPre F p q := by
  haveI : CharZero W := hW.2.2
  have hA := GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hW
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨f, hf, hiff⟩ := GlobalTheory.Mum.Recog.exists_goodLab hA hH U F
  have hx₀ : f k p ^ k = 1 := hf.pow k hk p
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback Q.A H (jK W) (U.gen.inv.left ≫ pullback.fst H.hom (jK W)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback H (jK W))).congr (Category.id_comp _) rfl
  have w₁ : ((f k p).left ≫ U.gen.inv.left ≫ pullback.fst H.hom (jK W)) ≫ H.hom = jFK (R := W) F ≫ jK W := by
    rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w (f k p)]; rfl
  let xG : TF (R := W) F ⟶ H := Over.homMk ((f k p).left ≫ U.gen.inv.left ≫ pullback.fst H.hom (jK W)) w₁
  have hxG : xG ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := f k p) rfl).1 hx₀
  have fixG := hfixH xG hxG
  let σ' : F →ₐ[FractionRing W] F := ⟨σ.toRingHom, RingHom.congr_fun hσ⟩
  have s₂ : spMap σ.toRingHom ≫ jFK (R := W) F = jFK (R := W) F := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]
  have fix₀ : spMap σ.toRingHom ≫ (f k p).left = (f k p).left := by
    refine gp.1.hom_ext ?_ ?_
    · rw [Category.assoc]; exact fixG
    · rw [Category.assoc, Over.w (f k p)]; exact s₂
  let x' : TFK (R := W) F ⟶ Q.A := Over.homMk (spMap σ.toRingHom ≫ (f k p).left) (by
    rw [Category.assoc, Over.w (f k p)]; exact s₂)
  have hq : QkToAkU U.toUnifPre F k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL W (maximalIdeal W) hA D Q H hH U F F σ' k hk p q (f k p) x' hpq rfl).1
      ((hiff k hk p (f k p)).2 rfl)
  have e : x' = f k p := Over.OverMorphism.ext fix₀
  exact (hf.eqv k hk p q).1 (e.symm.trans ((hiff k hk q x').1 hq))

end GlobalTheory.TorsRam

namespace GlobalTheory.TorsRam
open GlobalTheory.BXOf in

theorem psiLoc_not_unit {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (D : DegData W (maximalIdeal W))
    (J₀ : D.toPre.P.A.left → D.toPre.P.L.ι) (h₀ : ∀ x, x ∈ D.toPre.P.L.U (J₀ x)) (χ : D.toPre.X) (hχ : χ ≠ 0) (u : Wˣ)
    (hu : (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W))) : FractionRing W) =
      algebraMap W _ u) : False := by
  obtain ⟨e, -, a, ha, hψ⟩ := GlobalTheory.LevelOneIdeal.exists_psi_val D.toPre χ (D.psi_pos χ hχ)
  have := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨J, hJ, eJ⟩ := GlobalTheory.UnramTorsion.exists_good_ext D.toPre.P.isLB (algebraMap W (FractionRing W))
    (IsFractionRing.injective W (FractionRing W)) J₀ h₀
  have h1 := hψ (TK W).left (𝟙 _) (closedPoint (FractionRing W)) J hJ
  have hj : J (𝟙 _ ≫ D.toPre.xK χ) = J₀ ((D.toPre.c χ).left (closedPoint W)) := by
    rw [Category.id_comp]
    exact eJ (D.toPre.c χ).left
  have e0 := val_of (D.toPre.psi χ) (𝟙 _) (closedPoint (FractionRing W)) J _ (fun _ => hj)
  have e1 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (val (D.toPre.psi χ) (𝟙 _) (closedPoint (FractionRing W)) J).val = algebraMap W _ u := by
    rw [e0]; exact hu
  obtain ⟨u', hu'⟩ := GlobalTheory.UnramTorsion.val_integral (algebraMap W (FractionRing W)) h₀ eJ e (𝟙 _)
  have e2 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (cst (𝟙 (TK W).left ≫ jK W) (closedPoint (FractionRing W)) a) = algebraMap W _ a := by
    rw [Category.id_comp]; exact GlobalTheory.UnramTorsion.stalk_gs_top _ a
  have e3 : (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom
      (val e (𝟙 (TK W).left ≫ jK W) (closedPoint (FractionRing W)) J).val = algebraMap W _ u' := by
    rw [Category.id_comp]; exact hu'
  have e4 := congrArg (stalkClosedPointIso (CommRingCat.of (FractionRing W))).hom.hom h1
  rw [map_mul, e1, e2, e3, ← map_mul] at e4
  have e5 := IsFractionRing.injective W (FractionRing W) e4
  exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_mul_isUnit_left (e5 ▸ u.isUnit))

end GlobalTheory.TorsRam

namespace GlobalTheory.TorsRam

theorem zpow_of_mul_eq {F : Type} [Field F] {a b c : F} {e : ℕ} (hb : b ≠ 0) (h : a * b = c ^ e) (m : ℤ) :
    a ^ m = c ^ ((e : ℤ) * m) * b ^ (-m) := by
  rw [show a = c ^ e * b⁻¹ by rw [← h, mul_inv_cancel_right₀ hb], mul_zpow, zpow_mul, zpow_natCast, inv_zpow']

theorem coe_units_zpow {F : Type} [Field F] (T : Subring F) (w : Tˣ) (z : ℤ) :
    (((w ^ z : Tˣ) : T) : F) = ((w : T) : F) ^ z :=
  (congrArg Units.val (map_zpow (Units.map T.subtype.toMonoidHom) w z)).trans (Units.val_zpow_eq_zpow_val _ _)

theorem subsingleton_of_bounded_ramification : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ U : Unif (maximalIdeal W) D Q H, GlobalTheory.LN.ToATotal U.toUnifPre → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (n N : ℕ), 2 ≤ n → (∀ j : ℕ, ∃ (T : Subring F) (_ : IsDiscreteValuationRing T) (g : W →+* T) (e : ℕ), (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ (∀ π, Irreducible π → ∃ ϖ : T, Irreducible ϖ ∧ Associated (g π) (ϖ ^ e)) ∧ ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) → ∀ x : TF (R := W) F ⟶ H, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → Subsingleton D.toPre.X := by
  intro W _ _ _ hW D Q H _ _ hH U _ F _ _ _ n N hn Hj
  haveI : IsDiscreteValuationRing W := hW.1
  haveI : CharZero W := hW.2.2
  haveI : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing W) F).injective
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  choose J₀ h₀ using fun x : D.toPre.P.A.left => exists_chart D.toPre.P.isLB x
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  choose m u hu using fun χ => IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := FractionRing W) hπ
    (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W)))).ne_zero
  have key : ∀ j : ℕ, ∃ e : ℕ, 1 ≤ e ∧ e ≤ N ∧ (∀ y χ, ((n ^ j : ℕ) : ℤ) ∣ (e : ℤ) * m (y + χ) - (e : ℤ) * m y - (e : ℤ) * m χ) ∧
      ∀ χ, (e : ℤ) * m (-χ) = (e : ℤ) * m χ := fun j => by
    obtain ⟨T, hT, g, e, hg, he1, heN, hram, hfix⟩ := Hj j
    obtain ⟨ϖ, hϖ, v, hv⟩ := hram π hπ
    have hP : ∀ r, r ∈ (closedPoint W).asIdeal ↔ ¬ IsUnit (g r) := fun r => by
      show r ∈ maximalIdeal W ↔ _
      refine ⟨fun hr hgr => ?_, fun h => (mem_maximalIdeal r).2 fun hr => h (hr.map g)⟩
      · rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hr
        obtain ⟨s, rfl⟩ := hr
        rw [map_mul] at hgr
        have h1 : IsUnit (ϖ ^ e) := hv ▸ (isUnit_of_mul_isUnit_left hgr).mul v.isUnit
        exact hϖ.not_isUnit (isUnit_pow_iff (by omega) |>.1 h1)
    have hv' : (g π : F) * ((v : T) : F) = (ϖ : F) ^ e := by
      have := congrArg (fun t : T => (t : F)) hv
      simpa only [Subring.coe_mul, Subring.coe_pow] using this
    have hvne : ((v : T) : F) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
    have hm : ∀ χ, ∃ u' : Tˣ, algebraMap (FractionRing W) F
        (GlobalTheory.UnramTorsion.psiLoc D.toPre χ (J₀ ((D.toPre.c χ).left (closedPoint W))) : FractionRing W) =
        ((u' : T) : F) * (ϖ : F) ^ ((fun χ => (e : ℤ) * m χ) χ) := fun χ =>
      ⟨Units.map g.toMonoidHom (u χ) * v ^ (-(m χ)), by
        rw [hu χ, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, ← hg, ← hg, Units.val_mul, Subring.coe_mul,
          coe_units_zpow, zpow_of_mul_eq hvne hv' (m χ)]
        rw [show (((Units.map g.toMonoidHom (u χ) : Tˣ) : T) : F) = (g (u χ) : F) from rfl]
        ring⟩
    have hσ : ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) →
        σ.toRingHom.comp (algebraMap (FractionRing W) F) = algebraMap (FractionRing W) F := fun σ hσ =>
      IsLocalization.ringHom_ext (nonZeroDivisors W) (RingHom.ext fun r => by
        show σ (algebraMap (FractionRing W) F (algebraMap W _ r)) = algebraMap (FractionRing W) F (algebraMap W _ r)
        rw [← hg]; exact hσ _ (g r).2)
    obtain ⟨h1, h2⟩ := GlobalTheory.UnramTorsion.level_step hL.1.mulN D.tau_bimult D.psi_even (closedPoint W) J₀ h₀ (n ^ j)
      (pow_ne_zero _ (by omega)) T g hg hP ϖ hϖ (fun χ => (e : ℤ) * m χ) hm
      (fun σ hσ' p q hpq => classes_fixed hW hH U F (Nat.one_le_pow _ _ (by omega)) σ (hσ σ hσ')
        (fun x hx => hfix σ hσ' x hx) p q hpq)
    exact ⟨e, he1, heN, h1, h2⟩
  have add : ∀ y χ, m (y + χ) = m y + m χ := fun y χ => by
    obtain ⟨e, he1, heN, hdiv, -⟩ := key (N * (m (y + χ) - m y - m χ).natAbs)
    have h1 := hdiv y χ
    rw [show (e : ℤ) * m (y + χ) - (e : ℤ) * m y - (e : ℤ) * m χ = (e : ℤ) * (m (y + χ) - m y - m χ) by ring] at h1
    by_contra hne
    have hd : m (y + χ) - m y - m χ ≠ 0 := fun h => hne (by omega)
    have h2 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h1 (by
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right _ heN) (Nat.lt_pow_self (by omega)))
    exact (mul_ne_zero (by exact_mod_cast (show e ≠ 0 by omega)) hd) h2
  have even : ∀ χ, m (-χ) = m χ := fun χ => by
    obtain ⟨e, he1, -, -, h⟩ := key 0
    exact Int.eq_of_mul_eq_mul_left (by exact_mod_cast (show e ≠ 0 by omega)) (h χ)
  have m0 : ∀ y, m y = 0 := fun y => by
    have a := add 0 0
    have b := add y (-y)
    rw [add_zero] at a
    rw [add_neg_cancel, even] at b
    omega
  have z : ∀ y : D.toPre.X, y = 0 := fun y => by
    by_contra hy
    refine psiLoc_not_unit D J₀ h₀ y hy (u y) ?_
    rw [hu y, m0, zpow_zero, Units.smul_def, Algebra.smul_def, _root_.mul_one]
  exact ⟨fun a b => (z a).trans (z b).symm⟩

end GlobalTheory.TorsRam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLineBundleAdditiveOfEquivariantGenerato
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem isAdditive_of_isEquivGen : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → M.IsLB → IsEquivGen i q χ M e → IsAdditive M := by
  intro K _ _ A A' N T _ _ _ i q χ M e hA hA' hi hq hfin hflat hsurj hker hχ hM he
  haveI := hA
  haveI := hq
  haveI : IsCommMonObj A := IsAbelianScheme.comm
  obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.T.prodMapPairTimesIdentity_flat_surjective_affine _ A A' T q hflat hsurj inferInstance
  exact isAdditive_of_universal hM (GlobalTheory.T.lineBundle_trivial_of_invariant_pullback_generator _ _ (pmap2 q T).left h₁ h₂ h₃ (addBundle M) (addGen q M e)
    (GlobalTheory.T.isPullbackLineBundleGenerator_additivityDefect _ A A' T q M e he.1) (GlobalTheory.T.additivityDefect_generator_invariant_same_image _ A A' N T i q χ M e hi hker hχ he))

end GlobalTheory.CharKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def ChartExpOn (U : UnifPre I D A G) (e k : ℕ) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens)
    (g : Γ((thickObj R I e G).left, W)) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) : Prop :=
  ∃ S : Finset D.toPre.X,
    (∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) ∧
    ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      i' 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res ((inf_le_left.trans inf_le_left).trans inf_le_left :
          U.expW e p i' S jf jt ⊓ W ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_right :
          U.expW e p i' S jf jt ⊓ W ≤ W)).op).hom g =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (inf_le_left.trans (U.expW_le_f e p i' jf jt α.2))).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (inf_le_left.trans (U.expWeight_le_chart_weight e p i' jf jt α.2)) (((U.gt e).t α.1).s (jt α.1))).val

end GlobalTheory.MumMult
end
end

