import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0946
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0935
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0921
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0945
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0741
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0054
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
import Formalism.LocalToGlobal.Columns.MtAdWt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0938
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0944
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfLargeResidueChar
section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UseLoc
open Module

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), tableLineDegreeTwo.aux₃ D HW F → tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ), ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) → ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)) := by
  intro D HW F i r ρ π hconds hadm20 hJa hGood hπ hG2 hG3 hCont hDec hEps h5 hsm hq hd hposition w hw
  obtain ⟨C, hA, lam, hlam, θ, h, w', η, typ, U, hS⟩ :=
    GlobalTheory.T.exists_exactLocalConditionData_at_place D HW F i r ρ π hadm20 hJa hGood hπ hG2 hG3 hCont hDec hEps h5 hsm hq hd hposition w hw
  have hTop : tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) :=
    hconds (D.nd.l i) (D.nbr i w hw).Kw C.LL hA lam hlam
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.unramifiedEnlargement_cut_cocycles_blochKato D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hS hGood hπ hDec hCont
  refine ⟨?_, ?_, ?_⟩
  · have hsub : ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
        z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (WpO D.nd i ρ π)) :=
      fun z hz => GlobalTheory.T.mem_finite_part_of_lift D i w hw C D.R.r _ z (h1 z hz)
    have hle := Submodule.span_le.2 hsub
    unfold LocBound lenModN
    have h0 : Module.length (Br.OLL D.nbr i w hw)
        (↥(Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Set.univ (WpO D.nd i ρ π))) ⧸
          (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (WpO D.nd i ρ π))).comap
            (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Set.univ (WpO D.nd i ρ π))).subtype) = 0 := by
      rw [Module.length_eq_zero_iff, Submodule.comap_subtype_eq_top.2 hle]
      refine ⟨fun a b => ?_⟩
      induction a using Submodule.Quotient.induction_on
      induction b using Submodule.Quotient.induction_on
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top
    rw [h0]
    exact zero_le
  · intro c hc z hz
    exact GlobalTheory.T.coboundary_descent_enlargement_coefficients D i w hw C 1 _ z (h2 c hc z hz)
  · intro z hz
    have := GlobalTheory.T.unramifiedCocycle_descent_enlargement D i w hw C 1 _ _ z (h3 z hz)
    rwa [← GlobalTheory.BridgeInertia.inertEq D i w hw] at this

end GlobalTheory.UseLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseLevelCharacterMemCoefficientRing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.LamVal

theorem exists_of_pow {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] {a : FractionRing A} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ∃ y : A, algebraMap A (FractionRing A) y = a := by
  have hi : IsIntegral A a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  exact IsIntegrallyClosed.isIntegral_iff.1 hi

variable {D : D7}

theorem e_mem_of_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ρ.e i b a ∈ (ρ.eOk i b 0).range := by
  obtain ⟨y, rfl⟩ := exists_of_pow hn h
  exact ⟨algebraMap _ _ y, hρ.ek_e i b 0 y⟩

theorem de_mem {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eOk i b 0).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (D.ntw.Ok i 0)
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.ek_e, hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

theorem typeCharacterExtension_mem_range_coefficientRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : G0 (Y.Z.ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (Y.Z.ρ.B i j b).G.P.H (⇑(Y.Z.ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  unfold ext1
  split_ifs with h
  · set g' := (Y.Z.ρ.eG i j b).symm g with hg'
    have hg : Y.Z.ρ.eG i j b g' = g := MulEquiv.apply_symm_apply _ _
    have h' : Y.Z.ρ.eG i j b g' ∈ (Y.Z.ρ.B i j b).G.P.H := by rw [hg]; exact h
    have hu : g' ∈ D.nexp.U := ((Y.Z.tie i j b).U_eq g').1 h'
    have e1 := (Y.Z.tie i j b).psiU_eq ⟨g', hu⟩ h'
    have e2 : (Y.Z.ρ.B i j b).G.P.chi ⟨g, h⟩ = (Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩ := by
      congr 1
      exact Subtype.ext hg.symm
    rw [e2, e1]
    have hfin : ((Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩) ^ Nat.card (Y.Z.ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    refine e_mem_of_pow Y.Z.good i b (n := Nat.card (Y.Z.ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    apply (Y.Z.ρ.e i b).injective
    rw [map_pow, ← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one, map_one]
  · exact one_mem _

theorem mu_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hμ : ∀ PP ∈ (Y.Z.ρ.B i j b).G.Pg, ∀ (u : (kP PP)ˣ) (x : (AE D)ˣ), GlobalTheory.ConjTwist.IsLocUnit PP u x →
      (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range)
    {PP : Pl D.host.E} (hPP : PP ∈ (Y.Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((Y.Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hB := Y.Z.good.base i j b
  obtain ⟨P, hPg, -, hsp⟩ := hB.places.split
  obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w
  have e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x := (hx.eq (hB.tame PP hPP)).symm
  show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _
  rw [e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  exact mul_mem (hμ PP hPP w x hx) (de_mem Y.Z.good i j b x)

theorem loc_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (PP : Pl D.host.E) (w : (kP PP)ˣ) :
    ((((Y.Z.ρ.B i j b).de.locC PP * (Y.Z.ρ.tw i b 0 ∅ 1).locC PP) w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).locC PP = 1 := by
    simp [Twist.locC, Setup.tw, twistOf, half_empty]
  rw [hψ, mul_one]
  unfold Twist.locC
  split_ifs with hq
  · have hB := Y.Z.good.base i j b
    obtain ⟨P, -, hQ, hsp⟩ := hB.places.split
    obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hQ hq)) w
    show (((Y.Z.ρ.B i j b).de.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (hB.de.res PP hq)]
    exact de_mem Y.Z.good i j b x
  · simp

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

theorem levLam_mem : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    (∀ PP ∈ (Y.Z.ρ.B i j b).G.Pg, ∀ (u : (kP PP)ˣ) (x : (AE D)ˣ), GlobalTheory.ConjTwist.IsLocUnit PP u x →
      (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range) →
    ∀ (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
      (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  intro D X E Y i j b hμ k
  rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  exact mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => mu_mem Y i j b hμ hPP _))
    (prod_mem fun PP _ => loc_mem Y i j b PP _)

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

theorem de_frac {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    ∃ d, ρ.e i b d = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) _
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem baseCharacter_finiteIdeles_mem_range_fractionRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ a, Y.Z.ρ.e i b a = (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) := by
  obtain ⟨y, hy⟩ := X.valKs j x hx
  refine ⟨sideEmb D.ntw i b (Y.S.kKs ((Y.YS.fi j).eK.symm y)), ?_⟩
  rw [Y.Z.good.e_LL0, Y.Z.pin.mu0 i j b]
  refine Eq.trans ?_ hy.symm
  change D.what₂.embLL ((Y.S.kKs ((Y.YS.fi j).eK.symm y) : D.LL0) : D.what₂.LL) = _
  rw [Y.S.kKs_spec, ← (Y.YS.fi j).eK_LL, RingEquiv.apply_symm_apply]

theorem muC_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {PP : Pl D.host.E} (hPP : PP ∈ (Y.Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((Y.Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hB := Y.Z.good.base i j b
  obtain ⟨P, hPg, -, hsp⟩ := hB.places.split
  obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w
  have e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x := (hx.eq (hB.tame PP hPP)).symm
  show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _
  obtain ⟨a, ha⟩ := baseCharacter_finiteIdeles_mem_range_fractionRing Y i j b x hx.inf
  obtain ⟨d, hd⟩ := de_frac Y.Z.good i j b x
  have e2 : (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) = Y.Z.ρ.e i b (a * d) := by
    rw [e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul, map_mul, ha, hd]
  haveI : Finite (kP PP)ˣ := inferInstance
  have hfin : ((Y.Z.ρ.B i j b).G.mu PP w) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  rw [e2]
  refine e_mem_of_pow Y.Z.good i b (n := Nat.card (kP PP)ˣ) Nat.card_pos.ne' ?_
  apply (Y.Z.ρ.e i b).injective
  rw [map_pow, ← e2, ← Circle.coe_pow, hfin, Circle.coe_one, map_one]

theorem levLam_mem_coef : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
    (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  intro D X E Y i j b k
  rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  exact mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem Y i j b hPP _))
    (prod_mem fun PP _ => loc_mem Y i j b PP _)

end GlobalTheory.LamVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddAllOfThetaSumOnCover
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

namespace GlobalTheory.CoverBound

theorem inV_iff (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0
    simp [InV, vV]
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log (valV_ne_zero (V := T.V) h0) one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV
    omega
  · intro h3
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log (valV_ne_zero h0) one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h3
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_map_iff {T T' : CDVR} (i : T.Fr →+* T'.Fr) {r : ℕ} (hr : 0 < r)
    (hi : ∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) (x : T.Fr) : InV T' (i x) ↔ InV T x := by
  rw [inV_iff, inV_iff, hi]
  exact mul_nonneg_iff_of_pos_left (by exact_mod_cast hr)

theorem inV_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) {x : K} (hx : la.valuation K x ≤ 1) : InV T (io x) := by
  rw [inV_iff, ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : x = 0
  · simp [vLa, h0]
  have h2 := (WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 hx
  rw [WithZero.log_one] at h2
  unfold vLa
  omega

theorem inV_of_pow_eq (T : CDVR) {x : T.Fr} {e : ℕ} (he : 0 < e) (hx : x ^ (e + 1) = x) : InV T x := by
  by_cases h0 : x = 0
  · subst h0
    exact zero_mem (algebraMap T.V T.Fr).range
  have h := GlobalTheory.PlaceExtField.vV_pow (V := T.V) h0 (e + 1)
  rw [hx] at h
  rw [inV_iff]
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  push_cast at h
  have : (e : ℤ) * vV T.V x = 0 := by linarith
  exact ((mul_eq_zero.1 this).resolve_left he'.ne').ge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem good_lift {X X₂ : Scheme.{0}} (t : SAB H X) (t₂ : SAB H X₂) (r : X₂ ⟶ X) (m : SABMap t₂ t r) (T T' : CDVR)
    (i : T.Fr →+* T'.Fr) (e : ℕ) (hi : ∀ a : T.Fr, vV T'.V (i a) = (e : ℤ) * vV T.V a) (x : Sp T.Fr ⟶ X)
    (x₂ : Sp T'.Fr ⟶ X₂) (hx : x₂ ≫ r = spMap i ≫ x)
    (h : ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' t x)
      (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), IsProper G.G.hom) :
    ∃ (G : SAB H (Sp T'.V)) (t' : SAB H (Sp T'.Fr)) (_ : SABMap t' t₂ x₂)
      (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), IsProper G.G.hom := by
  obtain ⟨G, t', m1, m2, hp⟩ := h
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceInt.Ext.exists_restrict T T' i e hi
  obtain ⟨G', ⟨mG⟩⟩ : ∃ G' : SAB H (Sp T'.V), Nonempty (SABMap G' G (spMap φ)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap φ) G⟩⟩
  obtain ⟨s, ⟨n⟩⟩ : ∃ s : SAB H (Sp T'.Fr), Nonempty (SABMap s t' (spMap i)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap i) t'⟩⟩
  have hio : spMap i ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← GlobalTheory.FramedBaseChange.spec_comp, ← GlobalTheory.FramedBaseChange.spec_comp]
    exact congrArg spMap (RingHom.ext fun a => (hφ a).symm)
  obtain ⟨a1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 n
  obtain ⟨a2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 n
  rw [← hx] at a1
  rw [hio] at a2
  obtain ⟨b1, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m a1
  obtain ⟨b2, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mG a2
  exact ⟨G', s, b1, b2, MorphismProperty.of_isPullback mG.cart.1 hp⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem shortValAt_of_map (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (La : GenLat E n) (β : c.F)
    (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {K k : Type} [Field K] [Field k] [Algebra c.F K] [Algebra c.F k]
    (ψ : K →ₐ[c.F] k) (y : FrPt Xo c K) (z : FrPt Xo c k) (h : FrMap ψ y z) (v : K)
    (hv : ShortValAt Xo c nab w La β N P z (ψ v)) : ShortValAt Xo c nab w La β N P y v := by
  obtain ⟨S, _, _, φ, y', a, b, F, hf, hm, h1, h2, h3, h4, h5⟩ := hv
  refine ⟨S, inferInstance, inferInstance, φ.comp ψ, y', a, b, F, ?_, GlobalTheory.FramedBaseChange.trans ψ φ h hm,
    h1, h2, h3, h4, h5⟩
  haveI : Nontrivial S := hf.injective.nontrivial
  letI := (φ.comp ψ).toRingHom.toAlgebra
  exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

theorem evR_pow_succ (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (e : ℕ) :
    evR Xo c (f ^ (e + 1)) y = evR Xo c f y ^ (e + 1) := by
  induction e with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ e ih => rw [pow_succ f, pow_succ (evR Xo c f y), ← ih]; exact evalAt_mul _ _ _ _ _

set_option maxHeartbeats 1000000 in

theorem bddAll_of_theta_sum_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n d N m : ℕ) (dδ : DeltaDat Xo c n) (La : GenLat E n) (cs : Fin m → Rul dδ.Xo₂ dδ.c₂) (e : ℕ) (w : Fin m → (Fin n → LevQ Dw dδ.l₂) → c.F) (P : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Dom a n → dδ.IsLev → IsNab dδ.Xo₂ dδ.c₂ dδ.nab₂ → La.Unimod → La.TrivAt dδ.l₂.M → La.LevOK N dδ.l₂.M → 0 < e → (∀ t, cs t ∈ sec dδ.Xo₂ dδ.c₂ 0 0 ∧ cs t ^ (e + 1) = cs t) → (∀ t q, la.valuation c.F (w t q) ≤ 1) → (∀ t, P t ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ∧ (P t).IsHomogeneous d ∧ ∀ k, la.valuation c.F ((P t).coeff k) ≤ 1) → f ∈ cusp Xo c U a n → (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra dδ.c₂.F k], (∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x) → ∀ (y : FrPt Xo c k) (y₂ : FrPt dδ.Xo₂ dδ.c₂ k), FrOver dδ y₂ y → ∃ v : Fin m → k, (∀ t, thLaValAt dδ.Xo₂ dδ.c₂ dδ.nab₂ (fun q => dδ.eF (w t q)) La N (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) y₂ (v t)) ∧ evR Xo c f y = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) y₂ * v t) → BddAll Xo c la (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw dδ.l₂) : ℕ) : c.F) * ((2 * NumberField.discr E * N : ℤ) : c.F) ^ d) f := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hl _ a n d N m dδ La cs e w P f hdom hlev hnab hun htr hN he hcs hw hP hf
    hval
  refine GlobalTheory.T.cuspFormBound_goodPoints_extends_allPoints E H Dw l Xo c r U hU la p hp hpl hl a n f _ hdom hf ?_
  intro T io e₀ ho y hfin hgood
  have laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨T₁, i₁, e₁, y₁, io₁, z₁, ⟨he₁, hv₁, φ₁, hφ₁, hm₁⟩, -, hio₁, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover E H Dw l Xo c n dδ hlev T io y hfin
  letI a0 : Algebra c.F T.Fr := io.toAlgebra
  letI a1 : Algebra c.F T₁.Fr := (i₁.comp io).toAlgebra
  letI b1 : Algebra dδ.c₂.F T₁.Fr := io₁.toAlgebra
  obtain ⟨k, _, _, _, _, -⟩ : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra T₁.Fr k)
      (_ : Algebra.IsAlgebraic T₁.Fr k), True :=
    ⟨AlgebraicClosure T₁.Fr, inferInstance, inferInstance, inferInstance, inferInstance, trivial⟩
  letI ak : Algebra c.F k := ((algebraMap T₁.Fr k).comp (i₁.comp io)).toAlgebra
  letI bk : Algebra dδ.c₂.F k := ((algebraMap T₁.Fr k).comp io₁).toAlgebra
  let ψ₁ : T₁.Fr →ₐ[c.F] k := { algebraMap T₁.Fr k with commutes' := fun _ => rfl }
  let ψ₂ : T₁.Fr →ₐ[dδ.c₂.F] k := { algebraMap T₁.Fr k with commutes' := fun _ => rfl }
  obtain ⟨yk, hyk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw l Xo c _ _ ψ₁ y₁.1
  obtain ⟨zk, hzk⟩ := GlobalTheory.FramedBaseChange.exists_frMap laws E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ _ _ ψ₂ z₁.1
  have hc1 : ∀ x : c.F, algebraMap dδ.c₂.F T₁.Fr (dδ.eF x) = algebraMap c.F T₁.Fr x := hio₁
  have hck : ∀ x : c.F, algebraMap dδ.c₂.F k (dδ.eF x) = algebraMap c.F k x := fun x =>
    congrArg (algebraMap T₁.Fr k) (hio₁ x)
  have hoverk : FrOver dδ zk yk :=
    (GlobalTheory.frames_lift_to_cover laws E H Dw l Xo c n dδ).2.1 T₁.Fr hc1 k hck ψ₁ ψ₂ rfl y₁.1 z₁.1 yk zk hover hyk hzk
  obtain ⟨v, hv, hev⟩ := hval k hck yk zk hoverk
  let K := IntermediateField.adjoin T₁.Fr (Set.range v)
  haveI : FiniteDimensional T₁.Fr K := IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  obtain ⟨T₂, i₂, e₂, ρ, -, he₂, hv₂, hρ, -, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T₁ K
  obtain ⟨z₂, -, -, φ₂, hφ₂, hm₂⟩ :=
    (GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ T₁ T₂ io₁ z₁ i₂ e₂ he₂ hv₂).1
  letI b2 : Algebra dδ.c₂.F T₂.Fr := (i₂.comp io₁).toAlgebra
  obtain ⟨j, hj, hjv⟩ : ∃ j : T₂.Fr →+* k, (∀ x, j (i₂ x) = algebraMap T₁.Fr k x) ∧ ∀ t, ∃ u, j u = v t := by
    refine ⟨(algebraMap K k).comp ρ.symm.toRingHom, fun x => ?_, fun t =>
      ⟨ρ ⟨v t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩, ?_⟩⟩
    · rw [← hρ]
      exact congrArg (algebraMap K k) (ρ.symm_apply_apply _)
    · exact congrArg (algebraMap K k) (ρ.symm_apply_apply _)
  choose u hu using hjv
  let χ : T₂.Fr →ₐ[dδ.c₂.F] k := { j with commutes' := fun x => hj (io₁ x) }
  have hχ : χ.comp φ₂ = ψ₂ := AlgHom.ext fun x => by
    show j (φ₂.toRingHom x) = algebraMap T₁.Fr k x
    rw [hφ₂, hj]
  have hm₃ : FrMap χ z₂.1 zk := GlobalTheory.FramedBaseChange.cancel φ₂ χ hm₂ (hχ ▸ hzk)
  have hv₀ : ∀ x : T.Fr, vV T₂.V ((i₂.comp i₁) x) = ((e₂ * e₁ : ℕ) : ℤ) * vV T.V x := fun x => by
    rw [RingHom.comp_apply, hv₂, hv₁]
    push_cast
    ring
  have he₀ : 0 < e₂ * e₁ := Nat.mul_pos he₂ he₁
  have hgood₂ : Good z₂ := by
    refine good_lift Xo.univ.t dδ.Xo₂.univ.t dδ.r dδ.m T T₂ (i₂.comp i₁) _ hv₀ y.1.x z₂.1.x ?_ hgood
    rw [hm₂.1, Category.assoc, hover.1, hm₁.1, hφ₁, hφ₂, ← Category.assoc, ← GlobalTheory.FramedBaseChange.spec_comp]
  have hint : ∀ x : c.F, la.valuation c.F x ≤ 1 → InV T₂ ((i₂.comp io₁) (dδ.eF x)) := fun x hx => by
    rw [RingHom.comp_apply, hio₁]
    exact (inV_map_iff (i₂.comp i₁) he₀ hv₀ _).2 (inV_of_overLa ho hx)
  have hth := fun t => GlobalTheory.T.shortThetaValue_bounded_goodReduction E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂ dδ.nab₂ hnab T₂ (i₂.comp io₁) z₂ n d N La
    (fun q => dδ.eF (w t q)) (MvPolynomial.map (dδ.eF : c.F →+* dδ.c₂.F) (P t)) (u t) hgood₂ hun htr hN
    (fun q => hint _ (hw t q)) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map _ (hP t).1) ((hP t).2.1.map _)
    (fun q => by rw [coeff_map]; exact hint _ ((hP t).2.2 q))
    (shortValAt_of_map _ _ _ _ _ _ χ z₂.1 zk hm₃ (u t) (by
      have h := hv t
      rw [← hu t] at h
      exact h))
  have e1 : evR Xo c f yk = (ψ₁.comp φ₁) (evR Xo c f y.1) :=
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw l Xo c).2.2.1 f
      (cusp_le_sec Xo c U a n hf).1 _ y.1 y.2.1 yk (GlobalTheory.FramedBaseChange.trans φ₁ ψ₁ hm₁ hyk)
  have e2 : ∀ t, evR dδ.Xo₂ dδ.c₂ (cs t) zk = j (evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1) := fun t =>
    GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange E H Dw dδ.l₂ dδ.Xo₂ dδ.c₂).2.2.1 (cs t) (hcs t).1.1 χ z₂.1
      z₂.2.1 zk hm₃
  have e3 : (i₂.comp i₁) (evI y f) = ∑ t, evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1 * u t := by
    apply j.injective
    have e4 : j ((i₂.comp i₁) (evI y f)) = (ψ₁.comp φ₁) (evR Xo c f y.1) := by
      show j (i₂ (i₁ (evR Xo c f y.1))) = algebraMap T₁.Fr k (φ₁.toRingHom (evR Xo c f y.1))
      rw [hφ₁, hj]
    rw [e4, ← e1, hev, map_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [map_mul, e2, hu]
  rw [← inV_map_iff (i₂.comp i₁) he₀ hv₀, map_mul, e3, Finset.mul_sum]
  refine sum_mem (S := (algebraMap T₂.V T₂.Fr).range) fun t _ => ?_
  have h1 : InV T₂ (evR dδ.Xo₂ dδ.c₂ (cs t) z₂.1) :=
    inV_of_pow_eq T₂ he (by rw [← evR_pow_succ, (hcs t).2])
  have h2 := mul_mem h1 (hth t)
  rw [map_mul, map_natCast, map_pow, map_intCast, map_mul, map_natCast, map_pow, map_intCast, mul_left_comm]
  exact h2

end GlobalTheory.CoverBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContragredientPolynomialWeightUniqueHighestWeighStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_polynomialWeight_unique_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  first | exact @GlobalTheory.mtRatDual_hw | exact GlobalTheory.mtRatDual_hw | (intros; apply GlobalTheory.mtRatDual_hw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralArcSectionEqualCharStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_integral_arc_section_equalChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → IsOpen (abLocus Y.t.G) → Y.N4 → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a' n → f ∈ cusp Xo c U a' n → (∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ k : c.F, io₁ k ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ y₁ : IntFr Xo c T₁ io₁, (letI := io₁.toAlgebra; ExtIn Y (abLocus Y.t.G) T₁ io₁ y₁.1.x) → evI y₁ f ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → (∃ κ : T.Fr →+* ℂ, κ.comp io = c.F.val.toRingHom) → ∀ (b : (la.valuation c.F).valuationSubring →+* T.V), (algebraMap T.V T.Fr).comp b = io.comp (la.valuation c.F).valuationSubring.subtype → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (a : ArcIn Dw l (la.valuation c.F).valuationSubring.subtype T.V b) (y' : Sp T.V ⟶ Y.X), y' ≫ Y.s = spMap b → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y' → ∀ (y : IntFr Xo c T io) (z : Sp T.Fr ⟶ Xo.XF c), (letI := io.toAlgebra; z ≫ pullback.fst _ _ = y.1.x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | exact GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | (intros; apply GlobalTheory.GoodTransfer.inV_of_arc_of_extIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugateForms_thetaLift_eq_thetaSeries : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∃ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' ∧ ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ser R i t (R.vP i t) u h (c x) g ∧ R.thF i t' y' (fun ρ => u ρ) g = ser R i t' (R.vP i t') u h (c x') g := by
  first | exact @GlobalTheory.ConjTwist.exists_conjForm_thF_eq_ser | exact GlobalTheory.ConjTwist.exists_conjForm_thF_eq_ser | (intros; apply GlobalTheory.ConjTwist.exists_conjForm_thF_eq_ser <;> assumption)
end

