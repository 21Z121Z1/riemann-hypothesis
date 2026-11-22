import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0177
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromy
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.FromMat

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {n : Type} [Fintype n] [DecidableEq n]

def matRep (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l) :=
  MonoidHom.toHomUnits
    ((((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).mapMatrix : Matrix n n ℚ_[l] →+* Matrix n n ↥(MaximalUnramifiedExtension l)) :
        Matrix n n ℚ_[l] →* Matrix n n ↥(MaximalUnramifiedExtension l)).comp
      (((LinearMap.toMatrixAlgEquiv b : (V →ₗ[ℚ_[l]] V) ≃ₐ[ℚ_[l]] Matrix n n ℚ_[l]) :
        (V →ₗ[ℚ_[l]] V) →* Matrix n n ℚ_[l]).comp ρ))

theorem matRep_apply (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (i j : n) :
    (matRep b ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (b.repr (ρ g (b j)) i) := by
  simp [matRep, LinearMap.toMatrixAlgEquiv_apply]

theorem toMatrix_map_apply (b : Module.Basis n ℚ_[l] V) (f : V →ₗ[ℚ_[l]] V) {A : Type} [Semiring A] [Algebra ℚ_[l] A]
    (i j : n) : (LinearMap.toMatrix b b f).map (algebraMap ℚ_[l] A) i j = algebraMap ℚ_[l] A (b.repr (f (b j)) i) := by
  simp [LinearMap.toMatrix_apply]

end GlobalTheory.PMon.FromMat

namespace GlobalTheory.PMon.FromMat

open GlobalTheory.PMon.Inhab

theorem deRhamPotSemistable_of_matThm : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  intro hM l _ P AI hT K V _ _ _ _ _ ρ hc hDR
  obtain ⟨T⟩ := hT
  let b := Module.finBasis ℚ_[l] V
  have hR : IsRat 1 (matRep b ρ) := by
    refine ⟨one_pos, fun c hc' => ?_, fun g i j => ?_, fun i j => ?_⟩
    · obtain ⟨q, rfl⟩ := fixed_frob P c (by rwa [fr_one] at hc')
      exact K.1.algebraMap_mem q
    · rw [matRep_apply, fr_q]
    · simp only [matRep_apply]
      have h1 : Continuous fun g : ↥(GK K) => b.coord i (ρ g (b j)) :=
        (IsModuleTopology.continuous_of_linearMap (R := ℚ_[l]) (b.coord i)).comp (hc (b j))
      exact (continuous_algebraMap ℚ_[l] (Om l)).comp h1
  have hD : AdmDR P (matRep b ρ) := by
    intro m
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_invertible_deRhamPeriodMatrix_of_isDR l P AI T _ K V b ρ hDR
    refine ⟨Q, fun g => ?_⟩
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    rw [matD, Matrix.map_apply, matRep_apply, fr_q, kd_alg, toMatrix_map_apply]
  obtain ⟨K', hK, Q, hQ⟩ := hM l P AI T _ K 1 (matRep b ρ) hR hD
  have hS : IsSst P (resTo ρ hK) := by
    refine GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing l P AI T _ K' V b (resTo ρ hK) Q fun g => ?_
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [matRep_apply, LinearMap.toMatrix_apply, ks, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      Polynomial.algebraMap_apply]
    rfl
  exact GlobalTheory.T.isPotentiallySemistable_of_semistable_restrict l P AI T K K' hK V ρ hS

end GlobalTheory.PMon.FromMat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseNumberFieldOfContinuousCompletionEquiv
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

open IsDedekindDomain.HeightOneSpectrum

theorem valuationSubring_le_one_of_ringOfIntegers {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] (A' : ValuationSubring Ω') (m : 𝓞 E') :
    A'.valuation (algebraMap E' Ω' (m : E')) ≤ 1 :=
  (A'.valuation_le_one_iff _).2
    (mem_of_isIntegral_int A' (map_isIntegral_int (algebraMap E' Ω') (RingOfIntegers.isIntegral_coe m)))

theorem valuationSubring_lt_one_of_placeOver {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (hP : IsPlaceOver A' w')
    (t : E') (ht : w'.valuation E' t < 1) : A'.valuation (algebraMap E' Ω' t) < 1 := by
  obtain ⟨s, hs, hq⟩ := GlobalTheory.exists_notMem_mul_valuation_le_one_of_ne w' (fun _ : Unit => t)
  have hsle : w'.valuation E' (s : E') ≤ 1 := by
    rw [RingOfIntegers.coe_eq_algebraMap]; exact w'.valuation_le_one (K := E') s
  have hw : w'.valuation E' ((s : E') * t) < 1 := by
    rw [map_mul]
    calc w'.valuation E' (s : E') * w'.valuation E' t ≤ 1 * w'.valuation E' t := by gcongr
      _ < 1 := by rwa [one_mul]
  have hall : ∀ q : HeightOneSpectrum (𝓞 E'), q.valuation E' ((s : E') * t) ≤ 1 := by
    intro q
    by_cases hq' : q = w'
    · subst hq'; exact hw.le
    · exact hq q hq' ()
  obtain ⟨m, hm⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E' _ hall
  have hmw : m ∈ w'.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]
    show w'.valuation E' (algebraMap (𝓞 E') E' m) < 1
    rw [hm]; exact hw
  have h1 := (hP m).2 hmw
  have h2 : A'.valuation (algebraMap E' Ω' (s : E')) = 1 :=
    le_antisymm (valuationSubring_le_one_of_ringOfIntegers A' s) (not_lt.1 (fun h => hs ((hP s).1 h)))
  have hm' : ((m : 𝓞 E') : E') = (s : E') * t := by rw [← hm]
  rw [hm', map_mul, map_mul, h2, one_mul] at h1
  exact h1

theorem exists_int_valuationSubring_le {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') {δ : Ω'} (hδ : δ ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ A'.valuation (algebraMap E' Ω' (n : E')) ≤ A'.valuation δ := by
  haveI : Algebra.IsAlgebraic ℤ E' :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ E').mpr (Algebra.IsAlgebraic.isAlgebraic x)⟩
  haveI : Algebra.IsAlgebraic ℤ Ω' := Algebra.IsAlgebraic.trans ℤ E' Ω'
  obtain ⟨n, hn, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) δ⁻¹).exists_integral_multiple
  refine ⟨n, hn, ?_⟩
  have hle := (A'.valuation_le_one_iff _).2 (mem_of_isIntegral_int A' hint)
  rw [zsmul_eq_mul, map_mul, map_inv₀] at hle
  have hd : A'.valuation δ ≠ 0 := by simpa using hδ
  rw [map_intCast]
  calc A'.valuation (n : Ω') = A'.valuation (n : Ω') * (A'.valuation δ)⁻¹ * A'.valuation δ := by
        rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
    _ ≤ 1 * A'.valuation δ := by gcongr
    _ = A'.valuation δ := one_mul _

end GlobalTheory

namespace GlobalTheory

theorem approx_of_completion_equiv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')), IsPlaceOver A' w' → ∀ (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∀ (y : E') (δ : Ω'), δ ≠ 0 → ∃ x : E, A'.valuation (algebraMap E' Ω' y - algebraMap E' Ω' (j x)) < A'.valuation δ := by
  intro E _ _ w E' Ω' _ _ _ _ _ A' w' hP j i hi hij y δ hδ
  obtain ⟨n, hn, hnδ⟩ := exists_int_valuationSubring_le (E' := E') A' hδ
  set c : E' := (n : E') with hcdef
  have hc : c ≠ 0 := Int.cast_ne_zero.mpr hn
  let U : Set (w'.adicCompletion E') :=
    {z | Valued.v ((z - algebraMap E' _ y) * (algebraMap E' (w'.adicCompletion E') c)⁻¹) < 1}
  have hU : IsOpen U := by
    have h := (Valued.isOpen_ball (w'.adicCompletion E') 1).preimage
      ((continuous_sub_right (algebraMap E' (w'.adicCompletion E') y)).mul
        (continuous_const (y := (algebraMap E' (w'.adicCompletion E') c)⁻¹)))
    convert h using 2 with z
    simp [U, Valuation.restrict_lt_iff_lt_embedding]
  have hdense : DenseRange (i ∘ algebraMap E (w.adicCompletion E)) :=
    i.surjective.denseRange.comp (HeightOneSpectrum.denseRange_algebraMap E w) hi
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hU ⟨algebraMap E' _ y, by simp [U]⟩
  refine ⟨x, ?_⟩
  have hx' : w'.valuation E' ((j x - y) * c⁻¹) < 1 := by
    have e : (i (algebraMap E _ x) - algebraMap E' (w'.adicCompletion E') y) *
        (algebraMap E' (w'.adicCompletion E') c)⁻¹ = algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹) := by
      rw [hij, map_mul, map_sub, map_inv₀]
    have hx2 : (i ∘ algebraMap E (w.adicCompletion E)) x ∈ U := hx
    simp only [Function.comp, U, Set.mem_ofPred_eq] at hx2
    rw [e] at hx2
    have hv : Valued.v (algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹)) = w'.valuation E' ((j x - y) * c⁻¹) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w' _
    rw [hv] at hx2
    exact hx2
  have ht := valuationSubring_lt_one_of_placeOver A' w' hP _ hx'
  have e2 : algebraMap E' Ω' y - algebraMap E' Ω' (j x) = -(algebraMap E' Ω' ((j x - y) * c⁻¹) * algebraMap E' Ω' c) := by
    rw [← map_mul, ← map_sub, ← map_neg]; congr 1; field_simp; ring
  have hcpos : 0 < A'.valuation (algebraMap E' Ω' c) := by
    rw [zero_lt_iff]; simpa using hc
  rw [e2, Valuation.map_neg, map_mul]
  calc _ < A'.valuation (algebraMap E' Ω' c) := mul_lt_of_lt_one_left hcpos ht
    _ ≤ A'.valuation δ := hnδ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftRealPointsEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardThetaLift_real_points_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (u, 1) f) l g = downInt R i t y f (l ∘ₗ (R.cV i).ρ u) g := by
  first | exact @GlobalTheory.DownLift.downInt_realEquiv | exact GlobalTheory.DownLift.downInt_realEquiv | (intros; apply GlobalTheory.DownLift.downInt_realEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OffPl {S T' : HSp D} (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T') : Prop :=
  u.map (infPart D) = 0 ∧
    ∀ v ∈ Sb, ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = 0

def SuppIn (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (V : HSp D) (g : GA D V) : Prop :=
  (mt V g - 1).map (infPart D) = 0 ∧
    ∀ v, v ∉ Sb → ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = 0

def Over (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def LikeOff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ c : WO (Vc D i) (Wc D i) →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = 0 →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = 0

def TypeIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), SuppIn Sb (Vc D i) κ →
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def CleanIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    (∃ v ∈ Sb, Over PP.1 v) → ∀ κ : G → GA D (Vc D i), IsLifts R i t κ →
      (∀ g, mirC R i PP a tr ε g ≠ 0 → SuppIn Sb (Vc D i) (κ g)) → avgW R i t PP a tr ε κ f = 0

def StepGen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ),
    TypeIn R i t Sb f ∧ CleanIn R i t Sb f ∧ LikeOff R i t Sb f ∧ φ = R.ωP i t (1, g) f}

open Classical in

def dropPl (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Sb.erase v

theorem dropPl_insert [DecidableEq (HeightOneSpectrum (𝓞 D.host.F))] {s : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ s) : dropPl (insert v s) v = s := by
  unfold dropPl
  convert Finset.erase_insert hv

end GlobalTheory.DownLift.GenFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem elementDenominator_adm7 : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  intro D l _ _ K LL _ T _
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  exact @GlobalTheory.T.h1f_generated_lattice l _ (D.loc l) (D.locA l) (D.locT l) K LL (Fintype.ofFinite _) T _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductive
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilBrauer

theorem eq_of_induced : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  intro hB E Ω _ _ _ _ _ A w h ε ε' hε hε' hcp hchar hind
  classical
  set f : WD h → ℂˣ := fun x => ε x / ε' x with hf
  have fmul : ∀ x y, f (x.lpSum y) = f x * f y := by
    intro x y
    simp only [hf, hε, hε']
    exact mul_div_mul_comm _ _ _ _
  have fcp : ∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y := by
    intro x y hxy
    obtain ⟨h1, h2⟩ := hcp x y hxy
    simp only [hf, h1, h2]
  have key : ∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ),
      (Set.range a.ρ).Finite → f (WD.mk (a.twist μ hμ)) = 1 := by
    intro n a μ hμ hfin
    let u : Weil h →* (Module.End ℂ (Fin n → ℂ))ˣ := a.ρ.toHomUnits
    let G : Subgroup (Module.End ℂ (Fin n → ℂ))ˣ := u.range
    have hGfin : Finite G := by
      have hr : (Set.range u).Finite := by
        refine Set.Finite.of_finite_image (f := Units.val) ?_ Units.val_injective.injOn
        refine hfin.subset ?_
        rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
      have : ((G : Set (Module.End ℂ (Fin n → ℂ))ˣ)) = Set.range u := MonoidHom.coe_range u
      exact Set.finite_coe_iff.mpr (this ▸ hr)
    letI : Fintype G := Fintype.ofFinite G
    let π : Weil h →* G := u.rangeRestrict
    have hπs : Function.Surjective π := MonoidHom.rangeRestrict_surjective u
    let ρG : Representation ℂ G (Fin n → ℂ) := (Units.coeHom _).comp G.subtype
    have hρG : ∀ σ, ρG (π σ) = a.ρ σ := fun σ => rfl
    have hπ1 : ∀ σ, π σ = 1 ↔ a.ρ σ = 1 := by
      intro σ
      constructor
      · intro h1
        rw [← hρG, h1, map_one]
      · intro h1
        apply Subtype.ext
        apply Units.ext
        exact h1
    have hopen : IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} := by
      have : {σ : Ine (F := E) A | π (ineIncl h σ) = 1} = {σ | a.ρ (ineIncl h σ) = 1} :=
        Set.ext fun σ => hπ1 _
      rw [this]
      exact a.smooth
    obtain ⟨r, H, χ, c, hbr⟩ := hB G (Fin n → ℂ) ρG
    have hi1 := fun i => GlobalTheory.T.induced_representation_character G (H i) (χ i)
    have hi2 := fun i => GlobalTheory.T.induced_representation_character G (H i) 1
    choose Rχ vχ hRχ using hi1
    choose R1 v1 hR1 using hi2
    have hp1 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (Rχ i) μ hμ
    have hp2 := fun i => GlobalTheory.T.weil_deligne_of_finite_image E Ω A w h G π hopen _ (R1 i) μ hμ
    choose bχ hbχ using hp1
    choose b1 hb1 using hp2
    have span_of : ∀ (i : Fin r) (R : Representation ℂ G (Fin (H i).index → ℂ))
        (b : WDRep h (Fin (H i).index → ℂ)) (v : Fin (H i).index → ℂ),
        (∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ)) → Submodule.span ℂ (Set.range fun g => R g v) = ⊤ →
        Submodule.span ℂ (Set.range fun σ => b.ρ σ v) = ⊤ := by
      intro i R b v hb hs
      rw [eq_top_iff, ← hs, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨σ, rfl⟩ := hπs g
      show R (π σ) v ∈ _
      have e : R (π σ) v = (((μ σ)⁻¹ : ℂˣ) : ℂ) • b.ρ σ v := by
        rw [hb, LinearMap.smul_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
    have hpair : ∀ i, f (WD.mk (bχ i)) = f (WD.mk (b1 i)) := by
      intro i
      let H' := (H i).comap π
      have hidx : (H i).index = H'.index := (Subgroup.index_comap_of_surjective _ hπs).symm
      haveI : H'.FiniteIndex := ⟨by rw [← hidx]; exact Subgroup.index_ne_zero_of_finite⟩
      have hop : IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H'} := by
        have hle : (π.comp (ineIncl h)).ker ≤ H'.comap (ineIncl h) := by
          intro σ hσ
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ
          show π (ineIncl h σ) ∈ H i
          rw [hσ]
          exact one_mem _
        exact Subgroup.isOpen_mono hle hopen
      let χ₁ : H' →* ℂˣ := μ.comp H'.subtype * (χ i).comp (π.subgroupComap (H i))
      let χ₂ : H' →* ℂˣ := μ.comp H'.subtype * (1 : H i →* ℂˣ).comp (π.subgroupComap (H i))
      have e1 : ∀ σ : H', (bχ i).ρ σ (vχ i) = (χ₁ σ : ℂ) • vχ i := by
        intro σ
        rw [hbχ, LinearMap.smul_apply, (hRχ i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have e2 : ∀ σ : H', (b1 i).ρ σ (v1 i) = (χ₂ σ : ℂ) • v1 i := by
        intro σ
        rw [hb1, LinearMap.smul_apply, (hR1 i).1 ⟨π σ, σ.2⟩, smul_smul]
        rfl
      have hh := hind H' inferInstance hop χ₁ χ₂ _ (bχ i) (b1 i) (vχ i) (v1 i) hidx e1 e2
        (span_of i _ _ _ (hbχ i) (hRχ i).2.1) (span_of i _ _ _ (hb1 i) (hR1 i).2.1)
      simp only [hf]
      exact div_eq_div_iff_mul_eq_mul.mpr hh
    have hμ1 : f (WD.mk (WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ)) = 1 := by
      have := hchar μ hμ
      simp only [hf]
      exact div_eq_one.mpr this
    let F : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → Σ m, WDRep h (Fin m → ℂ) :=
      Sum.elim (Sum.elim (fun _ => ⟨n, a.twist μ hμ⟩)
          (fun _ => ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ⟩))
        (Sum.elim (fun i => ⟨_, bχ i⟩) (fun i => ⟨_, b1 i⟩))
    let cc : (Unit ⊕ Unit) ⊕ (Fin r ⊕ Fin r) → ℤ :=
      Sum.elim (Sum.elim (fun _ => 1) (fun _ => -(n : ℤ))) (Sum.elim (fun i => -c i) (fun i => c i))
    have htr : ∀ σ, ∑ j, (cc j : ℂ) * LinearMap.trace ℂ (Fin (F j).1 → ℂ) ((F j).2.ρ σ) = 0 := by
      intro σ
      have hb := hbr (π σ)
      rw [Module.finrank_fin_fun] at hb
      have t0 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inl (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inl (default : Unit)))).2.ρ σ) =
          (μ σ : ℂ) * LinearMap.trace ℂ (Fin n → ℂ) (ρG (π σ)) := by
        show LinearMap.trace ℂ (Fin n → ℂ) ((a.twist μ hμ).ρ σ) = _
        rw [WDRep.twist_ρ, map_smul, smul_eq_mul, hρG]
      have t1 : LinearMap.trace ℂ (Fin (F (Sum.inl (Sum.inr (default : Unit)))).1 → ℂ)
          ((F (Sum.inl (Sum.inr (default : Unit)))).2.ρ σ) = (μ σ : ℂ) := by
        show LinearMap.trace ℂ (Fin 1 → ℂ)
          ((WDRep.ofChars h (ι := Fin 1) (fun _ => μ) fun _ => hμ).ρ σ) = _
        rw [WDRep.ofChars_ρ]
        have e : (diagEnd fun _ : Fin 1 => (μ σ : ℂ)) = (μ σ : ℂ) • (1 : Module.End ℂ (Fin 1 → ℂ)) := by
          ext v i
          simp
        rw [e, map_smul, LinearMap.trace_one, smul_eq_mul, Module.finrank_fin_fun, Nat.cast_one,
          mul_one]
      have tχ : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inl i))).1 → ℂ)
          ((F (Sum.inr (Sum.inl i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((bχ i).ρ σ) = _
        rw [hbχ, map_smul, smul_eq_mul, (hRχ i).2.2]
      have t1' : ∀ i, LinearMap.trace ℂ (Fin (F (Sum.inr (Sum.inr i))).1 → ℂ)
          ((F (Sum.inr (Sum.inr i))).2.ρ σ) =
          (μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ) := by
        intro i
        show LinearMap.trace ℂ _ ((b1 i).ρ σ) = _
        rw [hb1, map_smul, smul_eq_mul, (hR1 i).2.2]
        simp
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, t0, t1, tχ, t1']
      simp only [cc, Sum.elim_inl, Sum.elim_inr, Int.cast_one, Int.cast_neg, Int.cast_natCast,
        one_mul]
      have hs : ∑ i, -(c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun x => (χ i x : ℂ)) (π σ)) +
          ∑ i, (c i : ℂ) * ((μ σ : ℂ) * indFun (H i) (fun _ => 1) (π σ)) =
          -(μ σ : ℂ) * ∑ i, (c i : ℂ) * (indFun (H i) (fun x => (χ i x : ℂ)) (π σ) -
            indFun (H i) (fun _ => 1) (π σ)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hs]
      linear_combination (μ σ : ℂ) * hb
    have hv := GlobalTheory.T.multiplicative_virtual_character E Ω A w h f fmul fcp _ (fun j => (F j).1) (fun j => (F j).2) cc htr
    have hμ1' : f (WD.mk (F (Sum.inl (Sum.inr (default : Unit)))).2) = 1 := hμ1
    have hp' : ∀ i, f (WD.mk (F (Sum.inr (Sum.inl i))).2) = f (WD.mk (F (Sum.inr (Sum.inr i))).2) :=
      hpair
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, hμ1', hp'] at hv
    simp only [cc, Sum.elim_inl, Sum.elim_inr, zpow_one, _root_.zpow_neg, _root_.one_zpow, inv_one,
      mul_one, ← Finset.prod_mul_distrib, _root_.inv_mul_cancel, Finset.prod_const_one] at hv
    exact hv
  intro x
  have hx := GlobalTheory.T.weil_deligne_induction_principle E Ω A w h (fun x => f x = 1)
    (fun x y hx hy => by rw [fmul, hx, hy, one_mul])
    (fun x y hxy hx => by rw [← fcp x y hxy, hx]) key x
  simp only [hf] at hx
  exact div_eq_one.mp hx

end GlobalTheory.WeilBrauer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisLimitLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_basis_limit_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val), ∃ (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), ∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r := by
  first | (exact @GlobalTheory.BKLim.limit_pre_exists) | (exact GlobalTheory.BKLim.limit_pre_exists) | (intros; apply GlobalTheory.BKLim.limit_pre_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeLEqToricSumNeZeroStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  first | exact @GlobalTheory.ToricValue.exists_heckeL_toricSum | exact GlobalTheory.ToricValue.exists_heckeL_toricSum | (intros; apply GlobalTheory.ToricValue.exists_heckeL_toricSum <;> assumption)
end

