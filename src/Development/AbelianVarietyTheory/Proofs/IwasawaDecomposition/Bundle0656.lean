import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.SharpRestriction.Divisibility.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0121
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlanarOfDenseCarriers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPoleOfBounded
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcReg

theorem valR_eq_ev {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = ev x U h f := by
  rw [valR, dif_pos h]; rfl

theorem not_pole_of_bounded : ∀ (X : Scheme.{0}) (U₀ W₀ : X.Opens) (f₀ : Γ(X, W₀)) (χ : Sp (PowerSeries ℂ) ⟶ X) (y : ℂ → (Sp ℂ ⟶ X)), IsAffineOpen U₀ → W₀ ≤ U₀ → ⊤ ≤ χ ⁻¹ᵁ U₀ → (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ⊤ ≤ y w ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (y w) U f)) → (∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ hy : ⊤ ≤ y w ⁻¹ᵁ W₀, ‖ev (y w) W₀ hy f₀‖ ≤ C) → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range := by
  intro X U₀ W₀ f₀ χ y hU₀ hWU hχ harc hbd h
  have hηW : (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) (default : PrimeSpectrum (LaurentSeries ℂ)) ∈ W₀ :=
    h trivial
  obtain ⟨s, hsW, hsη⟩ := hU₀.exists_basicOpen_le (V := W₀) ⟨_, hηW⟩ (hWU hηW)
  obtain ⟨n, t, ht⟩ := exists_eq_pow_mul_of_isAffineOpen X U₀ hU₀ s
    ((X.presheaf.map (homOfLE hsW).op).hom f₀)
  have hsU : X.basicOpen s ≤ U₀ := X.basicOpen_le s

  have key : ∀ (A : Type) [CommRing A] (z : Sp A ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ X.basicOpen s),
      valR z U₀ (t * s) = valR z U₀ (s ^ (n + 1)) * valR z W₀ f₀ := by
    intro A _ z hz
    have hzU : ⊤ ≤ z ⁻¹ᵁ U₀ := GlobalTheory.FlagMod.le_preimage_mono hsU hz
    have e := congrArg (GlobalTheory.HolHom.evalHom z _ hz) ht
    rw [map_mul, map_pow] at e
    simp only [← GlobalTheory.HolHom.valR_eq z _ hz] at e
    erw [GlobalTheory.HolHom.valR_res z hsU t hz, GlobalTheory.HolHom.valR_res z hsU s hz, GlobalTheory.HolHom.valR_res z hsW f₀ hz] at e
    rw [GlobalTheory.HolHom.valR_eq z U₀ hzU, GlobalTheory.HolHom.valR_eq z U₀ hzU, map_mul, map_pow,
      ← GlobalTheory.HolHom.valR_eq z U₀ hzU, ← GlobalTheory.HolHom.valR_eq z U₀ hzU, e]
    ring

  have hηs : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ X.basicOpen s := fun p _ => by
    obtain rfl : p = (default : PrimeSpectrum (LaurentSeries ℂ)) := Subsingleton.elim _ _
    exact hsη
  have hηU : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ U₀ := GlobalTheory.FlagMod.le_preimage_mono hsU hηs
  have hu : IsUnit (HahnSeries.ofPowerSeries ℤ ℂ (valR χ U₀ (s ^ (n + 1)))) := by
    rw [← GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, GlobalTheory.HolHom.valR_eq _ U₀ hηU, map_pow, ← GlobalTheory.HolHom.valR_eq _ U₀ hηU]
    exact ((GlobalTheory.ArcLie.le_basicOpen_iff_isUnit _ hηU s).1 hηs).pow _
  have kη := key _ _ hηs
  rw [GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, valR_eq_ev _ W₀ h] at kη
  have hH : valR χ U₀ (s ^ (n + 1)) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨T₁, h₁⟩ := harc U₀ (t * s) hχ
  obtain ⟨T₂, h₂⟩ := harc U₀ (s ^ (n + 1)) hχ
  obtain ⟨T₃, C, h₃⟩ := hbd
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.nomePowerSeries_dvd_of_sum_bounded (valR χ U₀ (t * s)) (valR χ U₀ (s ^ (n + 1))) (max T₁ (max T₂ T₃)) C
    (fun w => valAt' (y w) U₀ (t * s)) (fun w => valAt' (y w) U₀ (s ^ (n + 1))) hH (fun w hw => by
      have hw1 : T₁ < w.im := lt_of_le_of_lt (le_max_left _ _) hw
      have hw2 : T₂ < w.im := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hw
      have hw3 : T₃ < w.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hw
      obtain ⟨hyU, hG⟩ := h₁ w hw1
      obtain ⟨-, hH'⟩ := h₂ w hw2
      refine ⟨hG, hH', fun hne => ?_⟩
      have hys : ⊤ ≤ y w ⁻¹ᵁ X.basicOpen s := by
        rw [GlobalTheory.HolHom.le_basicOpen_iff (y w) hyU s]
        intro h0
        apply hne
        rw [GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_eq _ _ hyU, map_pow]
        rw [GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_eq _ _ hyU] at h0
        rw [h0, zero_pow (Nat.succ_ne_zero n)]
      have hyW : ⊤ ≤ y w ⁻¹ᵁ W₀ := GlobalTheory.FlagMod.le_preimage_mono hsW hys
      show ‖valR (y w) U₀ (t * s)‖ ≤ C * ‖valR (y w) U₀ (s ^ (n + 1))‖
      rw [key ℂ (y w) hys, valR_eq_ev (y w) W₀ hyW, norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (h₃ w hw3 hyW) (norm_nonneg _))
  rw [hQ, map_mul] at kη
  exact ⟨Q, hu.mul_left_cancel kη⟩

end GlobalTheory.ArcReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartnerPointIntegralModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.GeoGraft
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PartnerIn

section Lift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_lift (Z : Mdl Y i₀) {C : SCF p} (P : PointsOfFlagModel.PtC (Y Z.i) C) (u : Vecs Dw (Y Z.i).t ↥C.S)
    (hu : IsFrame (c := Z.i.c) (Y Z.i).t P.fK (P.y ≫ (Y Z.i).j) u) :
    ∃ z : Sp ↥(intO ↥C.S) ⟶ Z.X, z ≫ Z.π = P.yt := by
  obtain ⟨w, ⟨hw, -⟩, -⟩ := Z.bij ↥C.S P.fK P.y P.y_over u hu
  have : IsProper Z.s := projProper _ _ Z.s ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  have hpr : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
  have := GlobalTheory.LocM.Cht.isFractionRing_ball ↥C.S
  have hs : w ≫ Z.s = spMap ((intO ↥C.S).subtype.comp P.alg) := by
    rw [← Z.π_s, ← Category.assoc, hw, ← P.ext, Category.assoc, P.yt_over, GlobalTheory.EtaVal.spMap_comp_spMap]
  have hE : ValuativeCriterion.Existence Z.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s).1
  let S : ValuativeCommSq Z.s :=
    { R := ↥(intO ↥C.S)
      K := ↥C.S
      i₁ := w
      i₂ := spMap P.alg
      commSq := ⟨by rw [hs, spMap_comp]; rfl⟩ }
  obtain ⟨⟨l⟩⟩ := hE S
  have hl : spMap (intO ↥C.S).subtype ≫ l.l = w := l.fac_left
  have hr : l.l ≫ Z.s = spMap P.alg := l.fac_right
  refine ⟨l.l, GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective (Y Z.i).s _ _ ?_ ?_⟩
  · rw [← Category.assoc, hl, hw, P.ext]
  · rw [Category.assoc, Z.π_s, hr, P.yt_over]

end Lift

section Frame
open GlobalTheory.Exist.FlagBaseChange MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c₂ : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c₂.F}
  {p : ℕ} {C : SCF p}

end Frame

section Place

variable {K : Type} [Field K] [NumberField K]

theorem exists_overLa (T : CDVR) (s : K →+* T.Fr) {p : ℕ} (hp : p.Prime) (hpm : (p : T.V) ∈ maximalIdeal T.V) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la T.V s e ∧ ((p : ℕ) : 𝓞 K) ∈ la.asIdeal := by
  have hint : ∀ x : 𝓞 K, ∃ v : T.V, algebraMap T.V T.Fr v = s x := fun x => by
    have h : IsIntegral T.V (s (x : K)) := (RingOfIntegers.isIntegral_coe x).map_of_comp_eq
      (Int.castRingHom T.V) s (RingHom.ext_int _ _)
    exact IsIntegrallyClosed.isIntegral_iff.1 h
  choose f₀ hf₀ using hint
  have hinj := IsFractionRing.injective T.V T.Fr
  let f : 𝓞 K →+* T.V :=
    { toFun := f₀
      map_one' := hinj (by simp [hf₀])
      map_mul' := fun x y => hinj (by simp [hf₀])
      map_zero' := hinj (by simp [hf₀])
      map_add' := fun x y => hinj (by simp [hf₀]) }
  have hf : ∀ x, algebraMap T.V T.Fr (f x) = s x := hf₀
  have hpP : ((p : ℕ) : 𝓞 K) ∈ Ideal.comap f (maximalIdeal T.V) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpm
  have hne : Ideal.comap f (maximalIdeal T.V) ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  let la : HeightOneSpectrum (𝓞 K) := ⟨Ideal.comap f (maximalIdeal T.V), Ideal.comap_isPrime _ _, hne⟩
  obtain ⟨hdvr, -⟩ := isDiscreteValuationRing_and_finite_residueField_valuationSubringAtPrime K la
    (Ring.HasFiniteQuotients.finiteQuotient la.ne_bot)
  let V₀ := la.valuationSubringAtPrime K
  haveI : IsLocalization la.asIdeal.primeCompl V₀ :=
    Localization.subalgebra.isLocalization_ofField K la.asIdeal.primeCompl la.asIdeal.primeCompl_le_nonZeroDivisors
  have hunit : ∀ y : la.asIdeal.primeCompl, IsUnit (f y) := fun y =>
    IsLocalRing.notMem_maximalIdeal.1 fun h => y.2 h
  let o : V₀ →+* T.V := IsLocalization.lift (M := la.asIdeal.primeCompl) hunit
  have ho : ∀ a : 𝓞 K, o (algebraMap (𝓞 K) V₀ a) = f a := fun a => IsLocalization.lift_eq hunit a
  have e : s.comp V₀.subtype = (algebraMap T.V T.Fr).comp o :=
    IsLocalization.ringHom_ext la.asIdeal.primeCompl (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, ho, hf]
      rfl)
  have hloc : IsLocalHom o := ⟨fun a ha => by
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj la.asIdeal.primeCompl a
    have h1 : o a * f y = f x := by
      have := congrArg o hxy
      simpa [ho] using this
    have h2 : IsUnit (f x) := h1 ▸ ha.mul (hunit y)
    have h3 : x ∉ la.asIdeal := fun h => h (by exact h2)
    have h4 : IsUnit (algebraMap (𝓞 K) V₀ x) :=
      IsLocalization.map_units V₀ (⟨x, h3⟩ : la.asIdeal.primeCompl)
    rw [← hxy] at h4
    exact isUnit_of_mul_isUnit_left h4⟩
  obtain ⟨r, hr, hv⟩ := GlobalTheory.PlaceExtField.exists_index (V := V₀) (K' := K) (V' := T.V) (K'' := T.Fr) o s
    (fun v => RingHom.congr_fun e v)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V₀
  have h1 := GlobalTheory.PlaceCompletion.overLa_one_of_irreducible (la := la) (V := V₀) (K' := K) (RingHom.id K)
    (RingHom.id V₀) (fun x => rfl) hπ hπ
  refine ⟨la, r, ⟨hr, fun a => ?_⟩, hpP⟩
  have h2 := h1.2 a
  simp only [RingHom.id_apply, Nat.cast_one, one_mul] at h2
  rw [hv, h2]

end Place

section Ext
open scoped TensorProduct

end Ext

section Core
open GlobalTheory.Exist.FlagBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c₂ : Coeff l}

end Core

section Core0
open GlobalTheory.Exist.FlagBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c₂ : Coeff l}

end Core0

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Main

section Tr
variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def piPt {ι : Type} (L : ι → ModuliIntegralCharts.Loc D N j p) (v : ι) (y : (L v).Pt (L v).YY) : (Loc.pi L).Pt (Loc.pi L).YY := ⟨v, y⟩

end Tr

end GlobalTheory.PartnerIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomain
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

noncomputable section

namespace GlobalTheory.RiemSmooth

def stdR (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (hermForm Hm z w).im := rfl

theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (p q : Fin g) :
    Hm p q = ((imForm Hm (stdR g ⟨p, 1⟩) (stdR g ⟨q, 0⟩) : ℝ) : ℂ) +
      ((imForm Hm (stdR g ⟨p, 0⟩) (stdR g ⟨q, 0⟩) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [imForm_apply, stdR, hermForm, Pi.basis_apply]

end GlobalTheory.RiemSmooth

namespace GlobalTheory.RiemSmooth

def coordMat {g : ℕ} (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ)) :
    Matrix (Σ _ : Fin g, Fin 2) (Σ _ : Fin g, Fin 2) ℝ :=
  Matrix.of fun a k => (stdR g).repr (u k) a

theorem std_eq_sum {g : ℕ} (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ)) (hM : (coordMat u).det ≠ 0)
    (a : Σ _ : Fin g, Fin 2) :
    stdR g a = ∑ k, ((coordMat u)⁻¹ k a) • u k := by
  apply (stdR g).repr.injective
  ext a'
  have h1 : coordMat u * (coordMat u)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hM)
  have h2 : ∑ k, coordMat u a' k * (coordMat u)⁻¹ k a = if a = a' then 1 else 0 := by
    rw [← Matrix.mul_apply, h1, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.smul_apply, Finset.sum_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply]
  rw [← h2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem imForm_std {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u : (Σ _ : Fin g, Fin 2) → (Fin g → ℂ))
    (hM : (coordMat u).det ≠ 0) (F : (Σ _ : Fin g, Fin 2) → (Σ _ : Fin g, Fin 2) → ℝ)
    (hF : ∀ k l, (hermForm Hm (u k) (u l)).im = F k l) (a c : Σ _ : Fin g, Fin 2) :
    imForm Hm (stdR g a) (stdR g c) =
      ∑ k, ∑ l, (coordMat u)⁻¹ k a * (coordMat u)⁻¹ l c * F k l := by
  rw [std_eq_sum u hM a, std_eq_sum u hM c]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    imForm_apply, hF]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem contDiffOn_det_real {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s) :
    ContDiffOn ℝ ∞ (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem contDiffOn_inv_entry {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : X → Matrix ι ι ℝ} {s : Set X} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => M x a b) s)
    (hdet : ∀ x ∈ s, (M x).det ≠ 0) (k a : ι) :
    ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ k a) s := by
  have hadj : ContDiffOn ℝ ∞ (fun x => (M x).adjugate k a) s := by
    simp only [Matrix.adjugate_apply]
    refine contDiffOn_det_real fun i j => ?_
    by_cases hi : i = a
    · subst hi; simpa [Matrix.updateRow_apply] using contDiffOn_const
    · simpa [Matrix.updateRow_apply, hi] using h i j
  refine ((contDiffOn_det_real h).inv hdet |>.mul hadj).congr fun x hx => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp [smul_eq_mul]

end GlobalTheory.RiemSmooth

namespace GlobalTheory.RiemSmooth

theorem contDiffOn_of_im_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : Type} [AddCommGroup L] {g : ℕ}
    {B : Set X} (hB : IsOpen B) (P : X → (L →+ (Fin g → ℂ))) (F : L → L → ℝ)
    (hP : ∀ v, ContDiffOn ℝ ∞ (fun b => P b v) B)
    (hspan : ∀ b ∈ B, Submodule.span ℝ (Set.range (P b)) = ⊤)
    (Hm : X → Matrix (Fin g) (Fin g) ℂ)
    (hH : ∀ b ∈ B, ∀ x y, (hermForm (Hm b) (P b x) (P b y)).im = F x y) (p q : Fin g) :
    ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  refine contDiffOn_of_locally_contDiffOn fun b₀ hb₀ => ?_
  obtain ⟨t, ht, hts, hli⟩ := exists_linearIndependent ℝ (Set.range (P b₀))
  rw [hspan b₀ hb₀] at hts
  let bt : Module.Basis t ℝ (Fin g → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hts])
  let e := bt.indexEquiv (stdR g)
  have hv : ∀ k, ∃ v, P b₀ v = bt (e.symm k) := fun k => by
    obtain ⟨v, hv⟩ := ht (e.symm k).2
    exact ⟨v, by rw [hv, Module.Basis.mk_apply]⟩
  choose v hv using hv
  let M : X → Matrix (Σ _ : Fin g, Fin 2) (Σ _ : Fin g, Fin 2) ℝ := fun b => coordMat fun k => P b (v k)
  have hMs : ∀ a k, ContDiffOn ℝ ∞ (fun b => M b a k) B := fun a k => by
    let ℓ : (Fin g → ℂ) →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap ((Finsupp.lapply a).comp (stdR g).repr.toLinearMap)
    exact ℓ.contDiff.comp_contDiffOn (hP (v k))
  have hdet0 : (M b₀).det ≠ 0 := by
    have : M b₀ = (stdR g).toMatrix (bt.reindex e) := by
      ext a k
      simp [M, coordMat, Module.Basis.toMatrix_apply, hv]
    rw [this, ← Module.Basis.det_apply]
    exact ((stdR g).isUnit_det _).ne_zero
  have hcont : ContinuousAt (fun b => (M b).det) b₀ :=
    (contDiffOn_det_real hMs).continuousOn.continuousAt (hB.mem_nhds hb₀)
  obtain ⟨U, hU, hUo, hb₀U⟩ := eventually_nhds_iff.1 (hcont.eventually_ne hdet0)
  refine ⟨U, hUo, hb₀U, ?_⟩
  have hdet : ∀ b ∈ B ∩ U, (M b).det ≠ 0 := fun b hb => hU b hb.2
  have hN := contDiffOn_inv_entry (fun a k => (hMs a k).mono Set.inter_subset_left) hdet
  have hsum : ∀ a c, ContDiffOn ℝ ∞ (fun b => ∑ k, ∑ l, (M b)⁻¹ k a * (M b)⁻¹ l c * F (v k) (v l)) (B ∩ U) :=
    fun a c => ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ =>
      ((hN k a).mul (hN l c)).mul contDiffOn_const
  refine ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hsum ⟨p, 1⟩ ⟨q, 0⟩)).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hsum ⟨p, 0⟩ ⟨q, 0⟩)).mul (contDiffOn_const (c := Complex.I)))).congr
    fun b hb => ?_
  have hF : ∀ k l, (hermForm (Hm b) (P b (v k)) (P b (v l))).im = F (v k) (v l) :=
    fun k l => hH b hb.1 _ _
  have h1 := entry_eq (Hm b) p q
  rw [imForm_std (Hm b) _ (hdet b hb) _ hF, imForm_std (Hm b) _ (hdet b hb) _ hF] at h1
  exact h1

theorem exists_riem_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → ∃ Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ, (∀ b ∈ B, IsRiem Fu i (P b) (Hm b)) ∧ ∀ p q, ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  intro E _ _ _ H Dw l Xo c σ g ty Fu i d B P hB hper hhol
  classical
  let Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ :=
    fun b => if h : b ∈ B then Classical.choose (hper b h).2.2.2.2 else 0
  have hHm : ∀ b (h : b ∈ B), Hm b = Classical.choose (hper b h).2.2.2.2 := fun b h => dif_pos h
  have hR : ∀ b ∈ B, IsRiem Fu i (P b) (Hm b) := fun b h => by
    rw [hHm b h]
    exact Classical.choose_spec (hper b h).2.2.2.2
  refine ⟨Hm, hR, fun p q => ?_⟩
  refine contDiffOn_of_im_eq hB P (fun x y => ((Fu.Di i).EF x y : ℝ)) (fun v => ?_)
    (fun b h => (hper b h).2.2.2.1) Hm (fun b h x y => (hR b h).2.2 x y) p q
  exact contDiffOn_pi.2 fun j =>
    GlobalTheory.ChartGlue.contDiffOn_real hB ((differentiableOn_pi.1 (hhol v)) j)

end GlobalTheory.RiemSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplitStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_over_real_subfield_split : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (A : SideA D cf jE) (S : RatDat D.ntw) (In : RatIn D S)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    (∀ v, NG.OverPl (Pq v) v) →
    (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) →
    ∀ (wt : WtData D T), (∀ i j b, 1 ≤ j → j ≤ D.R.m → (wt.rhoW i j b).IsIrreducible ∧
      NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b)) →
    ∀ (hE : IsEmpty D.nd.Loc) (F : TwF T) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m →
      Formalism.MainNotions.NAdm.TWSet (T.ntw hE F (TwL.empty T)) i Q →
      (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) →
      IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) → AntiHom T.cc ψ → (∀ σ, ∃ N : ℕ, ψ σ ^ (T.l i ^ N) = 1) →
      (∀ P, P ∉ Q → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, ψ σ = 1) →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) := by
  first | exact @GlobalTheory.LevForms.levDatum_forms | exact GlobalTheory.LevForms.levDatum_forms | (intros; apply GlobalTheory.LevForms.levDatum_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlanarOfDenseCarriersStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.planar_of_dense_carriers : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (Ω : Set Z'), IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ ξ, Car Em f q w α h ξ) → Planar Em f q := by
  first | exact @GlobalTheory.GrCl.PlanarMap.planar_of_generic | exact GlobalTheory.GrCl.PlanarMap.planar_of_generic | (intros; apply GlobalTheory.GrCl.PlanarMap.planar_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_nonzero_iff_independent : ∀ (K : Type) [Field K] (N k : ℕ) (u u' : Fin k → Fin (N + 1) → K), (plk u id ≠ 0 ↔ LinearIndependent K u) ∧ (LinearIndependent K u → ((LinearIndependent K u' ∧ Submodule.span K (Set.range u') = Submodule.span K (Set.range u)) ↔ ∃ r : Kˣ, plk u' id = (r : K) • plk u id)) := by
  first | exact @GlobalTheory.FlagEmb.PlkSpan.main | exact GlobalTheory.FlagEmb.PlkSpan.main | (intros; apply GlobalTheory.FlagEmb.PlkSpan.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModelsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_transfer_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPhiDiv φ Z BD → IsPhiDiv φ Z' BD' →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Z.X) (χ' : Sp W ⟶ Z'.X)
      (y : Sp (FractionRing W) ⟶ Xo'.XF c'), jK W ≫ χ' = y ≫ Z'.j → jK W ≫ χ = y ≫ r ≫ Z.j →
      idlAlong BD'.idealSheaf χ' = idlAlong BD.idealSheaf χ := by
  first | exact @GlobalTheory.TraitOrder.idlAlong_eq | exact GlobalTheory.TraitOrder.idlAlong_eq | (intros; apply GlobalTheory.TraitOrder.idlAlong_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_series_arc_abelian_locus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) (O' : Type) [CommRing O'] [IsDomain O']
    [CharZero O'] (b' : c.V W →+* O') (χ₀ : Sp (PowerSeries O') ⟶ Y.X),
    χ₀ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b' →
    (∀ x : Sp (PowerSeries O'), χ₀ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) →
    ∃ x₀ : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, Out.jK (PowerSeries O') ≫ χ₀ = x₀ ≫ Y.j := by
  first | exact @GlobalTheory.PolArc.generic_factors_open | exact GlobalTheory.PolArc.generic_factors_open | (intros; apply GlobalTheory.PolArc.generic_factors_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → Down u → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (z : Sp ↥(intO C) ⟶ Z.X) a i (φ : Γ(Z.X, (Z.U a).1) →+* C), spMap φ ≫ Z.chart a = spMap (intO C).subtype ≫ z → ⊤ ≤ z ⁻¹ᵁ L'.U i → Real.log ‖valF (spMap (intO C).subtype ≫ z) _ (r a i).val‖ + Real.log (grNorm (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π) (latDR (Y Z.i).t ((spMap (intO C).subtype ≫ z) ≫ Z.π)) (fun j => (Z.fr a).bc φ (u j).1 (u j).2) kk) = 0 := by
  first | exact @GlobalTheory.FlagEmb.LineNorm.log_norm_add_log_grNorm | exact GlobalTheory.FlagEmb.LineNorm.log_norm_add_log_grNorm | (intros; apply GlobalTheory.FlagEmb.LineNorm.log_norm_add_log_grNorm <;> assumption)
end

