import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTwistColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMulInv
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorProof

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTwistColumns
open scoped TensorProduct

def WeilUnique (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f

def WeilChange (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT νS νT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 →
    ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h)

variable {D : D7}

theorem isHeckeChar_mul_inv {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2, inv_one, mul_one]⟩

theorem isDetRoot_one (V : HSp D) : IsDetRoot V 1 1 := by
  unfold IsDetRoot
  rw [map_one, Units.val_one, Units.val_one, Matrix.det_one, map_one, one_mul]

theorem weil_ratio (hU : WeilUnique D) (hC : WeilChange D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT χS' χT' : (AE D)ˣ →* Circle} {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (ho : IsWeilDatumO ψ S T χS χT om) (ho' : IsWeilDatumO ψ S T χS' χT' om') {g : GA D S} {h : GA D T}
    {x y : (AE D)ˣ} (hx : IsDetRoot S g x) (hy : IsDetRoot T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om' (g, h) f = ((((χT' x * (χT x)⁻¹)⁻¹ * (χS' y * (χS y)⁻¹) : Circle) : ℂ)) • om (g, h) f := by
  obtain ⟨o, h1, h2⟩ := hC ψ ho.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om ho
    (isHeckeChar_mul_inv ho'.hecS ho.hecS) (isHeckeChar_mul_inv ho'.hecT ho.hecT)
    (resEta_parity (resEta_mul ho'.resS (resEta_inv ho.resS)) (by omega))
    (resEta_parity (resEta_mul ho'.resT (resEta_inv ho.resT)) (by omega))
  have e : ∀ a b : (AE D)ˣ →* Circle, a * (b * a⁻¹) = b := fun a b => by
    ext1 z
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [mul_comm (b z), mul_inv_cancel_left]
  rw [e, e] at h1
  rw [hU ψ ho.std S T χS' χT' om' o ho' h1 _ f hf, h2 g h x y hx hy]
  rfl

theorem vac_ne_zero {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := h.2.norm
  have := hn p hp
  simp [nrm2] at this

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem frame_ratio (hU : WeilUnique D) (hC : WeilChange D) (hω : R.thP_ωP) (i : Fin D.R.m) (t t' : T0)
    {h : GA D (Wc D i)} {x : (AE D)ˣ} (hx : IsDetRoot (Wc D i) h x) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) :
    ((R.xi t x : Circle) : ℂ) • R.ωP i t' (1, h) f = ((R.xi t' x : Circle) : ℂ) • R.ωP i t (1, h) f := by
  rw [weil_ratio hU hC (hω i t) (hω i t') (isDetRoot_one _) hx hf, smul_smul, ← Circle.coe_mul]
  congr 2
  show R.xi t x * (_ * (R.mu0 _ x * R.xi t' x * (R.mu0 _ x * R.xi t x)⁻¹)) = _
  rw [map_one, map_one, mul_inv_cancel, inv_one, one_mul, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul,
    mul_comm (R.xi t' x), mul_inv_cancel_left]

end GlobalTheory.TwistFactorProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IntCoefExt

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem nval_nonneg_iff {e : ℕ} (he : 0 < e) (x : K') : 0 ≤ nval V e x ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    simp [nval_zero, vV]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ he', zero_mul]
  exact_mod_cast Iff.rfl

theorem exists_nat_pos {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {ι : K →+* K'} {e : ℕ}
    (ho : OverLa la V ι e) : ∃ N : ℕ, N ≠ 0 ∧ 0 < vV V (N : K') := by
  have hN : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm la.asIdeal, hN, ?_⟩
  have h1 := ho.2 (Ideal.absNorm la.asIdeal : K)
  rw [map_natCast] at h1
  rw [h1]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h2 : la.valuation K (Ideal.absNorm la.asIdeal : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) _).2 (Ideal.absNorm_mem la.asIdeal)
    simpa using this
  have h0 : la.valuation K (Ideal.absNorm la.asIdeal : K) ≠ 0 := by
    simpa using hN
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
  simp only [vLa]
  omega

theorem exists_overLa {K : Type} [Field K] [NumberField K] (ι : K →+* K') {N : ℕ} (hN : N ≠ 0)
    (h : 0 < vV V (N : K')) : ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la V ι e := by
  let u := (valV V (K' := K')).comap ι
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.CommonValuation.exists_centre u
  have hN' : (N : K') ≠ 0 := by
    rw [← map_natCast ι]
    exact (map_ne_zero ι).2 (Nat.cast_ne_zero.2 hN)
  have hNQ : (N : 𝓞 K) ∈ Q := by
    rw [hQm, map_natCast]
    show valV V (ι N) < 1
    rw [map_natCast, ← WithZero.exp_log (valV_ne_zero (V := V) hN'), ← WithZero.exp_zero, WithZero.exp_lt_exp]
    simp only [vV] at h
    omega
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hN (Nat.cast_eq_zero.1 ((Submodule.mem_bot _).1 hNQ))
  let la : HeightOneSpectrum (𝓞 K) := ⟨Q, hQ, h0⟩
  obtain ⟨e, he, hv⟩ := GlobalTheory.CommonValuation.exists_eq_pow la u
    (GlobalTheory.CommonValuation.le_one_of_ringOfIntegers u) (fun r => (hQm r).symm)
  refine ⟨la, e, he, fun a => ?_⟩
  have := hv a
  rw [Valuation.comap_apply] at this
  simp only [vV, vLa, this, WithZero.log_pow, nsmul_eq_mul]
  ring

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem integral_res_iff (T : CDVR) (io' : c'.F →+* T.Fr) (io : c.F →+* T.Fr)
    (h : ∀ a, io' (incF c c' hle a) = io a) (y : letI := io'.toAlgebra; FrPt Xo c' T.Fr) :
    Integral T io' y ↔ Integral T io (letI := io.toAlgebra; letI := io'.toAlgebra; y.res hle h) := by
  have e : ∀ (G : SAB H (Sp T.V)) τ v, IsEigV c' io' G τ v ↔ IsEigV c io G τ v := fun G τ v => by
    unfold IsEigV
    simp only [← embK_incF hle τ, h]
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).1 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).2 he), h4⟩, h5⟩
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).2 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).1 he), h4⟩, h5⟩

theorem intAt_iff (f : Rul Xo c) : IntAt Xo c f ↔ ∀ (T : CDVR) (io : c.F →+* T.Fr) (N : ℕ), N ≠ 0 →
    0 < vV T.V (N : T.Fr) → T.FinRes → ∀ y : IntFr Xo c T io, 0 ≤ vV T.V (evI y f) := by
  constructor
  · intro h T io N hN hp hT y
    obtain ⟨la, e, ho⟩ := exists_overLa io hN hp
    exact (nval_nonneg_iff ho.1 _).1 (h la _ ⟨PtV.mk la ho y hT () trivial, rfl⟩)
  · rintro h la _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩
    obtain ⟨N, hN, hp⟩ := exists_nat_pos ho
    exact (nval_nonneg_iff ho.1 _).2 (h T io N hN hp hy y)

theorem intAt_rulBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, (IntAt Xo c' (rulBC hle f) ↔ IntAt Xo c f) := by
  intro E _ _ _ H Dw l Xo c c' hle a n f hf
  have hval := ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2
  rw [intAt_iff, intAt_iff]
  constructor
  · intro h T io N hN hp hT y
    letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
    haveI := c.fin
    haveI := c'.fin
    haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun x => by simp
    haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ _ _
    obtain ⟨L, _, _, g, hL, -, hg⟩ := GlobalTheory.exists_finite_separable_compositum c.F T.Fr c'.F io
    obtain ⟨T', iT, e, ψ, -, he, hv, hψ, -, hfin⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
    obtain ⟨⟨y₁, -, -, φ, hφ, hm⟩, -⟩ := GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T' io y iT e he hv
    let io' : c'.F →+* T'.Fr := ψ.toRingHom.comp g
    have hio : ∀ x, io' (incF c c' hle x) = (iT.comp io) x := fun x => by
      have := DFunLike.congr_fun hg x
      exact (congrArg ψ this).trans (hψ _)
    have hp' : 0 < vV T'.V (N : T'.Fr) := by
      rw [← map_natCast iT, hv]
      exact mul_pos (by exact_mod_cast he) hp
    have e1 : evI y₁ f = iT (evI y f) := by
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      exact (pos_evR (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1 y.2.1 y₁.1 hm).trans
        (DFunLike.congr_fun hφ _)
    letI := (iT.comp io).toAlgebra
    letI := io'.toAlgebra
    let y' : IntFr Xo c' T' io' := ⟨y₁.1.ext hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T' io' (iT.comp io) hio _).2 y₁.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y₁ f := hval T'.Fr hio y'.1
    have key := h T' io' N hN hp' (hfin hT) y'
    rw [e2, e1, hv] at key
    exact nonneg_of_mul_nonneg_right key (by exact_mod_cast he)
  · intro h T io' N hN hp hT y'
    let io : c.F →+* T.Fr := io'.comp (incF c c' hle)
    have hio : ∀ x, io' (incF c c' hle x) = io x := fun _ => rfl
    letI := io.toAlgebra
    letI := io'.toAlgebra
    let y : IntFr Xo c T io := ⟨y'.1.res hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T io' io hio _).1 y'.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y f := hval T.Fr hio y'.1
    rw [e2]
    exact h T io N hN hp hT y

end GlobalTheory.IntCoefExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSquareSqMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def OActN.pullback {O : Type} [Ring O] (A : Over S) [GrpObj A] (a : GlobalTheory.UPel.HT.OActN O A) :
    GlobalTheory.UPel.HT.OActN O ((Over.pullback f).obj A) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

theorem OActN.pullback_left {O : Type} [Ring O] (A : Over S) [GrpObj A] (a : GlobalTheory.UPel.HT.OActN O A) (c : O) :
    ((OActN.pullback f A a).act c).left ≫ pullback.fst A.hom f = pullback.fst A.hom f ≫ (a.act c).left :=
  pullback.lift_fst _ _ _

end Act

section Sq

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

def sqMap (w : φ ≫ A.hom = A'.hom ≫ f) : (G2 A').left ⟶ (G2 A).left :=
  (lift (pushPt w (fst A' A')) (pushPt w (snd A' A'))).left

theorem pushPt_left (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} (x : T ⟶ A') : (pushPt w x).left = x.left ≫ φ := rfl

theorem pushPt_comp (w : φ ≫ A.hom = A'.hom ≫ f) {T U : Over S'} (g : T ⟶ U) (x : U ⟶ A') :
    pushPt w (g ≫ x) = (Over.homMk g.left (by
      show g.left ≫ U.hom ≫ f = T.hom ≫ f
      rw [← Category.assoc, Over.w g]) : Over.mk (T.hom ≫ f) ⟶ Over.mk (U.hom ≫ f)) ≫ pushPt w x :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

theorem lift_sqMap (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} (a b : T ⟶ A') :
    (lift a b).left ≫ sqMap w = (lift (pushPt w a) (pushPt w b)).left := by
  have e := pushPt_comp w (lift a b) (fst A' A')
  have e' := pushPt_comp w (lift a b) (snd A' A')
  rw [lift_fst] at e
  rw [lift_snd] at e'
  rw [e, e', ← comp_lift]
  rfl

theorem isSquare_sqMap (w : φ ≫ A.hom = A'.hom ≫ f) : IsSquare φ (sqMap w) := by
  constructor
  · show (lift (pushPt w (fst A' A')) (pushPt w (snd A' A')) ≫ fst A A).left = _
    rw [lift_fst]; rfl
  · show (lift (pushPt w (fst A' A')) (pushPt w (snd A' A')) ≫ snd A A).left = _
    rw [lift_snd]; rfl

end Sq

section Tate

variable {p : ℕ} [Fact p.Prime]

def tateMoveO {D : GlobalTheory.UPel.HT.Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) : GlobalTheory.UPel.HT.TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem tateMoveO_ev {D : GlobalTheory.UPel.HT.Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (n : ℕ) (a : D.La) :
    (tateMoveO Φ hact he I).ev n a = Φ.symm (I.ev n a) := rfl

end Tate

section Pts

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem sqMap_of (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} {T₀ : Over S} (u : Over.mk (T.hom ≫ f) ⟶ T₀)
    (a' b' : T ⟶ A') (a b : T₀ ⟶ A) (ha : pushPt w a' = u ≫ a) (hb : pushPt w b' = u ≫ b) :
    (lift a' b').left ≫ sqMap w = u.left ≫ (lift a b).left := by
  rw [lift_sqMap, ha, hb, ← comp_lift]
  rfl

end Pts

end GlobalTheory.UPel.HT.Pull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubbundleKernelOfLocallyPrincipal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.VB

theorem isFrame_of_epi_mono_principal {Y : Scheme.{0}} [IsIntegral Y] {E M L : Y.Modules}
    [E.IsQuasicoherent] [M.IsQuasicoherent] (π : E ⟶ M) (m : M ⟶ L) [Epi π] [Mono m]
    {V : Y.Opens} {l : Fin 1 → Γ(L, V)} {g : Γ(Y, V)} {t : Γ(E, V)} (hl : IsFrame l) (hg : g ≠ 0)
    (ht : (π ≫ m).app V t = g • l 0)
    (hs : ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ(E, W)), ∃ a : Γ(Y, W),
      (π ≫ m).app W s = a • resM L h (g • l 0)) :
    IsFrame (fun _ : Fin 1 => π.app V t) := by
  have hc (W : Y.Opens) (s : Γ(E, W)) : (π ≫ m).app W s = m.app W (π.app W s) := rfl
  refine isFrame_of_forall_exists fun V' h x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := QCoh.exists_affine_mem_le x hx
  refine ⟨W, hle, hxW, ?_⟩
  have hWV : W ≤ V := hle.trans h
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hm (a : Fin 1 → Γ(Y, W)) :
      m.app W (Fintype.linearCombination Γ(Y, W) (fun _ : Fin 1 => resM M hWV (π.app V t)) a) =
        a 0 • resM L hWV (g • l 0) := by
    rw [Fintype.linearCombination_apply, Fin.sum_univ_one, Scheme.Modules.Hom.app_smul, app_resM,
      ← hc, ht]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h1 := hm a
    rw [ha, map_zero, resM_smul, smul_smul] at h1
    have h2 := (hl W hWV).1 (a₁ := fun _ => a 0 * resG Y hWV g) (a₂ := 0) (by
      rw [map_zero, Fintype.linearCombination_apply, Fin.sum_univ_one]
      exact h1.symm)
    have h3 : a 0 * resG Y hWV g = 0 := congrFun h2 0
    have h4 : resG Y hWV g ≠ 0 := fun h0 =>
      hg (map_injective_of_isIntegral Y (homOfLE hWV) (h0.trans (map_zero _).symm))
    funext i
    rw [Subsingleton.elim i 0]
    exact (mul_eq_zero.1 h3).resolve_right h4
  · intro s
    obtain ⟨u, rfl⟩ := QCoh.surjective_app_of_epi π hW s
    obtain ⟨a, ha⟩ := hs W hWV u
    refine ⟨fun _ => a, QCoh.injective_app_of_mono m W ?_⟩
    rw [hm, ← hc, ha]

theorem isSubbundle_kernel_of_locally_principal :
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (E L : Y.Modules) (ψ : E ⟶ L) (n : ℕ), IsVB E (n + 1) →
      IsVB L 1 → (∀ y : Y, ∃ (V : Y.Opens) (l : Fin 1 → Γ(L, V)) (g : Γ(Y, V)) (t : Γ(E, V)),
        y ∈ V ∧ IsFrame l ∧ g ≠ 0 ∧ (ψ).app V t = g • l 0 ∧
        ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ(E, W)), ∃ a : Γ(Y, W),
          (ψ).app W s = a • GlobalTheory.Twist.resM (L) h (g • l 0)) →
      IsSubbundle (Limits.kernel.ι ψ) ∧ IsVB (Limits.kernel ψ) n := by
  intro Y _ E L ψ n hE hL H
  have := hE.isQuasicoherent
  have := hL.isQuasicoherent
  have hM : IsVB (cokernel (kernel.ι ψ)) 1 := by
    intro y
    obtain ⟨V, l, g, t, hy, hl, hg, ht, hs⟩ := H y
    have e : cokernel.π (kernel.ι ψ) ≫ Abelian.factorThruCoimage ψ = ψ := Abelian.coimage.fac ψ
    exact ⟨V, _, hy, isFrame_of_epi_mono_principal (cokernel.π (kernel.ι ψ))
      (Abelian.factorThruCoimage ψ) hl hg (by rw [e]; exact ht) (by rw [e]; exact hs)⟩
  refine ⟨⟨inferInstance, 1, hM⟩, ?_⟩
  have hS : (ShortComplex.mk _ _ (cokernel.condition (kernel.ι ψ))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact isVB_X₁_of_shortExact Y _ n 1 hS hE hM

end GlobalTheory.VB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorLatticeLocalStatement
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_vector_lattice_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  first | exact @GlobalTheory.InertIwasawaUnram.main | exact GlobalTheory.InertIwasawaUnram.main | (intros; apply GlobalTheory.InertIwasawaUnram.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOrbitalIntegralCongruenceInertLatticeCountStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaOrbitalIntegral_congruence_inert_latticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (n a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), a + b = n → Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → (1 + algebraMap K.O B₁.A t * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A t * B₁.g) = 1 → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (1 + algebraMap K.O B₂.A t * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A t * B₂.g) = 1 → kapOrb n w Q₁ Q₂ ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) = ((GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ : ℚ) : ℂ) := by
  first | exact @GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum | exact GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum | (intros; apply GlobalTheory.KapLat.kapOrb_congruence_eq_kapSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.kTriv_rigTransl_any | exact GlobalTheory.RigidTranslate.kTriv_rigTransl_any | (intros; apply GlobalTheory.RigidTranslate.kTriv_rigTransl_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormCutoffLogWeightLowerBoundStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviForm_cutoffLogWeight_lower_bound : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → (∀ t, |deriv (deriv χ) t| ≤ A) → ∀ (n : ℕ) (ρ δ : ℝ), 0 < ρ → 0 < δ → δ ≤ 1 → ∀ (z : V n) (ξ : Fin n → ℂ), -((13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) ≤ (leviV n (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ)) z ξ).re := by
  first | exact @GlobalTheory.PeakWeightLevi.levi_cutLog_lower | exact GlobalTheory.PeakWeightLevi.levi_cutLog_lower | (intros; apply GlobalTheory.PeakWeightLevi.levi_cutLog_lower <;> assumption)
end

