import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorExtendsHyperbolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePointOfNonvanishingCoords
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mem_blockChart_iff (y : CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) (i : Bk n k) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔
      GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ y ∈
        ptsIn (PSpace.str ℤ (n k)) σ₀ (chart ℤ (n k) i) :=
  Iff.rfl

theorem ev_pullRatio (y : CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) (i j : Bk n k) :
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y =
      CxPts.ev (PSpace.str ℤ (n k)) σ₀ (chart ℤ (n k) i) (ratio ℤ (n k) i j)
        (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ y) := by
  have e : pullRatio (prB n k) (blockChart n k i) i le_rfl j = (prB n k).app (chart ℤ (n k) i) (ratio ℤ (n k) i j) := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  rw [e]
  exact CxPts.ev_app (p := PSpace.str ℤ (n k)) (q := mpStr ℤ m n) (prB n k)
    (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) y

theorem isUnder_ptMP (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    IsUnder (GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z) z ∧ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  have H : IsUnder (multiprojectivePoint c z) z := fun k i => by
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.projective_point_chart_ratio (n k) (c k) (fun i => z ⟨k, i⟩) (hz k)
    have e := map_prB_ptMP c z k
    refine ⟨?_, fun j hy => ?_⟩
    · rw [mem_blockChart_iff, e]
      exact h₁ i
    · rw [ev_pullRatio, e]
      exact h₂ i j (by rw [← e]; exact (mem_blockChart_iff _ k i).1 hy)
  refine ⟨H, CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => ?_)⟩
  exact CxPts.mem_ptsIn.1 ((H k (c k)).1.2 (hz k))

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
section
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField Ad3 Ad3.R
open GroundTheory.Global.RationalSymbol (prime unitAt)
open GroundTheory.Automorphic.GodementSection (adeleAt)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelbergQ

open DirichletHecke
open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

theorem mem_adicCompletionIntegers_of_ord_nonneg (v : Pl) {x : Qv v} (hx : x ≠ 0) (h : 0 ≤ ord x) :
    x ∈ v.adicCompletionIntegers ℚ := by
  have h1 : normalizedValuation (Qv v) x ≤ normalizedValuation (Qv v) 1 := by
    rw [map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 := normalizedValuation_le_iff.1 h1
  rw [map_one] at h2
  exact (mem_valuationInteger_iff v x).1 h2

theorem norm_padicRingEquiv_of_ord_eq_zero (v : Pl) (a : (Qv v)ˣ) (h : ord (a : Qv v) = 0) :
    ‖padicRingEquiv v (a : Qv v)‖ = 1 := by
  refine norm_padicRingEquiv_eq_one ((Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩)
  · exact mem_adicCompletionIntegers_of_ord_nonneg v a.ne_zero h.ge
  · refine mem_adicCompletionIntegers_of_ord_nonneg v (a⁻¹).ne_zero ?_
    rw [ord_units_inv, h]
    simp

theorem ofFinite_mem_positiveSubgroup (e : Afˣ) (h : ∀ v, ord (lf v e : Qv v) = 0) :
    IdeleGroup.ofFinite e ∈ RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w => norm_padicRingEquiv_of_ord_eq_zero w (lf w e) (h w)) ?_
  change 0 < ((RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom
    (IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite e)) : ℝˣ) : ℝ)
  rw [IdeleGroup.toInfinite_ofFinite, map_one, Units.val_one]
  exact one_pos

theorem toZModPow_eq_of_congr {N : ℕ} [NeZero N] (w : Pl) (x : Qv w) (u : ℤ_[prime w]) (n : ℤ)
    (hu : (u : ℚ_[prime w]) = padicRingEquiv w x)
    (hx : ((N : Qv w))⁻¹ * (x - n) ∈ 𝒪[Qv w]) :
    PadicInt.toZModPow (N.factorization (prime w)) u =
      ZMod.castHom (Nat.ordProj_dvd N (prime w)) _ (n : ZMod N) := by
  have hO := (mem_valuationInteger_iff w _).1 hx
  have hn : ‖padicRingEquiv w (((N : Qv w))⁻¹ * (x - n))‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).mapsTo hO)
  let z : ℤ_[prime w] := ⟨_, hn⟩
  have hN : ((N : ℕ) : ℚ_[prime w]) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hz : u = (n : ℤ_[prime w]) + (N : ℤ_[prime w]) * z := by
    apply PadicInt.ext
    have hzc : ((z : ℤ_[prime w]) : ℚ_[prime w]) = ((N : ℚ_[prime w]))⁻¹ * (padicRingEquiv w x - n) := by
      change padicRingEquiv w (((N : Qv w))⁻¹ * (x - n)) = _
      simp only [map_mul, map_inv₀, map_sub, map_natCast, map_intCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, hzc, hu]
    push_cast
    field_simp
    ring
  have h0 : ((N : ℕ) : ZMod (prime w ^ N.factorization (prime w))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.ordProj_dvd N (prime w))
  rw [hz, map_add, map_mul, map_natCast, map_intCast, map_intCast, h0, zero_mul, add_zero]

theorem heckeCharacter_ofFinite_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (d : Afˣ) (n : ℤ)
    (h0 : ∀ v, ord (lf v d : Qv v) = 0)
    (h1 : ∀ v, pOf v ∣ N → ((N : Qv v))⁻¹ * ((lf v d : Qv v) - n) ∈ 𝒪[Qv v]) :
    ((heckeCharacter χ).toIdele (IdeleGroup.ofFinite d) : ℂ) * χ (n : ZMod N) = 1 := by
  have hinv : ∀ v, ord (lf v d⁻¹ : Qv v) = 0 := fun v => by
    have : lf v d⁻¹ = (lf v d)⁻¹ := map_inv (Units.map (adeleAt v).toMonoidHom) d
    rw [this, ord_units_inv, h0 v]
    simp
  let y : RationalIdeles.positiveSubgroup :=
    ⟨IdeleGroup.ofFinite d⁻¹, ofFinite_mem_positiveSubgroup d⁻¹ hinv⟩
  have key : (heckeCharacter χ (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℂ) = χ (n : ZMod N) := by
    refine coe_heckeCharacter_mk_of_forall χ y fun w hw => ?_
    refine toZModPow_eq_of_congr w (lf w d : Qv w) _ n ?_ (h1 w ?_)
    · have hc := coe_unitAt y w
      have hy : (IdeleGroup.finiteProj w (y : IdeleGroup ℚ) : Qv w) = ((lf w d : Qv w))⁻¹ := by
        have : lf w d⁻¹ = (lf w d)⁻¹ := map_inv (Units.map (adeleAt w).toMonoidHom) d
        change ((lf w d⁻¹ : (Qv w)ˣ) : Qv w) = _
        rw [this, Units.val_inv_eq_inv_val]
      have hm : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) *
          ((unitAt y w : ℤ_[prime w]) : ℚ_[prime w]) = 1 := by
        rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
      rw [hc, hy, map_inv₀] at hm
      have hne : padicRingEquiv w (lf w d : Qv w) ≠ 0 := (map_ne_zero _).2 (lf w d).ne_zero
      field_simp at hm
      exact hm
    · rw [show pOf w = prime w from absNorm_asIdeal w]
      exact hw
  rw [← key, HeckeCharacter.toIdele_apply, ← Circle.coe_mul, ← map_mul, ← map_mul, ← map_mul]
  simp [y]

theorem f0 : Ad3.R.B0 → Ad3.R.F0 := fun _ _ _ χ =>
  ⟨heckeCharacter χ, ⟨isOfFinOrder_heckeCharacter χ, fun d n h0 h1 =>
    heckeCharacter_ofFinite_mul χ d n h0 h1⟩⟩

end GlobalTheory.CompanionTheory.RankinSelbergQ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_integer_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx]

omit [MeasurableSpace F] [BorelSpace F] in

theorem inv_mul_mem_of_ord_le {m y : F} (hm : m ≠ 0) (hy : y ≠ 0 → ord m ≤ ord y) :
    m⁻¹ * y ∈ 𝒪[F] := by
  rcases eq_or_ne y 0 with rfl | h0
  · simp
  · have := hy h0
    rw [mem_integer_iff_ord (mul_ne_zero (inv_ne_zero hm) h0), ord_mul (inv_ne_zero hm) h0,
      ord_inv hm]
    omega

omit [MeasurableSpace F] [BorelSpace F] in
theorem le_ord_of_mem {n : ℕ} {y : F} (h0 : y ≠ 0)
    (hc : (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * y ∈ 𝒪[F]) : (n : ℤ) ≤ ord y := by
  have e : ((unifUnit F)⁻¹ ^ n : Fˣ) = unifUnit F ^ (-(n : ℤ)) := by
    rw [inv_pow, _root_.zpow_neg, zpow_natCast]
  have h := (mem_integer_iff_ord (mul_ne_zero (Units.ne_zero _) h0)).1 hc
  rw [ord_mul (Units.ne_zero _) h0, e, ord_unifUnit_zpow] at h
  omega

omit [MeasurableSpace F] [BorelSpace F] in

theorem ord_lower_right {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin 2) F} {d : Fˣ} (h : GammaZeroLevelMembership n x d) :
    ord (d : F) = 0 := by
  obtain ⟨hx, hc, hd⟩ := h
  have hxi := ((GLnLocal.mem_integralGL_iff F 2).1 hx).1
  have hπ : ((unifUnit F : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have h0 : 0 ≤ ord (d : F) := (mem_integer_iff_ord d.ne_zero).1 (hd ▸ hxi 1 1)
  by_contra hne
  have h1 : ord ((unifUnit F : Fˣ) : F) ≤ ord (x 1 1) := by
    rw [ord_unifUnit, ← hd]; omega
  have hd' := inv_mul_mem_of_ord_le hπ (y := x 1 1) fun _ => h1
  have hc' := inv_mul_mem_of_ord_le hπ (y := x 1 0) fun h0 => by
    have := le_ord_of_mem h0 hc
    rw [ord_unifUnit]; omega
  have hdet : ((unifUnit F : Fˣ) : F)⁻¹ * (Matrix.GeneralLinearGroup.det x : F) ∈ 𝒪[F] := by
    have : ((unifUnit F : Fˣ) : F)⁻¹ * (Matrix.GeneralLinearGroup.det x : F) =
        x 0 0 * (((unifUnit F : Fˣ) : F)⁻¹ * x 1 1) -
          x 0 1 * (((unifUnit F : Fˣ) : F)⁻¹ * x 1 0) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      ring
    rw [this]
    exact sub_mem (mul_mem (hxi 0 0) hd') (mul_mem (hxi 0 1) hc')
  have hz : ord (Matrix.GeneralLinearGroup.det x : F) = 0 := GodementSectionLocal.ord_det_eq_zero hx
  have hdn : (Matrix.GeneralLinearGroup.det x : F) ≠ 0 := Units.ne_zero _
  have := (mem_integer_iff_ord (mul_ne_zero (inv_ne_zero hπ) hdn)).1 hdet
  rw [ord_mul (inv_ne_zero hπ) hdn, ord_inv hπ, ord_unifUnit, hz] at this
  omega

end Local

theorem mem_Gamma0Level_of_places (N : ℕ) [NeZero N] (u : AdelicGLn.FiniteAdelicGL ℚ 2)
    (hint : ∀ v : Pl, glAt v u ∈ integralGL (Qv v) 2)
    (hlev : ∀ v : Pl, ((N : Qv v))⁻¹ * glAt v u 1 0 ∈ 𝒪[Qv v]) : u ∈ Gamma0Level N := by
  refine ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall ℚ 2).2 fun v => ?_, ?_⟩
  · have e : (AdelicGLn.finiteRestrictedEquiv ℚ 2 u v : GL (Fin 2) (Qv v)) = glAt v u :=
      Units.ext (Matrix.ext fun a b => rfl)
    rw [e]
    exact hint v
  · rw [GL2Classical.mem_levelIdeal_iff, mem_integralFiniteAdeles]
    intro v
    have hw : adeleAt v ((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) = ((N : Qv v))⁻¹ := by
      have h1 : ((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) * (N : Af) = 1 := by
        rw [← GL2Classical.coe_levelUnit N, Units.inv_mul]
      have h2 := congrArg (adeleAt v) h1
      rw [map_mul, map_natCast, map_one] at h2
      exact eq_inv_of_mul_eq_one_left h2
    have e : (((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) *
        (u : Matrix (Fin 2) (Fin 2) Af) 1 0) v = ((N : Qv v))⁻¹ * glAt v u 1 0 := by
      rw [← hw]
      exact map_mul (adeleAt v) _ _
    rw [e]
    exact (mem_valuationInteger_iff v _).1 (hlev v)

theorem exists_finEmb (h : G2) (hinf : ∀ w, infAt w h = 1) :
    ∃ u : AdelicGLn.FiniteAdelicGL ℚ 2, h = finEmb ℚ 2 u ∧ ∀ v : Pl, glAt v u = finAt v h := by
  refine ⟨(AdelicGLn.prodEquiv ℚ 2 h).2, ?_, fun v => Units.ext (Matrix.ext fun a b => rfl)⟩
  apply (AdelicGLn.prodEquiv ℚ 2).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ rfl
  apply (AdelicGLn.infiniteEquiv ℚ 2).injective
  funext w
  rw [map_one]
  exact hinf w

theorem lift_right {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hL : Lift k N f ω φ) {h : G2} (hinf : ∀ w, infAt w h = 1)
    (hint : ∀ v : Pl, finAt v h ∈ integralGL (Qv v) 2)
    (hlev : ∀ v : Pl, ((N : Qv v))⁻¹ * finAt v h 1 0 ∈ 𝒪[Qv v])
    (D : Afˣ) (hD : ∀ v, ord (lf v D : Qv v) = 0)
    (hD' : ∀ v, pOf v ∣ N → (lf v D : Qv v) = finAt v h 1 1) (g : G2) :
    φ (g * h) = (ω.toIdele (IdeleGroup.ofFinite D) : ℂ) * φ g := by
  obtain ⟨u, rfl, hu⟩ := exists_finEmb h hinf
  refine hL.level u (mem_Gamma0Level_of_places N u (fun v => ?_) fun v => ?_) D hD (fun v hv => ?_) g
  · rw [hu v]; exact hint v
  · rw [hu v]; exact hlev v
  · rw [hu v]; exact hD' v hv

theorem natCast_ne_zero_at (N : ℕ) [NeZero N] (v : Pl) : (N : Qv v) ≠ 0 := by
  have h : (algebraMap ℚ (Qv v)) (N : ℚ) ≠ 0 :=
    (map_ne_zero _).2 (Nat.cast_ne_zero.2 (NeZero.ne N))
  rwa [map_natCast] at h

theorem lf_one (v : Pl) : (lf v (1 : Afˣ) : Qv v) = 1 := by
  simp [lf]

theorem lift_right_good {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ}
    {φ : G2 → ℂ} (hord : ∀ v : Pl, ¬ pOf v ∣ N → ord (N : Qv v) = 0)
    (hL : Lift k N f ω φ) {h : G2} (hinf : ∀ w, infAt w h = 1)
    (hint : ∀ v : Pl, finAt v h ∈ integralGL (Qv v) 2)
    (hbad : ∀ v : Pl, pOf v ∣ N → finAt v h = 1) (g : G2) : φ (g * h) = φ g := by
  have key := lift_right hL hinf hint (fun v => ?_) 1 (fun v => ?_) (fun v hv => ?_) g
  · simpa using key
  · by_cases hv : pOf v ∣ N
    · rw [hbad v hv]; simp
    · refine inv_mul_mem_of_ord_le (natCast_ne_zero_at N v) fun h0 => ?_
      rw [hord v hv]
      exact (mem_integer_iff_ord h0).1 (((GLnLocal.mem_integralGL_iff _ 2).1 (hint v)).1 1 0)
  · rw [lf_one]; exact ord_one
  · rw [lf_one, hbad v hv]; simp

theorem ofFinite_toFinite_of_inf {a' d' : Jd} (h3 : ∀ w, infAt w (dg2 a' d' : G2) = 1) :
    IdeleGroup.ofFinite (IdeleGroup.toFinite ℚ d') = d' := by
  apply (IdeleGroup.prodEquiv ℚ).injective
  refine Prod.ext ?_ ?_
  · have e : (IdeleGroup.prodEquiv ℚ d').1 = 1 := by
      apply Units.ext
      funext w
      have h := congrArg (fun M : GL (Fin 2) _ => M 1 1) (h3 w)
      show (d' : 𝔸[ℚ]).1 w = 1
      simpa [dg2] using h
    rw [e]
    exact IdeleGroup.toInfinite_ofFinite _
  · exact IdeleGroup.toFinite_ofFinite _

theorem lift_local_invariance : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  intro hB k N _ hk χ hχ f a hf he ω φ hω hL
  obtain ⟨hloc, -, -, -, -, -, -, hid⟩ := hB
  have hordN : ∀ v : Pl, ord (N : Qv v) = N.factorization (pOf v) :=
    fun v => (hloc v).2.2.2.2.1 N (NeZero.ne N)
  have hgood : ∀ v : Pl, ¬ pOf v ∣ N → ord (N : Qv v) = 0 := fun v hv => by
    rw [hordN v, Nat.factorization_eq_zero_of_not_dvd hv]; rfl
  refine ⟨fun v hv x hx h hh g => ?_, fun v hv x d hxd h hh g => ?_, fun κ hκ hκ' g => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hh
    refine lift_right_good hgood hL h3 (fun v' => ?_) (fun v' hv' => ?_) g
    · by_cases e : v' = v
      · subst e; rw [h1]; exact hx
      · rw [h2 v' e]; exact one_mem _
    · refine h2 v' fun e => hv (e ▸ hv')
  · obtain ⟨h1, h2, h3⟩ := hh
    have hn : 1 ≤ N.factorization (pOf v) :=
      (hloc v).2.2.1.factorization_pos_of_dvd (NeZero.ne N) hv
    have hu : ord (d : Qv v) = 0 := ord_lower_right hn hxd
    obtain ⟨x', a', d', -, ⟨e1, e2, e3⟩, -, -, hc⟩ := hid v 0 1 d
    have hcomp : ∀ v' : Pl, (lf v' (IdeleGroup.toFinite ℚ d') : Qv v') =
        finAt v' (dg2 a' d' : G2) 1 1 := fun v' => rfl
    have hdv : (lf v (IdeleGroup.toFinite ℚ d') : Qv v) = d := by
      rw [hcomp v, e1]; simp [dg2]
    have hov : ∀ v' : Pl, v' ≠ v → (lf v' (IdeleGroup.toFinite ℚ d') : Qv v') = 1 := fun v' hv' => by
      rw [hcomp v', e2 v' hv']; simp
    have key := lift_right hL h3 (fun v' => ?_) (fun v' => ?_) (IdeleGroup.toFinite ℚ d')
      (fun v' => ?_) (fun v' hv' => ?_) g
    · rw [ofFinite_toFinite_of_inf e3, (hc ω).2] at key
      exact key
    · by_cases e : v' = v
      · subst e; rw [h1]; exact hxd.1
      · rw [h2 v' e]; exact one_mem _
    · by_cases e : v' = v
      · subst e
        rw [h1]
        refine inv_mul_mem_of_ord_le (natCast_ne_zero_at N v') fun h0 => ?_
        rw [hordN v']
        exact le_ord_of_mem h0 hxd.2.1
      · rw [h2 v' e]; simp
    · by_cases e : v' = v
      · subst e; rw [hdv]; exact hu
      · rw [hov v' e]; exact ord_one
    · by_cases e : v' = v
      · subst e; rw [hdv, h1]; exact hxd.2.2
      · rw [hov v' e, h2 v' e]; simp
  · exact lift_right_good hgood hL hκ (fun v' => κ.2.2 v') hκ' g

end GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneDim
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

namespace GlobalTheory.CompanionTheory.RSFT

def oneDim (S : Finset Pl) (g : ∀ v : S, Qv v.1 → ℂ) : Af → ℂ :=
  (awayIntegral S : Set Af).indicator fun x => ∏ v : S, g v (x v.1)

def idl (S : Finset Pl) (N : S → ℤ) : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ :=
  ∏ᶠ w : Pl, primeIdealUnit w ^ (if h : w ∈ S then N ⟨w, h⟩ else 0)

def sup (S : Finset Pl) (a : ∀ v : S, Qv v.1) : Af := ∑ v : S, finiteAdeleSingleAdd v.1 (a v)

def cE {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (N : ℤ) (a : Fin 2 → F) : (Fin 2 → F) → ℂ :=
  localTensor fun i => cosetInd (valBall F N) (a i)

end GlobalTheory.CompanionTheory.RSFT

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairEmbedding
section
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairEmb_of_steps : PairSlices → PairStep₁ → PairStep₂ → PairEmb := by
  intro hS h₁ h₂ E _ _ _ a b ι _ K₁ K₂ W₁ W₂ X₁ Y₁ X₂ Y₂ G hW₁ hW₂ hX₁ hX₂ hE₁ hE₂ hG hGp hGt
  obtain ⟨e₁, he₁Y, he₁i, he₁q⟩ := hE₁
  obtain ⟨e₂, he₂Y, he₂i, he₂q⟩ := hE₂
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hG
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hi
  obtain ⟨hmem, hval⟩ := (hS E a b X₁ X₂ (G i) (hGp i)).1 x.2
  have hφ : sl₁ (G i) x.2 ≠ 0 := by
    intro h0
    apply hx
    have h := congrFun hval x.1
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₁, p₁, t₁, c₁⟩ := h₁ E a b ι K₁ K₂ W₁ W₂ X₁ Y₁ X₂ e₁ G hW₁ hW₂ hX₁ he₁q he₁Y hGp hGt
    ⟨i, x.2, sl₁ (G i) x.2, hval, fun h0 => hφ (he₁i _ hmem h0)⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp n₁
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hj
  obtain ⟨hmem₂, hval₂⟩ := (hS E a b Y₁ X₂ (ap₁ e₁ (G j)) (p₁ j)).2 y.1
  have hψ : sl₂ (ap₁ e₁ (G j)) y.1 ≠ 0 := by
    intro h0
    apply hy
    have h := congrFun hval₂ y.2
    rw [h0] at h
    simpa using h.symm
  obtain ⟨n₂, p₂, t₂, c₂⟩ := h₂ E a b ι K₁ K₂ W₁ W₂ Y₁ X₂ Y₂ e₂ (fun i => ap₁ e₁ (G i)) hW₁ hW₂ hX₂ he₂q he₂Y p₁ t₁
    ⟨j, y.1, sl₂ (ap₁ e₁ (G j)) y.1, hval₂, fun h0 => hψ (he₂i _ hmem₂ h0)⟩
  exact ⟨fun i => ap₂ e₂ (ap₁ e₁ (G i)), n₂, p₂, t₂, fun h c hc => c₂ h c (c₁ h c hc)⟩

end GlobalTheory.CompanionTheory.EGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbitStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_eq_iff_same_torus_orbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder (PtsOver.map i rfl _ y) z → IsUnder (PtsOver.map i rfl _ y') z' → (y = y' ↔ SameOrbit z z') := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit | exact GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitivePointwiseBound
section
noncomputable section

open MeasureTheory Complex
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.SecTorus

def sc (c : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' (Matrix.diagonal ![c, 1])

def rc (c : ℝ) : M22 →ₗ[ℝ] M22 := LinearMap.pi fun i => (sc c).comp (LinearMap.proj i)

end GlobalTheory.CompanionTheory.SecTorus
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorExtendsHyperbolicStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_vector_extends_hyperbolic : ∀ (T : Type) [CommRing T] (O : Subring T) (s : T →+* T), (∀ y ∈ O, s y ∈ O) → (∀ y, s (s y) = y) → IsUnit (2 : O) → (∃ δ : O, IsUnit δ ∧ s δ = -δ) → ∀ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) → ∀ (M : ℕ) (J Ji : Matrix (Fin M) (Fin M) T), (∀ i j, J i j ∈ O) → (∀ i j, Ji i j ∈ O) → J * Ji = 1 → (∀ i j, s (J j i) = J i j) → ∀ x : Fin (M + 2) → O, (∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P) → hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) = 0 → ∃ g ∈ UJ s (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) *ᵥ (e0 T M 0) = (fun i => (x i : T)) ∧ (∀ i j, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O) ∧ ∀ i j, ((g⁻¹ : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionLogNormOnSheetStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_log_norm_on_sheet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.value_of_ne_zero <;> assumption)
end

