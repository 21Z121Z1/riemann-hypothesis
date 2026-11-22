import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatInPadicIntegersOfTwistedDifferenceStatement
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRatInPadicIntegers_of_twisted_difference : ∀ {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime] (g : G) (q : ℕ), l ∣ q →
    ∀ x : G → ℚ, (∀ C, InZl l (x C - (q : ℚ) * x (C * g))) → ∀ C, InZl l (x C) := by
  first | exact @GlobalTheory.inZl_of_twisted_difference | exact GlobalTheory.inZl_of_twisted_difference | (intros; apply GlobalTheory.inZl_of_twisted_difference <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieAway

section Basic

variable {R : Type} [CommRing R]

theorem scaleS_toRingHom (c : R) : (Chart.scaleS (S := R) c).toRingHom = epsScaleR c := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [Chart.scaleS_fst, epsScaleR]
  · simp [Chart.scaleS_snd, epsScaleR]

variable {G : Over (Sp R)} [GrpObj G]

theorem tanS_of_isTangent {v : epsR R ⟶ G} (h : IsTangent v) : Chart.TanS (S := R) (A := R) v :=
  (Chart.isTan_iff v).mpr h

theorem isTangent_of_tanS {v : epsR R ⟶ G} (h : Chart.TanS (S := R) (A := R) v) : IsTangent v :=
  (Chart.isTan_iff v).mp h

theorem isTangent_iff_tanS (r : R) (y : epsR (Localization.Away r) ⟶ Chart.Gs G r) :
    IsTangent y ↔ Chart.TanS (Chart.pushR G y) := by
  rw [← Chart.isTan_iff]
  constructor
  · intro h
    have := congrArg (Chart.pushR G) h
    rw [Chart.pushR_spMap, Chart.pushR_one] at this
    exact this
  · intro h
    apply Chart.pushR_inj G
    rw [Chart.pushR_spMap, Chart.pushR_one]
    exact h

theorem scale_left (c : R) (v : epsR R ⟶ G) :
    Geo.Tor.spMap (epsScaleR c) ≫ v.left = (Chart.spMap (Chart.scaleS (S := R) c) ≫ v).left := by
  rw [Over.comp_left, Chart.spMap_left, ← scaleS_toRingHom]

end Basic

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

section Res

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (r : R)

def resA (v : epsR R ⟶ G) : epsR (Localization.Away r) ⟶ Chart.Gs G r :=
  Chart.pullR G (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v)

theorem pushR_resA (v : epsR R ⟶ G) :
    Chart.pushR G (resA r v) = Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v :=
  Chart.pushR_pullR G _

variable {O O' : Type} [CommRing O] [CommRing O'] [IsCommMonObj G] (a : OAct O G)
  (a' : OAct O' (Chart.Gs G r))

def resL (v : GlobalTheory.Serre.Lie a) : GlobalTheory.Serre.Lie a' :=
  GlobalTheory.Serre.Lie.mk a' (resA r v.hom) (by
    rw [isTangent_iff_tanS, pushR_resA]
    exact Chart.tanS_restrict _ (tanS_of_isTangent v.isTangent))

theorem pushR_resL (v : GlobalTheory.Serre.Lie a) :
    Chart.pushR G (resL r a a' v).hom = Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v.hom :=
  pushR_resA r v.hom

theorem pushR_smul (c : Localization.Away r) (y : GlobalTheory.Serre.Lie a') :
    Chart.pushR G (c • y).hom = Chart.spMap (Chart.scaleS (S := R) c) ≫ Chart.pushR G y.hom := by
  have e : (c • y).hom = Chart.spMap (Chart.scaleS (S := Localization.Away r) c) ≫ y.hom :=
    Over.OverMorphism.ext ((GlobalTheory.Serre.Lie.hom_smul_left c y).trans (scale_left c y.hom))
  rw [e, Chart.pushR_spMap]
  rfl

theorem hom_smul_eq (c : R) (v : GlobalTheory.Serre.Lie a) :
    (c • v).hom = Chart.spMap (Chart.scaleS (S := R) c) ≫ v.hom :=
  Over.OverMorphism.ext ((GlobalTheory.Serre.Lie.hom_smul_left c v).trans (scale_left c v.hom))

theorem pushR_add (y z : GlobalTheory.Serre.Lie a') :
    Chart.pushR G (y + z).hom = Chart.pushR G y.hom * Chart.pushR G z.hom :=
  map_mul (Chart.pushforwardHom G) y.hom z.hom

theorem resL_add (v w : GlobalTheory.Serre.Lie a) : resL r a a' (v + w) = resL r a a' v + resL r a a' w := by
  ext1
  apply Chart.pushR_inj G
  rw [pushR_add, pushR_resL, pushR_resL, pushR_resL, GlobalTheory.Serre.Lie.hom_add, MonObj.comp_mul]

theorem resL_smul (c : R) (v : GlobalTheory.Serre.Lie a) :
    resL r a a' (c • v) = algebraMap R (Localization.Away r) c • resL r a a' v := by
  ext1
  apply Chart.pushR_inj G
  rw [pushR_smul, pushR_resL, pushR_resL, hom_smul_eq, Chart.res_scale]
  rfl

end Res

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

section Cover

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [∀ s : R, Smooth (Chart.Gs G s).hom]

theorem tan_away_uniq (r : R) {w : Chart.sp (R₀ := R) (DualNumber R) ⟶ G} (hw : Chart.TanS w)
    (h1 : Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ w = 1) :
    ∃ N : ℕ, Chart.spMap (Chart.scaleS (S := R) (r ^ N)) ≫ w = 1 := by
  classical
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover G
  have C : ∀ k, Chart.Chart (Chart.Gs G (s k)) := fun k => (hC k).some
  have hwk : ∀ k, Chart.TanS (Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away (s k)))) ≫ w) :=
    fun k => Chart.tanS_restrict _ hw
  have hone : ∀ (A : Type) [CommRing A] [Algebra R A], Chart.TanS (1 : Chart.sp (R₀ := R) (DualNumber A) ⟶ G) :=
    fun A _ _ => Chart.comp_one' _
  have h2 : ∀ k, ∃ N : ℕ, Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away (s k)) r ^ N)) ≫
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away (s k)))) ≫ w =
      Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away (s k)) r ^ N)) ≫ 1 := by
    intro k
    apply Chart.tanS_away_uniq (C k) (A := Localization.Away (s k)) r (hwk k) (hone _)
    have hu : IsUnit (algebraMap R (Localization.Away (algebraMap R (Localization.Away (s k)) r)) r) :=
      Chart.isUnit_qv (s k) r
    rw [Chart.comp_one', Chart.res_res,
      show (IsScalarTower.toAlgHom R (Localization.Away (s k))
          (Localization.Away (algebraMap R (Localization.Away (s k)) r))).comp
          (Algebra.ofId R (Localization.Away (s k))) =
        (Chart.awayHom r _ hu).comp (Algebra.ofId R (Localization.Away r)) from Chart.ofId_ext _ _,
      ← Chart.res_res, h1, Chart.comp_one']
  choose N hN using h2
  refine ⟨Finset.univ.sup N, Chart.tan_ext_cover s hs fun k => ?_⟩
  rw [Chart.comp_one', Chart.res_scale, Algebra.ofId_apply, map_pow,
    Chart.scale_pow_mono _ (Finset.le_sup (f := N) (Finset.mem_univ k)) (hN k), Chart.comp_one']

theorem tan_away_lift (r : R) (hr : Nonempty (Chart.Chart (Chart.Gs G r)))
    {y : Chart.sp (R₀ := R) (DualNumber (Localization.Away r)) ⟶ G} (hy : Chart.TanS y) :
    ∃ N : ℕ, ∃ w : Chart.sp (R₀ := R) (DualNumber R) ⟶ G, Chart.TanS w ∧
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ w =
        Chart.spMap (Chart.scaleS (S := R) (algebraMap R (Localization.Away r) r ^ N)) ≫ y := by
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover G
  let s' : Fin (n + 1) → R := Fin.cons r s
  have hs' : Ideal.span (Set.range s') = ⊤ := by
    rw [eq_top_iff, ← hs]
    apply Ideal.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨k.succ, Fin.cons_succ _ _ _⟩
  have C : ∀ k, Chart.Chart (Chart.Gs G (s' k)) := Fin.cases hr.some (fun k => (hC k).some)
  exact Chart.tan_extend s' hs' C 0 hy

end Cover

end GlobalTheory.LieAway

namespace GlobalTheory.LieAway

theorem lie_away {R O O' : Type} [CommRing R] [CommRing O] [CommRing O'] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (a : OAct O G) (r : R) (a' : OAct O' (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) :
    Nonempty (ReciprocityTheory.ChartRestriction.G.Chart.Chart (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) →
    Nonempty (LocalizedModule (Submonoid.powers r) (GlobalTheory.Serre.Lie a) ≃ₗ[Localization.Away r] GlobalTheory.Serre.Lie a') := by
  intro hr
  have : ∀ s : R, Smooth (Chart.Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  letI : Module R (GlobalTheory.Serre.Lie a') := Module.compHom _ (algebraMap R (Localization.Away r))
  haveI : IsScalarTower R (Localization.Away r) (GlobalTheory.Serre.Lie a') :=
    ⟨fun x y z => by rw [Algebra.smul_def]; exact mul_smul _ y z⟩
  let ρ : GlobalTheory.Serre.Lie a →ₗ[R] GlobalTheory.Serre.Lie a' :=
    { toFun := resL r a a'
      map_add' := resL_add r a a'
      map_smul' := resL_smul r a a' }
  have hρ : ∀ v, Chart.pushR G (ρ v).hom =
      Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ v.hom := pushR_resL r a a'
  haveI : IsLocalizedModule (Submonoid.powers r) ρ := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · rw [Module.End.isUnit_iff]
      obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.Away r) x
      have hx : ∀ m : GlobalTheory.Serre.Lie a',
          (algebraMap R (Module.End R (GlobalTheory.Serre.Lie a')) x) m = (u : Localization.Away r) • m := fun m => by
        rw [Module.algebraMap_end_apply, hu]; rfl
      refine ⟨fun m₁ m₂ e => ?_, fun m => ⟨(↑u⁻¹ : Localization.Away r) • m, ?_⟩⟩
      · rw [hx, hx] at e
        have := congrArg (fun z => (↑u⁻¹ : Localization.Away r) • z) e
        simp only [smul_smul, Units.inv_mul, one_smul] at this
        exact this
      · rw [hx, smul_smul, Units.mul_inv, one_smul]
    · have hy : Chart.TanS (Chart.pushR G y.hom) := (isTangent_iff_tanS r y.hom).mp y.isTangent
      obtain ⟨N, w, hw, he⟩ := tan_away_lift r hr hy
      refine ⟨(GlobalTheory.Serre.Lie.mk a w (isTangent_of_tanS hw), ⟨r ^ N, N, rfl⟩), ?_⟩
      ext1
      apply Chart.pushR_inj G
      rw [hρ, GlobalTheory.Serre.Lie.hom_mk, he]
      change Chart.pushR G ((algebraMap R (Localization.Away r) (r ^ N)) • y).hom = _
      rw [pushR_smul, map_pow]
    · have h0 : ρ (x₁ - x₂) = 0 := by rw [map_sub, h, sub_self]
      have h1 : Chart.spMap (Chart.dualMapS (Algebra.ofId R (Localization.Away r))) ≫ (x₁ - x₂).hom = 1 := by
        rw [← hρ, h0, GlobalTheory.Serre.Lie.hom_zero, Chart.pushR_one]
      obtain ⟨N, hN⟩ := tan_away_uniq r (tanS_of_isTangent (x₁ - x₂).isTangent) h1
      refine ⟨⟨r ^ N, N, rfl⟩, ?_⟩
      rw [← sub_eq_zero, ← smul_sub]
      ext1
      rw [Submonoid.smul_def, hom_smul_eq, hN, GlobalTheory.Serre.Lie.hom_zero]
  exact ⟨(IsLocalizedModule.iso (Submonoid.powers r) ρ).extendScalarsOfIsLocalization (Submonoid.powers r)
    (Localization.Away r)⟩

end GlobalTheory.LieAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

theorem isTest_pullback : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (T T' : Scheme.{0}) (t : T ⟶ Sp Rg) (h : T' ⟶ T) (A₁ B₁ : Over T) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → ∃ (A₂ : Over T') (_ : GrpObj A₂) (B₂ : Over T') (_ : GrpObj B₂) (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂), IsTest A B L M (h ≫ t) A₂ B₂ φA₂ φB₂ Φ₂ ∧ IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h := by
  intro Rg _ A B _ _ L M T T' t h A₁ B₁ _ _ φA₁ φB₁ Φ₁ hT
  obtain ⟨hA, hB, hm, hl⟩ := hT
  haveI : IsMonHom Φ₁ := hm
  have eΦ : ((Over.pullback h).map Φ₁).left ≫ pullback.fst B₁.hom h = pullback.fst A₁.hom h ≫ Φ₁.left :=
    pullback.lift_fst _ _ _
  have gA := isGrpPullback_pullback A₁ h
  have gB := isGrpPullback_pullback B₁ h
  refine ⟨(Over.pullback h).obj A₁, inferInstance, (Over.pullback h).obj B₁, inferInstance,
    pullback.fst A₁.hom h ≫ φA₁, pullback.fst B₁.hom h ≫ φB₁, (Over.pullback h).map Φ₁,
    ⟨gA.comp hA, gB.comp hB, PullGtPf.isMonHom_of_grpPullback gA gB Φ₁ _ eΦ, ?_⟩,
    pullback.fst A₁.hom h, pullback.fst B₁.hom h, gA, gB, rfl, rfl, eΦ⟩
  exact LBIso.chartPull
    (chartPullSame L (fun _ => pullback.fst A₁.hom h ≫ φA₁) (fun _ => φA₁) (fun _ => 1) (pullback.fst A₁.hom h)
      (fun _ => rfl))
    (HomFixGlue.chartPullPullPull M _ _ _ _ (pullback.fst A₁.hom h)
      (by rw [← Category.assoc, eΦ, Category.assoc])) hl

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerIdealFinrankEqPowOfIdempotent
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem natSeq_pow_of_mul_eq {p h : ℕ} (hp : p.Prime) (a b : ℕ → ℕ)
    (hab : ∀ n, a n * b n = p ^ (n * h))
    (ha : ∀ n, a (n + 1) ≤ a 1 * a n) (hb : ∀ n, b (n + 1) ≤ b 1 * b n) :
    ∃ s : ℕ, ∀ n, a n = p ^ (n * s) := by
  have h1 : a 1 * b 1 = p ^ h := by simpa using hab 1
  obtain ⟨s, hs, hs'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ h1)
  obtain ⟨t, ht, ht'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ h1)
  have h0 : a 0 * b 0 = 1 := by simpa using hab 0
  have ha0 : a 0 = 1 := Nat.eq_one_of_mul_eq_one_right h0
  have hb0 : b 0 = 1 := Nat.eq_one_of_mul_eq_one_left h0
  have hst : s + t = h := by
    rw [hs', ht', ← pow_add] at h1
    exact Nat.pow_right_injective hp.two_le h1
  have hale : ∀ n, a n ≤ p ^ (n * s) := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      calc a (n + 1) ≤ a 1 * a n := ha n
        _ ≤ p ^ s * p ^ (n * s) := by rw [hs']; exact Nat.mul_le_mul_left _ ih
        _ = p ^ ((n + 1) * s) := by rw [← pow_add]; ring_nf
  have hble : ∀ n, b n ≤ p ^ (n * t) := by
    intro n
    induction n with
    | zero => simp [hb0]
    | succ n ih =>
      calc b (n + 1) ≤ b 1 * b n := hb n
        _ ≤ p ^ t * p ^ (n * t) := by rw [ht']; exact Nat.mul_le_mul_left _ ih
        _ = p ^ ((n + 1) * t) := by rw [← pow_add]; ring_nf
  refine ⟨s, fun n => ?_⟩
  by_contra hne
  have hlt : a n < p ^ (n * s) := lt_of_le_of_ne (hale n) hne
  have hpos : 0 < p ^ (n * t) := pow_pos hp.pos _
  have key : a n * b n < p ^ (n * s) * p ^ (n * t) :=
    calc a n * b n ≤ a n * p ^ (n * t) := Nat.mul_le_mul_left _ (hble n)
      _ < p ^ (n * s) * p ^ (n * t) := Nat.mul_lt_mul_of_pos_right hlt hpos
  rw [hab n, ← pow_add, ← Nat.mul_add, hst] at key
  exact lt_irrefl _ key

theorem kerIdeal_finrank_eq_pow_of_idempotent : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 →
    ∃ h₀ : ℕ, ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) = p ^ (n * h₀) := by
  intro p _ k _ G u v huv h1 h2
  exact natSeq_pow_of_mul_eq (Fact.out : p.Prime)
    (fun n => Module.finrank k (G.A n ⧸ kerIdeal (u.app n)))
    (fun n => Module.finrank k (G.A n ⧸ kerIdeal (v.app n)))
    (GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents p k G u v huv h1 h2)
    (GlobalTheory.T.finrank_kernelIdeal_succ_le_mul_levels p k G u) (GlobalTheory.T.finrank_kernelIdeal_succ_le_mul_levels p k G v)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensorStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B) (m N : ℕ), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → (∀ f, evA f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, evB f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∀ f, E f = 0 → ∀ α : σ ⊕ τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  first | exact @GlobalTheory.KerTensor.ker_tensor | exact GlobalTheory.KerTensor.ker_tensor | (intros; apply GlobalTheory.KerTensor.ker_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeISupOfUniformisationParametersCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem le_iSup_of_pre_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  intro A _ g L u hA U K W h x hx
  obtain ⟨-, -, -, -, hinf, hmono, hsup, -, -, -, hbasic, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
  have hV' : IsAffineOpen V := hV
  let p : Ideal Γ(A.left, V) :=
    (IsLocalRing.maximalIdeal (A.left.presheaf.stalk x)).comap (A.left.presheaf.germ V x hxV).hom
  have hp : p ≠ ⊤ := Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp
  obtain ⟨z, hzV, hz⟩ := GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint A g L u hA V hV' m hm
  obtain ⟨i, hi⟩ := h z (hmono U V hVU hzV)
  have hzi : z ∈ pre u.ex (W i ⊓ V) := by rw [hinf]; exact ⟨hi, hzV⟩
  have hle : W i ⊓ V ≤ ⨆ b : {b : Γ(A.left, V) // A.left.basicOpen b ≤ W i}, A.left.basicOpen b.1 := by
    intro y hy
    obtain ⟨f, hf, hyf⟩ := hV'.exists_basicOpen_le (V := W i) ⟨y, hy.1⟩ hy.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨⟨b, hb⟩, hzb⟩ := (hsup _ _ z).mp (hmono _ _ hle hzi)
  have hbm : b ∉ m := fun hh ↦ (hbasic V b z).mp hzb ((hz b).mp hh)
  have hxb : x ∈ A.left.basicOpen b := by
    rw [Scheme.mem_basicOpen _ b x hxV]
    by_contra hn
    exact hbm (hpm (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn)))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hb hxb⟩

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAtlasMeasureEtalePullbackLebesgueStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_atlasMeasure_etale_pullback_lebesgue : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ≥0∞, Measurable φ → ∫⁻ y in U, φ y ∂A.mu = ∫⁻ x : U, φ x * ENNReal.ofReal (A.nsq A.kap (jdet A z) x)⁻¹ ∂vol n (fun y : U => z y) := by
  first | exact @GlobalTheory.EtaleMeasure.lintegral_mu_etale | exact GlobalTheory.EtaleMeasure.lintegral_mu_etale | (intros; apply GlobalTheory.EtaleMeasure.lintegral_mu_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCocycleCohomologous
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem log_cocycle_cohomologous : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by

  intro I _ g Λ _ F K a lg β ha hdw hsh hlgsh hlgadd e uu ℓ huu hℓ
  have hnil : ∀ T : K.Obj, IsNilDP T.δ := fun T ↦ by letI := T.ratAlg; exact isPDNilpotent_of_rat _ T.nil
  have hdp : ∀ {T T' : K.Obj} (ψ : T ⟶ T'), DividedPowers.IsDPMorphism T.δ T'.δ (ψ.φ : T.C →+* T'.C) := fun {T T'} ψ ↦ by
    letI := T'.ratAlg; exact isDPMorphism_of_rat T.δ T'.δ (ψ.φ : T.C →+* T'.C) ψ.mem
  have hw : ∀ (T T' : K.Obj) (φ : T ⟶ T'), ∃ n ∈ T'.J, dpExp T'.δ n =
      uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) := by
    intro T T' φ
    have hm : uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) * (((e T')⁻¹ : (T'.C)ˣ) : T'.C) - 1 ∈ T'.J := by
      have := T'.J.mul_mem_right (((e T')⁻¹ : (T'.C)ˣ) : T'.C) (huu T T' φ)
      convert this using 1
      rw [sub_mul, Units.mul_inv]
    obtain ⟨x, hx, hx'⟩ := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T'.C T'.J T'.δ (hnil T')).surjOn hm
    exact ⟨x, hx, hx'⟩
  choose n hnJ hn using hw
  refine ⟨fun T T' φ ↦ (n T T' φ - T'.ρ (lg φ.deg T'.k) : T'.C), ?_⟩
  intro T T' T'' φ ψ
  obtain ⟨hℓJ, hℓe⟩ := hℓ T T' T'' φ ψ
  have hce := close_exp T''.J T''.δ (hnil T'') _ _ (a φ.deg T'.k) (lg φ.deg T'.k) (hdw φ.deg T'.k) ψ.close
  have hxJ := ψ.close.sub_mem (lg φ.deg T'.k)
  simp only [RingHom.comp_apply, AlgHom.coe_toRingHom] at hce hxJ
  have hnat : ∀ c ∈ T'.J, ψ.φ (dpExp T'.δ c) = dpExp T''.δ (ψ.φ c) := fun c hc ↦
    (dpExp_add_and_natural _ _ _ _ T'.δ T''.δ (hnil T')).2 _ (hdp ψ) c hc
  have hadd := (dpExp_add_and_natural _ _ _ _ T''.δ T''.δ (hnil T'')).1
  have hQ : ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * ψ.φ (e T' : T'.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have haa : T''.ρ (a (φ ≫ ψ).deg T''.k) = T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) := by
    rw [Charts.comp_deg, hsh _ _ _ _ (Charts.Hom.le ψ), map_mul]
  have hn1 := hn T T'' (φ ≫ ψ)
  have hn2 := hn T T' φ
  have hn3 := hn T' T'' ψ
  rw [Charts.comp_φ, haa] at hn1
  set x := ψ.φ (T'.ρ (lg φ.deg T'.k)) - T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) with hx
  have key : dpExp T''.δ (ℓ T T' T'' φ ψ + n T T'' (φ ≫ ψ) + x) = dpExp T''.δ (ψ.φ (n T T' φ) + n T' T'' ψ) := by
    rw [hadd _ (T''.J.add_mem hℓJ (hnJ _ _ _)) _ hxJ, hadd _ hℓJ _ (hnJ _ _ _),
      hadd _ (ψ.mem _ (hnJ _ _ _)) _ (hnJ _ _ _), ← hnat _ (hnJ _ _ _), hn1, hn2, hn3]
    simp only [map_mul]
    linear_combination (ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) * T''.ρ (a ψ.deg T''.k) *
        (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hℓe
      - (ψ.φ (uu T T' φ) * ψ.φ (φ.φ (e T : T.C)) * ψ.φ (((e T')⁻¹ : (T'.C)ˣ) : T'.C) * uu T' T'' ψ * ψ.φ (e T' : T'.C) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C)) * hce
      - (ψ.φ (uu T T' φ) * uu T' T'' ψ * ψ.φ (φ.φ (e T : T.C)) * T''.ρ (Charts.sh (Charts.Hom.le ψ) (a φ.deg T'.k)) *
        T''.ρ (a ψ.deg T''.k) * (((e T'')⁻¹ : (T''.C)ˣ) : T''.C) * dpExp T''.δ x) * hQ
  have hinj := (GlobalTheory.Cris.ExpBij.dpExp_bijOn T''.C T''.J T''.δ (hnil T'')).injOn
    (T''.J.add_mem (T''.J.add_mem hℓJ (hnJ _ _ _)) hxJ) (T''.J.add_mem (ψ.mem _ (hnJ _ _ _)) (hnJ _ _ _)) key
  have hb : T''.ρ (Charts.sh (Charts.Hom.le ψ) (lg φ.deg T'.k)) = T''.ρ (lg φ.deg T''.k) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by
    rw [hlgsh _ _ _ _ (Charts.Hom.le ψ), map_add, T''.ρ_cst]
  show ℓ T T' T'' φ ψ = (ψ.φ (n T T' φ - T'.ρ (lg φ.deg T'.k)) - (n T T'' (φ ≫ ψ) - T''.ρ (lg (φ ≫ ψ).deg T''.k)) +
    (n T' T'' ψ - T''.ρ (lg ψ.deg T''.k))) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)
  rw [Charts.comp_deg, hlgadd, map_sub, map_add]
  rw [hx, hb] at hinj
  linear_combination hinj

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinPadicValPowSubOneCoprimeEqClosedFormulaStatement
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minPadicValPowSubOneCoprime_eq_closedFormula : Formalism.PairingDivisionLocalBalance.MinVal → ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n → mMin l n = Formalism.PairingDivisionLocalBalance.mE l n := by
  first | exact @GlobalTheory.MinValClosed.mMin_eq_mE | exact GlobalTheory.MinValClosed.mMin_eq_mE | (intros; apply GlobalTheory.MinValClosed.mMin_eq_mE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObstructionClassNaturalStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.obstructionClass_natural : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → ∀ (x : HO1 s') (z : HO2 s₀) (z' : HO2 q₀), Bock h.w h₀.w t x z → Bock k.w k₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
  first | exact @GlobalTheory.AbCoh.bock_natural | exact GlobalTheory.AbCoh.bock_natural | (intros; apply GlobalTheory.AbCoh.bock_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmEFormAndDegree
section
noncomputable section
namespace GlobalTheory.FockOm
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem omE_form_and_degree : ∀ (p q r s : ℕ) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → (linePos l = linePos l' → omE l l' P ∈ homog (Ix p q × Ix r s) d) ∧ (linePos l = true → linePos l' = false → omE l l' P = X l * X l' * P) ∧ (linePos l = false → linePos l' = true → omE l l' P = - pderiv l (pderiv l' P)) := by
  intro p q r s l l' d P hP
  refine ⟨fun h => GlobalTheory.FockDeg.omE_mem_homog h hP, fun hl hl' => ?_, fun hl hl' => ?_⟩
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne, mul_assoc]
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne]

end GlobalTheory.FockOm
end
end

