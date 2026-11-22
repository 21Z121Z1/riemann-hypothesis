import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3506
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfield
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3530
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3526
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantEqScalarRootMulUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit : ∀ (n : ℕ), n.Prime → Odd n → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (n : V₁) →
  ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen →
  ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th →
  ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K),
    GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd j hj V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, rfl⟩
    omega
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  have hmu : IsUnit ((n ^ j : ℕ) : V₁) := by push_cast; exact hunit.pow j
  obtain ⟨M, lam, hM, H⟩ := GlobalTheory.T.theta_terms_separation_algebraically_closed (n ^ j) (hodd.pow) hm3 V₁ hV hmu D X C e u mo hmo hT K ev ρ₀ hρ₀ th hth
  refine ⟨M, lam, hM, fun y c hc => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant (Sp V₁) D.P ρ₀ hρ₀ (n ^ j) (hodd.pow) _ th y _ hc
  exact H (y ^ n ^ j) τ c (GlobalTheory.USep.isTorsFrame_sq _ D.P ρ₀ (n ^ j) _ (y ^ n ^ j) τ hτ) hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield : ∀ (R : Type) [CommRing R] [IsDomain R]
    (Q : DegPre R) (τ₀ : Gens Q) (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
    ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
      (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
      (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
      IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ →
      w.IsGen →
      (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) →
      ∀ (a b : Q.X) (τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])),
        τ₁.IsGen → ∃ x : k₀ˣ, ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val (τ₀ a b) (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  first | exact @GlobalTheory.UCanon.BaseDescent.main | exact GlobalTheory.UCanon.BaseDescent.main | (intros; apply GlobalTheory.UCanon.BaseDescent.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsValLocalUnitsMulSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a b : D.X, ∃ c ∈ k₀, (val (τ₀ a b) (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (a + b)).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
        (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c b).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c 0).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.fromBase_tau_val | exact GlobalTheory.USep.EvG.fromBase_tau_val | (intros; apply GlobalTheory.USep.EvG.fromBase_tau_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfOrderLeftActionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_order_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → (∀ x : O, x ≠ 0 → ∃ y : O, ∃ c : ℤ, c ≠ 0 ∧ x * y = (c : O)) → g < Module.finrank ℤ O → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.potModel_of_intDivOrder_leftAction | exact GlobalTheory.potModel_of_intDivOrder_leftAction | (intros; apply GlobalTheory.potModel_of_intDivOrder_leftAction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnBasicOpenOfComesFromBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnitOpen

theorem zpow_mul_toNat {F : Type} [Field F] {x : F} (hx : x ≠ 0) (m : ℤ) :
    x ^ m * x ^ (-m).toNat = x ^ m.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  have := Int.toNat_sub_toNat_neg m
  omega

theorem psiUnitOn_basicOpen_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ f : V, (∀ k, ∃ n : ℕ, s k ∣ f ^ n) → ∀ y, PsiUnitOn Q y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hdiv f hf y
  obtain ⟨g, hD, hg, -, -⟩ := hdiv
  have h1 : ∀ χ, PsiUnitOn (mulDeg L.D l.M') χ Set.univ := fun χ => L.gen (l.M' • χ)
  have h2 : PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ := GlobalTheory.T.psiUnitOn_univ_of_pullback_generating _ _ _ _ _ hD h1 y
  have h3 : PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) :=
    fun j W hW _ => h2 j W hW (Set.subset_univ _)
  by_cases hf0 : f = 0
  · subst hf0
    refine GlobalTheory.T.psiUnitOn_of_rescaled_psiUnitOn V Q g y _ 0 0 (by simp) (fun p hp => ?_) h3
    exact ((hp : (0 : V) ∉ (p : PrimeSpectrum V).asIdeal) (Ideal.zero_mem _)).elim
  set m : I → ℤ := fun k => (l.M' : ℤ) * ε k (e y) (H.w0 • e y) with hm
  have hs : ∀ k, s k ≠ 0 := fun k hk => by
    obtain ⟨n, hn⟩ := hf k
    rw [hk, zero_dvd_iff] at hn
    exact hf0 (pow_eq_zero_iff'.1 hn).1
  refine GlobalTheory.T.psiUnitOn_of_rescaled_psiUnitOn V Q g y _ (∏ k, s k ^ (m k).toNat) (∏ k, s k ^ (-m k).toNat) ?_ (fun p hp => ?_) h3
  · have hy := hg y
    have hgy : ((g y : (FractionRing V)ˣ) : FractionRing V) = (∏ k, algebraMap V (FractionRing V) (s k) ^ m k)⁻¹ := by
      rw [← hy, Units.val_inv_eq_inv_val, inv_inv]
    have hne : ∀ k, algebraMap V (FractionRing V) (s k) ≠ 0 := fun k =>
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs k)
    rw [hgy, map_prod, map_prod, inv_mul_eq_iff_eq_mul₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, map_pow, zpow_mul_toNat (hne k)]
  · have hp' : f ∉ (p : PrimeSpectrum V).asIdeal := hp
    have hk : ∀ k, s k ∉ (p : PrimeSpectrum V).asIdeal := fun k hk => by
      obtain ⟨n, hn⟩ := hf k
      exact hp' ((p : PrimeSpectrum V).isPrime.mem_of_pow_mem n (Ideal.mem_of_dvd _ hn hk))
    constructor <;>
    · intro hmem
      obtain ⟨k, -, hk'⟩ := ((p : PrimeSpectrum V).isPrime.prod_mem_iff).1 hmem
      exact hk k ((p : PrimeSpectrum V).isPrime.mem_of_pow_mem _ hk')

end GlobalTheory.UnitOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledLowerObjectDescendsWithPointsSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.PtsDescent

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') (z : Over.mk (T.hom ≫ f) ⟶ G)
    (hz : z.left = x.left ≫ φ) (n : ℕ) : (z ^ n).left = (x ^ n).left ≫ φ := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
  have e : Φ x = z := Over.OverMorphism.ext ((hΦ x).trans hz.symm)
  rw [← hΦ, map_pow, e]

theorem degPre_c_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : D.X) (n : ℕ) :
    D.c (n • y) = D.c y ^ n := by
  have h0 : D.c 0 = 1 := by
    have := D.c_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, D.c_add, ih, pow_succ]; rfl

end GlobalTheory.UCanon.PtsDescent

namespace GlobalTheory.UCanon.PtsDescent

theorem pulledObj_descends_with_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (θ : o'.t.G.left ⟶ B'.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → IsGrpPullback o'.t.G B' (𝟙 _) θ → LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) → (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) → IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) ∧ LBIso o'.t.PP.L (M₀.pull (θ ≫ π₀)) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ θ ≫ π₀ = spMap k₀.subtype ≫ x₀ := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hdiv K _ _ _ ev k₀ hk₀ o' m₁ B₀ _ _ M₀ c₀ B' _ π₁ π₀ w c' θ hB₀ hM₀ hpb1 hpb0 hw hc' hθ hL hpts
  have h1 : IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) :=
    (hθ.comp hpb0).congr (Category.id_comp _) rfl
  refine ⟨h1, ?_, ?_⟩
  · exact LBIso.trans o'.t.PP.isLB (pull_isLB Q.P.isLB _) (pull_isLB hM₀ _) hL
      (GlobalTheory.GenSpread.lbIso_pull_comp θ rfl rfl ⟨w, hw⟩)

  · intro y
    have hpb : IsGrpPullback o'.t.G L.D.P.A (spMap (ev.comp iw)) (m₁.toSABMap.φ ≫ L.φB) :=
      (m₁.cart.comp L.ab.1).congr (Category.comp_id _) rfl
    let x : Sp K ⟶ o'.t.G.left := hpb.1.lift (spMap (ev.comp iw) ≫ (L.D.c y).left) (𝟙 _)
      (by rw [Category.assoc, Over.w (L.D.c y)]; simp)
    have hx1 : x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left := hpb.1.lift_fst _ _ _
    have hx2 : x ≫ o'.t.G.hom = 𝟙 _ := hpb.1.lift_snd _ _ _
    refine ⟨x, hx2, hx1, ?_⟩
    let xp : 𝟙_ (Over (Sp K)) ⟶ o'.t.G := Over.homMk x (by simpa using hx2)
    let z : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw)) ⟶ L.D.P.A := toUnit _ ≫ L.D.c y
    have htu : (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw)))).left =
        (𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw) := by
      simpa using Over.w (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))))
    have hz : z.left = xp.left ≫ m₁.toSABMap.φ ≫ L.φB := by
      show (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))) ≫ L.D.c y).left = x ≫ m₁.toSABMap.φ ≫ L.φB
      rw [Over.comp_left, htu, hx1]; simp
    have hpow := pow_left_of_isGrpPullback hpb _ xp z hz l.M'
    have hxa : (xp ^ l.M').left ≫ m₁.toSABMap.φ ≫ L.φB =
        spMap (ev.comp iw) ≫ (L.D.c (l.M' • e (e.symm y))).left := by
      rw [LinearEquiv.apply_symm_apply, degPre_c_nsmul, ← hpow]
      show ((toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (ev.comp iw))) ≫ L.D.c y) ^ l.M').left = _
      rw [← MonObj.comp_pow, Over.comp_left, htu]; simp
    have hxs : (xp ^ l.M').left ≫ o'.t.G.hom = 𝟙 _ := by simpa using Over.w (xp ^ l.M')
    have h₁ := hpts _ (e.symm y) hxs hxa
    have hsec : (xp ^ l.M').left ≫ θ = c' (e.symm y) := by
      apply hpb1.1.hom_ext
      · rw [Category.assoc, h₁, (hc' _).2.1]
      · rw [Category.assoc, hθ.1.w, ← Category.assoc, hxs, (hc' _).1]; simp
    have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.grpPullback_point_descends_algClosed_subfield K k₀ hk₀ B₀ o'.t.G (θ ≫ π₀) hB₀ h1 l.M' hM' xp (c₀ (e.symm y))
      (by rw [← Category.assoc, hsec, (hc' _).2.2])
    exact ⟨y₀, hy₀⟩

end GlobalTheory.UCanon.PtsDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDivisionStepDecomposition
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogStep

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem constantCoeff_up_eq_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) : constantCoeff (up E μ i) = 0 := by
  rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
    map_zero]

theorem ql_add {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} {f g : MvPowerSeries (Fin d) E} (hf : QL μ N f) (hg : QL μ N g) :
    QL μ N (f + g) := by
  obtain ⟨f0, f1, f2⟩ := hf
  obtain ⟨g0, g1, g2⟩ := hg
  refine ⟨by rw [map_add, f0, g0, add_zero], fun i => ?_, fun α => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := f1 i
    obtain ⟨b, hb, hb'⟩ := g1 i
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    simp only [lin, map_add] at ha' hb' ⊢
    rw [ha', hb']
  · obtain ⟨a, ha, ha'⟩ := f2 α
    obtain ⟨b, hb, hb'⟩ := g2 α
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    rw [formalCoboundary_add (constantCoeff_up_eq_zero hμ), map_add, ha', hb', map_add]

theorem ql_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} (a : O) {f : MvPowerSeries (Fin d) E} (hf : QL μ N f) :
    QL μ N (algebraMap O E a • f) := by
  obtain ⟨f0, f1, f2⟩ := hf
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, f0,
      mul_zero]
  · obtain ⟨b, hb, hb'⟩ := f1 i
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    simp only [lin, coeff_smul] at hb' ⊢
    rw [hb', map_mul]
  · obtain ⟨b, hb, hb'⟩ := f2 α
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    rw [formalCoboundary_smul (constantCoeff_up_eq_zero hμ), coeff_smul, hb', map_mul]

theorem ql_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (N : Ideal O) : QL μ N (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
  have := formalCoboundary_smul (constantCoeff_up_eq_zero (E := E) hμ) 0 0
  rw [zero_smul, zero_smul] at this
  rw [this, map_zero, map_zero]

theorem comb_add {ι : Type} [Fintype ι] (b b' : ι → O) (e : ι → MvPowerSeries (Fin d) E) :
    comb (b + b') e = comb b e + comb b' e := by
  simp only [comb, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem ql_comb {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {ι : Type} [Fintype ι] (b : ι → O) (e : ι → MvPowerSeries (Fin d) E)
    (he : ∀ i, QL μ ⊤ (e i)) : QL μ ⊤ (comb b e) := by
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => rw [Finset.sum_empty]; exact ql_zero hμ _
  | cons i s hi ih => rw [Finset.sum_cons]; exact ql_add hμ (ql_smul hμ _ (he i)) ih

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → (∀ i, lin (e (Sum.inl i)) = Pi.single i 1) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → ∀ f, QL c.μ ⊤ f → ∃ (b : Fin d ⊕ Fin k → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL c.μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQe hcob hlin hLie f hf
  have hμ := c.isLaw.const
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hc0 := constantCoeff_up_eq_zero (E := E) hμ

  let t : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) fun j => lb j
  have ht : ∀ i, c.IsLie (e i) (t i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hF _ (hQe (Sum.inl i))
      have := ((GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF _ _ l l 0 hl hl).2.2 (hcob i))
      subst this
      exact hl
    · exact hLie j

  have hcombS : ∀ (b : Fin d ⊕ Fin k → O) (S : Finset (Fin d ⊕ Fin k)),
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e i) (∑ i ∈ S, b i • t i) ∧
        QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e i) := by
    intro b S
    induction S using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact ⟨c.isLie_zero hinj, ql_zero hμ _⟩
    | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons, add_comm, add_comm (b i • t i)]
      exact ⟨(GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF _ _ _ _ (b i) ih.1 (ht i)).1 ih.2 (hQe i),
        ql_add hμ ih.2 (ql_smul hμ _ (hQe i))⟩
  have hcombLie : ∀ b : Fin d ⊕ Fin k → O, c.IsLie (comb b e) (∑ i, b i • t i) :=
    fun b => (hcombS b Finset.univ).1

  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c E hF f hf
  let b0 : Fin d ⊕ Fin k → O := Sum.elim (0 : Fin d → O) fun j => lb.repr l j
  have hb0 : ∑ i, b0 i • t i = l := by
    rw [Fintype.sum_sum_type]
    simp only [b0, t, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      zero_add]
    exact lb.sum_repr l
  set f' := f + algebraMap O E (-1) • comb b0 e with hf'
  have hQf' : QL c.μ ⊤ f' := ql_add hμ hf (ql_smul hμ _ (ql_comb hμ b0 e hQe))
  have hLf' : c.IsLie f' ((p : O) • 0) := by
    have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c E hF f (comb b0 e) l _ (-1) hl (hcombLie b0)).1 hf
      (ql_comb hμ b0 e hQe)
    rwa [hb0, neg_one_smul, add_neg_cancel, ← smul_zero (p : O)] at this
  obtain ⟨s, g, hg, hh⟩ := GlobalTheory.T.quasiLogarithm_decomposition_of_tangent_divisible_by_p p C v O hv G d c E hF f' 0 hQf' hLf'
  set h := f' - map (algebraMap O E) s - g with hhdef

  have hw : ∀ i, ∃ w : O, lin g i = algebraMap O E w := by
    intro i
    obtain ⟨b1, -, hb1⟩ := hQf'.2.1 i
    obtain ⟨b3, -, hb3⟩ := hh.2.1 i
    refine ⟨b1 - coeff (Finsupp.single i 1) s - b3, ?_⟩
    have : g = f' - map (algebraMap O E) s - h := by rw [hhdef]; ring
    simp only [lin] at hb1 hb3 ⊢
    rw [this, map_sub, map_sub, hb1, hb3, coeff_map, map_sub, map_sub]
  choose w hw using hw
  let bw : Fin d ⊕ Fin k → O := Sum.elim w 0
  have hcw : comb bw e = ∑ i, algebraMap O E (w i) • e (Sum.inl i) := by
    simp [comb, bw, Fintype.sum_sum_type]

  have hgw : g = comb bw e := by
    have key := GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero p O E hF d c.μ c.isLaw (g - comb bw e) ?_ ?_
    · exact sub_eq_zero.1 key
    · funext i
      simp only [lin, hcw, map_sub, map_sum, coeff_smul, Pi.zero_apply] at hw ⊢
      have hl' : ∀ j, coeff (Finsupp.single i 1) (e (Sum.inl j)) =
          (Pi.single j (1 : E) : Fin d → E) i := fun j => congrFun (hlin j) i
      simp only [hl', hw]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, Ne.symm hj]) (by simp)]
      simp
    · let L : MvPowerSeries (Fin d) E →+ MvPowerSeries (Fin d ⊕ Fin d) E :=
        AddMonoidHom.mk' (cob1 (up E c.μ)) (formalCoboundary_add hc0)
      have hL : ∀ x, L x = cob1 (up E c.μ) x := fun _ => rfl
      rw [← hL, map_sub, hcw, map_sum]
      simp only [hL, formalCoboundary_smul hc0, hcob, smul_zero, Finset.sum_const_zero, sub_zero]
      exact hg

  obtain ⟨u, hu⟩ := hF.unit_p
  refine ⟨bw + b0, s, (↑u⁻¹ : E) • h, ?_, ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hh
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0,
        mul_zero]
    · obtain ⟨b, hb, hb'⟩ := h1 i
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      simp only [lin, coeff_smul] at hb' ⊢
      rw [hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    · obtain ⟨b, hb, hb'⟩ := h2 α
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      rw [formalCoboundary_smul hc0, coeff_smul, hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul,
        one_mul]
  · rw [smul_smul, ← hu, Units.mul_inv, one_smul, comb_add, ← hgw]
    rw [map_neg, map_one, neg_one_smul] at hf'
    rw [hhdef, hf']
    ring

end GlobalTheory.QLogStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidCubicalExtensionPullbackOfToricChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidCubicalExtension_pullback_of_toricChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] {m n : ℕ} (tC : SAB H (Sp (ChartRing k m n))) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp (ChartRing k m n) ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (PP : RigLB G) (cub : CubicalStr G PP) {X' : Scheme.{0}} (tF : SAB H X') (j : X' ⟶ S) (e : tF.G.left ⟶ G.left) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ (y : Sp (FractionRing (ChartRing k m n)) ⟶ X'), y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK tC (jK _)) (b : SABMap tK tF y), a.φ ≫ πC = b.φ ≫ e → ∃ cm' : CubeMap tC.G G, cm'.F = πC ∧ cm'.e = ξ ∧ cm'.IsPullCubical tC.cub cub := by
  first | exact @GlobalTheory.ChartCubExt.cube_pull_of_chart | exact GlobalTheory.ChartCubExt.cube_pull_of_chart | (intros; apply GlobalTheory.ChartCubExt.cube_pull_of_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SabMapKeepsLevelEtaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sabMap_keeps_levelEta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (A W : Type) [CommRing A] [IsDomain A] [CommRing W] (bA : c.F →+* A) (b : c.F →+* W) (o' : LowObj D c bA) (o : LowObj D c b) (f : W →+* A), f.comp b = bA → ∀ m : SABMap o'.t o.t (spMap f), (∀ a, (o'.etaA a).left ≫ m.φ = spMap f ≫ (o.etaA a).left) → ∀ a, (o'.eta a).left ≫ m.φ = spMap f ≫ (o.eta a).left := by
  first | exact @GlobalTheory.UCanon.sabMap_keeps_eta | exact GlobalTheory.UCanon.sabMap_keeps_eta | (intros; apply GlobalTheory.UCanon.sabMap_keeps_eta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionCanonicalWeightsTendstoZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfIntersection_canonicalWeights_tendsto_zero : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ C : ℝ, ∀ (n : ℕ) (u : SmFn p) (a : ℝ), 1 ≤ n → IsCan P e n x u → (up P.L u).IsSelfInter a → |a| ≤ C / n := by
  first | exact @GlobalTheory.HSAmp.selfInter_canWeight_le | exact GlobalTheory.HSAmp.selfInter_canWeight_le | (intros; apply GlobalTheory.HSAmp.selfInter_canWeight_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantBundlePowEightIsoDetHodgePowFour
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyZh

theorem lft_of_arithBase : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (M : ZH.RatModel o Ω), LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  intro o Ω _ _ _ _ M
  have := M.lft
  have hft : Algebra.FiniteType ℤ o := (inferInstance : ZH.ArithBase o Ω).ft
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  infer_instance

theorem charZero_of_arithBase : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (M : ZH.RatModel o Ω), CharZero Γ(M.Z, ⊤) := by
  intro o Ω _ _ _ _ M
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨genericPoint M.Z, trivial⟩
  have := (inferInstance : ZH.ArithBase o Ω).char
  exact (M.res ⊤ hne).charZero

theorem unifAlong_of_zhOut : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), UnifAlong Zh.G Zh.L.L := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh V _ _ _ _ hc _ ξ hne _
  obtain ⟨D, A, U, hU, -⟩ := Zh.unif V inferInstance inferInstance hc ξ hne
  exact ⟨D, A, U, hU⟩

theorem key_zh : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), 1 ≤ S.g → S.Over₀ M U₀ → IsOpen (abLocus Zh.G) → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge Zh.G S.g) 4) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hg hO hab δ t hδ hcov hsc
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_glued_thetaSection_nonzero_every_fibre o Ω S ρ M U₀ EE Zh hO δ t hδ hcov hsc
    (fun a z hz => GlobalTheory.T.coordinate_divides_on_nonzeroLocus_section o Ω M δ t S.th hδ hsc a z hz)
  exact GlobalTheory.T.keyFormula_evenDegeneration_global M.Z (M.s ≫ spMap (algebraMap ℤ o)) Zh.G S.g Zh.L δ σ hg inferInstance hO.normal
    (lft_of_arithBase o Ω M) (charZero_of_arithBase o Ω M) Zh.semi Zh.dim (GlobalTheory.T.semiAbelianExtension_abelianLocus_nonempty o Ω S ρ M U₀ EE Zh hO) hab
    Zh.sym hδ Zh.pol (unifAlong_of_zhOut o Ω S ρ M U₀ EE Zh) hσ

end GlobalTheory.KeyZh
end

