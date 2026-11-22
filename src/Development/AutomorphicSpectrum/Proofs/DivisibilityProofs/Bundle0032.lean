import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import Development.WeilBound.CoreStatements.FlagImmersions.ArithmeticIntersectionDivisorSupport
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0030
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0019
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3PadicGlobal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0031

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Top.Link

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def reline (M : RootModel Ψ N) (xdeg : Ψ × Fin N → M.K → ℤ) (x : ℝ → Ψ × Fin N → HermLine M.ι)
    (x_deg : ∀ t r, (x t r).a = xdeg r) (x_smooth : ∀ t r, IsSmoothHerm (x t r))
    (x_conj : ∀ t r, IsConjInvariantH (x t r)) (A : HermLine M.ι) (A_smooth : IsSmoothHerm A)
    (A_conj : IsConjInvariantH A) : RootModel Ψ N :=
  { M with xdeg := xdeg, x := x, x_deg := x_deg, x_smooth := x_smooth, x_conj := x_conj, A := A,
           A_smooth := A_smooth, A_conj := A_conj }

theorem arMono_reline (M : RootModel Ψ N) {d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁ d₂ x₂ h₂ s₂ c₂ A₂ a₂ b₂}
    (II : IntersectionSystem) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (hx : ∀ r, x₁ t r = x₂ t r) (hA : A₁ = A₂) :
    (reline M d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁).arMono II t m = (reline M d₂ x₂ h₂ s₂ c₂ A₂ a₂ b₂).arMono II t m := by
  subst hA
  have hl : (reline M d₁ x₁ h₁ s₁ c₁ A₁ a₁ b₁).line t = (reline M d₂ x₂ h₂ s₂ c₂ A₁ a₂ b₂).line t := by
    funext o
    cases o with
    | none => rfl
    | some r => exact hx r
  unfold RootModel.arMono
  rw [hl]
  rfl

def pullModel (M₀ : RootModel Ψ N) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (ha : IsArithVar (mCoordIdeal y) (dimFl Ψ N + 1)) (hb : Birational y)
    {κ : M₀.K → K} {v : (Σ k, M₀.ι k) → Σ k, J k} (hv : IsBlockMap κ v) (δ : ℕ) (hδ : 0 < δ) : RootModel Ψ N where
  K := K
  ι := J
  Ω := Ω
  y := y
  arith := ha
  birational := hb
  xdeg r := pullDeg κ (M₀.xdeg r)
  x t r := pullHerm hv (M₀.x t r)
  x_deg t r := by
    show pullDeg κ (M₀.x t r).a = _
    rw [M₀.x_deg]
  x_smooth t r := Chg.isSmoothHerm_pull hv (M₀.x_smooth t r)
  x_conj t r := Chg.isConj_pull hv (M₀.x_conj t r)
  kA := M₀.kA
  kA_pos := M₀.kA_pos
  A := pullHerm hv M₀.A
  A_smooth := Chg.isSmoothHerm_pull hv M₀.A_smooth
  A_conj := Chg.isConj_pull hv M₀.A_conj
  δ := δ
  δ_pos := hδ

end GlobalTheory.CompanionTheory.Ar.Top.Link
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupport
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem kleiman_generic_fibre_integral : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι), IsArithVar W (e + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
  RootFieldNumerics.arithmetic_intersection_divisor_support

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainArithVarietyStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_chain_arith_variety : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [Nonempty K] (j : K → FlBlock Ψ N), IsChain j → IsArithVar (PPart j) (cellDim j + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightI9PropertiesStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_I9_properties : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N → I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 | exact GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagM3PadicGlobalStatement
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_m3_padic_global : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ D : ℕ, IsArithVar (mCoordIdeal y) (D + 1) → ∀ (p : Nat.Primes) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (S : Finset Nat.Primes) (T : LocPair ι ℤ (Ψ × Fin N)), T.IsVertOff (mCoordIdeal y) S → (AtPlacesOver A Ω p fun O _ _ _ _ => FlagChernComparison (pointIdeal O y) D p j φ (T.map (Int.castRingHom O))) → FlagChernComparison (extTo (ZP p) (mCoordIdeal y)) D p j φ (T.map (Int.castRingHom (ZP p))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3.flag_m3_padic | exact GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3.flag_m3_padic | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PlacesFlagM3.flag_m3_padic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerNefGeneralStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_nef_general : PB.NefPol → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → ∀ B c, (∀ lam : Wt Ψ N, Dominant lam → (T.M B c).NefGen lam 0) ∧ (T.M B c).NefGen 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rt_nefgen | exact GlobalTheory.CompanionTheory.Ar.Top.rt_nefgen | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rt_nefgen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportionalStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_proportional : PB.Proportional → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (R : RealTower T), R.Unif → T.Proportional := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif | exact GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangLowerBoundRationalStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zhang_lower_bound_rational : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) → ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤ M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model | exact GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangUpperBoundDensePointsStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zhang_upper_bound_dense_points : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model | exact GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model <;> assumption)
end

