import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DIsoDR0
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Lim (r : Res l K) (M : Model l K) (j : ℕ) : Type 1 := (Wc.HS l (B.schFn M.p) r.ρ j).lim

def LimCup (r : Res l K) (M : Model l K) {i j n : ℕ} (h : i + j = n) (x : Lim r M i) (y : Lim r M j) (z : Lim r M n) : Prop :=
  ∀ m, z.1 m = (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)).cup h (x.1 m) (y.1 m)

def LimOne (r : Res l K) (M : Model l K) (x : Lim r M 0) : Prop := ∀ m, x.1 m = CH.oneH (Wc.OA l (B.schFn M.p) r.ρ m)

def toD (r : Res l K) (M : Model l K) (j : ℕ) (x : Lim r M j) : r.iso.D M j := (1 : Wc.K₀ l r.k) ⊗ₜ[WittVector l r.k] x

structure DIso (r : Res l K) where
  k₀ : Wc.K₀ l r.k →+* K
  lifts : ∀ x : WittVector l r.k, ∃ a : OK l K, (a : K) = k₀ (algebraMap _ _ x) ∧ r.ρ a = WittVector.constantCoeff x
  e : ∀ (M : Model l K) (j : ℕ), r.iso.D M j →ₛₗ[k₀] HdR M.q j
  iso : ∀ (M : Model l K), M.Sm → ∀ j : ℕ, letI := k₀.toAlgebra
    ∃ g : K ⊗[Wc.K₀ l r.k] r.iso.D M j ≃ₗ[K] HdR M.q j, ∀ x, g (1 ⊗ₜ x) = e M j x
  nat : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p), M.Sm → N.Sm → ∀ (j : ℕ) (x : r.iso.D N j),
    e M j (r.iso.pull u hu j x) = pullR j (Model.genMap u hu) (Model.genMap_q u hu) (e N j x)
  cup : ∀ (M : Model l K), M.Sm → ∀ {i j n : ℕ} (h : i + j = n) (x : Lim r M i) (y : Lim r M j) (z : Lim r M n),
    LimCup r M h x y z → e M n (toD r M n z) = cupK M.q h (e M i (toD r M i x)) (e M j (toD r M j y))
  one : ∀ (M : Model l K), M.Sm → ∀ x, LimOne r M x → e M 0 (toD r M 0 x) = oneK M.q

def DIsoDR0 : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (r : Res l K), Irreducible (l : OK l K) → Nonempty (DIso r)

def DIsoDR : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (r : Res l K), Nonempty (DIso r)

def PhiBij : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (r : Res l K) (M : Model l K), M.Sm → ∀ j, Function.Bijective (r.iso.φ M j)

end CrystallineSemistableComparison.Pb
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Zar2
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem zar2 : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 : Set X.Opens) (Q' : ObjectProperty (Thick (nlFun γ p X q κ))) (h : St Q₀ 𝒱 ≤ Q') (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := @GlobalTheory.CompanionTheory.ZarCosieve.main

end CrystallineSemistableComparison.Pb
end
end

