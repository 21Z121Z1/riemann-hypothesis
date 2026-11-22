import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

def twSecs {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules} (S : Subobject P) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤)

def twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  ((Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤))

structure OpSeq {X : Scheme.{0}} (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (d : ℕ) : Prop where
  coherent : ∀ e, IsCoherent (M e)
  comm : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)
  gen : ∀ e, d ≤ e → ∀ U : X.affineOpens,
    Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤

def GradedNoeth : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (k : ℕ) (M : ℕ → Type)
    [∀ e, AddCommGroup (M e)] [∀ e, Module R (M e)] [∀ e, Module.Finite R (M e)]
    (T : Fin k → ∀ e, M e →ₗ[R] M (e + 1)),
    (∀ i j e x, T j (e + 1) (T i e x) = T i (e + 1) (T j e x)) →
    ∀ d : ℕ, (∀ e, d ≤ e → ⨆ i, LinearMap.range (T i e) = ⊤) →
    ∀ L : ∀ e, Submodule R (M e), (∀ i e, (L e).map (T i e) ≤ L (e + 1)) →
    ∃ d' : ℕ, ∀ e, d' ≤ e → ⨆ i, (L e).map (T i e) = L (e + 1)

def UniformVanishing : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q)

def UniformGen : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, d ≤ e →
      Submodule.span Γ(X, ⊤)
        (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (T i e)).app ⊤)) = ⊤

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.XProdPowSmulMemRangeResIter
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem xProd_pow_smul_mem_range_res_iter : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ (T S : Finset ι) (b : P (S ∪ T)), S.Nonempty → ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S (S ∪ T) Finset.subset_union_left)) := by
  intro ι _ A _ P _ _ res hid hcomp hstep
  have hA : ∀ (S0 U : Finset ι) (h : S0 ⊆ U) (j : ι), U ⊆ insert j S0 → ∀ b : P U, S0.Nonempty →
      ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S0 U h) := by
    intro S0 U h j hU b hS0
    by_cases hj : j ∈ U
    · obtain rfl : U = insert j S0 := subset_antisymm hU (Finset.insert_subset hj h)
      exact hstep S0 j b hS0
    · have hUS : U ⊆ S0 := by
        intro x hx
        rcases Finset.mem_insert.mp (hU hx) with hx' | hx'
        · subst hx'
          exact absurd hx hj
        · exact hx'
      obtain rfl : U = S0 := subset_antisymm hUS h
      exact ⟨0, LinearMap.mem_range.mpr ⟨b, by rw [hid, pow_zero, one_smul]⟩⟩
  have hQ : ∀ T : Finset ι, ∀ (S U : Finset ι) (h : S ⊆ U), U ⊆ S ∪ T → ∀ b : P U, S.Nonempty →
      ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S U h) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro S U h hU b hS
      obtain rfl : U = S := subset_antisymm (by simpa using hU) h
      exact ⟨0, LinearMap.mem_range.mpr ⟨b, by rw [hid, pow_zero, one_smul]⟩⟩
    | insert j T hj ih =>
      intro S U h hU b hS
      have hSV : S ⊆ S ∪ U.erase j := Finset.subset_union_left
      have hVU : S ∪ U.erase j ⊆ U := Finset.union_subset h (Finset.erase_subset j U)
      have hUV : U ⊆ insert j (S ∪ U.erase j) := by
        intro x hx
        by_cases hxj : x = j
        · subst hxj
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxj, hx⟩))
      have hVT : S ∪ U.erase j ⊆ S ∪ T := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ hx
        · obtain ⟨hxj, hxU⟩ := Finset.mem_erase.mp hx
          rcases Finset.mem_union.mp (hU hxU) with h1 | h1
          · exact Finset.mem_union_left _ h1
          · rcases Finset.mem_insert.mp h1 with h2 | h2
            · exact absurd h2 hxj
            · exact Finset.mem_union_right _ h2
      have hVne : (S ∪ U.erase j).Nonempty := hS.mono hSV
      obtain ⟨k, hk⟩ := hA (S ∪ U.erase j) U hVU j hUV b hVne
      obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hk
      obtain ⟨l, hl⟩ := ih S (S ∪ U.erase j) hSV hVT c hS
      obtain ⟨d, hd⟩ := LinearMap.mem_range.mp hl
      refine ⟨k + l, ?_⟩
      have hmem : xProd A T ^ l • (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈
          LinearMap.range (res S U h) := by
        refine LinearMap.mem_range.mpr ⟨d, ?_⟩
        rw [← hc, ← (res (S ∪ U.erase j) U hVU).map_smul, ← hd, hcomp]
      have heq : xProd A (insert j T) ^ (k + l) • b =
          ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T ^ k) •
            (xProd A T ^ l • (MvPolynomial.X j : MvPolynomial ι A) ^ k • b) := by
        rw [smul_smul, smul_smul]
        congr 1
        simp only [GlobalTheory.xProd, Finset.prod_insert hj]
        ring
      rw [heq]
      exact Submodule.smul_mem _ _ hmem
  intro T S b hS
  exact hQ T S (S ∪ T) Finset.subset_union_left (Finset.Subset.refl _) b hS

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

