import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePtRight

-- bundled from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.RealCase
open ReciprocityTheory.ChartRestriction.G.Out Classical
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

variable {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem exists_chart (χ : u.D.toPre.X) : ∃ j : PUnit → u.D.toPre.P.L.ι,
    ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U (j PUnit.unit) := by
  obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart u.D.toPre.P.isLB
    ((u.D.toPre.c χ).left (IsLocalRing.closedPoint u.V))
  refine ⟨fun _ => i, fun x _ => ?_⟩
  rw [Scheme.Hom.mem_preimage]
  exact ((IsLocalRing.specializes_closedPoint (R := u.V) x).map
    (u.D.toPre.c χ).left.continuous).mem_open (u.D.toPre.P.L.U i).isOpen hi

theorem psiNorm_unique (χ : u.D.toPre.X) {r r' : ℝ} (h : u.PsiNorm χ r) (h' : u.PsiNorm χ r') : r = r' := by
  obtain ⟨j, hj⟩ := exists_chart u χ
  exact (h j hj).symm.trans (h' j hj)

theorem big_third (S : ThetaSys o Ω) (hg : 1 ≤ S.g)
    (h1 : 1 + 2 * (S.g : ℝ) * (2 : ℝ) ^ ((S.g : ℝ) / 2) < S.N)
    (h2 : 2 * ((S.N ^ S.g * S.g.factorial : ℕ) : ℝ) * ((S.g : ℝ) * (3 / 2 : ℝ) ^ S.g * (2 : ℝ) ^ ((S.g : ℝ) / 2 - 1)) * S.N
      < (S.r * S.N : ℕ)) : S.Big := by
  refine ⟨h1, h2, ?_⟩
  have hg' : (1:ℝ) ≤ S.g := by exact_mod_cast hg
  have hN3 : (3:ℝ) < S.N := by
    have h2g : (1:ℝ) ≤ (2:ℝ) ^ ((S.g:ℝ)/2) := Real.one_le_rpow (by norm_num) (by positivity)
    nlinarith
  have hN4 : (4:ℝ) ≤ S.N := by
    have h3 : 3 < S.N := by exact_mod_cast hN3
    have h4 : 4 ≤ S.N := h3
    exact_mod_cast h4
  have h32 : (3/2:ℝ) ≤ (3/2:ℝ) ^ S.g := by
    calc (3/2:ℝ) = (3/2) ^ 1 := by norm_num
      _ ≤ (3/2) ^ S.g := pow_le_pow_right₀ (by norm_num) hg
  have h12 : (1/2:ℝ) ≤ (2:ℝ) ^ ((S.g:ℝ)/2 - 1) := by
    calc (1/2:ℝ) = (2:ℝ) ^ (-1:ℝ) := by rw [Real.rpow_neg_one]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hB : (3/4:ℝ) ≤ (S.g : ℝ) * (3 / 2 : ℝ) ^ S.g * (2 : ℝ) ^ ((S.g : ℝ) / 2 - 1) := by
    calc (3/4:ℝ) = 1 * (3/2) * (1/2) := by norm_num
      _ ≤ _ := by gcongr
  have hBN : (3:ℝ) ≤ ((S.g : ℝ) * (3 / 2 : ℝ) ^ S.g * (2 : ℝ) ^ ((S.g : ℝ) / 2 - 1)) * S.N := by
    nlinarith
  generalize (S.g : ℝ) * (3 / 2 : ℝ) ^ S.g * (2 : ℝ) ^ ((S.g : ℝ) / 2 - 1) = B at h2 hBN
  generalize S.N ^ S.g * S.g.factorial = A at h2 ⊢
  generalize S.r * S.N = M at h2 ⊢
  have hA0 : (0:ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  have hlt : ((6 * A : ℕ) : ℝ) < (M : ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hBN hA0]
  exact_mod_cast hlt
end GlobalTheory.ZH.RealCase
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.FinExtHomInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelTests

section Ext
variable {V W : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]

end Ext

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem isNsmul_b {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, hl⟩ := H
  have key : ∀ (n : ℕ) (hn : n < k + 1), (gs ⟨n, hn⟩).b = g.b ^ n := by
    intro n
    induction n with
    | zero => intro hn; rw [pow_zero]; exact h0.1
    | succ n ih =>
      intro hn
      have e := (hs ⟨n, by omega⟩).1
      rw [pow_succ, ← ih (by omega)]
      exact e
  rw [← hl]
  exact key k (Nat.lt_succ_self k)

end Tors

theorem not_allPre_fe : ¬ AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => U.FE (FractionRing V) 2 := fun h => by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : FractionRing ℤ_[2]) ≠ 0 := two_ne_zero
  have e := (RelModel.fe_zeroUq_iff ℤ_[2] (IsLocalRing.maximalIdeal ℤ_[2]) (FractionRing ℤ_[2]) 1
    (Units.mk0 2 h2)).1 (h ℤ_[2] (cdvr_padicInt 2) _ _ _ (RelModel.zeroUq ℤ_[2] _ (Units.mk0 2 h2)))
  have e' : (2 : FractionRing ℤ_[2]) = 1 := by simpa using congrArg Units.val e
  norm_num at e'

end GlobalTheory.UU.RelTests
end
end

