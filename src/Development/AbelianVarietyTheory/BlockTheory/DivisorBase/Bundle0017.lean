import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0003
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalRingCardinality.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeAutomorphismLcm
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeAutomorphismLcm

open Formalism.BasicNotions Formalism.MainNotions NumberField

def minkRank (D : D7) : ℕ := 2 * D.R.f * D.R.N D.R.m

def PrimeToLevel (D : D7) (n : ℕ) : Prop :=
  n ∣ minkM (minkRank D) ∧
  (∀ p : ℕ, p.Prime → p ∣ n → p ≤ minkRank D + 1) ∧
  Nat.Coprime n D.host.q ∧ Nat.Coprime n D.host.d ∧
  (∀ i : Fin 2, Nat.Coprime n (D.host.g i)) ∧
  ∀ u : D.what₂.Word, Nat.Coprime n (D.mem u).A.T

def PrimeToLevelAt (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), PrimeToLevel D (D.chTw u μ).DGam

def PrimeToLevelF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, PrimeToLevelAt (Fm.D x i)

def SizesUsed {D : D7} (L : SizeData₂ D) : Prop :=
  Nonempty (ParameterChoice' D L) ∧ (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ (L.Ct + 1) ∧ L.TuGe ∧ 2 ≤ L.sc.x

def RowAt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D), SizesUsed L → DGamDef D → DGamChoice_at D → PrimeToLevelAt D

def RowFamily : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps), DGamChoiceF Fm → TuSize Fm → PrimeToLevelF Fm

def Row : Prop := RowAt ∧ RowFamily

def latticeAut {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V) :
    Subgroup (S.V ≃ₗ[E] S.V) where
  carrier := {γ | (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ ∀ x, γ x ∈ Λ ↔ x ∈ Λ}
  one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨fun x y => (ha.1 (b x) (b y)).trans (hb.1 x y), fun x => (ha.2 (b x)).trans (hb.2 x)⟩
  inv_mem' := fun {a} ha =>
    ⟨fun x y => by
      have := ha.1 (a.symm x) (a.symm y)
      rw [a.apply_symm_apply, a.apply_symm_apply] at this
      exact this.symm,
    fun x => by
      have := ha.2 (a.symm x)
      rw [a.apply_symm_apply] at this
      exact this.symm⟩

def autOrders {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) : Set ℕ :=
  {a | ∃ Λ : Submodule (𝓞 E) S.V, Submodule.IsLattice E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ ∧
    a = Nat.card (latticeAut S Λ)}

def definiteAutOrders (D : D7) : Set ℕ :=
  letI := D.host.cmStar
  (⋃ j ∈ Set.Icc 1 D.R.m, autOrders (D.sp.X j)) ∪ autOrders D.sp.X' ∪ autOrders (D.sp.Y (D.R.m - 1)) ∪
    ⋃ j ∈ Set.Icc 1 D.R.m, autOrders (D.sp.V j)

def IsAutLcm (D : D7) (n : ℕ) : Prop :=
  0 < n ∧ (∀ a ∈ definiteAutOrders D, a ∣ n) ∧ ∀ n' : ℕ, (∀ a ∈ definiteAutOrders D, a ∣ n') → n ∣ n'

def RowObjects : Prop :=
  (∀ (D : D7) (L : SizeData₂ D), SizesUsed L → ∀ n : ℕ, IsAutLcm D n → PrimeToLevel D n) ∧
  ∀ (eps : ℝ) (Fm : FamP eps), TuSize Fm →
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (n : ℕ), IsAutLcm (Fm.D x i) n → PrimeToLevel (Fm.D x i) n

example (D : D7) : PrimeToLevel D 1 :=
  ⟨one_dvd _, fun p hp h => absurd (Nat.dvd_one.1 h) hp.one_lt.ne', Nat.coprime_one_left _,
    Nat.coprime_one_left _, fun _ => Nat.coprime_one_left _, fun _ => Nat.coprime_one_left _⟩

example (D : D7) : ¬ PrimeToLevel D (D.host.g 0) := fun h =>
  (D.host.g_prime 0).one_lt.ne' ((Nat.coprime_self _).1 (h.2.2.2.2.1 0))

example : minkM 2 = 24 := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeAutomorphismLcm

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RationalRankMinkowski
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRankMinkowski

open Formalism.BasicNotions Formalism.MainNotions

def minkExp (n p : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), n / (p ^ i * (p - 1))

def minkNum (n : ℕ) : ℕ := ∏ p ∈ (Finset.range (n + 2)).filter Nat.Prime, p ^ minkExp n p

def ratRank (D : D7) : ℕ := 2 * D.R.f * D.R.N D.R.m

def DvdMinkowski (D : D7) : Prop := ∀ u, (D.mem u).C.DGam ∣ minkNum (ratRank D)

def SmallPrimes (D : D7) : Prop := ∀ u (p : ℕ), p.Prime → p ∣ (D.mem u).C.DGam → p ≤ ratRank D + 1

def CoprimeAt (D : D7) : Prop :=
  ∀ u, Nat.Coprime (D.mem u).C.DGam D.host.q ∧ Nat.Coprime (D.mem u).C.DGam D.host.d ∧
    (∀ a : Fin 2, Nat.Coprime (D.mem u).C.DGam (D.host.g a)) ∧
    ∀ u', Nat.Coprime (D.mem u).C.DGam (D.mem u').A.T

def StatementAt (D : D7) : Prop := DvdMinkowski D ∧ SmallPrimes D ∧ CoprimeAt D

def CoprimeF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, CoprimeAt (Fm.D x i)

def StatementF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, StatementAt (Fm.D x i)

example : minkNum 1 = 2 ∧ minkNum 2 = 24 ∧ minkNum 3 = 48 ∧ minkNum 4 = 5760 := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRankMinkowski

end
end

