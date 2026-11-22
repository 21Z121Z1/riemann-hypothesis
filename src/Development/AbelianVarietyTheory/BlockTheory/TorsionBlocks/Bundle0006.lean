import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Formalism.HermitianLattices.Bundle0003
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues

open Formalism.BasicNotions.TH

def lowerOp {p q : ℕ} (n : ℕ) (a : Fin p) (b : Fin q) (Φ : Pol p q n 0) : Pol p q n 0 :=
  ∑ c : Fin n, MvPolynomial.pderiv ((Sum.inl a, Sum.inl c) : Ln p q n 0)
    (MvPolynomial.pderiv ((Sum.inr b, Sum.inl c) : Ln p q n 0) Φ)

def KilledByPMinus {p q n : ℕ} (Φ : Pol p q n 0) : Prop :=
  ∀ (a : Fin p) (b : Fin q), lowerOp n a b Φ = 0

def singVal {p q : ℕ} (X : Mat p q) (i : Fin (min p q)) : ℝ :=
  (Matrix.toEuclideanLin X.toBlocks₁₂ :
    EuclideanSpace ℂ (Fin q) →ₗ[ℂ] EuclideanSpace ℂ (Fin p)).singularValues i.val

def coef {p q n : ℕ} {T₀ : GrpData (p * n + q * 0) (p * 0 + q * n)} {T₁ : GrpData p q}
    {T₂ : GrpData n 0} (F : FockData T₀ T₁ T₂) (X : Mat p q) (Φ₁ Φ₂ : Pol p q n 0) : ℂ :=
  inner ℂ (F.ι Φ₂) (F.π (T₁.expt X, 1) (F.ι Φ₁))

def HarmonicDecay : Prop :=
  ∀ (p q n : ℕ) (T₀ : GrpData (p * n + q * 0) (p * 0 + q * n)) (T₁ : GrpData p q) (T₂ : GrpData n 0)
    (F : FockData T₀ T₁ T₂) (X : Mat p q), X ∈ pR p q →
    ∀ Φ₁ Φ₂ : Pol p q n 0, KilledByPMinus Φ₁ → KilledByPMinus Φ₂ →
      ‖coef F X Φ₁ Φ₂‖ ≤
        (∏ i : Fin (min p q), Real.cosh (singVal X i) ^ (-(n : ℤ))) * ‖F.ι Φ₁‖ * ‖F.ι Φ₂‖

theorem fockAct1_lower {p q n : ℕ} (a : Fin p) (b : Fin q) (Φ : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (Sum.inr b) (Sum.inl a)) Φ = -lowerOp n a b Φ := by
  rw [fockAct1_Eab, lowerOp, LinearMap.sum_apply, Fintype.sum_sum_type, ← Finset.sum_neg_distrib]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hne : ((Sum.inr b, Sum.inl c) : Ln p q n 0) ≠ (Sum.inl a, Sum.inl c) := by simp
  have hc : ∀ (i j : Ln p q n 0) (P : Pol p q n 0),
      MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
    intro i j P
    classical
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add P Q hP hQ => simp [hP, hQ]
    | mul_X P k hP =>
      simp only [Derivation.leibniz, map_add, smul_eq_mul, hP, MvPolynomial.pderiv_X]
      by_cases h1 : k = i <;> by_cases h2 : k = j <;> simp [Pi.single_apply, h1, h2] <;>
        (try split_ifs) <;> (try simp) <;> (try ring)
  simp [omE, raiB, lowB, linePos, hne, hc (Sum.inr b, Sum.inl c) (Sum.inl a, Sum.inl c)]

example {p q n : ℕ} : KilledByPMinus (1 : Pol p q n 0) := by
  intro a b; simp [lowerOp]

example {p q n : ℕ} (a : Fin p) (c : Fin n) :
    KilledByPMinus (MvPolynomial.X (Sum.inl a, Sum.inl c) : Pol p q n 0) := by
  intro a' b
  refine Finset.sum_eq_zero fun c' _ => ?_
  rw [MvPolynomial.pderiv_X_of_ne (by simp), map_zero]

example : ¬ KilledByPMinus
    (MvPolynomial.X (Sum.inl 0, Sum.inl 0) * MvPolynomial.X (Sum.inr 0, Sum.inl 0) : Pol 1 1 1 0) := by
  intro h
  have := h 0 0
  simp [lowerOp, MvPolynomial.pderiv_X, Pi.single_apply] at this

end GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelfDualLatticeMass
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass

open NumberField Formalism.BasicNotions

def PosDefAtRealPlaces {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) : Prop :=
  ∀ (τ : E →+* ℂ) (x : W.V), x ≠ 0 → 0 < (τ (W.hD x x)).re

def SelfDualMass : Prop :=
  ∀ D : D7,
    letI := D.host.cmStar
    ∀ W : HSpace D.host.E, PosDefAtRealPlaces W →
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.MainNotions.StandardLattice.massI D W.rank

theorem SelfDualMass.all_lattices (h : SelfDualMass) (D : D7) :
    letI := D.host.cmStar
    ∀ W : HSpace D.host.E, PosDefAtRealPlaces W →
      ∀ L : Submodule (𝓞 D.host.E) W.V, Submodule.IsLattice D.host.E L →
        Formalism.HermitianLatticesTheory.IsUnimodular W.hT L →
        Formalism.HermitianLatticesTheory.mass W.hT L = Formalism.MainNotions.StandardLattice.massI D W.rank := by
  letI := D.host.cmStar
  intro W hW L hL hu
  exact h D { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hu } hW

section Std

variable (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)

open Formalism.MainNotions.StandardLattice

omit [NumberField E] in
theorem stdForm_apply (x y : Fin M → E) : stdForm E M x y = ∑ i, star (x i) * y i := rfl

omit [StarRing E] in
theorem mem_stdLat_iff (x : Fin M → E) : x ∈ stdLat E M ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    | zero => intro i; simpa using isIntegral_zero
    | add a b _ _ ha hb => intro i; exact (ha i).add (hb i)
    | smul a y _ hy =>
      intro i
      have : (a • y) i = (a : E) * y i := by simp [Algebra.smul_def]
      rw [this]
      exact a.isIntegral_coe.mul (hy i)
  · intro hx
    have : x = ∑ i, (⟨x i, hx i⟩ : 𝓞 E) • (Pi.single i 1 : Fin M → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [NumberField E] [StarRing E] in
theorem mem_one_iff (a : E) : a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def stdSpace : HSpace E where
  V := Fin M → E
  hT := stdForm E M
  herm := ⟨fun x y => by
    simp [stdForm_apply, starRingEnd_apply, mul_comm]⟩
  nondeg := by
    constructor
    · intro x hx
      ext i
      have := hx (Pi.single i 1)
      simpa [stdForm_apply, Pi.single_apply] using this
    · intro x hx
      ext i
      have := hx (Pi.single i 1)
      simpa [stdForm_apply, Pi.single_apply, apply_ite star] using this
  rank := M
  rank_eq := by simp
  frame := Pi.basisFun E (Fin M)
  sig := fun _ => (M, 0)
  L0 := stdLat E M
  standardTuple_isLattice :=
    { fg := Submodule.fg_span (Set.finite_range _)
      span_eq_top := by
        rw [eq_top_iff, ← (Pi.basisFun E (Fin M)).span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, by simp⟩ }
  baseLattice_isUnimodular := by
    ext x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, mem_one_iff, stdForm_apply, mem_stdLat_iff]
    constructor
    · intro h i
      have := h (Pi.single i 1) ((mem_stdLat_iff E M _).1 (Submodule.subset_span ⟨i, rfl⟩))
      simpa [Pi.single_apply, apply_ite star] using this
    · intro hx y hy
      exact IsIntegral.sum _ fun i _ => ((hy i).map (starRingEnd E).toIntAlgHom).mul (hx i)

theorem stdSpace_posDef (hc : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) :
    PosDefAtRealPlaces (stdSpace E M) := by
  intro τ x hx
  change 0 < (τ (∑ i, star (x i) * x i)).re
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
  simp only [map_sum, map_mul, hc, Complex.re_sum, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re]
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨j, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero τ).2 hj)⟩

end Std

theorem stdSpace_case (D : D7) (M : ℕ) :
    letI := D.host.cmStar
    PosDefAtRealPlaces (stdSpace D.host.E M) ∧
      Formalism.HermitianLatticesTheory.mass (stdSpace D.host.E M).hT (stdSpace D.host.E M).L0 =
        Formalism.MainNotions.StandardLattice.massI D (stdSpace D.host.E M).rank := by
  letI := D.host.cmStar
  exact ⟨stdSpace_posDef _ M D.sp.cm.cmUnram.2.1, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SplitColumnClasses
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  p.Prime ∧ (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E

theorem splitsCompletely_g (D : D7) (i : Fin 2) : SplitsCompletely D.host.E (D.host.g i) :=
  ⟨D.host.g_prime i, D.nd.g_split i⟩

def ColClassSet (D : D7) (L : LevelData D) (u : D.what₂.Word) : Type :=
  letI := D.host.cmStar
  ClassSet
    ((ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
      (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    ((L u).U.subgroupOf (UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))

theorem card_colClassSet (D : D7) (L : LevelData D) (u : D.what₂.Word) :
    Nat.card (ColClassSet D L u) = Nat.card ((D.mem u).C.cls 0) := by
  letI := D.host.cmStar
  exact (Nat.card_eq_of_bijective _ (L u).y_bij).symm

def ClassCount (D : D7) (L : LevelData D) (u : D.what₂.Word) : Prop :=
  (Nat.card (ColClassSet D L u) : ℝ) =
    Formalism.MainNotions.StandardLattice.massI D D.R.k * Formalism.MainNotions.StandardLattice.idxPi D (D.host.g 0) (D.host.g 1) *
      ((((D.mem u).A.T : ℕ) : ℝ) ^ D.R.k - 1) ^ D.R.f

def ColumnClassNumber : Prop :=
  ∀ (D : D7) (L : LevelData D) (u : D.what₂.Word),
    (∀ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i) →
    (∀ i : Fin 2, SplitsCompletely D.host.E (D.host.g i)) →
    SplitsCompletely D.host.E (D.mem u).A.T →
    ClassCount D L u

end GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

end
end

