import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable (ι) in

abbrev Family := Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ

def coneSet : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

def AllSmooth {n : ℕ} (L : Fin n → HermLine ι) : Prop := ∀ j, IsSmoothHerm (L j)

def degs {n : ℕ} (L : Fin n → HermLine ι) : Fin n → K → ℤ := fun j => (L j).a

def pots {n : ℕ} (L : Fin n → HermLine ι) : Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)

def IsSec (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) : Prop :=
  ∃ a : K → ℕ, IsMultiHomog s a ∧ (∀ k, (a k : ℤ) = A.a k) ∧ s ∉ P

open Classical in

def horizPart (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ W ∈ (divSupp_finite P s).toFinset.filter (fun W => IsHorizontal W),
    (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L

open Classical in

def vertPart (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ V ∈ (divSupp_finite P s).toFinset.filter (fun V => ¬ IsHorizontal V),
    (multAt (P ⊔ Ideal.span {s}) V : ℝ) * (geoNum n V (degs L) : ℝ) * Real.log (charOf V)

def intPart (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) : ℝ :=
  ptsIntegral P (pots L) (logNorm A s)

def rhsR (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι)
    (s : MRing ι) : ℝ :=
  horizPart I P L s + vertPart P L s - intPart P L A s

def logNormQ (A : HermLine ι) (f g : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)

def rhsRQ (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι)
    (f g : MRing ι) : ℝ :=
  horizPart I P L f - horizPart I P L g + (vertPart P L f - vertPart P L g) -
    ptsIntegral P (pots L) (logNormQ A f g)

def IsFamilyOn (I : Family ι) (good : ℕ → Prop) : Prop :=
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)),
      good n → IsArithVar P n → AllSmooth L → I P n (L ∘ σ) = I P n L) ∧
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (j : Fin n) (A B : HermLine ι),
      good n → IsArithVar P n → AllSmooth L → IsSmoothHerm A → IsSmoothHerm B →
      I P n (Function.update L j (A.tensor B)) =
        I P n (Function.update L j A) + I P n (Function.update L j B)) ∧
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin (n + 1) → HermLine ι) (s : MRing ι),
      good (n + 1) → IsArithVar P (n + 1) → AllSmooth L → IsSec P (L (Fin.last n)) s →
      I P (n + 1) L = rhsR I P (Fin.init L) (L (Fin.last n)) s)

def IsFamily (I : Family ι) : Prop := IsFamilyOn I fun _ => True

def expLine (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) : HermLine ι where
  a := 0
  h z := Real.exp (u z / 2)
  pos _ _ := Real.exp_pos _
  smul c z hc := by simp [hu c z hc]

def IsClosedPt (x : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime x ∧ ringKrullDim (MRing ι ⧸ x) = ((Fintype.card K : ℕ) : WithBot ℕ∞)

end Objects

def ThmIExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ∃ I : Family ι, IsFamily I

def ThmIUnique.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I J : Family ι),
    IsFamily I → IsFamily J → ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι),
      IsArithVar P n → AllSmooth L → I P n L = J P n L

def R1.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 →
    (∀ (I J : Family ι) (A : HermLine ι) (s s' : MRing ι), IsSmoothHerm A → IsSec P A s → IsSec P A s' →
        rhsR I P ![] A s = rhsR J P ![] A s') ∧
    (∀ (I : Family ι) (A B : HermLine ι) (s t : MRing ι), IsSmoothHerm A → IsSmoothHerm B →
        IsSec P A s → IsSec P B t →
        rhsR I P ![] (A.tensor B) (s * t) = rhsR I P ![] A s + rhsR I P ![] B t)

def Swap.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι) (n : ℕ),
    IsFamilyOn I (· < n + 2) →
    ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s s' : MRing ι),
      IsArithVar P (n + 2) → AllSmooth L → IsSmoothHerm A → IsSmoothHerm B →
      IsSec P A s → IsSec P B s' → Disjoint (divSupp P s) (divSupp P s') →
      rhsR I P (Fin.snoc L B) A s = rhsR I P (Fin.snoc L A) B s'

def Choice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ),
    IsArithVar P d → ∀ (m : ℕ) (W x : Fin m → Ideal (MRing ι)),
      (∀ i, IsMultiProjPrime (W i) ∧ P ≤ W i) → (∀ i, W i ≤ x i ∧ IsClosedPt (x i)) →
      ∀ (a : K → ℤ) (b : K → ℕ), (∀ j, 1 ≤ b j) → ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (∀ j, 0 ≤ a j + k * b j) ∧
        (∃ s : MRing ι, IsMultiHomog s (fun j => (a j + k * b j).toNat) ∧ ∀ i, s ∉ x i) ∧
        (∃ s : MRing ι, IsMultiHomog s (fun j => k * b j) ∧ ∀ i, s ∉ x i)

def ArithmeticIntersectionSecond.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (u : ((Σ k, ι k) → ℂ) → ℝ)
      (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z),
      IsArithVar P (n + 1) → AllSmooth L → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u coneSet →
      I P (n + 1) (Fin.snoc L (expLine u hu)) = (1 / 2) * ptsIntegral P (pots L) u

def InductiveIntersectionFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι)
      (α β : K → ℕ), IsArithVar P (n + 1) → AllSmooth L → IsSmoothHerm A →
      IsMultiHomog f α → IsMultiHomog g β → (∀ k, (α k : ℤ) - β k = A.a k) → f ∉ P → g ∉ P →
      (∀ W, IsHorizontal W → divCycle P f W = divCycle P g W) →
      (∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ =
        ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z) →
      I P (n + 1) (Fin.snoc L A) = vertPart P L f - vertPart P L g

def ArithmeticIntersectionFifth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι), IsArithVar P 1 → IsSmoothHerm A →
      IsSec P A s → I P 1 ![A] = vertPart P ![] s - intPart P ![] A s

def Conservation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (p : ℕ), IsArithVar P (n + 1) → AllSmooth L → p.Prime →
    ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (degs L) : ℝ) =
      ptsIntegral P (pots L) (fun _ => 1)

def RationalSections.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι)
      (α β : K → ℕ), IsArithVar P (n + 1) → AllSmooth L → IsSmoothHerm A →
      IsMultiHomog f α → IsMultiHomog g β → (∀ k, (α k : ℤ) - β k = A.a k) → f ∉ P → g ∉ P →
      I P (n + 1) (Fin.snoc L A) = rhsRQ I P L A f g

section Inhabitants

abbrev GlobalTheory (n : ℕ) : Unit → Type := fun _ => Fin n

abbrev Xb (n : ℕ) (i : Fin n) : MRing (GlobalTheory n) := X ⟨(), i⟩

def fsO1 (n : ℕ) : HermLine (GlobalTheory n) := HermLine.sqMetric fun _ => 1

def triv (n : ℕ) : HermLine (GlobalTheory n) := HermLine.sqMetric fun _ => 0

example : Family (GlobalTheory 2) := fun _ _ _ => 0

theorem isSmoothHerm_fubiniStudyO1 (n : ℕ) : IsSmoothHerm (fsO1 n) := isSmoothHerm_sqMetric _

theorem isArithVar_bot (n : ℕ) : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (n + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [Nat.card_eq_fintype_card]
    exact add_comm _ _

theorem isMultiHomog_Xb (n : ℕ) (i : Fin n) : IsMultiHomog (Xb n i) fun _ => 1 := by
  intro m hm k
  rw [support_X] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  cases k
  simp [Finsupp.single_apply]

theorem isMultiHomog_C (c : ℤ) {n : ℕ} : IsMultiHomog (C c : MRing (GlobalTheory n)) 0 := by
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem isSec_Xb (n : ℕ) (i : Fin (n + 1)) : IsSec (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (fsO1 (n + 1)) (Xb (n + 1) i) :=
  ⟨fun _ => 1, isMultiHomog_Xb _ _, fun _ => by simp [fsO1, HermLine.sqMetric],
    by rw [Ideal.mem_bot]; exact X_ne_zero _⟩

theorem specInt_hypotheses_hold : IsArithVar (⊥ : Ideal (MRing (GlobalTheory 1))) 1 ∧ IsSmoothHerm (fsO1 1) ∧
    IsSec (⊥ : Ideal (MRing (GlobalTheory 1))) (fsO1 1) (Xb 1 0) :=
  ⟨isArithVar_bot 0, isSmoothHerm_fubiniStudyO1 1, isSec_Xb 0 0⟩

def halfLine : HermLine (GlobalTheory 1) := expLine (fun _ => 2 * Real.log 2) fun _ _ _ => rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def locRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    v ∉ W ∧ IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}

def locIdeal {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)) : Ideal (locRing P W) :=
  Ideal.span {z | (z : FractionRing (MRing ι ⧸ P)) = y}

theorem locIdeal_eq_span {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) :
    locIdeal P W y = Ideal.span {(⟨y, hy⟩ : locRing P W)} := by
  unfold locIdeal
  congr 1
  ext z
  simp only [Set.mem_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

def specZTwo : Ideal (MRing (PBlk 1)) := Ideal.span {C 2}

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsSemiPosHerm (M : HermLine ι) : Prop :=
  ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ v : (Σ k, ι k) → ℂ,
    0 ≤ Δ (fun t : ℂ => Real.log (M.h (z + t • v))) 0

def De (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι) : ℝ :=
  ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (logNorm A' s')) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s)) -
    ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s'}) W : ℝ) * ptsIntegral W (pot L) (logNorm A s)) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s'))

theorem De_swap (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι)
    (s s' : MRing ι) : De P L A' A s' s = -De P L A A' s s' := by
  unfold De
  ring

end Objects

def DeSlotAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (j : Fin n) (M N A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ i, IsSmoothHerm (L i)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P (Function.update L j (M.tensor N)) A A' s s' =
      De P (Function.update L j M) A A' s s' + De P (Function.update L j N) A A' s s'

def SemiPosTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (M : HermLine ι),
    IsSmoothHerm M → ∃ T : HermLine ι, IsSmoothHerm T ∧ IsSemiPosHerm T ∧ IsSemiPosHerm (M.tensor T)

def DeLeSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSemiPosHerm (L j)) →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P L A A' s s' ≤ 0

theorem isSectionOn_coordinate_plane (i : Fin 3) : IsSectionOn (⊥ : Ideal (MRing (PBlk 3))) (fsLine 3) (Xc 3 i) := by
  refine ⟨fun _ => 1, fun _ => rfl, fun m hm k => ?_, ?_⟩
  · rw [support_X, Finset.mem_singleton] at hm
    subst hm
    simp [Finsupp.single_apply]
  · rw [Submodule.mem_bot]
    exact X_ne_zero _

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem multiConeMap_ww_comp_yyEmb {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) (j : Fin 2) :
    (T.multiConeMap (T.wwCoord x δ e φ (a 0) (a 1))).comp
        (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
      (rename (diagonalBlockIndex j) : MvPolynomial T.YBlk Φ →ₐ[Φ] MvPolynomial T.WBlk Φ).toRingHom.comp
        (T.multiConeMap (T.yyCoord x δ e φ (a j))) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [T.multiConeMap]
  · rcases p with ⟨_ | _ | _, i⟩
    · simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]
    · simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]
    · fin_cases j <;> simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]

theorem comap_wwIdeal_yyEmb {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) (j : Fin 2) :
    (T.wwIdeal x δ e φ (a 0) (a 1)).comap
        (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
      T.yyIdeal x δ e φ (a j) := by
  ext f
  rw [Ideal.mem_comap, T.wwIdeal, T.yyIdeal, RingHom.mem_ker, RingHom.mem_ker, ← RingHom.comp_apply,
    multiConeMap_ww_comp_yyEmb, RingHom.comp_apply]
  exact map_eq_zero_iff _ (rename_injective _ (segreBlockEmbedding_injective j))

theorem wwDeg_sub_eq_llDeg (n : ℕ) :
    (fun k => (T.wwDeg n 1 k : ℤ) - (T.wwDeg (n + 3) 0 k : ℤ)) = T.llDeg := by
  funext k
  cases k <;> simp [T.wwDeg, T.llDeg, T.unitDeg]

theorem FibreProduct.proof (hWW : WWArithVar.Statement) (hDD : DiagDiv.Statement)
    (hDP : DiagPull.Statement) : FibreProduct.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ D a hs hg hd hc hbase hind
  obtain ⟨hY, hW, hΔ⟩ := hWW Ω ι ν κ E Φ x B e φ δ hs hg hd D hbase a hind
  obtain ⟨hex, hdiv⟩ := hDD Ω ι ν κ E Φ x B e φ δ hs hg hd hc a hind
  exact ⟨⟨hY, hW⟩, comap_wwIdeal_yyEmb x δ e φ a, hΔ, ⟨wwDeg_sub_eq_llDeg, T.two_llDeg⟩, hex, hdiv,
    (hDP Ω ι ν κ E Φ x e φ δ (a 0)).2.1⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial GroundTheory.Heights₂.Heights.Bridge GroundTheory.Heights₂.Heights.Bridge.GeoNum
  GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

theorem C_charOf_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) :
    (C ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by
  have h : ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) ∈
      V.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := by
    rw [← Submodule.IsPrincipal.span_singleton_generator (V.comap C), Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr dvd_rfl
  exact h

theorem GeoNumCut.full : GeoNumCut.Statement := by
  intro K _ ι _ V n a b t hV hp hdim ht htV
  classical
  set p := ReciprocityTheory.ChartRestriction.G.Geo.charOf V with hp_def
  have : Fact p.Prime := ⟨hp⟩
  have hpV : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := C_charOf_mem V
  have hker : RingHom.ker (red (ι := ι) p) ≤ V := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpV
  have hcm : (V.map (red p)).comap (red p) = V := comap_map_eq p hker
  have : V.IsPrime := hV.1

  have hQ : IsMultiProjPrime (V.map (red p)) := by
    refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) hker, ?_, ?_⟩
    · rw [isMultiHomogIdeal_iff]
      obtain ⟨S, hS, hVS⟩ := hV.2.1
      refine ⟨red p '' S, ?_, by rw [hVS, Ideal.map_span]⟩
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨c, hc⟩ := hS f hf
      exact ⟨c, fun m hm k => hc m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [← isRelevant_comap_iff p, hcm]
      exact hV.2.2
  have hd : relDim (V.map (red p)) = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))
    rw [hcm] at this
    exact this.symm

  have htr : IsMultiHomog (red p t) b := by
    rw [isMultiHomog_iff]
    exact fun m hm k => ht m (MvPolynomial.support_map_subset _ _ hm) k
  have htrV : red p t ∉ V.map (red p) := by
    intro h
    apply htV
    rw [← hcm]
    exact h

  rw [← intNum_map_eq_geoNum p (n + 1) V hV hpV hdim,
    CutRegular.full (ZMod p) K ι (V.map (red p)) hQ n hd b (red p t) htr htrV a]
  have hcut := cycEval_divCycle_eq p (V.map (red p)) t
    (fun W => intNum (ZMod p) W a) (fun W => ReciprocityTheory.ChartRestriction.G.Geo.geoNum n W a)
    (fun W' hW' => by
      obtain ⟨hW'm, hW'd⟩ :=
        DivCycleSupport.full (ZMod p) K ι (V.map (red p)) hQ n hd b _ htr htrV W' hW'
      exact intNum_eq_geoNum_comap p n W' hW'm hW'd a)
  rw [hcm] at hcut
  exact hcut

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIMultilin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace ThmIMultilin

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_update {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ i, IsSmoothHerm (L i)) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : ∀ i, IsSmoothHerm (Function.update L j X i) := by
  intro i
  by_cases h : i = j
  · subst h
    simpa using hX
  · simpa [Function.update_of_ne h] using hL i

omit [∀ k, Fintype (ι k)] in

theorem update_comp_swap {m : ℕ} (L : Fin (m + 1) → HermLine ι) (j : Fin (m + 1)) (X : HermLine ι) :
    Function.update L j X ∘ Equiv.swap j (Fin.last m) =
      Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · have hne : Equiv.swap j (Fin.last m) i.castSucc ≠ j := by
      intro h
      have h' : Equiv.swap j (Fin.last m) i.castSucc = Equiv.swap j (Fin.last m) (Fin.last m) := by
        rw [h, Equiv.swap_apply_right]
      exact Fin.castSucc_ne_last i ((Equiv.swap j (Fin.last m)).injective h')
    simp [Function.update_of_ne hne]

end ThmIMultilin

theorem ThmIMultilin.proof (hS : ThmISymm.Statement) : ThmIMultilin.Statement := by
  intro K _ ι _ I hR P n L j A B hP hL hA hB
  cases n with
  | zero => exact j.elim0
  | succ m =>
    have hAB : IsSmoothHerm (A.tensor B) := isSmoothHerm_tensor hA hB
    have e : ∀ X : HermLine ι, IsSmoothHerm X →
        I P (m + 1) (Function.update L j X) =
          I P (m + 1) (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
      intro X hX
      rw [← ThmIMultilin.update_comp_swap]
      exact (hS K ι I hR P (m + 1) _ _ hP (ThmIMultilin.smooth_update hL j hX)).symm
    have hM : ∀ i : Fin m, IsSmoothHerm (L (Equiv.swap j (Fin.last m) i.castSucc)) := fun i => hL _
    rw [e _ hAB, e A hA, e B hB]
    exact hR.1 P m _ A B hP hM hA hB

end GroundTheory.Heights₂.Heights.Inter
end

