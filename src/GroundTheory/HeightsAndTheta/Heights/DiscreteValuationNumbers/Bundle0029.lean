import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]

abbrev localQuot (P U : Ideal R) [U.IsPrime] : Type _ :=
  Localization.AtPrime U ⧸ P.map (algebraMap R (Localization.AtPrime U))

def localQuotMap (P U : Ideal R) [U.IsPrime] : R →+* localQuot P U :=
  (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime U))

end Defs

section Lemmas

def LocalQuotRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P.IsPrime → P ≤ U →
    IsDomain (localQuot P U) ∧ IsLocalRing (localQuot P U) ∧
      (∀ y : localQuot P U, IsUnit y ↔ y ∉ U.map (localQuotMap P U)) ∧
      ∀ x : R, localQuotMap P U x = 0 ↔ x ∈ P

def LocalQuotPrimes.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    (∀ W : Ideal R, W.IsPrime → P ≤ W → W ≤ U →
      (W.map (localQuotMap P U)).IsPrime ∧ (W.map (localQuotMap P U)).comap (localQuotMap P U) = W) ∧
    ∀ p : Ideal (localQuot P U), p.IsPrime →
      P ≤ p.comap (localQuotMap P U) ∧ p.comap (localQuotMap P U) ≤ U ∧
        (p.comap (localQuotMap P U)).map (localQuotMap P U) = p

def LocCycleLocalQuot.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (J W : Ideal R), P ≤ J → W.IsPrime → P ≤ W →
    W ≤ U → locCycle J W = locCycle (J.map (localQuotMap P U)) (W.map (localQuotMap P U))

def LocalQuotColon.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (f g : R),
    ((P ⊔ Ideal.span {f}).colon {g}).map (localQuotMap P U) =
      (Ideal.span {localQuotMap P U f}).colon {localQuotMap P U g}

def LocalQuotFinsum.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    ∀ (F : Ideal R → ℤ) (F' : Ideal (localQuot P U) → ℤ),
      (∀ G, F G ≠ 0 → G.IsPrime ∧ P ≤ G ∧ G ≤ U) → (∀ p, F' p ≠ 0 → p.IsPrime) →
      (∀ G : Ideal R, G.IsPrime → P ≤ G → G ≤ U → F G = F' (G.map (localQuotMap P U))) →
      ∑ᶠ G, F G = ∑ᶠ p, F' p

def LocalCoeffLocal.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    ∀ f g s u v : A, f ≠ 0 → g ≠ 0 → s ≠ 0 → IsUnit u → u * f = v * g →
    (∀ W : Ideal A, locCycle (Ideal.span {s}) W ≠ 0 →
      locCycle (Ideal.span {f}) W = locCycle (Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      ∑ᶠ W, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ (Ideal.span {f}).colon {g}) (IsLocalRing.maximalIdeal A)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeLinesIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairConeLinesIndep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (Φ : Type) [Field Φ] [Algebra Ω Φ] (K : Type) (N : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E),
    LinearIndependent Ω ψ → ∀ (t : Fin N → Φ), AlgebraicIndependent Ω t → ∀ g : Φ, g ≠ 0 →
      AlgebraicIndependent
        (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
        (Sum.elim (fun i : Fin N => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))) * X (some none))
          (fun _ : Unit => (C g * X none : MvPolynomial (Option (Option K)) Φ)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSpanBundleTrdegGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def SpanBundleTrdegGe.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) (ι : K → Type) (y : (Σ k, ι k) → Ω) (M i : ℕ) (G : Fin M → Fin i → Ω),
    LinearIndependent Ω (fun j l => G l j) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
        Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSpanBundleTrdegLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SpanBundleTrdegLe.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω) (M i : ℕ) (G : Fin M → Fin i → Ω)
    (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ),
      Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ≤
        Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTruncSpecialize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TruncSpecialize.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (w : Module.Basis (Fin N) Ω E)
    (M : ℕ) (φ : Fin M → Module.Dual Ω E) (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ),
    AlgebraicIndependent Ω t → ∀ i : Fin N,
      projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ≤ projIdeal F y w φ (truncCoord t i) ∧
      ∀ x z : MRing (bundleIdx ι M) F,
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) x =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) z →
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t i)) x = 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WeilNumbersImpVerticalDivisorsCommute
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace VerticalDivisorsCommuting

def CartierStatement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (n : ℕ) (b b' : K → ℤ) (f g f' g' : MRing ι O)
      (L : Fin n → K → ℤ) (Iκ : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι),
      IndefiniteRowSideFullHecke.NumbersDVR.IsModelOver P (n + 1) → IsVerticalDivisor P ϖ b f g →
      IsVerticalDivisor P ϖ b' f' g' → ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection Iκ →
      IndefiniteRowSideFullHecke.NumbersDVR.redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b'))
                                (IndefiniteRowSideFullHecke.NumbersDVR.divO P f g) =
        IndefiniteRowSideFullHecke.NumbersDVR.redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b))
          (IndefiniteRowSideFullHecke.NumbersDVR.divO P f' g')

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem intNum_snoc {F : Type u} [Field F] (V : Ideal (MRing ι F)) {n : ℕ} (L : Fin n → K → ℤ)
    (b : K → ℤ) :
    intNum F V (Fin.snoc (α := fun _ => K → ℤ) L b) = intNum F V (Matrix.vecCons b L) := by
  rw [← CutByFormField.vecCons_comp_finRotate]
  exact FieldNumbers.IntNumSymm.proof F K ι V (n + 1) _ _

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNum_snoc (W : Ideal (MRing ι O)) {n : ℕ} (L : Fin n → K → ℤ) (b : K → ℤ) :
    vNum W (Fin.snoc (α := fun _ => K → ℤ) L b) = vNum W (Matrix.vecCons b L) :=
  intNum_snoc _ L b

theorem redEval_divO (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (P : Ideal (MRing ι O)) (f g : MRing ι O) :
    IndefiniteRowSideFullHecke.NumbersDVR.redEval J (IndefiniteRowSideFullHecke.NumbersDVR.divO P f g) =
      cycEval (fun W => J (specialIdeal W)) (ratDiv P f g) := by
  rw [Objects.redEval_eq_cycEval]
  congr 1
  funext W
  exact Objects.divO_eq_ratDiv P f g W

theorem isProjVarF_specialIdeal (hDim : ComponentDim.Statement.{u}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {a : K → ℕ} {f : MRing ι O}
    (hf : IsMultiHomog f a) (hfP : f ∉ P) {W : Ideal (MRing ι O)} (hW : divCycle P f W ≠ 0)
    (hϖW : (C ϖ : MRing ι O) ∈ W) : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d := by
  have hmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by unfold divCycle; rw [dif_neg h])
  have hWp : W.IsPrime := hmin.1.1.1
  have hWh : IsMultiHomogIdeal W :=
    (Objects.isMultiHomogIdeal_iff W).mpr
      (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
        ((Objects.isMultiHomogIdeal_iff P).mp hP.multiProj.multiHomog)
        ((Objects.isMultiHomog_iff f a).mp hf) hmin.1)
  obtain ⟨hpr, -, hrel, -⟩ := SpecialIdealCorresp.proof O ϖ hϖ K ι P W hWp hϖW
  refine ⟨(Objects.isMultiProjPrime_iff _).mp
    ⟨hpr, SpecialIdealMultiHomog.proof O K ι W hWh, hrel.mp hmin.2⟩, ?_⟩
  have := SpecialQuotDim.proof O ϖ hϖ K ι W hϖW
  rw [hDim O ϖ hϖ K ι P d hP a f hf hfP W hW hϖW] at this
  exact this

theorem cycEval_family (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) {ϖ : O}
    (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {n : ℕ} (hP : IsModelOver P (n + 1)) {b : K → ℤ}
    {f g : MRing ι O} (hD : IsVerticalDivisor P ϖ b f g)
    (Iκ : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection Iκ) (M : Fin (n + 1) → K → ℤ) :
    cycEval (fun W => Iκ (specialIdeal W) (n + 1) M) (ratDiv P f g) =
      cycEval (fun W => vNum W M) (ratDiv P f g) := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases h0 : ratDiv P f g W = 0
  · rw [h0, zero_mul, zero_mul]
  · have hϖW := hD.vertical W h0
    obtain ⟨α, β, hα, hβ, -⟩ := hD.degrees
    have hV : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) (n + 1) := by
      by_cases hf : divCycle P f W = 0
      · have hg : divCycle P g W ≠ 0 := fun hg => h0 (by rw [ratDiv, hf, hg, sub_zero])
        exact isProjVarF_specialIdeal hDim hϖ hP hβ hD.den_not_mem hg hϖW
      · exact isProjVarF_specialIdeal hDim hϖ hP hα hD.num_not_mem hf hϖW
    dsimp only
    rw [Numbers.agree_of hBase hCut FieldNumbers.ExistsForm.proof FieldNumbers.DivCycleSupport.proof
      Iκ hI (specialIdeal W) (n + 1) M hV]
    rfl

end VerticalDivisorsCommuting

theorem VerticalDivisorsCommuting.cartier_imp (hN : Numbers.Statement.{u}) :
    VerticalDivisorsCommuting.CartierStatement.{u} → VerticalDivisorsCommute.Statement.{u} := by
  intro H O _ _ _ ϖ hϖ K _ _ ι _ P d hP b b' f g f' g' hD hD' L
  have h := H O ϖ hϖ K ι P d b b' f g f' g' L (fun V _ M => intNum _ V M)
    ((Objects.isModelOver_iff P _).mp hP) hD hD' (hN _ K ι)
  simp only [VerticalDivisorsCommuting.redEval_divO, VerticalDivisorsCommuting.intNum_snoc] at h
  exact h

theorem VerticalDivisorsCommuting.imp_cartier (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) :
    VerticalDivisorsCommute.Statement.{u} → VerticalDivisorsCommuting.CartierStatement.{u} := by
  intro H O _ _ _ ϖ hϖ K _ _ ι _ P n b b' f g f' g' L Iκ hP hD hD' hI
  have hP' := (Objects.isModelOver_iff P _).mpr hP
  rw [VerticalDivisorsCommuting.redEval_divO, VerticalDivisorsCommuting.redEval_divO,
    VerticalDivisorsCommuting.cycEval_family hBase hCut hDim hϖ hP' hD Iκ hI (Fin.snoc (α := fun _ => K → ℤ) L b'),
    VerticalDivisorsCommuting.cycEval_family hBase hCut hDim hϖ hP' hD' Iκ hI (Fin.snoc (α := fun _ => K → ℤ) L b)]
  simp only [VerticalDivisorsCommuting.vNum_snoc]
  exact H O ϖ hϖ K ι P n hP' b b' f g f' g' hD hD' L

theorem VerticalDivisorsCommuting.equiv (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) (hDim : ComponentDim.Statement.{u}) :
    VerticalDivisorsCommute.Statement.{u} ↔ VerticalDivisorsCommuting.CartierStatement.{u} :=
  ⟨VerticalDivisorsCommuting.imp_cartier hBase hCut hDim, VerticalDivisorsCommuting.cartier_imp (Numbers.proof hBase hCut)⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ZeroLeDivCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem zero_le_divCycle {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) (W : Ideal (MRing ι R)) : 0 ≤ divCycle P f W := by
  unfold divCycle
  split_ifs <;> positivity

theorem BlowUpExcessDecreases.proof (hpos : ExcessPositive.Statement.{u})
    (hres : ResidualComparison.Statement.{u}) (hexc : ExceptionalComparison.Statement.{u}) :
    BlowUpExcessDecreases.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH hcommon
  set N := commonExcess ϖ P f g s with hN
  have hε : 0 < N := hpos O ϖ hϖ K ι P d hP b f g hD s hsP hcommon

  have hbdd : BddAbove (Set.range fun G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G} =>
      (divCycle P s G.1 * ratDiv P f g G.1).toNat) := by
    refine (((DivCycleFiniteSupport.proof O K ι P s).image
      fun G => (divCycle P s G * ratDiv P f g G).toNat).insert 0).bddAbove.mono ?_
    rintro _ ⟨G, rfl⟩
    by_cases h : divCycle P s G.1 = 0
    · left; simp [h]
    · right; exact ⟨G.1, h, rfl⟩
  have hle : ∀ G, (C ϖ : MRing ι O) ∈ G → ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → x ≤ divCycle P s G →
      y ≤ ratDiv P f g G → x * y ≤ N := by
    intro G hG x y hx hy hxG hyG
    have h1 : (divCycle P s G * ratDiv P f g G).toNat ≤ N := le_ciSup hbdd ⟨G, hG⟩
    have h2 : x * y ≤ divCycle P s G * ratDiv P f g G := mul_le_mul hxG hyG hy (hx.trans hxG)
    exact h2.trans ((Int.self_le_toNat _).trans (by exact_mod_cast h1))

  have hterm : ∀ x y : ℤ, 0 ≤ x → (0 < x → 0 < y → x * y < N) → (x * y).toNat ≤ N - 1 := by
    intro x y hx h
    rcases lt_or_ge 0 x with hx' | hx'
    · rcases lt_or_ge 0 y with hy | hy
      · have h1 := h hx' hy
        generalize x * y = p at h1 ⊢
        omega
      · have h1 : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx hy
        generalize x * y = p at h1 ⊢
        omega
    · obtain rfl : x = 0 := le_antisymm hx' hx
      simp
  have hne : Nonempty {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O) //
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G'} := ⟨⟨⊤, Submodule.mem_top⟩⟩
  constructor
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m)
        (liftForm s) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hres O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ hx.le (by linarith) h1 h2
      nlinarith
    omega
  ·
    have h : commonExcess ϖ (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) (newVar none) ≤ N - 1 := by
      refine ciSup_le fun G' => hterm _ _ (zero_le_divCycle _ _ _) fun hx hy => ?_
      obtain ⟨G, hG, h1, h2⟩ :=
        hexc O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G'.1 G'.2 hx hy
      have h3 := hle G hG _ _ (by linarith) hy.le h1 h2
      nlinarith
    omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end

