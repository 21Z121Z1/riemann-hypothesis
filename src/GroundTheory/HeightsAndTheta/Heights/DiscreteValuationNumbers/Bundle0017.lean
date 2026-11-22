import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem IntNumIsFieldIntersection.of_intNumBase_cutRational
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) :
    IntNumIsFieldIntersection.Statement.{u} :=
  IntNumIsFieldIntersection.proof VocabMultiHomog.proof
    (VocabMultiHomogIdeal.proof VocabMultiHomog.proof) VocabDivCycle.proof
    (IntNumPoint.proof hBase) (IntNumRatSection.proof hCut)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpVerticalPush.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ a : Fin n → K → ℤ,
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing (extIdx ι J) O) ∈ W then vNum W (liftDegs a) else 0)
          (divCycle (blowUpOf P u) (liftForm x))) =
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) (divCycle P x))

def BlowUpDivisorPush.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ a : Fin n → K → ℤ,
      cycEval (fun G => vNum G (liftDegs a)) (ratDiv (blowUpOf P u) (liftForm (J := J) f) (liftForm g)) =
        cycEval (fun G => vNum G a) (ratDiv P f g)

def BlowUpHorizontalCorresp.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    (∀ h : Ideal (MRing ι O) → ℤ,
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing (extIdx ι J) O) ∈ W then 0
            else h (W.comap (liftForm (ι := ι) (J := J) (R := O))))
          (divCycle (blowUpOf P u) (liftForm x))) =
      (open Classical in
        cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then 0 else h W) (divCycle P x))) ∧
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      divCycle P x (W.comap (liftForm (ι := ι) (J := J) (R := O))) ≠ 0 ∧
      ((∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) →
        W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u)

def HorizontalComponentModel.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), divCycle P x W ≠ 0 → (C ϖ : MRing ι O) ∉ W → IsModelOver W d

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalAddOfFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

private theorem cycEval_add_of_finite {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    (φ : Ideal (MRing ι R) → ℤ) {Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite) :
    cycEval φ (Z₁ + Z₂) = cycEval φ Z₁ + cycEval φ Z₂ := by
  unfold cycEval
  have f₁ : (Function.support fun W => Z₁ W * φ W).Finite :=
    h₁.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => Z₂ W * φ W).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [← finsum_add_distrib f₁ f₂]
  refine finsum_congr fun W => ?_
  simp only [Pi.add_apply]
  ring

theorem RightSideMultiplicativeInForm.proof (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : RightSideMultiplicativeInForm.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g s₁ s₂ hs₁ hs₂ L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  unfold cutIdentityRightSide
  rw [h₁ O K ι P s₁ s₂ hPp hs₁ hs₂]
  exact cycEval_add_of_finite _ (h₂ O K ι P s₁) (h₂ O K ι P s₂)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleEqZeroOfFormNotMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_nonneg (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by
  unfold divCycle
  split_ifs <;> simp

theorem divCycle_eq_zero_of_form_not_mem (P : Ideal (MRing ι R)) {x : MRing ι R} {W : Ideal (MRing ι R)}
    (hx : x ∉ W) : divCycle P x W = 0 := by
  unfold divCycle
  rw [dif_neg]
  exact fun h => hx (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end

theorem ExcessPositive.proof : ExcessPositive.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP ⟨G, hϖG, hsG, hDG⟩
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hGdef : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant G := by
    by_contra h
    exact hsG (by unfold divCycle; rw [dif_neg h])
  have hGp : G.IsPrime := hGdef.1.1.1
  have hPG : P ≤ G := le_sup_left.trans hGdef.1.1.2
  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGp hPG hGdef.2
  have huP : u ∉ P := fun h => huG (hPG h)
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have hvP : v ∉ P := by
    intro hv
    have h1 : u * f ∈ P := by
      have h2 := P.add_mem huv (P.mul_mem_right g hv)
      rwa [sub_add_cancel] at h2
    exact (hPp.mem_or_mem h1).elim huP hfP
  have hcyc : divCycle P (u * f) G = divCycle P (v * g) G :=
    congrFun (divCycle_congr_of_sub_mem huv) G
  have huf := congrFun (DivCycleMul.proof O K ι P u f hPp huP hfP) G
  have hvg := congrFun (DivCycleMul.proof O K ι P v g hPp hvP hgP) G
  simp only [Pi.add_apply] at huf hvg
  have hu0 := divCycle_eq_zero_of_form_not_mem P huG
  have hv0 := divCycle_nonneg P v G
  have hs0 := divCycle_nonneg P s G
  have hDpos : 0 < ratDiv P f g G := by
    unfold ratDiv at hDG ⊢
    omega
  have hprod : 0 < (divCycle P s G * ratDiv P f g G).toNat := by
    have : 0 < divCycle P s G * ratDiv P f g G := mul_pos (lt_of_le_of_ne hs0 (Ne.symm hsG)) hDpos
    omega

  have hfin := DivCycleFiniteSupport.proof.{u} O K ι P s
  have hbdd : BddAbove (Set.range fun G' : {G' : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G'} =>
      (divCycle P s G'.1 * ratDiv P f g G'.1).toNat) := by
    apply Set.Finite.bddAbove
    apply ((hfin.image fun G' => (divCycle P s G' * ratDiv P f g G').toNat).insert 0).subset
    rintro _ ⟨G', rfl⟩
    by_cases h : divCycle P s G'.1 = 0
    · left
      simp [h]
    · right
      exact ⟨G'.1, h, rfl⟩
  exact lt_of_lt_of_le hprod (le_ciSup hbdd ⟨G, hϖG⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSub
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsModelOver mcIdeal joinCoord fnField mseg SameGeneric FlagModel FlagPair IsPull
  IsVertDiv pairNum pullDeg liftVar ptCoord noCoord ptIdx noIdx ptFlagModel stdE cE unif unif_frac_ne unif_ne_zero
  sameGeneric_cE pt_model mcIdeal_of_one frac_inj isModelOver_bot card_sigma_of_point fnField_of_one
  isPull_frame_of_one ptCoord_eq)

def FlagModelJoinLeftAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' →
    ∀ (F : FlagModel O x d N E E') (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (w : (Σ k, ι₂ k) → Ω),
      IsModelOver O (mcIdeal O (joinCoord x (joinCoord F.z w))) d →
      fnField O (joinCoord x (joinCoord F.z w)) = fnField O x →
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord F.z w))) N V,
      IsPull O x (joinCoord F.z w) E EB → IsPull O x (joinCoord F.z w) E' E'B →
    ∃ φ : FlagPair O (joinCoord x (joinCoord F.z w)) EB E'B,
      ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim F.ι' ι₂)))
        (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F.ι')),
        IsFieldIntersection I → IsFieldIntersection I₁ →
      ∀ (G : MvPolynomial (Fin N) ℤ) (r : ℕ) (y y' : Fin r → K → ℤ)
        (f g : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
        (∀ l, IsVertDiv O (mcIdeal O x) (y l - y' l) (f l) (g l)) →
      ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
        Q.IsHomogeneous (d + 1 - c) →
        F.value O I₁ G y y' f g Q =
          pairNum O I (mcIdeal O (joinCoord x (joinCoord F.z w))) d
            (Fin.append φ.deg fun l => pullDeg (K' := F.K' ⊕ K₂) (y l))
            (Fin.append φ.deg' fun l => pullDeg (K' := F.K' ⊕ K₂) (y' l))
            (Fin.append φ.f fun l => rename (liftVar (Sum.elim F.ι' ι₂)) (f l))
            (Fin.append φ.g fun l => rename (liftVar (Sum.elim F.ι' ι₂)) (g l))
            (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

namespace FlagModelJoinLeftAlt

end FlagModelJoinLeftAlt

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsModelOver mcIdeal joinCoord fnField mseg SameGeneric FlagModel FlagPair IsPull
  IsVertDiv pairNum pullDeg liftVar ptCoord noCoord ptIdx noIdx ptFlagModel stdE cE unif unif_frac_ne unif_ne_zero
  sameGeneric_cE pt_model mcIdeal_of_one frac_inj isModelOver_bot card_sigma_of_point fnField_of_one
  isPull_frame_of_one ptCoord_eq)

def FlagModelJoinRightAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' →
    ∀ (F : FlagModel O x d N E E') (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (w : (Σ k, ι₂ k) → Ω),
      IsModelOver O (mcIdeal O (joinCoord x (joinCoord w F.z))) d →
      fnField O (joinCoord x (joinCoord w F.z)) = fnField O x →
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord w F.z))) N V,
      IsPull O x (joinCoord w F.z) E EB → IsPull O x (joinCoord w F.z) E' E'B →
    ∃ φ : FlagPair O (joinCoord x (joinCoord w F.z)) EB E'B,
      ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim ι₂ F.ι')))
        (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F.ι')),
        IsFieldIntersection I → IsFieldIntersection I₁ →
      ∀ (G : MvPolynomial (Fin N) ℤ) (r : ℕ) (y y' : Fin r → K → ℤ)
        (f g : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
        (∀ l, IsVertDiv O (mcIdeal O x) (y l - y' l) (f l) (g l)) →
      ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
        Q.IsHomogeneous (d + 1 - c) →
        F.value O I₁ G y y' f g Q =
          pairNum O I (mcIdeal O (joinCoord x (joinCoord w F.z))) d
            (Fin.append φ.deg fun l => pullDeg (K' := K₂ ⊕ F.K') (y l))
            (Fin.append φ.deg' fun l => pullDeg (K' := K₂ ⊕ F.K') (y' l))
            (Fin.append φ.f fun l => rename (liftVar (Sum.elim ι₂ F.ι')) (f l))
            (Fin.append φ.g fun l => rename (liftVar (Sum.elim ι₂ F.ι')) (g l))
            (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

namespace FlagModelJoinRightAlt

end FlagModelJoinRightAlt

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExceptionalDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem BlowUpReduction.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hinv : BlowUpInvariance.Statement.{u}) (hcf : CommonFactorRemoval.Statement.{u})
    (hadd : AdditivityInDivisor.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (htaut : TautologicalCase.Statement.{u}) :
    BlowUpReduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L hId₁ hId₀
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  obtain ⟨hinvl, hinvr⟩ := hinv O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L
  set Q := blowUpOf P (blowUpGens s g f m e)
  set Y₀ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar none
  set Y₁ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar (some none)
  have hQ : Q.IsPrime := hmodel.multiProj.isPrime
  have hfmQ := hE.1.num_not_mem
  have hgYQ := hE.1.den_not_mem
  rw [map_mul] at hfmQ
  have hfQ : liftForm f ∉ Q := fun h => hfmQ (Q.mul_mem_right _ h)
  have hgQ : liftForm g ∉ Q := fun h => hgYQ (Q.mul_mem_right _ h)
  have hqQ : liftForm m * Y₁ ∉ Q := fun h =>
    (hQ.mem_or_mem h).elim hD₁.1.den_not_mem hD₁.1.num_not_mem

  have hcfq := hcf O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel (liftDeg b) (liftForm f)
    (liftForm g) (liftForm m * Y₁) (liftForm s) hfQ hgQ hqQ hslP (fun H hH hϖH => by
      obtain ⟨h₁, h₂⟩ := hH₁ H hH hϖH
      have hHp := isPrime_of_divCycle_ne_zero hH
      refine ⟨fun h => h₂.num_not_mem ?_, fun h => h₂.den_not_mem (H.mul_mem_right _ h),
        fun h => (hHp.mem_or_mem h).elim h₁.den_not_mem h₁.num_not_mem⟩
      rw [map_mul]; exact H.mul_mem_right _ h) (liftMDeg c) (liftDegs L)
  obtain ⟨haddl, haddr⟩ := hadd O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ _
    hD₁.1 hE.1 (liftMDeg c) (liftForm s) hsl hslP hH₁ (liftDegs L)
  have hnum : Y₁ * liftForm (f * m) = liftForm f * (liftForm m * Y₁) := by rw [map_mul]; ring
  have hden : liftForm m * (liftForm g * Y₁) = liftForm g * (liftForm m * Y₁) := by ring
  have hdeg : residualDeg e + exceptionalDeg b e = liftDeg b := by
    funext o; cases o <;> simp [residualDeg, exceptionalDeg, liftDeg]
  rw [hnum, hden, hcfq.1] at haddl
  rw [hnum, hden, hdeg, hcfq.2] at haddr

  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hE.1.degrees
  have ht := htaut O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf bg hbf hbg hb
    (liftDegs L)
  have hdegs : liftMDeg c + bg = bf + Pi.single none 1 := by
    funext o
    have h := congrFun hb o
    cases o with
    | none => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; omega
    | some k => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; have := he k; omega
  have hl₁ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 (liftMDeg c) bg
    (liftDegs L)
  have hl₂ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf
    (Pi.single none 1) (liftDegs L)
  rw [hdegs] at hl₁
  have hrel := cutIdentityRightSide_congr_of_sub_mem ϖ Q (exceptionalDeg b e) (liftForm (f * m))
    (liftForm g * Y₁) (blowUp_relation P s g f m e) (liftDegs L)
  have hsg : liftForm (s * g) * Y₁ = liftForm s * (liftForm g * Y₁) := by rw [map_mul]; ring
  rw [hsg, hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hslP hE.1.den_not_mem,
    hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hE.1.num_not_mem hY₀P] at hrel
  rw [cutIdentity_iff] at hId₁ hId₀ ⊢
  rw [← hinvl, ← hinvr]
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IdealCycleSupportFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem idealCycle_support_finite {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    [IsNoetherianRing (MRing ι R)] (J : Ideal (MRing ι R)) :
    (Function.support (idealCycle J)).Finite := by
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J)
  intro W hW
  by_contra hmin
  apply hW
  unfold idealCycle
  rw [dif_neg]
  exact fun h => hmin h.1

theorem finsum_mul_finsum_comm {α β : Type*} (a : α → ℤ) (c : α → β → ℤ) (n : β → ℤ)
    (ha : (Function.support a).Finite) (hc : ∀ W, (Function.support (c W)).Finite) :
    ∑ᶠ W, a W * ∑ᶠ U, c W U * n U = ∑ᶠ U, (∑ᶠ W, a W * c W U) * n U := by
  classical
  set S := ha.toFinset
  set T := S.biUnion (fun W => (hc W).toFinset)
  have hcT : ∀ W ∈ S, Function.support (c W) ⊆ ↑T := by
    intro W hW U hU
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨W, hW, (hc W).mem_toFinset.mpr hU⟩
  have hin : ∀ U, ∑ᶠ W, a W * c W U = ∑ W ∈ S, a W * c W U := by
    intro U
    apply finsum_eq_sum_of_support_subset
    intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW
  simp_rw [hin]
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := T)]
  · rw [Finset.sum_congr rfl (g := fun W => a W * ∑ U ∈ T, c W U * n U)]
    · simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    · intro W hW
      congr 1
      apply finsum_eq_sum_of_support_subset
      intro U hU
      exact hcT W hW (left_ne_zero_of_mul hU)
  · intro U hU
    obtain ⟨W, hW, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hU)
    exact hcT W hW (right_ne_zero_of_mul hne)
  · intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW

theorem RightExpansion.proof (hV : VertCutEff.Statement.{u})
    (hD : DivisorIdealCycle.Statement.{u}) : RightExpansion.Statement.{u} := by
  classical
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hmodel b f g heff c s hs hsP hhor hnc L
  have hPmh : IsMultiHomogIdeal (P ⊔ Ideal.span {s}) :=
    SupSpanMultiHomog.proof O K ι P s c hmodel.multiProj.multiHomog hs
  have key : ∀ W : Ideal (MRing ι O),
      divCycle P s W * (if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) =
        divCycle P s W * cycEval (fun U => vNum U L) (idealCycle (W ⊔ divisorIdeal P f g)) := by
    intro W
    by_cases hW : divCycle P s W = 0
    · rw [hW, zero_mul, zero_mul]
    congr 1
    obtain ⟨hWp, hPW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
      unfold divCycle at hW
      split_ifs at hW with h
      · exact h.1
      · exact absurd rfl hW
    split_ifs with hϖW
    · exact hV O ϖ hϖ K ι P d hmodel b f g heff W s hsP hWmin hWrel
        (MinimalPrimeMultiHomog.proof O K ι _ W hPmh hWmin) hϖW (hnc W hϖW hW) L
    · have hv := hhor W hW hϖW
      have hP : P.IsPrime := hmodel.multiProj.isPrime
      rw [hD O K ι P W f g g f hP hWp hPW heff.1.den_not_mem
        (fun U hU hWU hUrel => heff.2 U hU (hPW.trans hWU) hUrel)
        hv.den_not_mem hv.num_not_mem (by rw [mul_comm, sub_self]; exact P.zero_mem)]
  exact (finsum_congr key).trans <| finsum_mul_finsum_comm _ (fun W U => idealCycle (W ⊔ divisorIdeal P f g) U) _
    (DivCycleFiniteSupport.proof O K ι P s) (fun W => idealCycle_support_finite _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord midDeg midVar ptCoord ptFlagModel)

def JoinVerticalDivisorRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (b : K ⊕ K' → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
    IsVertDiv O (mcIdeal O (joinCoord x z)) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x (joinCoord w z))) (midDeg (K₂ := K₂) b)
      (rename (midVar ι₂) f) (rename (midVar ι₂) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

