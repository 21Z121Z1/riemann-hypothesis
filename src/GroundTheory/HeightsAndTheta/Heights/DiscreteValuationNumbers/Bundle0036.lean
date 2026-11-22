import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureNumber

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointFlagModel
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart pullDeg liftVar ptIdx ptCoord chartMon
  IsGradedFrame IsUnitOn FlagPair IsPull fnField IsVertDiv mcIdeal)

namespace JoinPointFlagModel

section Charts

variable {Ω : Type*} [Field Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def extChart (t : ∀ k, ι k) : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k
  | .inl k => t k
  | .inr _ => (0 : Fin 1)

theorem restrictChart_extChart (t : ∀ k, ι k) : restrictChart (extChart t) = t :=
  rfl

theorem mseg_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    mseg (joinCoord y (ptCoord (Ω := Ω))) s = mseg y (restrictChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart]

theorem chartMon_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : K → ℤ) :
    chartMon (joinCoord y (ptCoord (Ω := Ω))) s (pullDeg a) = chartMon y (restrictChart s) a := by
  simp only [chartMon, Fintype.prod_sum_type]
  simp [joinCoord, ptCoord, restrictChart, pullDeg]

variable (O : Type*) [CommRing O] [Algebra O Ω]

theorem chartRing_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) :
    chartRing O (mseg (joinCoord y (ptCoord (Ω := Ω)))) s = chartRing O (mseg y) (restrictChart s) := by
  unfold chartRing
  congr 1
  ext a
  simp only [Set.mem_range, mseg_join]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨restrictChart t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨extChart t, rfl⟩

theorem mem_chartRing_join (y : (Σ k, ι k) → Ω) (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) (a : Ω) :
    a ∈ chartRing O (mseg (joinCoord y (ptCoord (Ω := Ω)))) s ↔
      a ∈ chartRing O (mseg y) (restrictChart s) := by
  rw [chartRing_join]

end Charts

section Bundles

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def pullBundle (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    ChartBundle O (mseg (joinCoord y (ptCoord (Ω := Ω)))) N E where
  lat s := B.lat (restrictChart s)
  stable s a ha e he := B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he
  frame s hs := by
    rw [chartRing_join]
    exact B.frame _ (by rwa [mseg_join] at hs)
  overlap s t hs ht e he := by
    rw [mseg_join, mseg_join]
    rw [mseg_join] at hs ht
    exact B.overlap _ _ hs ht e he

theorem pullBundle_lat (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E)
    (s : ∀ k : K ⊕ Unit, Sum.elim ι ptIdx k) : (pullBundle O y B).lat s = B.lat (restrictChart s) :=
  rfl

theorem isPull_pullBundle (y : (Σ k, ι k) → Ω) (B : ChartBundle O (mseg y) N E) :
    IsPull O y (ptCoord (Ω := Ω)) B (pullBundle O y B) := by
  intro s _
  rw [pullBundle_lat]
  apply le_antisymm
  · intro v hv
    exact AddSubgroup.subset_closure ⟨1, one_mem _, v, hv, (one_smul _ _).symm⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact B.stable _ a ((mem_chartRing_join O y s a).mp ha) e he

theorem isGradedFrame_pull (y : (Σ k, ι k) → Ω) {B : ChartBundle O (mseg y) N E}
    {Vs : Fin (N + 1) → Submodule Ω E} {m : Fin N → K → ℤ} {gen : Fin N → E}
    (h : IsGradedFrame O y B Vs m gen) :
    IsGradedFrame O (joinCoord y (ptCoord (Ω := Ω))) (pullBundle O y B) Vs
      (fun i => pullDeg (m i)) gen := by
  intro s hs
  rw [mseg_join] at hs
  obtain ⟨k, f, c, hf, hc, hsum, hl⟩ := h _ hs
  refine ⟨k, f, c, fun l => (mem_chartRing_join O y s _).mpr (hf l),
    fun l => (mem_chartRing_join O y s _).mpr (hc l), hsum, fun l => ?_⟩
  obtain ⟨b, hli, hspan, hiff, hw⟩ := hl l
  refine ⟨b, hli, hspan, fun e => ?_, fun i => ?_⟩
  · rw [pullBundle_lat]
    simp only [mem_chartRing_join]
    exact hiff e
  · obtain ⟨w, ⟨hw0, ⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩, hmem⟩ := hw i
    refine ⟨w, ⟨hw0, ⟨n₁, (mem_chartRing_join O y s _).mpr hn₁⟩,
      ⟨n₂, (mem_chartRing_join O y s _).mpr hn₂⟩⟩, ?_⟩
    rw [chartMon_join]
    exact hmem

end Bundles

section Forms

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_join (y : (Σ k, ι k) → Ω) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) :
    aeval (joinCoord y (ptCoord (Ω := Ω))) (rename (liftVar ptIdx) f) = aeval y f := by
  rw [aeval_rename]
  rfl

theorem pullDeg_sub (a b : K → ℤ) :
    pullDeg (K' := Unit) a - pullDeg (K' := Unit) b = pullDeg (K' := Unit) (a - b) := by
  funext k
  cases k <;> simp [pullDeg]

end Forms

section Pairs

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω]
  [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def pullFlagPair (y : (Σ k, ι k) → Ω) {B B' : ChartBundle O (mseg y) N E} (F : FlagPair O y B B')
    (hvert : ∀ i, IsVertDiv O (mcIdeal O (joinCoord y (ptCoord (Ω := Ω))))
      (pullDeg (K' := Unit) (F.deg i - F.deg' i)) (rename (liftVar ptIdx) (F.f i))
      (rename (liftVar ptIdx) (F.g i))) :
    FlagPair O (joinCoord y (ptCoord (Ω := Ω))) (pullBundle O y B) (pullBundle O y B') where
  Vs := F.Vs
  mono := F.mono
  dim := F.dim
  top := F.top
  deg i := pullDeg (F.deg i)
  gen := F.gen
  gen_mem := F.gen_mem
  frame := isGradedFrame_pull O y F.frame
  deg' i := pullDeg (F.deg' i)
  gen' := F.gen'
  gen'_mem := F.gen'_mem
  frame' := isGradedFrame_pull O y F.frame'
  f i := rename (liftVar ptIdx) (F.f i)
  g i := rename (liftVar ptIdx) (F.g i)
  rel i := by
    simp only [aeval_join]
    exact F.rel i
  vert i := by
    simp only [pullDeg_sub]
    exact hvert i

theorem fnField_join (y : (Σ k, ι k) → Ω) :
    fnField O (joinCoord y (ptCoord (Ω := Ω))) = fnField O y := by
  unfold fnField
  apply le_antisymm
  · rw [Subfield.closure_le]
    rintro a (ha | ⟨⟨k | u, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ha)
    · exact Subfield.subset_closure (Or.inr ⟨⟨k, i, j⟩, rfl⟩)
    · have h1 : joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, i⟩ /
          joinCoord y (ptCoord (Ω := Ω)) ⟨Sum.inr u, j⟩ = 1 := by
        simp [joinCoord, ptCoord]
      simp only at h1 ⊢
      rw [h1]
      exact one_mem _
  · apply Subfield.closure_mono
    rintro a (ha | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨⟨Sum.inl k, i, j⟩, rfl⟩

end Pairs

end JoinPointFlagModel

open JoinPointFlagModel in

theorem JoinPointFlagModel.proof (hIff : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hModel : JoinPointModel.Statement) (hVert : JoinPointVerticalDivisor.Statement) :
    JoinPointFlagModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hW N E _ _ B B' _ w w' x x' f g hF
  obtain ⟨F, -, -, hdeg, hdeg', hf, hg⟩ :=
    ((hIff O Ω K ι y N E B B' ϖ hϖ hW.multiProj).1 w w' x x' f g).1 hF
  refine ⟨pullBundle O y B, pullBundle O y B',
    pullFlagPair O y F fun i => hVert O Ω K ι y _ _ _ (F.vert i),
    hModel O Ω K ι y d hW, fnField_join O y, isPull_pullBundle O y B, isPull_pullBundle O y B',
    ?_, ?_, ?_, ?_⟩
  · show (fun i => pullDeg (F.deg i)) = _
    rw [hdeg]
  · show (fun i => pullDeg (F.deg' i)) = _
    rw [hdeg']
  · show (fun i => rename (liftVar ptIdx) (F.f i)) = _
    rw [hf]
  · show (fun i => rename (liftVar ptIdx) (F.g i)) = _
    rw [hg]

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type} [DecidableEq K] {ι : K → Type} {J : Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open Classical in

def specialRelDeg (W' : Ideal (MRing (extIdx ι J) O)) : ℕ :=
  if h : (specialIdeal W').IsPrime then
    haveI := h
    FieldNumbers.relDeg Function.Embedding.some (specialIdeal W')
  else 0

end Objects

section Lemmas

def BlowUpFibreDegree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → divCycle P x W ≠ 0 →
      (open Classical in
        ∑ᶠ W' : Ideal (MRing (extIdx ι J) O),
          if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
            divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ)
          else 0) =
        divCycle P x W

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontalMult
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpHorizontalMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      W.comap (liftForm (ι := ι) (J := J) (R := O)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes

def BlowUpHorizontalChartLength.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      ∀ hW : W.IsPrime,
      haveI := hW
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) W =
        Module.length
          (Localization.AtPrime ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
            (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))))
          (LocalizedModule ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
              (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))).primeCompl
            (Polynomial (MRing ι O) ⧸
              (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))))

def PolynomialLocalizedLength.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (q : Ideal R) [q.IsPrime] (I : Ideal R),
    Module.length (Localization.AtPrime (q.map (Polynomial.C : R →+* Polynomial R)))
        (LocalizedModule (q.map (Polynomial.C : R →+* Polynomial R)).primeCompl
          (Polynomial R ⧸ I.map (Polynomial.C : R →+* Polynomial R))) =
      Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl (R ⧸ I))

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOrderLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def LocalizedQuotLength.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (P : Ideal S) (W₀ : Ideal (S ⧸ P)) [W₀.IsPrime] (z : S),
    Module.length (Localization.AtPrime (W₀.comap (Ideal.Quotient.mk P)))
        (LocalizedModule (W₀.comap (Ideal.Quotient.mk P)).primeCompl (S ⧸ (P ⊔ Ideal.span {z}))) =
      Module.length (Localization.AtPrime W₀)
        (Localization.AtPrime W₀ ⧸
          Ideal.span {algebraMap (S ⧸ P) (Localization.AtPrime W₀) (Ideal.Quotient.mk P z)})

def LengthMapIdealLe.Statement : Prop :=
  ∀ (C D : Type u) [CommRing C] [CommRing D] [IsLocalRing D] (φ : C →+* D),
    (∀ m : Ideal C, m.IsMaximal → m.map φ = ⊤ ∨ IsLocalRing.maximalIdeal D ≤ m.map φ) →
    ∀ I : Ideal C, Module.length D (D ⧸ I.map φ) ≤ Module.length C (C ⧸ I)

def IntermediateRingQuotLength.Statement : Prop :=
  ∀ (A C : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing C] [IsDomain C]
    [Algebra A C], ringKrullDim A = 1 → Function.Injective (algebraMap A C) →
    (∀ c : C, ∃ a : A, a ≠ 0 ∧ a • c ∈ Set.range (algebraMap A C)) →
    ∀ a : A, a ≠ 0 →
      Module.length A (C ⧸ Ideal.span {algebraMap A C a}) ≤ Module.length A (A ⧸ Ideal.span {a})

def BlowUpLocalChart.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (P : Ideal (MRing ι R)), P.IsPrime →
    ∀ (u : J → MRing ι R) (G' : Ideal (MRing (extIdx ι J) R)) (y : MRing (extIdx ι J) R),
      y ∉ blowUpOf P u → G' ∈ (blowUpOf P u ⊔ Ideal.span {y}).minimalPrimes → IsRelevant G' →
    ∀ x : MRing ι R, x ∉ P → G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
    ∀ (G₀ : Ideal (MRing ι R ⧸ P)) [G₀.IsPrime],
      G₀.comap (Ideal.Quotient.mk P) = G'.comap (liftForm (J := J)) →
    ∀ (W₀ : Ideal (MRing (extIdx ι J) R ⧸ blowUpOf P u)) [W₀.IsPrime],
      W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = G' →
    ∃ (C : Subring (Localization.AtPrime W₀)) (f : Localization.AtPrime G₀ →+* C),
      Function.Injective f ∧ (∀ c : C, ∃ a, a ≠ 0 ∧ f a * c ∈ Set.range f) ∧
      (∀ s : MRing ι R,
        (f (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀) (Ideal.Quotient.mk P s)) :
            Localization.AtPrime W₀) =
          algebraMap (MRing (extIdx ι J) R ⧸ blowUpOf P u) (Localization.AtPrime W₀)
            (Ideal.Quotient.mk (blowUpOf P u) (liftForm s))) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime W₀) ≤
        ((IsLocalRing.maximalIdeal (Localization.AtPrime W₀)).comap C.subtype).map C.subtype

end Lemmas

section Examples

theorem BlowUpLocalChart.exists_quotient_primes {R : Type*} [CommRing R] {K : Type*} {ι : K → Type}
    {J : Type} {P : Ideal (MRing ι R)} {u : J → MRing ι R} {G' : Ideal (MRing (extIdx ι J) R)}
    (hG' : G'.IsPrime) (hQ : blowUpOf P u ≤ G') (hP : P ≤ G'.comap (liftForm (J := J))) :
    ∃ (G₀ : Ideal (MRing ι R ⧸ P)) (W₀ : Ideal (MRing (extIdx ι J) R ⧸ blowUpOf P u)),
      G₀.IsPrime ∧ W₀.IsPrime ∧ G₀.comap (Ideal.Quotient.mk P) = G'.comap (liftForm (J := J)) ∧
        W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = G' := by
  refine ⟨(G'.comap (liftForm (J := J))).map (Ideal.Quotient.mk P), G'.map (Ideal.Quotient.mk _),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]),
    Ideal.comap_map_mk hP, Ideal.comap_map_mk hQ⟩

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

universe u

section Lemmas

def LocCycleSpanMul.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x y : A), x ≠ 0 → y ≠ 0 →
    ∀ W : Ideal A, locCycle (Ideal.span {x * y}) W =
      locCycle (Ideal.span {x}) W + locCycle (Ideal.span {y}) W

def LocCyclePos.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (J W : Ideal R), W ∈ J.minimalPrimes →
    0 < locCycle J W

def MinimalPrimesSpanSingleton.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x : A), x ≠ 0 →
    ∀ W : Ideal A, W ∈ (Ideal.span {x}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ x ∈ W

def LocalDomainDimTwo.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    (∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A) →
    ringKrullDim A = 2 ∧ (IsLocalRing.maximalIdeal A).height = 2 ∧
      ∀ Q : Ideal A, Q.IsPrime → ⊥ < Q → Q < IsLocalRing.maximalIdeal A → Q.height = 1

def DimTwoSumReading.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    ringKrullDim A = 2 → ∀ a b : A, a ≠ 0 →
    (∀ p : Ideal A, p.IsPrime → p.height = 1 → a ∈ p → b ∉ p) →
    ∃ n : ℕ, ∑ᶠ W : Ideal A, locCycle (Ideal.span {a}) W *
        locCycle (W ⊔ Ideal.span {b}) (IsLocalRing.maximalIdeal A) = n ∧
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b = n

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensExist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensExist.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle O (segreVec y) N E),
    ∃ a₁ : K → ℤ, ∀ a : K → ℤ, a₁ ≤ a →
      ∃ (M : ℕ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

