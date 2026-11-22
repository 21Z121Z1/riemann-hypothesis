import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import GroundTheory.ArithmeticGeometry.IwasawaModules.SpanFinrankMaximalIdealLeTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemOfMemSupportDivCycle
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section Lengths

def colonMod {A : Type*} [CommRing A] (a b : A) : Submodule A (A ⧸ Ideal.span {a}) :=
  Submodule.map (Ideal.span {a}).mkQ ((Ideal.span {a}).colon (Ideal.span {b}) : Submodule A A)

def NumbersBirationalInvariance.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) ≠ ⊤ →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) =
      length A (Submodule.torsionBy A M x) +
        ∑ᶠ (p : PrimeSpectrum A)
          (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes ∧
            p.asIdeal ≠ IsLocalRing.maximalIdeal A),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x}))

def NumbersBirationalInvariance.LocalRingStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) ≠ ⊤ →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) =
      length A (Submodule.torsionBy A M x) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x}))

def NumbersSymmetry.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (a b : A),
    ringKrullDim A = 2 → a ≠ 0 → b ≠ 0 → length A (A ⧸ Ideal.span {a, b}) ≠ ⊤ →
    length A (A ⧸ Ideal.span {a, b}) = length A (colonMod a b) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
          length (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal ⧸
                Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) ∧
      Nonempty (colonMod a b ≃ₗ[A] colonMod b a)

end Lengths

section Models

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def redMap : MRingOver O ι →+* MRingOver (IsLocalRing.ResidueField O) ι :=
  MvPolynomial.map (IsLocalRing.residue O)

def genMap : MRingOver O ι →+* MRingOver (FractionRing O) ι :=
  MvPolynomial.map (algebraMap O (FractionRing O))

def IsModelOver (P : Ideal (MRingOver O ι)) (d : ℕ) : Prop :=
  IsMultiProjPrime P ∧ P.comap (C : O →+* MRingOver O ι) = ⊥ ∧
    ringKrullDim (MRingOver O ι ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

def intCyc {R : Type*} [CommRing R] (Z : Ideal (MRingOver R ι) →₀ ℕ) : Ideal (MRingOver R ι) →₀ ℤ :=
  Finsupp.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero Z

def specCyc (ϖ : O) (P : Ideal (MRingOver O ι)) : Ideal (MRingOver O ι) →₀ ℕ :=
  divCycle P (C ϖ)

def genFib (P : Ideal (MRingOver O ι)) : Ideal (MRingOver (FractionRing O) ι) :=
  P.map genMap

def divO (P : Ideal (MRingOver O ι)) (f g : MRingOver O ι) : Ideal (MRingOver O ι) →₀ ℤ :=
  intCyc (divCycle P f) - intCyc (divCycle P g)

def redEval (J : Ideal (MRingOver (IsLocalRing.ResidueField O) ι) → ℤ)
    (Z : Ideal (MRingOver O ι) →₀ ℤ) : ℤ :=
  Z.sum fun W m => m * J (W.map redMap)

def IsVerticalDiv (ϖ : O) (P : Ideal (MRingOver O ι)) (b : K → ℤ) (f g : MRingOver O ι) : Prop :=
  (∃ α β : K → ℕ, IsMultiHomog f α ∧ IsMultiHomog g β ∧ ∀ k, (α k : ℤ) - β k = b k) ∧
    g ∉ P ∧ ∀ W ∈ (divO P f g).support, C ϖ ∈ W

def IsRegSection (P : Ideal (MRingOver O ι)) (c : K → ℕ) (s : MRingOver O ι) : Prop :=
  IsMultiHomog s c ∧ s ∉ P

end Models

def NumbersMultilinearity.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (d : ℕ) (a : Fin d → K → ℤ)
      (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (IK : IFamily (FractionRing O) ι),
      IsModelOver P d → IsFieldIntersection Iκ → IsFieldIntersection IK →
      redEval (fun W => Iκ W d a) (intCyc (specCyc ϖ P)) = IK (genFib P) d a

open Classical in

def NumbersProjectionFormula.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (n : ℕ) (b : K → ℤ) (f g : MRingOver O ι) (c : K → ℕ)
      (s : MRingOver O ι) (L : Fin n → K → ℤ) (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P (n + 1) → IsVerticalDiv ϖ P b f g → IsRegSection P c s →
      IsFieldIntersection Iκ →
      (∀ H ∈ (divCycle P s).support, C ϖ ∉ H → IsVerticalDiv ϖ H b f g) →
      redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L (fun k => (c k : ℤ))))
          (divO P f g) =
        (divCycle P s).sum fun H m =>
          if C ϖ ∈ H then (m : ℤ) * Iκ (H.map redMap) (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)
          else (m : ℤ) * redEval (fun G => Iκ G n L) (divO H f g)

def VerticalDivisorsCommuting.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (n : ℕ) (b b' : K → ℤ) (f g f' g' : MRingOver O ι)
      (L : Fin n → K → ℤ) (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P (n + 1) → IsVerticalDiv ϖ P b f g → IsVerticalDiv ϖ P b' f' g' →
      IsFieldIntersection Iκ →
      redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b')) (divO P f g) =
        redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)) (divO P f' g')

section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem mem_of_mem_support_divCycle {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P W : Ideal (MRingOver R ι)} {s : MRingOver R ι} (h : W ∈ (divCycle P s).support) :
    W.IsPrime ∧ s ∈ W := by
  classical
  have hW : W ∈ divSupp P s := by
    by_contra hn
    apply Finsupp.mem_support_iff.mp h
    simp only [divCycle]
    rw [Finsupp.ofSupportFinite_coe, if_neg hn]
  exact ⟨hW.1.1.1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))⟩

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem mem_of_mem_support_divO {P W : Ideal (MRingOver O ι)} {f g : MRingOver O ι}
    (h : W ∈ (divO P f g).support) :
    W ∈ (divCycle P f).support ∨ W ∈ (divCycle P g).support := by
  classical
  rcases Finset.mem_union.mp (Finsupp.support_sub h) with h1 | h1
  · exact Or.inl (Finsupp.support_mapRange h1)
  · exact Or.inr (Finsupp.support_mapRange h1)

omit [Fintype K] [IsDomain O] [IsDiscreteValuationRing O] in

theorem isMultiHomog_C (a : O) : IsMultiHomog (C a : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm

theorem isVerticalDiv_unif (ϖ : O) {P : Ideal (MRingOver O ι)} (hP : P.IsPrime) :
    IsVerticalDiv ϖ P 0 (C ϖ) 1 := by
  refine ⟨⟨0, 0, isMultiHomog_C ϖ, by simpa using isMultiHomog_C (ι := ι) (1 : O), by simp⟩,
    hP.one_notMem, fun W hW => ?_⟩
  rcases mem_of_mem_support_divO hW with h | h
  · exact (mem_of_mem_support_divCycle h).2
  · exact absurd (mem_of_mem_support_divCycle h).2 (mem_of_mem_support_divCycle h).1.one_notMem

variable (O) in

theorem isModelOver_line : IsModelOver (⊥ : Ideal (MRingOver O (fun _ : Unit => Fin 2))) 1 := by
  refine ⟨⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun k => ⟨0, by simp [X_ne_zero]⟩⟩, ?_, ?_⟩
  · exact Ideal.comap_bot_of_injective _ (MvPolynomial.C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
    rfl

end Inhabitants

section LengthInhabitants

open IsLocalRing

end LengthInhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByEffectiveDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem IsVerticalDivisor.uniformiser_pow_mul {K : Type*} [DecidableEq K] {ι : K → Type*}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {H : Ideal (MRing ι O)}
    [hH : H.IsPrime] {ϖ : O} (hϖ : (C ϖ : MRing ι O) ∉ H) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor H ϖ b f g) (n : ℕ) :
    IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
  · have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
      rw [← map_pow]
      exact isWeightedHomogeneous_C _ _
    have := h0.mul hf
    rwa [zero_add] at this
  · exact hH.mul_notMem (fun h => hϖ (hH.mem_of_pow_mem n h)) hD.num_not_mem
  · intro W hW hHW hrel hϖW
    obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hHW hrel hϖW
    refine ⟨u, C ϖ ^ n * v, hu, hW.mul_notMem (fun h => hϖW (hW.mem_of_pow_mem n h)) hv, ?_⟩
    have e : u * (C ϖ ^ n * f) - C ϖ ^ n * v * g = C ϖ ^ n * (u * f - v * g) := by ring
    rw [e]
    exact H.mul_mem_left _ huv

theorem CutByEffectiveDivisor.proof (h1 : EffectiveCase.Statement.{u})
    (h2 : UniformiserCase.Statement.{u}) (h3 : ShiftByUniformiser.Statement.{u})
    (h4 : EffectiveShift.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH L
  obtain ⟨n, hEff⟩ := h4 O ϖ hϖ K ι P (d + 1) hP b f g hD
  have hH' : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
    intro H hsH hϖH
    have := (le_and_isRelevant_of_divCycle_ne_zero hsH).1
    exact (hH H hsH hϖH).uniformiser_pow_mul hϖH n
  have e1 := h1 O ϖ hϖ K ι P d hP b (C ϖ ^ n * f) g hEff c s hs hsP hH' L
  have e2 := h2 O ϖ hϖ K ι P d hP c s hs hsP L
  exact h3 O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH L n e1 e2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DivCycleFiniteSupport.proof : DivCycleFiniteSupport.Statement.{u} := by
  intro R _ _ K _ ι _ P f
  apply Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f}))
  intro W hW
  by_contra hmin
  apply hW
  unfold divCycle
  rw [dif_neg]
  exact fun h => hmin h.1

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem localizedQuot_subsingleton_of_not_le (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by
  obtain ⟨q, hqQ, hqW⟩ := Set.not_subset.mp h
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨q, hqW, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Q.mul_mem_right a hqQ

theorem length_localizedQuot_sup_span_mul (P W : Ideal A) [P.IsPrime] [W.IsPrime] {x : A} (y : A)
    (hx : x ∉ P) :
    Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x * y}))) =
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {y}))) +
        Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x}))) := by
  have hle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
    sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
  let g₁ : (A ⧸ (P ⊔ Ideal.span {y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x * y}) :=
    Submodule.mapQ _ _ (LinearMap.mulLeft A x) (fun a ha => by
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      show x * (p + c * y) ∈ P ⊔ Ideal.span {x * y}
      have e : x * (p + c * y) = x * p + c * (x * y) := by ring
      rw [e]
      exact Submodule.add_mem_sup (P.mul_mem_left _ hp) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  let g₂ : (A ⧸ (P ⊔ Ideal.span {x * y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x}) :=
    Submodule.mapQ _ _ LinearMap.id (fun a ha => hle ha)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    rw [LinearMap.mem_ker] at hz
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hm : x * (a - c * y) ∈ P := by
      have e : x * (a - c * y) = p := by linear_combination hpr.symm
      rw [e]; exact hp
    have ha : a - c * y ∈ P := (‹P.IsPrime›.mem_or_mem hm).resolve_left hx
    have e : a = (a - c * y) + c * y := by ring
    rw [e]
    exact Submodule.add_mem_sup ha (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have hsurj : Function.Surjective g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
      rw [Submodule.Quotient.eq]
      have e : x * c - (p + c * x) = -p := by ring
      rw [e]
      exact Submodule.mem_sup_left (P.neg_mem hp)
    · rintro ⟨z, hz⟩
      induction z using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply] at hz
      rw [Submodule.Quotient.eq] at hz
      have e : a = -(x * c - a) + c * x := by ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.neg_mem _ (hle hz))
        (Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  exact Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)

theorem length_localizedQuot_ne_top [IsNoetherianRing A] (J W : Ideal A) [W.IsPrime]
    (hW : W ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) ≠ ⊤ := by
  have : IsNoetherianRing (Localization.AtPrime W) :=
    IsLocalization.isNoetherianRing W.primeCompl _ inferInstance
  have hI : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      (J.map (algebraMap A (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J,
      Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hW
  have : IsArtinianRing (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := J.map (algebraMap A (Localization.AtPrime W))))
  have : IsNoetherian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isNoetherian_quotient _
  have := IsLocalization.linearMap_compatibleSMul W.primeCompl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)))
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J))).restrictScalars (Localization.AtPrime W)
  rw [← e.length_eq, Ideal.localized'_eq_map]
  exact Module.length_ne_top

theorem mem_minimalPrimes_sup_span_mul [IsNoetherianRing A] {P W : Ideal A} [P.IsPrime] {x y : A}
    (hy : y ∉ P) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) :
    W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr (W.mul_mem_right y hxW))⟩, ?_⟩
  rintro Q ⟨hQp, hQ⟩ hQW
  have hPQ : P ≤ Q := le_sup_left.trans hQ
  rcases hQp.mem_or_mem (hQ (Ideal.mem_sup_right (Ideal.subset_span rfl))) with hxQ | hyQ
  · exact hW.2 ⟨hQp, sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hQW
  by_contra hWQ
  have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ h.ge)
  have hPQlt : P < Q := lt_of_le_of_ne hPQ (fun h => hy (h ▸ hyQ))
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hQ' : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPQ)
  have hW' : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPW)
  have h0 : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have hcQ : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPQ]
  have hcW : (W.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = W := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPW]
  have hcP : (⊥ : Ideal (A ⧸ P)).comap (Ideal.Quotient.mk P) = P := by
    rw [← RingHom.ker_eq_comap_bot, hker]
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne bot_le (fun h => hPQlt.ne
      (hcP.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcQ)))
  have h2 : Q.map (Ideal.Quotient.mk P) < W.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hQW) (fun h => hlt.ne
      (hcQ.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcW)))
  have hb := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have hc := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have hk := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have h2le : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal (A ⧸ P)).height + 1 + 1 := by gcongr; positivity
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ 1 := hc.trans hk
  exact absurd h2le (by norm_num)

end General

section Forms

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_eq_toNat_multAt {P : Ideal (MRing ι R)} (f g : MRing ι R)
    {W : Ideal (MRing ι R)} [W.IsPrime] (hW : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes)
    (hrel : IsRelevant W) (hle : P ⊔ Ideal.span {g} ≤ P ⊔ Ideal.span {f}) :
    divCycle P f W = ((multAt (P ⊔ Ideal.span {f}) W).toNat : ℤ) := by
  unfold divCycle
  by_cases hfW : P ⊔ Ideal.span {f} ≤ W
  · have hm : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes :=
      ⟨⟨hW.1.1, hfW⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, hle.trans hQ.2⟩ hQW⟩
    rw [dif_pos ⟨hm, hrel⟩]
  · rw [dif_neg (fun h => hfW h.1.1.2)]
    unfold multAt
    rw [Module.length_eq_zero_iff.mpr (localizedQuot_subsingleton_of_not_le _ W hfW)]
    rfl

end Forms

theorem DivCycleMul.proof : DivCycleMul.Statement := by
  intro R _ _ K _ ι _ P x y hP hx hy
  funext W
  have hxy : x * y ∉ P := fun h => (hP.mem_or_mem h).elim hx hy
  by_cases hrel : IsRelevant W
  swap
  · simp only [Pi.add_apply]
    unfold divCycle
    rw [dif_neg (fun h => hrel h.2), dif_neg (fun h => hrel h.2), dif_neg (fun h => hrel h.2),
      add_zero]
  by_cases hm : W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes
  · have hW : W.IsPrime := hm.1.1
    have hxle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
    have hyle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {y} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_left _ x (Ideal.mem_span_singleton_self y))) P
    simp only [Pi.add_apply]
    rw [divCycle_eq_toNat_multAt (x * y) (x * y) hm hrel le_rfl,
      divCycle_eq_toNat_multAt x (x * y) hm hrel hxle,
      divCycle_eq_toNat_multAt y (x * y) hm hrel hyle]
    have htop := length_localizedQuot_ne_top _ W hm
    have hadd := length_localizedQuot_sup_span_mul P W y hx
    unfold multAt
    rw [hadd] at htop ⊢
    rw [ENat.toNat_add (WithTop.add_ne_top.mp htop).1 (WithTop.add_ne_top.mp htop).2]
    push_cast
    ring
  · simp only [Pi.add_apply]
    unfold divCycle
    have hnx : ¬ W ∈ (P ⊔ Ideal.span {x}).minimalPrimes :=
      fun h => hm (mem_minimalPrimes_sup_span_mul hy h)
    have hny : ¬ W ∈ (P ⊔ Ideal.span {y}).minimalPrimes :=
      fun h => hm (mul_comm y x ▸ mem_minimalPrimes_sup_span_mul hx h)
    rw [dif_neg (fun h => hm h.1), dif_neg (fun h => hnx h.1), dif_neg (fun h => hny h.1), add_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

