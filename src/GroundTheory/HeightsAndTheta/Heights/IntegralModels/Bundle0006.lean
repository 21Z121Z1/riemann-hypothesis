import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSectionNef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open MvPolynomial NumbersDVR

noncomputable section

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type} [Field F]

theorem exists_forms_mem_of_not_le_relevant {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    (hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W → ¬ J ≤ W) :
    ∃ n : ℕ, ∀ m : K → ℕ, (∀ k, n * Fintype.card (ι k) < m k) →
      ∀ x : MRing ι F, IsMultiHomog x m → x ∈ J := by
  classical

  let e : (∀ k, ι k) → (Σ k, ι k) →₀ ℕ := fun σ =>
    Finsupp.equivFunOnFinite.symm (fun v => if v.2 = σ v.1 then 1 else 0)
  have he : ∀ σ v, e σ v = if v.2 = σ v.1 then 1 else 0 := fun σ v => rfl
  have hrad : ∀ σ : (∀ k, ι k), (monomial (e σ) (1 : F)) ∈ J.radical := by
    intro σ
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro W hW
    have hWp : Ideal.IsPrime W := hW.1.1
    have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof F K ι J W hJ hW
    obtain ⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ W := by
      by_contra h
      push Not at h
      exact hrel W hWp hWh h hW.1.2
    refine Ideal.mem_of_dvd _ ?_ (hk (σ k))
    rw [← pow_one (X _), X_pow_eq_monomial, monomial_dvd_monomial]
    refine ⟨Or.inr ?_, one_dvd _⟩
    rw [Finsupp.single_le_iff, he]
    simp
  have hrad' : ∀ σ : (∀ k, ι k), ∃ n : ℕ, (monomial (e σ) (1 : F)) ^ n ∈ J := fun σ => hrad σ
  choose N hN using hrad'
  refine ⟨Finset.univ.sup N, fun m hm x hx => ?_⟩
  rw [x.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hw := hx (mem_support_iff.mp hd)
  rw [Bridge.weight_blockWeight] at hw
  have hσ : ∀ k, ∃ i : ι k, Finset.univ.sup N ≤ d ⟨k, i⟩ := by
    intro k
    by_contra h
    push Not at h
    have h1 : ∑ i, d ⟨k, i⟩ ≤ ∑ _i : ι k, Finset.univ.sup N :=
      Finset.sum_le_sum fun i _ => (h i).le
    have h2 := congrFun hw k
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1 h2
    have h3 := hm k
    rw [h2] at h1
    rw [mul_comm] at h3
    omega
  choose σ hσ using hσ
  have hmem : monomial (e σ) (1 : F) ^ Finset.univ.sup N ∈ J :=
    Ideal.pow_mem_of_pow_mem _ (hN σ) (Finset.le_sup (Finset.mem_univ σ))
  refine Ideal.mem_of_dvd _ ?_ hmem
  rw [monomial_pow, one_pow, monomial_dvd_monomial]
  refine ⟨Or.inr ?_, one_dvd _⟩
  intro v
  rw [Finsupp.smul_apply, he, smul_eq_mul]
  split_ifs with hv
  · obtain ⟨k, i⟩ := v
    simp only at hv
    subst hv
    simpa using hσ k
  · simp

theorem hilbFn_sub_le_of_regular {P : Ideal (MRing ι F)} (hP : IsMultiProjPrime P) {b : K → ℤ}
    {f g : MRing ι F} (hs : IsRegularSection P b f g) :
    ∀ᶠ m in Filter.atTop, hilbFn P (m - b) ≤ hilbFn P m := by
  classical
  have := hP.isPrime
  obtain ⟨bf, bg, hf, hg, hb⟩ := hs.degrees
  set J : Ideal (MRing ι F) := (P ⊔ Ideal.span {g}).colon {f} with hJdef
  have hJh : IsMultiHomogIdeal J :=
    ColonMultiHomog.proof F K ι _ f bf
      (SupSpanMultiHomog.proof F K ι P g bg hP.multiHomog hg) hf
  have hPJ : P ≤ J := fun p hp => by
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    exact Ideal.mem_sup_left (P.mul_mem_right f hp)
  have hrel : ∀ W : Ideal (MRing ι F), W.IsPrime → IsMultiHomogIdeal W → IsRelevant W →
      ¬ J ≤ W := by
    intro W hWp hWh hWr hJW
    obtain ⟨u, v, hu, huv⟩ := hs.regular W ⟨hWp, hWh, hWr⟩ (hPJ.trans hJW)
    apply hu
    apply hJW
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul]
    have : u * f = (u * f - v * g) + v * g := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left huv)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  obtain ⟨n, hn⟩ := exists_forms_mem_of_not_le_relevant hJh hrel
  rw [Filter.eventually_atTop]
  refine ⟨fun k => |b k| + (n * Fintype.card (ι k) : ℕ) + 1, fun m hm => ?_⟩
  have hm' : ∀ k, |b k| + (n * Fintype.card (ι k) : ℕ) + 1 ≤ m k := fun k => hm k
  have hb' : ∀ k, b k = (bf k : ℤ) - bg k := fun k => (congrFun hb k).symm
  have hm0 : ∀ k, 0 ≤ m k := fun k => by have := hm' k; have := abs_nonneg (b k); omega
  have hmb0 : ∀ k, 0 ≤ (m - b) k := fun k => by
    have := hm' k; have := le_abs_self (b k); simp only [Pi.sub_apply]; omega
  set M : K → ℕ := fun k => (m k).toNat with hM
  set M' : K → ℕ := fun k => ((m - b) k).toNat with hM'
  have hdeg : M' + bf = M + bg := by
    funext k
    have := hm0 k; have := hmb0 k; have := hb' k
    simp only [Pi.add_apply, hM, hM', Pi.sub_apply] at *
    omega
  have hbig : ∀ k, n * Fintype.card (ι k) < M' k := by
    intro k
    have := hm' k; have := le_abs_self (b k)
    simp only [hM', Pi.sub_apply]
    omega
  have hfin := (FieldNumbers.GradedFinite.proof F K ι P M).1
  have hfin' := (FieldNumbers.GradedFinite.proof F K ι P M').1
  have e1 : hilbFn P m = Module.finrank F (gradedPiece P M) := by
    unfold hilbFn; rw [if_pos hm0]
  have e2 : hilbFn P (m - b) = Module.finrank F (gradedPiece P M') := by
    unfold hilbFn; rw [if_pos hmb0]
  rw [e1, e2, Nat.cast_le]

  let φ : MRing ι F → (MRing ι F ⧸ P) →ₗ[F] (MRing ι F ⧸ P) := fun a =>
    LinearMap.mulLeft F (Ideal.Quotient.mk P a)
  have hinj : ∀ a, a ∉ P → Function.Injective (φ a) := by
    intro a ha
    exact mul_right_injective₀ (fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hle : (gradedPiece P M').map (φ f) ≤ (gradedPiece P M).map (φ g) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxh : IsMultiHomog x M' := (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx
    have hxJ : x ∈ J := hn M' hbig x hxh
    rw [hJdef, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_sup] at hxJ
    obtain ⟨p, hp, q, hq, hpq⟩ := hxJ
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    set y := weightedHomogeneousComponent (blockWeight ι) M a
    have hxf : IsMultiHomog (x * f) (M + bg) := by
      rw [← hdeg]; exact hxh.mul hf
    have hcomp := congrArg (weightedHomogeneousComponent (blockWeight ι) (M + bg)) hpq
    rw [map_add, ← component_mul_multiHomog a g M bg hg,
      hxf.weightedHomogeneousComponent_same] at hcomp
    have hpc : weightedHomogeneousComponent (blockWeight ι) (M + bg) p ∈ P :=
      hP.multiHomog p hp _
    refine ⟨Ideal.Quotient.mk P y, ⟨y, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      rfl⟩, ?_⟩
    simp only [φ, LinearMap.mulLeft_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.toLinearMap_apply,
      ← map_mul]
    rw [Ideal.Quotient.eq, mul_comm f x, ← hcomp]
    have : g * y - (weightedHomogeneousComponent (blockWeight ι) (M + bg) p + y * g) =
      -weightedHomogeneousComponent (blockWeight ι) (M + bg) p := by ring
    rw [this]
    exact P.neg_mem hpc
  calc Module.finrank F (gradedPiece P M')
      = Module.finrank F ((gradedPiece P M').map (φ f)) :=
        (Submodule.equivMapOfInjective _ (hinj f hs.num_not_mem) _).finrank_eq
    _ ≤ Module.finrank F ((gradedPiece P M).map (φ g)) := by
        have : FiniteDimensional F ((gradedPiece P M).map (φ g)) :=
          Module.Finite.map _ _
        exact LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
          (Submodule.inclusion_injective hle)
    _ = Module.finrank F (gradedPiece P M) :=
        ((Submodule.equivMapOfInjective _ (hinj g hs.den_not_mem) _).finrank_eq).symm

end

theorem SectionNef.proof : SectionNef.Statement := by
  intro K _ _ ι _ F _ P hP _ b f g hs
  have hev := hilbFn_sub_le_of_regular hP hs
  unfold intNum eventualValue
  split_ifs with h
  · obtain ⟨m, hm1, hm2⟩ := (h.choose_spec.and hev).exists
    rw [← hm1]
    simp only [mixedDiff, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
      Matrix.cons_val_zero, diffStep]
    linarith
  · exact le_rfl

theorem SectionNefGenerated.proof : SectionNefGenerated.Statement :=
  SectionNefGenerated.of_sectionNef SectionNef.proof

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PullbackBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

def pullSectionOn {T Z : Scheme.{u}} (g : T ⟶ Z) (M : Z.Modules) (U : Z.Opens) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U).hom

lemma pullSectionOn_top {T Z : Scheme.{u}} (g : T ⟶ Z) (M : Z.Modules) :
    pullSectionOn g M ⊤ = pullSection g M := rfl

def PullbackBasis.Statement : Prop :=
  ∀ (T Z : Scheme.{u}) (g : T ⟶ Z) (M : Z.Modules) (U : Z.Opens) (n : ℕ) (s : Fin n → Γ(M, U)),
    IsBasisOn M U s →
      IsBasisOn ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (fun i => pullSectionOn g M U (s i))

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.RatLocalAffine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def RatLocalAffine.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [Flat f] (U : X.Opens), IsAffineOpen U →
    Function.Injective ((baseChangeMap f ℚ).app U) ∧
      ∀ b : Γ(baseChange f ℚ, baseChangeMap f ℚ ⁻¹ᵁ U),
        ∃ N : ℕ, 0 < N ∧ ∃ a : Γ(X, U), (baseChangeMap f ℚ).app U a = N • b

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsFreeSheafBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

abbrev freeModule (Y : Scheme.{u}) (n : ℕ) : Y.Modules :=
  SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin n))

def stdSection (Y : Scheme.{u}) (n : ℕ) (i : Fin n) : Γ(freeModule Y n, ⊤) :=
  (Scheme.Modules.Hom.app (M := structureModule Y)
    (SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i)) ⊤).hom (1 : Γ(Y, ⊤))

def FreeSheafBasis.Statement : Prop :=
  ∀ (Y : Scheme.{u}) (n : ℕ), IsBasisOn (freeModule Y n) ⊤ (stdSection Y n)

theorem FreeSheafBasis.objects_inhabited :
    Nonempty ((freeModule SpecZ 2 : SpecZ.Modules) ≅ freeModule SpecZ 2) ∧
      Nonempty (Fin 2 → Γ(freeModule SpecZ 2, ⊤)) :=
  ⟨⟨Iso.refl _⟩, ⟨stdSection SpecZ 2⟩⟩

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def GenericSectionsInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f],
    ∃ m : ℕ, 0 < m ∧ ∀ (k : ℤ) (hk : IsUnit (k : ℚ)), (m : ℤ) ∣ k →
      ∀ W : (invOpen f k : Scheme.{0}).Opens, Function.Injective ((toInvOpen f ℚ k hk).app W)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def GlueModulesStar.Statement : Prop :=
  ∀ (X : Scheme.{0}) (V : X.Opens) (ι : Type) (U : ι → X.Opens),
    V ⊔ ⨆ i, U i = ⊤ → (∀ i j, i ≠ j → U i ⊓ U j ≤ V) →
    ∀ (G : (V : Scheme.{0}).Modules) (F : ∀ i, (U i : Scheme.{0}).Modules)
      (ψ : ∀ i, (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i))).obj (F i) ≅
        (Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G),
    ∃ (E : X.Modules) (e₀ : (Scheme.Modules.pullback V.ι).obj E ≅ G)
      (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj E ≅ F i),
      ∀ i, pullbackCompIso (X.homOfLE_ι (inf_le_right : U i ⊓ V ≤ V)) e₀ =
        pullbackCompIso (X.homOfLE_ι (inf_le_left : U i ⊓ V ≤ U i)) (e i) ≪≫ ψ i

def VectorBundleRestrict.Statement : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsOpenImmersion f] (E : Y.Modules), IsVectorBundle E →
    IsVectorBundle ((Scheme.Modules.pullback f).obj E)

def VectorBundleLocal.Statement : Prop :=
  ∀ (X : Scheme.{0}) (ι : Type) (U : ι → X.Opens), ⨆ i, U i = ⊤ → ∀ E : X.Modules,
    (∀ i, IsVectorBundle ((Scheme.Modules.pullback (U i).ι).obj E)) → IsVectorBundle E

section Inhabitants

def halfThirdOpens : Bool → SpecZ.Opens := fun b =>
  if b then invOpen (𝟙 SpecZ) 2 else invOpen (𝟙 SpecZ) 3

lemma mem_invOpen_id (m : ℤ) (x : SpecZ) : x ∈ invOpen (𝟙 SpecZ) m ↔ m ∉ x.asIdeal := Iff.rfl

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsHeightOneSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

def HeightOneSections.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], IsNormalScheme X →
    ∀ (E : X.Modules), IsVectorBundle E →
    ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (v : E.presheaf.stalk (genericPoint X)),
      (∀ x : X, x ∈ U → ringKrullDim (X.presheaf.stalk x) = 1 → v ∈ genericImage E x) →
      ∃ s : Γ(E, U), E.presheaf.germ U (genericPoint X) hU s = v

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsInvOpenInside
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def InvOpenInside.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [QuasiCompact f] (p : Nat.Primes) (W : X.Opens),
    Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ invOpen f m ≤ W

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsInvOpenInsideRat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def InvOpenInsideRat.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (W : X.Opens),
    Set.range (baseChangeMap f ℚ) ⊆ Set.range W.ι →
    ∃ m : ℕ, 0 < m ∧ invOpen f m ≤ W

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

def TorsionFreeQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (r : ℕ),
      Module.rank R M = r → ∀ a : R, a ≠ 0 →
        Module.length R (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ≤
          (r : ℕ∞) * Module.length R (R ⧸ Ideal.span {a})

def KrullAkizukiQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
      [IsScalarTower R K L] (S : Subalgebra R L) (b : R), b ≠ 0 →
        IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsLocSectionsInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def LocSectionsInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes),
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ k : ℤ, ¬ ((p : ℕ) : ℤ) ∣ k → (m : ℤ) ∣ k →
      ∀ W : X.Opens, W ≤ invOpen f k →
        Function.Injective ((baseChangeMap f (ZLoc p)).app W)

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullbackFaithful
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

def PullbackFaithful.Statement : Prop :=
  ∀ (T U : Scheme.{u}) (g : T ⟶ U), (∀ W : U.Opens, Function.Injective (g.app W)) →
    ∀ (A B : U.Modules), IsVectorBundle B → ∀ ψ₁ ψ₂ : A ⟶ B,
      (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂ → ψ₁ = ψ₂

end

end GroundTheory.Heights₂.Heights.Model
end

