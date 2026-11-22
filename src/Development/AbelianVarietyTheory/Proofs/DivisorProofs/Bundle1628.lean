import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertiaElementRestrictingToFiniteGalois
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaRestrict

variable {Ω : Type} [Field Ω]

theorem lt_one_iff_of_sub_lt (V : ValuationSubring Ω) {x y : Ω} (h : V.valuation (x - y) < 1) :
    V.valuation x < 1 ↔ V.valuation y < 1 := by
  constructor
  · intro hx
    have : y = x - (x - y) := by ring
    rw [this]
    exact Valuation.map_sub_lt _ hx h
  · intro hy
    have : x = y + (x - y) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hy h

theorem comap_valuation_lt_one_iff {L : Type} [Field L] (f : L →+* Ω) (V : ValuationSubring Ω) (z : L) :
    (V.comap f).valuation z < 1 ↔ V.valuation (f z) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

theorem valuation_eq_one {V : ValuationSubring Ω} {s : Ω} (hs : s ∈ V) (h : ¬ V.valuation s < 1) :
    V.valuation s = 1 :=
  le_antisymm ((V.valuation_le_one_iff s).2 hs) (not_lt.1 h)

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj IntermediateField

theorem exists_den_integral (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsSeparable K Ω] (V : ValuationSubring Ω) (hR : ∀ r : R, algebraMap R Ω r ∈ V) {x : Ω}
    (hx : x ∈ V) :
    ∃ s t : Ω, IsIntegral R s ∧ IsIntegral R t ∧ V.valuation s = 1 ∧ s * x = t := by
  let M : IntermediateField K Ω := K⟮x⟯
  haveI : FiniteDimensional K M := adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral K x)
  haveI : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  haveI : IsDedekindDomain (integralClosure R M) := integralClosure.isDedekindDomain R K M
  haveI : IsFractionRing (integralClosure R M) M := integralClosure.isFractionRing_of_finite_extension K M
  haveI : IsScalarTower R M Ω := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K Ω, IsScalarTower.algebraMap_apply R K M]
    rfl
  let A := V.comap (algebraMap M Ω)
  have hint : ∀ s : integralClosure R M, IsIntegral R ((s : M) : Ω) := fun s =>
    (s.2).map (IsScalarTower.toAlgHom R M Ω)
  have hS : ∀ s : integralClosure R M, algebraMap (integralClosure R M) M s ∈ A := fun s =>
    mem_of_isIntegral V hR (hint s)
  obtain ⟨s, t, hs, e⟩ := exists_den (integralClosure R M) A hS (x := ⟨x, mem_adjoin_simple_self K x⟩) hx
  refine ⟨((s : M) : Ω), ((t : M) : Ω), hint s, hint t, valuation_eq_one (hS s) ?_, ?_⟩
  · intro h
    have h2 : A.valuation (algebraMap (integralClosure R M) M s) < 1 :=
      (comap_valuation_lt_one_iff (algebraMap M Ω) V _).2 h
    rw [hs] at h2
    exact lt_irrefl _ h2
  · have := congrArg (algebraMap M Ω) e
    simpa using this

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj

section crit

variable (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsSeparable K Ω] (V : ValuationSubring Ω) (hR : ∀ r : R, algebraMap R Ω r ∈ V)

include hR in
theorem map_mem_of_lt_one_iff (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ b : Ω, IsIntegral R b → (V.valuation (g b) < 1 ↔ V.valuation b < 1)) {x : Ω} (hx : x ∈ V) :
    g x ∈ V := by
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den_integral R K Ω V hR hx
  have hgs : V.valuation (g s) = 1 :=
    valuation_eq_one (mem_of_isIntegral V hR (hs.map (g.restrictScalars R))) (by
      rw [hg s hs, hs1]; exact lt_irrefl 1)
  have e' : g s * g x = g t := by rw [← map_mul, e]
  have := congrArg V.valuation e'
  rw [Valuation.map_mul, hgs, _root_.one_mul] at this
  rw [← V.valuation_le_one_iff, this, V.valuation_le_one_iff]
  exact mem_of_isIntegral V hR (ht.map (g.restrictScalars R))

include hR in

theorem smul_eq_of_lt_one_iff (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ b : Ω, IsIntegral R b → (V.valuation (g b) < 1 ↔ V.valuation b < 1)) : g • V = V := by
  have hgi : ∀ y : Ω, g (g⁻¹ y) = y := fun y => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hg' : ∀ b : Ω, IsIntegral R b → (V.valuation (g⁻¹ b) < 1 ↔ V.valuation b < 1) := by
    intro b hb
    have := hg (g⁻¹ b) (hb.map ((g⁻¹ : Ω ≃ₐ[K] Ω).restrictScalars R))
    rw [hgi] at this
    exact this.symm
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  constructor
  · intro h
    have := map_mem_of_lt_one_iff R K Ω V hR g hg h
    rwa [hgi] at this
  · intro h
    exact map_mem_of_lt_one_iff R K Ω V hR g⁻¹ hg' h

include hR in

theorem mem_inertia_of_sub_lt_one (g : Ω ≃ₐ[K] Ω)
    (h : ∀ b : Ω, IsIntegral R b → V.valuation (g b - b) < 1) : g ∈ inertia K V := by
  have hg : g • V = V := smul_eq_of_lt_one_iff R K Ω V hR g fun b hb => lt_one_iff_of_sub_lt V (h b hb)
  rw [mem_inertia_iff]
  refine ⟨hg, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den_integral R K Ω V hR hx
  have hgs : V.valuation (g s) = 1 :=
    valuation_eq_one (mem_of_isIntegral V hR (hs.map (g.restrictScalars R))) (by
      rw [lt_one_iff_of_sub_lt V (h s hs), hs1]; exact lt_irrefl 1)
  have key : g s * (g x - x) = (g t - t) - x * (g s - s) := by
    rw [← e, map_mul]; ring
  have := congrArg V.valuation key
  rw [Valuation.map_mul, hgs, _root_.one_mul] at this
  rw [this]
  refine Valuation.map_sub_lt _ (h t ht) ?_
  rw [Valuation.map_mul]
  calc V.valuation x * V.valuation (g s - s) ≤ 1 * V.valuation (g s - s) :=
        mul_le_mul_left ((V.valuation_le_one_iff x).2 hx) _
    _ < 1 := by rw [_root_.one_mul]; exact h s hs

end crit

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj

theorem exists_mem_inertia_eq_on : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] (τ : L ≃ₐ[K] L), τ ∈ inertia K (V.comap (algebraMap L Ω)) →
    ∃ σ ∈ inertia K V, ∀ y : L, σ (y : Ω) = (τ y : Ω) := by
  first
  | exact @_root_.GlobalTheory.IntegralFractionLift.inertia_surjective
  | exact _root_.GlobalTheory.IntegralFractionLift.inertia_surjective
  | (apply _root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralFractionLift.inertia_surjective ..)

end GlobalTheory.InertiaRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandardStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  first | exact @GlobalTheory.WeilAdm.RealModel.exists_model | exact GlobalTheory.WeilAdm.RealModel.exists_model | (intros; apply GlobalTheory.WeilAdm.RealModel.exists_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalQuotientTransitionIsomorphisms
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace QuotTransition

section

variable {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
  (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)

lemma w_left : qU.left ≫ BU.hom = pullback.snd A.hom fU := Over.w qU

noncomputable abbrev src : Scheme.{0} := pullback qU.left (pullback.fst (BU.hom ≫ fU) fV)

noncomputable def toV : src fU fV A BU qU ⟶ pullback A.hom fV :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst A.hom fU) (pullback.snd _ _ ≫ pullback.snd _ _) (by
    have h1 := pullback.condition (f := A.hom) (g := fU)
    have h2 := pullback.condition (f := qU.left) (g := pullback.fst (BU.hom ≫ fU) fV)
    have h3 := pullback.condition (f := BU.hom ≫ fU) (g := fV)
    have h4 := w_left fU A BU qU
    simp only [Category.assoc] at h1 h2 h3 ⊢
    rw [h1, ← h4, Category.assoc, reassoc_of% h2, h3])

@[reassoc (attr := simp)]
lemma toV_fst : toV fU fV A BU qU ≫ pullback.fst A.hom fV =
    pullback.fst _ _ ≫ pullback.fst A.hom fU := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma toV_snd : toV fU fV A BU qU ≫ pullback.snd A.hom fV =
    pullback.snd _ _ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _

variable (H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)

lemma map_left_fst {T : Scheme.{0}} (f : T ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

lemma toV_comp_eq [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (hU : IsPullback ((fst ((Over.pullback fU).obj H) ((Over.pullback fU).obj A) ≫ (Over.pullback fU).map i) *
      snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A))
      (snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A)) qU qU)
    (hV : IsPullback ((fst ((Over.pullback fV).obj H) ((Over.pullback fV).obj A) ≫ (Over.pullback fV).map i) *
      snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A))
      (snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A)) qV qV)
    {T : Scheme.{0}} (u v : T ⟶ src fU fV A BU qU)
    (huv : u ≫ pullback.snd _ _ = v ≫ pullback.snd _ _) :
    u ≫ toV fU fV A BU qU ≫ qV.left = v ≫ toV fU fV A BU qU ≫ qV.left := by
  obtain ⟨yu, hyu_def⟩ : ∃ y, y = u ≫ pullback.fst qU.left (pullback.fst (BU.hom ≫ fU) fV) := ⟨_, rfl⟩
  obtain ⟨yv, hyv_def⟩ : ∃ y, y = v ≫ pullback.fst qU.left (pullback.fst (BU.hom ≫ fU) fV) := ⟨_, rfl⟩
  have hq : yu ≫ qU.left = yv ≫ qU.left := by
    simp only [hyu_def, hyv_def, Category.assoc, pullback.condition, reassoc_of% huv]
  have hs : yu ≫ pullback.snd A.hom fU = yv ≫ pullback.snd A.hom fU := by
    rw [← w_left fU A BU qU, reassoc_of% hq]
  let Tj : Over U := Over.mk (yv ≫ pullback.snd A.hom fU)
  let yu' : Tj ⟶ (Over.pullback fU).obj A := Over.homMk yu hs
  let yv' : Tj ⟶ (Over.pullback fU).obj A := Over.homMk yv rfl
  have hq' : yu' ≫ qU = yv' ≫ qU := Over.OverMorphism.ext hq
  let s := hU.lift yu' yv' hq' ≫ fst _ _
  have hyu : yu' = (s ≫ (Over.pullback fU).map i) * yv' := by
    have h1 := hU.lift_fst yu' yv' hq'
    rw [comp_mul, hU.lift_snd] at h1
    rw [Category.assoc, h1]
  have e1 : yv ≫ pullback.snd A.hom fU ≫ fU =
      u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV ≫ fV := by
    rw [← w_left fU A BU qU, hyv_def]
    simp only [Category.assoc]
    rw [reassoc_of% (pullback.condition (f := qU.left) (g := pullback.fst (BU.hom ≫ fU) fV)),
      pullback.condition, reassoc_of% huv]
  have hsw : s.left ≫ pullback.snd H.hom fU = yv ≫ pullback.snd A.hom fU := Over.w s
  have hc1 : (s.left ≫ pullback.fst H.hom fU) ≫ H.hom =
      (u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV) ≫ fV := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% hsw, e1]
  let Tk : Over V := Over.mk (u ≫ pullback.snd _ _ ≫ pullback.snd (BU.hom ≫ fU) fV)
  let s' : Tk ⟶ (Over.pullback fV).obj H :=
    Over.homMk (pullback.lift (s.left ≫ pullback.fst H.hom fU) (u ≫ pullback.snd _ _ ≫ pullback.snd _ _) hc1)
      (pullback.lift_snd _ _ _)
  let zu : Tk ⟶ (Over.pullback fV).obj A :=
    Over.homMk (u ≫ toV fU fV A BU qU) (by simp [Tk])
  let zv : Tk ⟶ (Over.pullback fV).obj A :=
    Over.homMk (v ≫ toV fU fV A BU qU) (by simp [Tk, reassoc_of% huv])
  have hc0 : (s.left ≫ pullback.fst H.hom fU ≫ i.left) ≫ A.hom = yv ≫ pullback.fst A.hom fU ≫ A.hom := by
    rw [Category.assoc, Category.assoc, Over.w i, pullback.condition, reassoc_of% hsw, pullback.condition]
  let x0 : Over.mk (yv ≫ pullback.fst A.hom fU ≫ A.hom) ⟶ A :=
    Over.homMk (s.left ≫ pullback.fst H.hom fU ≫ i.left) hc0
  let y0 : Over.mk (yv ≫ pullback.fst A.hom fU ≫ A.hom) ⟶ A :=
    Over.homMk (yv ≫ pullback.fst A.hom fU) (Category.assoc _ _ _)
  have mU := GlobalTheory.TorusToProper.mul_left_fst fU A (s ≫ (Over.pullback fU).map i) yv' x0 y0
    (by rw [Over.comp_left, Category.assoc, map_left_fst]; rfl) rfl
  have mV := GlobalTheory.TorusToProper.mul_left_fst fV A (s' ≫ (Over.pullback fV).map i) zv x0 y0
    (by rw [Over.comp_left, Category.assoc, map_left_fst]; simp only [x0, s', Over.homMk_left]; rw [pullback.lift_fst_assoc, Category.assoc]) (by simp [y0, zv, hyv_def])
  have key : zu = (s' ≫ (Over.pullback fV).map i) * zv := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [mV, ← mU, ← hyu]
      simp [zu, yu', hyu_def]
    · exact (Over.w zu).trans (Over.w ((s' ≫ (Over.pullback fV).map i) * zv)).symm
  have hk : zu ≫ qV = zv ≫ qV := by
    rw [key]
    have := lift s' zv ≫= hV.w
    simpa [comp_mul, ← Category.assoc] using this
  have := congrArg CommaMorphism.left hk
  simpa [zu, zv] using this

theorem exists_trans [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (hU : IsPullback ((fst ((Over.pullback fU).obj H) ((Over.pullback fU).obj A) ≫ (Over.pullback fU).map i) *
      snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A))
      (snd ((Over.pullback fU).obj H) ((Over.pullback fU).obj A)) qU qU)
    (hV : IsPullback ((fst ((Over.pullback fV).obj H) ((Over.pullback fV).obj A) ≫ (Over.pullback fV).map i) *
      snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A))
      (snd ((Over.pullback fV).obj H) ((Over.pullback fV).obj A)) qV qV) :
    ∃ b : pullback (BU.hom ≫ fU) fV ⟶ BV.left, b ≫ BV.hom = pullback.snd _ _ ∧
      ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left := by
  have hc : ∀ {T : Scheme.{0}} (u v : T ⟶ src fU fV A BU qU),
      u ≫ pullback.snd _ _ = v ≫ pullback.snd _ _ →
      u ≫ (toV fU fV A BU qU ≫ qV.left) = v ≫ (toV fU fV A BU qU ≫ qV.left) :=
    fun u v huv => toV_comp_eq fU fV A BU BV qU qV H i hU hV u v huv
  have fac := EffectiveEpi.fac (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV))
    (toV fU fV A BU qU ≫ qV.left) hc
  refine ⟨EffectiveEpi.desc (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV))
    (toV fU fV A BU qU ≫ qV.left) hc, ?_, ?_⟩
  · rw [← cancel_epi (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV)), reassoc_of% fac,
      w_left fV A BV qV, toV_snd]
  · intro T y z w h1 h2 h3
    have hw : w = pullback.lift y w h2.symm ≫ pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) :=
      (pullback.lift_snd _ _ _).symm
    have hz : pullback.lift y w h2.symm ≫ toV fU fV A BU qU = z := by
      apply pullback.hom_ext
      · rw [Category.assoc, toV_fst, pullback.lift_fst_assoc, h1]
      · rw [Category.assoc, toV_snd, pullback.lift_snd_assoc, h3]
    rw [hw, Category.assoc, fac, ← Category.assoc, hz]

end

lemma lift_comp_lift {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
    (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)
    [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    (b : pullback (BU.hom ≫ fU) fV ⟶ BV.left) (b' : pullback (BV.hom ≫ fV) fU ⟶ BU.left)
    (hb : b ≫ BV.hom = pullback.snd _ _)
    (cb : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left)
    (cb' : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fV) (z : T ⟶ pullback A.hom fU)
        (w : T ⟶ pullback (BV.hom ≫ fV) fU), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qV.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b' = z ≫ qU.left)
    (h₁ : b ≫ BV.hom ≫ fV = (pullback.fst _ _ ≫ BU.hom) ≫ fU)
    (h₂ : b' ≫ BU.hom ≫ fU = (pullback.fst _ _ ≫ BV.hom) ≫ fV) :
    pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁ ≫ pullback.lift b' (pullback.fst _ _ ≫ BV.hom) h₂ =
      𝟙 _ := by
  rw [← cancel_epi (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV)), Category.comp_id]
  have k1 : pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) ≫ b = toV fU fV A BU qU ≫ qV.left :=
    cb _ (pullback.fst _ _) (toV fU fV A BU qU) _ (toV_fst fU fV A BU qU).symm pullback.condition.symm
      (toV_snd fU fV A BU qU).symm
  have k2 := cb' _ (toV fU fV A BU qU) (pullback.fst _ _)
    (pullback.snd qU.left (pullback.fst (BU.hom ≫ fU) fV) ≫ pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁)
    (toV_fst fU fV A BU qU) (by rw [Category.assoc, pullback.lift_fst, k1])
    (by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← pullback.condition, Category.assoc,
      w_left fU A BU qU])
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, k2, pullback.condition]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc (pullback.lift b _ _),
      pullback.lift_fst, hb]

theorem isPullback_trans {S U V : Scheme.{0}} (fU : U ⟶ S) (fV : V ⟶ S) (A : Over S)
    (BU : Over U) (BV : Over V) (qU : (Over.pullback fU).obj A ⟶ BU) (qV : (Over.pullback fV).obj A ⟶ BV)
    [Flat qU.left] [Surjective qU.left] [QuasiCompact qU.left]
    [Flat qV.left] [Surjective qV.left] [QuasiCompact qV.left]
    (b : pullback (BU.hom ≫ fU) fV ⟶ BV.left) (b' : pullback (BV.hom ≫ fV) fU ⟶ BU.left)
    (hb : b ≫ BV.hom = pullback.snd _ _) (hb' : b' ≫ BU.hom = pullback.snd _ _)
    (cb : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fU) (z : T ⟶ pullback A.hom fV)
        (w : T ⟶ pullback (BU.hom ≫ fU) fV), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qU.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ qV.left)
    (cb' : ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom fV) (z : T ⟶ pullback A.hom fU)
        (w : T ⟶ pullback (BV.hom ≫ fV) fU), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ qV.left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b' = z ≫ qU.left) :
    IsPullback b (pullback.fst _ _ ≫ BU.hom) (BV.hom ≫ fV) fU := by
  have h₁ : b ≫ BV.hom ≫ fV = (pullback.fst _ _ ≫ BU.hom) ≫ fU := by
    rw [reassoc_of% hb, Category.assoc]; exact pullback.condition.symm
  have h₂ : b' ≫ BU.hom ≫ fU = (pullback.fst _ _ ≫ BV.hom) ≫ fV := by
    rw [reassoc_of% hb', Category.assoc]; exact pullback.condition.symm
  let e : pullback (BU.hom ≫ fU) fV ≅ pullback (BV.hom ≫ fV) fU :=
    { hom := pullback.lift b (pullback.fst _ _ ≫ BU.hom) h₁
      inv := pullback.lift b' (pullback.fst _ _ ≫ BV.hom) h₂
      hom_inv_id := lift_comp_lift fU fV A BU BV qU qV b b' hb cb cb' h₁ h₂
      inv_hom_id := lift_comp_lift fV fU A BV BU qV qU b' b hb' cb' cb h₂ h₁ }
  exact IsPullback.of_iso_pullback ⟨h₁⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem exists_transition : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) →
    ∃ b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left,
      (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) ∧
      (∀ j k, IsPullback (b j k) (pullback.fst _ _ ≫ (B j).hom) ((B k).hom ≫ 𝒰.f k) (𝒰.f j)) ∧
      ∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left := by
  intro S 𝒰 A H _ _ i B q hf hs hqc hpb
  have key : ∀ j k, ∃ b : pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left,
      b ≫ (B k).hom = pullback.snd _ _ ∧
      ∀ (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ →
        w ≫ b = z ≫ (q k).left := fun j k => by
    haveI := hf j; haveI := hs j; haveI := hqc j
    exact exists_trans (𝒰.f j) (𝒰.f k) A (B j) (B k) (q j) (q k) H i (hpb j) (hpb k)
  choose b hb1 hb3 using key
  refine ⟨b, hb1, fun j k => ?_, hb3⟩
  haveI := hf j; haveI := hs j; haveI := hqc j
  haveI := hf k; haveI := hs k; haveI := hqc k
  exact isPullback_trans (𝒰.f j) (𝒰.f k) A (B j) (B k) (q j) (q k) (b j k) (b k j) (hb1 j k) (hb1 k j)
    (hb3 j k) (hb3 k j)

end QuotTransition
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSpaceDualVectorTraceFormStatement
section
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedSpace_dual_vector_traceForm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z : mixedEmbedding.mixedSpace F, z ≠ 0 → ∃ u, ℓ (z * u) ≠ 0) →
    ∀ lam : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ, ∃ u : κ → mixedEmbedding.mixedSpace F,
      ∀ x, ℓ (∑ k, x k * u k) = lam x := by
  first | exact @GlobalTheory.dualform | exact GlobalTheory.dualform | (intros; apply GlobalTheory.dualform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ¬ IsProper G.hom → ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  first | exact @GlobalTheory.RatCurve.exists_rational_curve | exact GlobalTheory.RatCurve.exists_rational_curve | (intros; apply GlobalTheory.RatCurve.exists_rational_curve <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensEtaleGenericallyFiniteDominantStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_opens_etale_generically_finite_dominant : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  first | exact @GlobalTheory.GenEtale.exists_opens_etale | exact GlobalTheory.GenEtale.exists_opens_etale | (intros; apply GlobalTheory.GenEtale.exists_opens_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecDetDualTensorSupportStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratSec_det_dual_tensor_support : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (F Q : X.Modules) (g' : VMetric p F 1) (g : VMetric p Q 1) (H' : g'.IsCInf) (H : g.IsCInf) (s : F ⟶ Q), s ≠ 0 → ∃ (r : ((VMetric.det H').dual.tens (VMetric.det H)).B.ι → X.functionFieldˣ) (hr : IsRatSec ((VMetric.det H').dual.tens (VMetric.det H)).B r), (∀ z ∈ (((VMetric.det H').dual.tens (VMetric.det H)).div hr).supp, VanishesAt s z) ∧ ∀ σ : k →+* ℂ, ∀ y ∈ offSupp p σ (((VMetric.det H').dual.tens (VMetric.det H)).div hr), ∀ (U : X.Opens) (t : Γ(F, U)), IsFrame (fun _ : Fin 1 => t) → y ∈ ptsIn p σ U → 0 < ((g.met σ).form (s.app U t) (s.app U t) y).re ∧ logNorm (((VMetric.det H').dual.tens (VMetric.det H)).φ σ) r y = Real.log (((g.met σ).form (s.app U t) (s.app U t) y).re / ((g'.met σ).form t t y).re) / 2 := by
  first | exact @GlobalTheory.LineHomSec.exists_ratSec | exact GlobalTheory.LineHomSec.exists_ratSec | (intros; apply GlobalTheory.LineHomSec.exists_ratSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularAlterationArithmetic
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RegAlteration

theorem exists_regular_alteration : Published.RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (ρ : Y' ⟶ Y), CxForm.IsRegVar (ρ ≫ q) e ∧ ρ (genericPoint Y') = genericPoint Y ∧ ρ.residueDegree (genericPoint Y') ≠ 0 := by
  intro H k _ Y _ q e h
  obtain ⟨Z, _, ρ, hZ, hr, hg, hd⟩ := H Y _ e (ShFam.Pad.isArithVar_toSpZ h)
  exact ⟨Z, inferInstance, ρ, ⟨RegCoverExists.isArithVar_of_toSpZ h.isDomain h.finite _ hZ, hr⟩, hg, hd⟩

end GlobalTheory.RegAlteration

end
end

