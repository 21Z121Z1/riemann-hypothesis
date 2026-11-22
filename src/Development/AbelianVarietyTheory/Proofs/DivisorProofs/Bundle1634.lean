import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthDvdOfNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.FixAllGood
open GlobalTheory.Hk3 (UnrPl VacFix)

theorem unrPl_mul {D : D7} {P : Pl D.host.E} {χ χ' : (AE D)ˣ →* Circle} (h : UnrPl P χ) (h' : UnrPl P χ') :
    UnrPl P (χ * χ') := fun e f hP x a b c => by
  rw [MonoidHom.mul_apply, h e f hP x a b c, h' e f hP x a b c, mul_one]

theorem unrPl_inv {D : D7} {P : Pl D.host.E} {χ : (AE D)ˣ →* Circle} (h : UnrPl P χ) :
    UnrPl P χ⁻¹ := fun e f hP x a b c => by
  rw [MonoidHom.inv_apply, h e f hP x a b c, inv_one]

theorem unrPl_chrStep {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrStep μ η j).1 ∧ UnrPl P (Lift.chrStep μ η j).2 := by
  unfold Lift.chrStep
  split_ifs
  · exact ⟨unrPl_mul hμ (unrPl_inv hη), hμ⟩
  · exact ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem unrPl_chrTh {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrTh μ η j).1 ∧ UnrPl P (Lift.chrTh μ η j).2 :=
  ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem fixAll_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ t P, Good R.toRealDat t P → conjPl P = P → FixAll R.toRealDat t P := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h _ t P hP _
  have hu := GlobalTheory.T.splittingCharacters_unramified_offLevels R.toRealDat F.lv2 h.base.lev t P hP
  have hm := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · have hc := unrPl_chrStep (hu.2 (k + 1) (Nat.le_add_left _ _) hk.le) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullY t k hk).datum hc.1 hc.2
  · have hc := unrPl_chrStep (hu.2 D.R.m (by omega) le_rfl) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullX t).datum hc.1 hc.2
  · have hc := unrPl_chrTh (hu.2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullP i t).datum hc.1 hc.2

end GlobalTheory.FixAllGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusSecPullLin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

variable {R : Type} [CommRing R] {m N : ℕ}

def lin (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : Fin (m + 1) → (O1 R N).Sec :=
  fun i => ∑ j, GlobalTheory.AbLaw.cst (PSpace.str R N) ⊤ (a i j) • coord R N j

def dom (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : (PSpace R N).Opens := ⨆ i, nonzeroLocus (lin a i)

theorem iSup_nonzeroLocus_secPull_lin (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) :
    ⨆ i, nonzeroLocus (GlobalTheory.Cartier.secPull (lin a i) (dom a).ι) = ⊤ := by
  simp only [GlobalTheory.Cartier.nonzeroLocus_secPull]
  rw [← Scheme.Hom.preimage_iSup]
  exact (dom a).ι_preimage_self

def proj (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) : (dom a).toScheme ⟶ PSpace R m :=
  toProj ((dom a).ι ≫ PSpace.str R N) (fun i => GlobalTheory.Cartier.secPull (lin a i) (dom a).ι)
    (iSup_nonzeroLocus_secPull_lin a)

def liftDom {X : Scheme.{0}} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (φ : X ⟶ PSpace R N)
    (h : φ ⁻¹ᵁ dom a = ⊤) : X ⟶ (dom a).toScheme :=
  IsOpenImmersion.lift (dom a).ι φ (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x ∈ φ ⁻¹ᵁ dom a := h.ge trivial
    exact hx)

theorem liftDom_fac {X : Scheme.{0}} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (φ : X ⟶ PSpace R N)
    (h : φ ⁻¹ᵁ dom a = ⊤) : liftDom a φ h ≫ (dom a).ι = φ :=
  IsOpenImmersion.lift_fac _ _ _

end GlobalTheory.SpanVA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElement
section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem exists_aut (φ₀ φ : E →+* C) : ∃ g : E ≃ₐ[ℚ] E, φ = φ₀.comp g.toRingHom := by
  let K := AlgebraicClosure C
  let ι := algebraMap C K
  let F : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] K) := fun g => ((ι.comp φ₀).comp g.toRingHom).toRatAlgHom
  have hF : Function.Injective F := by
    intro g h hgh
    ext x
    have := congrArg (fun f : E →ₐ[ℚ] K => f x) hgh
    simp only [F, RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
    exact φ₀.injective (ι.injective this)
  have hbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hF, ?_⟩
    rw [AlgHom.card, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  obtain ⟨g, hg⟩ := hbij.2 ((ι.comp φ).toRatAlgHom)
  refine ⟨g, ?_⟩
  ext x
  have := congrArg (fun f : E →ₐ[ℚ] K => f x) hg
  simp only [F, RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
  exact (ι.injective this).symm

theorem sum_aut_eq_trace (φ₀ : E →+* C) (x : E) :
    ∑ g : E ≃ₐ[ℚ] E, φ₀ (g x) = algebraMap ℚ C (Algebra.trace ℚ E x) := by
  have h := GlobalTheory.ColengthDifferent.sum_eq_trace (fun g : E ≃ₐ[ℚ] E => φ₀.comp g.toRingHom) ?_
    (by rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]) x
  · simpa using h
  · intro g h hgh
    ext y
    exact φ₀.injective (RingHom.congr_fun hgh y)

theorem comp_eq_iff (φ₀ : E →+* C) (h : E ≃ₐ[ℚ] E) : φ₀.comp h.toRingHom = φ₀ ↔ h = 1 := by
  constructor
  · intro hh
    ext x
    exact φ₀.injective (RingHom.congr_fun hh x)
  · rintro rfl
    ext x
    rfl

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem map_expand (φ₀ : E →+* C) (x : E) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * algebraMap ℚ C (Algebra.trace ℚ E (integralBasis E k * x)) = φ₀ x := by
  set b := integralBasis E
  conv_rhs => rw [← b.traceDual.sum_repr x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul φ₀, mul_comm x (b k),
    mul_comm (φ₀ (b.traceDual k))]
  congr 1
  exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ C) (φ₀.comp (algebraMap ℚ E))) _

theorem orth_aut (φ₀ : E →+* C) (h : E ≃ₐ[ℚ] E) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * φ₀ (h (integralBasis E k)) = if h = 1 then 1 else 0 := by
  set b := integralBasis E
  let f : (E ≃ₐ[ℚ] E) → (E →* C) := fun g => (φ₀.comp g.toRingHom).toMonoidHom
  have hf : Function.Injective f := by
    intro g g' hgg
    ext y
    exact φ₀.injective (DFunLike.congr_fun hgg y)
  have li := (linearIndependent_monoidHom E C).comp f hf
  let c : (E ≃ₐ[ℚ] E) → C := fun g =>
    (∑ k, φ₀ (b.traceDual k) * φ₀ (g (b k))) - if g = 1 then 1 else 0
  have hc : ∑ g, c g • ((fun f : E →* C => (f : E → C)) ∘ f) g = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, f,
      MonoidHom.coe_coe, RingHom.coe_comp, RingHom.toMonoidHom_eq_coe]
    have e1 : ∀ g : E ≃ₐ[ℚ] E, c g * φ₀ (g x) =
        (∑ k, φ₀ (b.traceDual k) * φ₀ (g (b k * x))) - (if g = 1 then φ₀ x else 0) := by
      intro g
      simp only [c, sub_mul, Finset.sum_mul, map_mul, mul_assoc]
      split_ifs with hg
      · subst hg; simp
      · simp
    show ∑ g, c g * φ₀ (g x) = 0
    rw [Finset.sum_congr rfl fun g _ => e1 g, Finset.sum_sub_distrib, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp_rw [sum_aut_eq_trace φ₀]
    rw [map_expand φ₀ x]
    simp
  have := Fintype.linearIndependent_iff.mp li c hc h
  simp only [c, sub_eq_zero] at this
  exact this

theorem orth (φ₀ σ : E →+* C) :
    ∑ k, φ₀ ((integralBasis E).traceDual k) * σ (integralBasis E k) = if σ = φ₀ then 1 else 0 := by
  obtain ⟨h, rfl⟩ := exists_aut φ₀ σ
  have := orth_aut φ₀ h
  rw [comp_eq_iff]
  exact this

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

variable {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {C : Type} [Field C] [CharZero C]

theorem trace_mul_traceDual (a : 𝓞 E) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E ((a : E) * (integralBasis E).traceDual k) =
      (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) := by
  have h := ((integralBasis E).traceDual).traceDual_repr_apply (algebraMap (𝓞 E) E a) k
  rw [Module.Basis.traceDual_traceDual, integralBasis_repr_apply, Algebra.traceForm_apply] at h
  rw [← eq_intCast (algebraMap ℤ ℚ), h]

theorem base {O : Type} [CommRing O] [Algebra O C] {v : Valuation C ℝ≥0} (hv : v.Integers O)
    (φ₀ : E →+* C) :
    ∃ δ : C, δ ≠ 0 ∧ (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C,
      ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ₀ then δ else 0) ∧
    ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C,
      ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ₀ then s else 0) → v s ≤ v δ := by
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) := (integralBasis E).index_nonempty
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ
    (fun k => v (φ₀ ((integralBasis E).traceDual k))) Finset.univ_nonempty
  have hy : φ₀ ((integralBasis E).traceDual k₀) ≠ 0 :=
    (map_ne_zero φ₀).2 ((integralBasis E).traceDual.ne_zero k₀)
  have hvy : v (φ₀ ((integralBasis E).traceDual k₀)) ≠ 0 := (Valuation.ne_zero_iff v).2 hy
  refine ⟨(φ₀ ((integralBasis E).traceDual k₀))⁻¹, inv_ne_zero hy, ?_, ?_⟩
  · have hr : ∀ k, ∃ o : O, algebraMap O C o =
        (φ₀ ((integralBasis E).traceDual k₀))⁻¹ * φ₀ ((integralBasis E).traceDual k) := by
      intro k
      apply hv.exists_of_le_one
      rw [map_mul, map_inv₀, inv_mul_le_iff₀ (pos_iff_ne_zero.2 hvy), mul_one]
      exact hk₀ k (Finset.mem_univ _)
    choose r hr using hr
    let e := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
    refine ⟨Fintype.card _, fun i => r (e.symm i), fun i => RingOfIntegers.basis E (e.symm i),
      fun σ => ?_⟩
    rw [Equiv.sum_comp e.symm (fun k => algebraMap O C (r k) * σ (RingOfIntegers.basis E k))]
    have h2 : ∀ k, σ (RingOfIntegers.basis E k : E) = σ (integralBasis E k) := by
      intro k
      rw [integralBasis_apply]
    simp_rw [hr, h2, mul_assoc, ← Finset.mul_sum]
    rw [orth φ₀ σ]
    split_ifs <;> simp
  · intro n r a s hs
    have h1 : ∀ g : E ≃ₐ[ℚ] E, ∑ k, algebraMap O C (r k) * φ₀ (g ((a k : E) * (integralBasis E).traceDual k₀)) =
        if g = 1 then s * φ₀ ((integralBasis E).traceDual k₀) else 0 := by
      intro g
      have := hs (φ₀.comp g.toRingHom)
      rw [comp_eq_iff] at this
      have e3 : ∀ k, algebraMap O C (r k) * φ₀ (g ((a k : E) * (integralBasis E).traceDual k₀)) =
          (algebraMap O C (r k) * φ₀ (g (a k))) * φ₀ (g ((integralBasis E).traceDual k₀)) := by
        intro k
        rw [map_mul, map_mul, mul_assoc]
      rw [Finset.sum_congr rfl fun k _ => e3 k, ← Finset.sum_mul]
      erw [this]
      split_ifs with hg
      · subst hg; rfl
      · simp
    have h2 := Finset.sum_congr rfl fun g (_ : g ∈ (Finset.univ : Finset (E ≃ₐ[ℚ] E))) => h1 g
    rw [Finset.sum_comm] at h2
    simp_rw [← Finset.mul_sum, sum_aut_eq_trace φ₀, trace_mul_traceDual] at h2
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    have hle : v (s * φ₀ ((integralBasis E).traceDual k₀)) ≤ 1 := by
      rw [← h2]
      have : ∑ k, algebraMap O C (r k) * algebraMap ℚ C (((RingOfIntegers.basis E).repr (a k) k₀ : ℤ) : ℚ) =
          algebraMap O C (∑ k, r k * (((RingOfIntegers.basis E).repr (a k) k₀ : ℤ) : O)) := by
        simp [map_sum, map_mul, map_intCast]
      rw [this]
      exact hv.map_le_one _
    calc v s = v (s * φ₀ ((integralBasis E).traceDual k₀)) * v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := by
          rw [← map_mul, mul_assoc, mul_inv_cancel₀ hy, mul_one]
      _ ≤ 1 * v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := by gcongr
      _ = v (φ₀ ((integralBasis E).traceDual k₀))⁻¹ := one_mul _

end GlobalTheory.InvDifferentArith

namespace GlobalTheory.InvDifferentArith

theorem indicator_inverseDifferent : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (C : Type) [Field C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∃ δ : C, δ ≠ 0 ∧ ∀ φ : E →+* C, (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then δ else 0) ∧ ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v δ := by
  intro E _ _ _ C _ _ v O _ _ hv
  by_cases hne : Nonempty (E →+* C)
  swap
  · exact ⟨1, one_ne_zero, fun φ => (hne ⟨φ⟩).elim⟩
  obtain ⟨φ₀⟩ := hne
  obtain ⟨δ, hδ0, ha, hb⟩ := base hv φ₀
  refine ⟨δ, hδ0, fun φ => ?_⟩
  obtain ⟨g, rfl⟩ := exists_aut φ₀ φ
  constructor
  · obtain ⟨n, r, a, h⟩ := ha
    refine ⟨n, r, fun k => RingOfIntegers.mapRingHom g.symm.toRingHom (a k), fun σ => ?_⟩
    have hσ := h (σ.comp g.symm.toRingHom)
    have e1 : σ.comp g.symm.toRingHom = φ₀ ↔ σ = φ₀.comp g.toRingHom := by
      constructor
      · rintro rfl
        ext x
        simp
      · rintro rfl
        ext x
        simp
    rw [if_congr e1 rfl rfl] at hσ
    rw [← hσ]
    rfl
  · intro n r a s hs
    apply hb n r (fun k => RingOfIntegers.mapRingHom g.toRingHom (a k)) s
    intro τ
    have hτ := hs (τ.comp g.toRingHom)
    have e1 : τ.comp g.toRingHom = φ₀.comp g.toRingHom ↔ τ = φ₀ := by
      constructor
      · intro hh
        ext x
        have := RingHom.congr_fun hh (g.symm x)
        simpa using this
      · rintro rfl
        rfl
    rw [if_congr e1 rfl rfl] at hτ
    rw [← hτ]
    rfl

end GlobalTheory.InvDifferentArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChart
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_eq_integral_chart_of_support : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld)
    (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) →
    A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  intro M _ _ _ _ _ _ n A α i K hα hK hKs h0
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set r : A.ι → V n → ℝ := fun j v => (dens (A.loc α j v)).re with hr
  have dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

  have hc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      r j (A.e j y) = ‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2 * r k (A.e k y) := by
    intro j k y hj hk
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    have h2 := A.loc_crd α (⟨(k, y), hk⟩ : A.Pt)
    have h3 := hα.compat (⟨(j, y), hj⟩ : A.Pt) ⟨(k, y), hk⟩ rfl
    simp only [hr]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul]
    rfl

  have hz : ∀ j y, y ∈ (A.e j).source → y ∉ K → r j (A.e j y) = 0 := by
    intro j y hj hy
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    simp only [hr]
    erw [h1, h0 _ hy, dens_zero]
    rfl

  have hpart : ∀ ε : ℤˣ, A.part α ε univ =
      ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    set ρ : A.ι → M → ENNReal := fun j y => ENNReal.ofReal (((ε : ℤ) : ℝ) * r j (A.e j y)) with hρ
    have hp : A.part α ε = ChartGlue.glueMeas A.e ρ := rfl
    have hρc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
        ρ j y = ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) * ρ k y := by
      intro j k y hj hk
      simp only [hρ]
      rw [hc j k y hj hk, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    have hcompl : ChartGlue.glueMeas A.e ρ Kᶜ = 0 := by
      have key : ChartGlue.glueMeas A.e ρ ≤ (ChartGlue.glueMeas A.e ρ).restrict K := iSup_le fun j => by
        have e : ChartGlue.chartMeas (A.e j) (ρ j) Kᶜ = 0 := by
          rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
          refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
            ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
          rintro _ ⟨y, hy, rfl⟩
          simp only [hρ, (A.e j).left_inv hy.1, hz j y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero, Pi.zero_apply]
        rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
        exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j) (ρ j)) j)
      refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
      rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
    rw [hp, ← measure_add_measure_compl hKm, hcompl, add_zero,
      ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hKm hKs, ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs]
    refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hKm hKs) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [hρ, (A.e i).left_inv (hKs hy)]

  have hBc : IsCompact (A.e i '' K) := hK.image_of_continuousOn ((A.e i).continuousOn.mono hKs)
  have hBt : A.e i '' K ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hKs hy)
  have hH0 : ∀ v ∉ A.e i '' K, r i v = 0 := by
    intro v hv
    by_cases ht : v ∈ (A.e i).target
    · have hs := (A.e i).map_target ht
      have hnK : (A.e i).symm v ∉ K := fun hk => hv ⟨_, hk, (A.e i).right_inv ht⟩
      have := hz i _ hs hnK
      rwa [(A.e i).right_inv ht] at this
    · simp [hr, loc, ht, dens_zero]
  have hcon : ContinuousOn (r i) (A.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)
  have hHc : Continuous (r i) := continuous_iff_continuousAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact hcon.continuousAt ((A.e i).open_target.mem_nhds ht)
    · have : r i =ᶠ[𝓝 v] fun _ => 0 := by
        filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds (fun h => ht (hBt h))] with w hw
        exact hH0 w hw
      exact continuousAt_const.congr this.symm
  have hHi : Integrable (r i) := hHc.integrable_of_hasCompactSupport (HasCompactSupport.intro hBc hH0)
  have hl : ∀ ε : ℤˣ, ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) =
      ∫⁻ v, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    rw [← lintegral_indicator hBc.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A.e i '' K
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, hH0 v hv, mul_zero, ENNReal.ofReal_zero]
  have e1 := hpart 1
  have e2 := hpart (-1)
  rw [hl] at e1 e2
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_one_mul] at e1 e2
  simp only [GlobalTheory.CxForm.HolAtlas.integral, Measure.real, e1, e2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi).symm

end GlobalTheory.CxForm.HolAtlas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeBaseChangeFieldAndCommStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_and_comm_baseChange_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsAbelianScheme ((Over.pullback (spMap (algebraMap K L))).obj A) ∧ IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A) := by
  first | exact @GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm | exact GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm | (intros; apply GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfChartsSurjectiveImage
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotAbelian

theorem isAbelianScheme_of_charts_of_surjective :
    ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) [GrpObj A] [GrpObj G] (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) [∀ j, GrpObj (B j)] (ψ : ∀ j, (B j).left ⟶ G.left),
    IsAbelianScheme A → IsCommMonObj G → Surjective Q.left → (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) →
    (∀ j, IsAbelianScheme (B j)) → IsAbelianScheme G := by
  intro S 𝒰 A G _ _ Q B _ ψ hA hG hQ hψ hB
  have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have hsm : Smooth G.hom := GlobalTheory.GroupGlue.of_charts @Smooth hψ fun j => (hB j).smooth
  have hpr : IsProper G.hom := GlobalTheory.GroupGlue.of_charts @IsProper hψ fun j => (hB j).proper
  have hw : Q.left ≫ G.hom = A.hom := Over.w Q
  have := hA.geomConnected
  have : GeometricallyConnected (Q.left ≫ G.hom) := by rw [hw]; infer_instance
  exact ⟨hG, hsm, hpr, GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp Q.left G.hom⟩

end GlobalTheory.QuotAbelian
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProperStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper G.hom → IsAbelianScheme G := by
  first | exact @GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper | exact GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper | (intros; apply GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper <;> assumption)
end

