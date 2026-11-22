import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntUnitOfMulLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FilteredIsoOfFilZero
section
noncomputable section

namespace GlobalTheory.DeRhamCompare

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]

def charLatticeOf (hinj : Function.Injective (algebraMap O LL)) (χ : G →* LLˣ)
    (hχ : ∀ g, ∃ a : O, algebraMap O LL a = χ g) : Lattice (O := O) (charRep χ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := hχ g
    refine ⟨c * a, ?_⟩
    change algebraMap O LL (c * a) = (χ g : LL) * algebraMap O LL a
    rw [map_mul, hc]
  fg := by
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have h : (1 : LL) ∈ Submodule.span LL (LinearMap.range (Algebra.linearMap O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h

variable [TopologicalSpace G] [TopologicalSpace LL]

def charLocLat (Qp : Type) [Field Qp] [Algebra Qp LL] [IsTopologicalRing LL]
    (hinj : Function.Injective (algebraMap O LL)) (χ : G →* LLˣ)
    (hχ : ∀ g, ∃ a : O, algebraMap O LL a = χ g) (hc : Continuous fun g => (χ g : LL)) :
    LocLat G Qp LL O where
  V := LL
  ρ := charRep χ
  cont := fun _ => hc.mul continuous_const
  L := charLatticeOf hinj χ hχ

section Whole

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  {ρ : Representation LL G V} {ρ' : Representation LL G V'}

omit [TopologicalSpace G] [TopologicalSpace LL]

end Whole

end Generic

section At

variable (K LL : FinExt l)

def cycLat : DualExactSequence.Lat K LL :=
  charLocLat ℚ_[l] Subtype.val_injective (cycLL (P.PD K) ↥LL.1)
    (fun g => ⟨algebraMap ℤ_[l] ↥(OL LL) ⟨_, ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).1 g).le⟩, by
      change _ = algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])
      rw [P.PD_χ]
      rfl⟩)
    (by
      change Continuous fun g : ↥(GK K) =>
        algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l])
      simp only [P.PD_χ]
      exact (continuous_algebraMap ℚ_[l] ↥LL.1).comp
        ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1.comp continuous_subtype_val))

end At

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem dualExactSequence_mapdR_eq {K LL : _root_.Formalism.BasicNotions.Loc.FinExt l}
    {T T' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.mapdR P f = _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.mapdR (Qp := ℚ_[l]) (BdR := P.R.BdR) f :=
  rfl

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem strictness_of_dualExactSequence_strict
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore
  · intro K s LL hg T₀ T₁ T₂ f g hf hg' hi he hs h₀ h₁ h₂ τ a
    obtain ⟨k₁, k₂, k₃⟩ := h K s LL hg T₀ T₁ T₂ f g ⟨hf, hg', hi, he, hs⟩ h₀ h₁ h₂ τ a
    simp only [dualExactSequence_mapdR_eq] at k₁ k₂ k₃
    refine ⟨k₁, ?_, ?_⟩
    · ext y
      simpa [Submodule.mem_inf] using k₂ y
    · ext z
      simpa using k₃ z

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
private theorem dualExactSequence_strict_of_strictness
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.StrictCore at h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.OverGood
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.StrictAt _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.IsSES _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.SubSES
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Emb
  · intro K s LL hg T₀ T₁ T₂ f g hfg h₀ h₁ h₂ τ a
    obtain ⟨hf, hg', hi, he, hs⟩ := hfg
    have k := h K s LL hg T₀ T₁ T₂ f g
    have k' := k hf hg' hi he hs
    have k'' := k' h₀ h₁ h₂
    have k3 := k'' τ
    have k4 := k3 a
    obtain ⟨k₁, k₂, k₃⟩ := k4
    refine ⟨k₁, fun y => ?_, fun z => ?_⟩
    · have := SetLike.ext_iff.mp k₂ y
      simpa [Submodule.mem_inf, dualExactSequence_mapdR_eq] using this
    · have := SetLike.ext_iff.mp k₃ z
      simpa [dualExactSequence_mapdR_eq] using this

open Module TensorProduct in
variable {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) in
theorem _root_.GlobalTheory.DeRhamCompare.strict_iff :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.Strict l P ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  ⟨strictness_of_dualExactSequence_strict P,
    dualExactSequence_strict_of_strictness P⟩

end GlobalTheory.DeRhamCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuot
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def levCongr {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (e : M ≃ₗ[O] N) (c : O) : Lev M c ≃ Lev N c where
  toFun x := Lev.mk (e x.val) (by rw [← map_smul, Lev.smul_val, map_zero])
  invFun y := Lev.mk (e.symm y.val) (by rw [← map_smul, Lev.smul_val, map_zero])
  left_inv x := Lev.ext (by simp [Lev.val_mk])
  right_inv y := Lev.ext (by simp [Lev.val_mk])

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def divPowQ (ϖ : O) (n : ℕ) : O →ₗ[O] Formalism.NG.KO O :=
  (1 : Submodule O (FractionRing O)).mkQ ∘ₗ
    LinearMap.mulLeft O ((algebraMap O (FractionRing O) ϖ ^ n)⁻¹) ∘ₗ
      Algebra.linearMap O (FractionRing O)

theorem divPowQ_apply (ϖ : O) (n : ℕ) (a : O) :
    divPowQ ϖ n a = Submodule.Quotient.mk
      ((algebraMap O (FractionRing O) ϖ ^ n)⁻¹ * algebraMap O (FractionRing O) a) := rfl

theorem ker_divPowQ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    LinearMap.ker (divPowQ ϖ n) = Ideal.span {ϖ ^ n} := by
  have hπ : (algebraMap O (FractionRing O) ϖ) ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ)
  ext a
  rw [LinearMap.mem_ker, divPowQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
    rw [map_mul, map_pow, hb, mul_comm, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    rw [map_mul, map_pow, mul_comm (algebraMap O (FractionRing O) b), ← mul_assoc,
      inv_mul_cancel₀ hπ, one_mul]

theorem range_divPowQ {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    LinearMap.range (divPowQ ϖ n) = LinearMap.ker ((ϖ ^ n) • LinearMap.id : Formalism.NG.KO O →ₗ[O] Formalism.NG.KO O) := by
  have hπ : (algebraMap O (FractionRing O) ϖ) ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ)
  ext y
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨a, rfl⟩
    rw [divPowQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_one, Algebra.smul_def, map_pow, ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    exact ⟨a, rfl⟩
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one,
      Algebra.smul_def, map_pow] at hy
    obtain ⟨b, hb⟩ := hy
    refine ⟨b, ?_⟩
    rw [divPowQ_apply, hb, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

theorem natCard_lev_KO {ϖ : O} (hϖ : ϖ ≠ 0) (n : ℕ) :
    Nat.card (Lev (Formalism.NG.KO O) (ϖ ^ n)) = Nat.card (O ⧸ Ideal.span {ϖ ^ n}) := by
  have h1 : Nat.card (Lev (Formalism.NG.KO O) (ϖ ^ n)) = Nat.card (LinearMap.range (divPowQ ϖ n)) := by
    rw [range_divPowQ hϖ n]; rfl
  rw [h1, ← Nat.card_congr (LinearMap.quotKerEquivRange (divPowQ ϖ n)).toEquiv, ker_divPowQ hϖ n]

theorem natCard_quot_pow {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {ϖ ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hp : (Ideal.span {ϖ}).IsPrime := hϖ.maximalIdeal_eq ▸ inferInstance
  have hq := cardQuot_pow_of_prime (P := Ideal.span {ϖ})
    (fun h => hϖ.ne_zero (Ideal.span_singleton_eq_bot.1 h)) (i := n)
  rw [Ideal.span_singleton_pow, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  rw [hq, ← hϖ.maximalIdeal_eq]
  rfl

theorem lev_pow_card {ϖ : O} (hϖ : Irreducible ϖ) {M : Type} [AddCommGroup M] [Module O M]
    (e : M ≃ₗ[O] Formalism.NG.KO O) (n : ℕ) [Finite (IsLocalRing.ResidueField O)] :
    Finite (Lev M (ϖ ^ n)) ∧
      Nat.card (Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  have hc : Nat.card (Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
    rw [Nat.card_congr (levCongr e (ϖ ^ n)), natCard_lev_KO hϖ.ne_zero, natCard_quot_pow hϖ]
  refine ⟨Nat.finite_of_card_ne_zero ?_, hc⟩
  rw [hc]
  exact pow_ne_zero _ Nat.card_pos.ne'

end DVR

theorem levKO_card : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ n : ℕ,
    Finite (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) ∧
      Nat.card (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  fun hϖ _ _ _ e n => lev_pow_card hϖ e n

end GlobalTheory.ShapeNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvr
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem finite_residueField_of_compact_isAdic :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  intro O _ _ _ _ _ _ h
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
    have := (isAdic_iff.mp h).1 1
    simpa using this
  have hfin : Finite (O ⧸ (IsLocalRing.maximalIdeal O).toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact hfin

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSelfDualIntegralHermitianLatticesModUnits
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.HullClasses

theorem exists_unit_mulLat_mem_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x →
    ∀ c : K.O, c ≠ 0 → ∃ S : Set (Submodule K.O B.A), S.Finite ∧ (∀ J ∈ S, IsLat K.O K.E J) ∧
      ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
        (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) →
        (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
          (algebraMap K.O K.E).range) →
        ∃ t ∈ B.T, mulLat K.O (t : B.A) J ∈ S :=
  fun K B hsep x _ _ c hc0 =>
    finite_mod_T_of K B (GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra K B hsep) (GlobalTheory.T.exists_finset_cosets_integral_norm_units K B hsep) (GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B) x c hc0

end GlobalTheory.HullClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformKProdLocallyConstantCompactSuppo
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.FourKTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def betaK (A : Et F E) : LinearMap.BilinForm F (A.K × A.K) :=
  (Algebra.traceForm F A.K).compl₁₂ (LinearMap.fst F A.K A.K) (LinearMap.snd F A.K A.K) +
    (Algebra.traceForm F A.K).compl₁₂ (LinearMap.snd F A.K A.K) (LinearMap.fst F A.K A.K)

theorem betaK_apply (A : Et F E) (x y : A.K × A.K) :
    betaK A x y = Algebra.trace F A.K (x.1 * y.2) + Algebra.trace F A.K (x.2 * y.1) := by
  simp [betaK, Algebra.traceForm_apply]

theorem betaK_isSymm (A : Et F E) : (betaK A).IsSymm :=
  ⟨fun x y => by rw [betaK_apply, betaK_apply, mul_comm x.1, mul_comm x.2, add_comm]⟩

theorem betaK_nondeg (A : Et F E) (h : (Algebra.traceForm F A.K).Nondegenerate) : (betaK A).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (betaK A) := by
    intro x hx
    have h1 : x.1 = 0 := h.1 x.1 fun z => by
      have := hx (0, z); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    have h2 : x.2 = 0 := h.1 x.2 fun z => by
      have := hx (z, 0); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    exact Prod.ext h1 h2
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [(betaK_isSymm A).eq]; exact hy x

theorem secondCountable [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem psi_continuous (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : ψ y = ψ x * ψ (y - x) := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
  rw [this, hψ.1 (y - x) (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy), mul_one]

theorem fourK_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  haveI := secondCountable A
  haveI : μK.IsAddHaarMeasure := hsd.1
  haveI : (μK.prod μK).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have key := (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ (A.K × A.K) (betaK A) (betaK_isSymm A) (betaK_nondeg A hnd)).2
    (μK.prod μK) inferInstance φ' hφ
  have hψc := psi_continuous ψ hψ
  have heq : A.fourK μK ψ φ' = fourB (μK.prod μK) (fun x y => ψ (betaK A x y)) φ' := by
    funext p
    simp only [fourB, Et.fourK]
    rw [integral_prod]
    · refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
      refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
      simp only [Et.psiK, betaK_apply, map_add]
      congr 1
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, mul_comm p.1, mul_comm c' p.1]
      ring
    · apply Continuous.integrable_of_hasCompactSupport
      · exact hφ.1.continuous.mul (hψc.comp (IsModuleTopology.continuous_of_linearMap ((betaK A).flip p)))
      · exact hφ.2.mul_right
  rw [heq]; exact key

end GlobalTheory.FourKTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizer
section
open ReciprocityTheory.Gal

namespace GlobalTheory

theorem KO_divisible_by_uniformiser : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ y : Formalism.NG.KO O, ϖ • y = x := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  refine ⟨Submodule.Quotient.mk (z / algebraMap O (FractionRing O) ϖ), ?_⟩
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_div_cancel₀ _ h0]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizer
section
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem ko_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  refine ⟨n, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨a * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq,
    ← map_mul]
  congr 1
  rw [hu]
  calc a * ((u⁻¹ : Oˣ) : O) * ((u : O) * ϖ ^ n) = a * ϖ ^ n * (((u⁻¹ : Oˣ) : O) * u) := by ring
    _ = ϖ ^ n * a := by simp [mul_comm]

end GlobalTheory.ShapeNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaMinusOneDivVariablePolarKernelLeSenWeightsStatement
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (w : ℕ) (Z : Submodule k V), (∀ x ∈ Z, x ∈ sh (-w) N ∧ nab g x ∈ N) → Module.finrank k (↥Z ⧸ (N.restrictScalars k).submoduleOf Z) ≤ ∑ j ∈ Finset.range w, sen g N ((-(w : ℤ) + j : ℤ) : k) := by
  first | exact @GlobalTheory.PhiGam.PolarKernel.main | exact GlobalTheory.PhiGam.PolarKernel.main | (intros; apply GlobalTheory.PhiGam.PolarKernel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianTraceDualIntegersEqUniformizerPowStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTraceDual_integers_eq_uniformizer_pow : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → IsField A.L → ∀ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) → (∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O) → ∀ a : A.Kˣ, ∃ e : ℤ, {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((ϖ ^ e : A.Kˣ) : A.K) * z} := by
  first | exact @GlobalTheory.JR.DualLattice.dual_eq_zpow | exact GlobalTheory.JR.DualLattice.dual_eq_zpow | (intros; apply GlobalTheory.JR.DualLattice.dual_eq_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionFromSubgroupTrans
section
open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory.BrauerZero

theorem ind_ind_of_le {G : Type} [Group G] [Finite G] (K A : Subgroup G) (hKA : K ≤ A)
    (ψ : K → ℂ) :
    ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by
  classical
  haveI := Fintype.ofFinite G
  funext g
  have hcard : Nat.card (K.subgroupOf A) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv
  have key : ∀ a y : A, ext0 (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩) (y⁻¹ * a * y)
      = ext0 K ψ ((y : G)⁻¹ * (a : G) * y) := by
    intro a y
    have hc : ((y⁻¹ * a * y : A) : G) = (y : G)⁻¹ * (a : G) * y := by simp
    by_cases h : (y : G)⁻¹ * (a : G) * y ∈ K
    · have h' : y⁻¹ * a * y ∈ K.subgroupOf A := by rw [Subgroup.mem_subgroupOf, hc]; exact h
      rw [ext0, ext0, dif_pos h', dif_pos h]
      congr 1
    · have h' : y⁻¹ * a * y ∉ K.subgroupOf A := by rw [Subgroup.mem_subgroupOf, hc]; exact h
      rw [ext0, ext0, dif_neg h', dif_neg h]
  have step : ∀ x : G, ext0 A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) (x⁻¹ * g * x)
      = (Nat.card K : ℂ)⁻¹ * ∑ y : A, ext0 K ψ ((x * y)⁻¹ * g * (x * y)) := by
    intro x
    by_cases hx : x⁻¹ * g * x ∈ A
    · rw [ext0, dif_pos hx, ind, hcard, finsum_eq_sum_of_fintype]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [key ⟨_, hx⟩ y]
      congr 1
      simp only [mul_inv_rev]
      group
    · rw [ext0, dif_neg hx]
      symm
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y _ => ?_)
      have hn : (x * y)⁻¹ * g * (x * y) ∉ K := by
        intro hk
        apply hx
        have hA : (x * y)⁻¹ * g * (x * y) ∈ A := hKA hk
        have e : x⁻¹ * g * x = (y : G) * ((x * y)⁻¹ * g * (x * y)) * (y : G)⁻¹ := by group
        rw [e]
        exact A.mul_mem (A.mul_mem y.2 hA) (A.inv_mem y.2)
      rw [ext0, dif_neg hn]
  rw [ind, ind, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun x _ => step x), ← Finset.mul_sum, Finset.sum_comm]
  have shift : ∀ y : A, ∑ x : G, ext0 K ψ ((x * y)⁻¹ * g * (x * y)) = ∑ z : G, ext0 K ψ (z⁻¹ * g * z) :=
    fun y => Fintype.sum_equiv (Equiv.mulRight (y : G)) _ _ (fun x => rfl)
  rw [Finset.sum_congr rfl (fun y _ => shift y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have hA0 : (Nat.card A : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := A)).ne'
  field_simp

end GlobalTheory.BrauerZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralUnitaryGroupTransitiveNormOneVectorsStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 → ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  first | exact @GlobalTheory.UnitaryTransitive.uO_transitive | exact GlobalTheory.UnitaryTransitive.uO_transitive | (intros; apply GlobalTheory.UnitaryTransitive.uO_transitive <;> assumption)
end

