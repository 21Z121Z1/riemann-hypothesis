import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0103
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0446
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0401
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0346
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbMassStabilizerLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanOne

open GlobalTheory.Mass.FixedSub GlobalTheory.Mass.PrimMean

theorem orbMass_stabilizer_le (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h) (U : Submodule K V) (n N₀ : ℕ) (T : 𝓞 K) (hT : T ≠ 0)
    (dW : Module.finrank K (perp h U) = 1) :
    orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
      (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
      (∀ x ∈ dual h L, T • x ∈ L) ∧ discN (hRes h U) (latIn U L) = n} ≤
    orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) *
      (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U)))
        (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) *
      ((Ideal.absNorm (Ideal.span {T}) * n : ℕ) : ℝ≥0∞) := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.definite_unitary_stabilizer_subspace_prod K V h hK hs hp U
  have hs1 := hRes_symm h hs U
  have hp1 := hRes_pd h hp U
  have hs2 := hRes_symm h hs (perp h U)
  have hp2 := hRes_pd h hp (perp h U)
  letI act : MulAction (MulAction.stabilizer (isom h) U)
      (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)) :=
    { smul := fun γ p => ((φ γ).1 • p.1, (φ γ).2 • p.2)
      one_smul := fun p => by
        change ((φ 1).1 • p.1, (φ 1).2 • p.2) = p
        simp
      mul_smul := fun a b p => by
        change ((φ (a * b)).1 • p.1, (φ (a * b)).2 • p.2) =
          ((φ a).1 • ((φ b).1 • p.1), (φ a).2 • ((φ b).2 • p.2))
        simp [mul_smul] }
  have hact : ∀ (γ : MulAction.stabilizer (isom h) U)
      (p : Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)),
      γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2) := fun _ _ => rfl
  set X : Set (Submodule (𝓞 K) V) := {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
    (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
    (∀ x ∈ dual h L, T • x ∈ L) ∧ discN (hRes h U) (latIn U L) = n} with hX
  set A : Set (Submodule (𝓞 K) U) := latsDisc (R := 𝓞 K) (hRes h U) n with hA
  set B : Set (Submodule (𝓞 K) (perp h U)) :=
    ⋃ n' ∈ Finset.Icc 1 (n * N₀), latsDisc (R := 𝓞 K) (hRes h (perp h U)) n' with hB
  have memB : ∀ M, M ∈ B ↔ IsIntLat (hRes h (perp h U)) M ∧
      1 ≤ discN (hRes h (perp h U)) M ∧ discN (hRes h (perp h U)) M ≤ n * N₀ := by
    intro M
    simp only [hB, Set.mem_iUnion, Finset.mem_Icc, latsDisc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, h1, rfl⟩
      exact ⟨h1, hi⟩
    · rintro ⟨h1, hi⟩
      exact ⟨_, hi, h1, rfl⟩
  have sA : Stable (isom (hRes h U)) A := stable_latsDisc _ n
  have sB : Stable (isom (hRes h (perp h U))) B := by
    intro g M hM
    rw [memB] at hM ⊢
    rw [discN_smul]
    exact ⟨isIntLat_smul _ g M hM.1, hM.2⟩
  have fA : ∀ M ∈ A, Finite (MulAction.stabilizer (isom (hRes h U)) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K U (hRes h U) hK hs1 hp1 M hM.1.1).2.2.2.1 M hM.1.1
  have fB : ∀ M ∈ B, Finite (MulAction.stabilizer (isom (hRes h (perp h U))) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K (perp h U) (hRes h (perp h U)) hK hs2 hp2 M ((memB M).1 hM).1.1).2.2.2.1 M
      ((memB M).1 hM).1.1
  have sX : Stable (MulAction.stabilizer (isom h) U) X := by
    rintro γ L ⟨h1, h2, h3, h5, h4⟩
    refine ⟨isIntLat_smul h γ.1 L h1, (discN_smul h γ.1 L).trans h2, gens_smul h γ.1 L 1 h3, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ γ.1 • dual h L := dual_smul h γ.1 L ▸ hx
      change T • x ∈ γ.1 • L
      rw [smul_def'] at hx' ⊢
      unfold gmap at hx' ⊢
      obtain ⟨y, hy, rfl⟩ := hx'
      exact ⟨T • y, h5 y hy, map_smul _ _ _⟩
    · rw [(hφ γ L).1, discN_smul, h4]
  have sY : Stable (MulAction.stabilizer (isom h) U) (A ×ˢ B) := by
    rintro γ p ⟨h1, h2⟩
    exact ⟨sA _ _ h1, sB _ _ h2⟩
  have mp : Set.MapsTo (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) X (A ×ˢ B) := by
    rintro L ⟨h1, h2, h3, -, h4⟩
    obtain ⟨k1, k2, k3, -⟩ := GlobalTheory.T.primitive_hermitian_sublattice_discriminant_generators K V h hK hs hp L U 1 h1 h3
    refine ⟨⟨k1, h4⟩, (memB _).2 ⟨k2, ?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.2
        (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K (perp h U) _ hK hs2 (pd_nondeg _ hp2) _ k2).1
    · rw [h2, h4] at k3
      exact k3
  have fY : ∀ p ∈ A ×ˢ B, Finite (MulAction.stabilizer (MulAction.stabilizer (isom h) U) p) := by
    rintro p ⟨h1, h2⟩
    haveI := fA _ h1
    haveI := fB _ h2
    refine Finite.of_injective
      (β := MulAction.stabilizer (isom (hRes h U)) p.1 ×
        MulAction.stabilizer (isom (hRes h (perp h U))) p.2)
      (fun γ => (⟨(φ γ.1).1, congrArg Prod.fst γ.2⟩, ⟨(φ γ.1).2, congrArg Prod.snd γ.2⟩)) ?_
    intro a b e
    apply Subtype.ext
    apply φ.injective
    exact Prod.ext (congrArg (fun q => q.1.1) e) (congrArg (fun q => q.2.1) e)
  have e1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (MulAction.stabilizer (isom h) U) _ _ X (A ×ˢ B)
    (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L))
    (fun γ L => Prod.ext (hφ γ L).1 (hφ γ L).2) sX sY mp fY
  have e2 := GlobalTheory.T.orbitStabilizerMass_prod_eq_mul (MulAction.stabilizer (isom h) U) _ _ _ _ φ A B hact sA sB fA fB
  have e3 : orbMass (isom (hRes h (perp h U))) B ≤ ∑ n' ∈ Finset.Icc 1 (n * N₀),
      orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') :=
    (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom (hRes h (perp h U))) (Submodule (𝓞 K) (perp h U))).2.2.1 ℕ _ B _ _ subset_rfl
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U)
    (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U))
  rw [e1]
  refine (m1 _ (A ×ˢ B) _
    (fun _ => ((Ideal.absNorm (Ideal.span {T}) * n : ℕ) : ℝ≥0∞))
    subset_rfl ?_).trans ?_
  · rintro ⟨M, M'⟩ ⟨h1, h2⟩
    obtain ⟨b1, -, -⟩ := (memB M').1 h2
    have cnt := GlobalTheory.T.card_hermitianLattices_glued_along_line K V h hK hs hp U M M' T hT dW h1.1 b1
    have sub : X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')} ⊆
        {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = M ∧
          latIn (perp h U) L = M'} :=
      fun N hN => ⟨hN.1.1, hN.1.2.2.2.1, congrArg Prod.fst hN.2, congrArg Prod.snd hN.2⟩
    have e : discN (hRes h U) M = n := h1.2
    rw [e] at cnt
    have := ENat.toENNReal_le.2 ((Set.encard_le_encard sub).trans cnt)
    rwa [ENat.toENNReal_coe] at this
  · rw [m2, e2, mul_comm]
    gcongr

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → j + 1 = Module.finrank K V → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ (V₂ : Type) [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂] (h₂ : V₂ →ₗ⋆[K] V₂ →ₗ[K] K) (I₂ : Submodule (𝓞 K) V₂), h₂.IsSymm → IsOrthoLattice h₂ I₂ 1 → ∀ (de t : ℕ) (T : 𝓞 K), 1 ≤ de → 1 ≤ t → T ≠ 0 → Ideal.absNorm (Ideal.span {T}) = t ^ 2 → ∀ 𝒢 : Set (Submodule (𝓞 K) V), Stable (isom h) 𝒢 → (∀ L ∈ 𝒢, IsIntLat h L ∧ discN h L = t ^ 2 ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ x ∈ dual h L, T • x ∈ L) → orbSum (isom h) 𝒢 (fun L => (((primSp h L j (de ^ 2)).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (mass h₁ I₁ * mass h₂ I₂ * (de : ℝ) ^ j * ((de : ℝ) ^ (4 + Real.logb 2 (fDeg K)) * (t : ℝ) ^ 2 * ((de : ℝ) * t) ^ (2 + Real.logb 2 (fDeg K)))) := by
  intro hM K V _ _ _ _ _ _ _ _ h hK hs hp hLand j hj hjs V₁ _ _ _ _ _ h₁ I₁ hs₁ hI₁ V₂ _ _ _ _ _ h₂ I₂ hs₂ hI₂
    de t T hde ht hT hN 𝒢 hst h𝒢
  obtain ⟨S, hdim, hcov, hsum⟩ := GlobalTheory.T.exists_subspaceReps_sum_orbitMass_le hM K V h hK hs hp hLand j hj V₁ h₁ I₁ hs₁ hI₁ de hde
  have hnd := pd_nondeg h hp
  set l : ℝ := Real.logb 2 (fDeg K) with hl
  have m1 := mass_nonneg h₁ I₁
  have m2 := mass_nonneg h₂ I₂
  have h1 := orbSum_encard_le (isom h) (Submodule (𝓞 K) V) (Submodule K V) 𝒢
    (fun L => primSp h L j (de ^ 2))
    (fun g L U => (GlobalTheory.T.primitive_sublattices_move_with_isometries K V h hK hs hnd g L U j (de ^ 2)).1) hst
    (fun L hL => (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L (h𝒢 L hL).1.1).2.2.2.1 L (h𝒢 L hL).1.1) S
    (fun L hL U hU => hcov U hU.1 ⟨latIn U L, isIntLat_latIn h (h𝒢 L hL).1 U, hU.2⟩)
  refine h1.trans ?_
  have d0 : (0 : ℝ) < de := by exact_mod_cast hde
  have t0 : (0 : ℝ) < t := by exact_mod_cast ht
  set C : ℝ := mass h₂ I₂ * ((de : ℝ) * t) ^ (2 + l) * ((t : ℝ) ^ 2 * (de : ℝ) ^ 2) with hC
  have h2 : ∀ U ∈ S, orbMass (MulAction.stabilizer (isom h) U) {L | L ∈ 𝒢 ∧ U ∈ primSp h L j (de ^ 2)} ≤
      orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) * ENNReal.ofReal C := by
    intro U hU
    have dU := hdim U hU
    obtain ⟨hc, -, -, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 U
    have dW : Module.finrank K (perp h U) = 1 := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      omega
    have a1 := (GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (MulAction.stabilizer (isom h) U) (Submodule (𝓞 K) V)).1
      {L | L ∈ 𝒢 ∧ U ∈ primSp h L j (de ^ 2)}
      {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = t ^ 2 ∧ (∃ t : Finset V, t.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧
        discN (hRes h U) (latIn U L) = de ^ 2}
      (fun _ => 1) (fun _ => 1)
      (fun L hL => ⟨(h𝒢 L hL.1).1, (h𝒢 L hL.1).2.1, (h𝒢 L hL.1).2.2.1, (h𝒢 L hL.1).2.2.2, hL.2.2⟩)
      (fun _ _ => le_rfl)
    refine a1.trans ((orbMass_stabilizer_le K V h hK hs hp U (de ^ 2) (t ^ 2) T hT dW).trans ?_)
    have a3 := GlobalTheory.T.totalMass_integralLattices_bounded_det_line hM K (perp h U) (hRes h (perp h U)) hK (hRes_symm h hs _) (hRes_pd h hp _) dW
      V₂ h₂ I₂ hs₂ hI₂ (de * t) (Nat.mul_pos hde ht)
    rw [mul_pow, Nat.cast_mul] at a3
    rw [mul_assoc, hC, ENNReal.ofReal_mul (by positivity), hN]
    refine mul_le_mul' le_rfl (mul_le_mul' a3 (le_of_eq ?_))
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.sum_mul]
  refine (mul_le_mul' hsum le_rfl).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have e : (de : ℝ) ^ (4 + l) = (de : ℝ) ^ (2 + l) * (de : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add d0]
    congr 1
    push_cast
    ring
  rw [e, hC]
  ring

end GlobalTheory.Mass.PrimMeanOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCast
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitRes

open IsDedekindDomain

section Cast

variable {E : Type} [Field E] [NumberField E]

theorem tensCastR_comm_symm_tmul_one {F₁ F₂ : Subfield E} (h : F₁ = F₂) (y : E) :
    GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
      (y ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁))) = y ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂) := by
  subst h
  exact (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _

theorem tensCastR_comm_symm_one_tmul {F₁ F₂ : Subfield E} (h : F₁ = F₂) (c : FiniteAdeleRing (𝓞 F₁) F₁)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F₁) :
    ∃ c' : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, c' v ∈ v.adicCompletionIntegers F₂) ∧
      GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
        ((1 : E) ⊗ₜ[F₁] c)) = (1 : E) ⊗ₜ[F₂] c' := by
  subst h
  exact ⟨c, hc, (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _⟩

end Cast

def projE (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) :
    Formalism.IndefR.Lev.EAf D →+* s.v.adicCompletion (maximalRealSubfield D.host.E) :=
  s.proj.comp (GlobalTheory.FixedConj.adeleEquiv D hF).symm.toRingHom

theorem projE_apply (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (x : Formalism.IndefR.Lev.EAf D) :
    projE D hF s x = s.proj (GlobalTheory.StdFrame.tensCastR hF
      ((Algebra.TensorProduct.comm (↥D.host.F) (FiniteAdeleRing (𝓞 ↥D.host.F) ↥D.host.F) D.host.E).symm x)) := rfl

theorem projE_adeleEquiv (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (a : ReciprocityTheory.Aut.AL D.host.E) : projE D hF s (GlobalTheory.FixedConj.adeleEquiv D hF a) = s.proj a := by
  simp [projE]

theorem projE_tmul_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (y : D.host.E) : projE D hF s (y ⊗ₜ[↥D.host.F] (1 : Formalism.L2.Herm.Af ↥D.host.F)) = s.i y := by
  rw [projE_apply, tensCastR_comm_symm_tmul_one]
  simp [SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem projE_le_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.IndefR.Lev.EAf D) (hz : z ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) : Valued.v (projE D hF s z) ≤ 1 := by
  have hle : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring.comap (projE D hF s) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, projE_tmul_one]
      exact s.split_le_one y
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      obtain ⟨c', hc', e⟩ := tensCastR_comm_symm_one_tmul hF c hc
      rw [projE_apply, e]
      simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact hc' s.v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hle hz)

theorem projE_lt_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (hz : z ∈ Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) :
    Valued.v (projE D hF s (z : Formalism.IndefR.Lev.EAf D)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, projE_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    calc Valued.v (projE D hF s (c : Formalism.IndefR.Lev.EAf D)) * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D))
        ≤ 1 * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D)) := by
          gcongr
          exact projE_le_one D hF s _ c.2
      _ < 1 := by rwa [one_mul]

theorem resS_adeleEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  intro D hF s a ha m _hA hm
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩)
  have e1 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) ⟨_, ha⟩ :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := ↥D.host.F) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) (Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b) :=
    Ideal.quotientMap_mk
  have hmem : (⟨_, ha⟩ : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) - Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b ∈
      Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) < 1 := by
    have := projE_lt_one D hF s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, projE_tmul_one, projE_adeleEquiv] at this
  have h2 : b - (m : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    show Valued.v (s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)) < 1
    have e : s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) -
          (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_sub, map_natCast, map_natCast]
      ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hm h1)
  rw [← hb, ← map_natCast (Ideal.Quotient.mk s.w.asIdeal) m, Ideal.Quotient.eq]
  exact h2

end GlobalTheory.SplitRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMean
section
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.HermitianLatticesTheory GlobalTheory.Mass

namespace GlobalTheory.RowsMean

section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sameGenus_trans (h : V →ₗ⋆[K] V →ₗ[K] K) {L M N : Submodule (𝓞 K) V}
    (h1 : SameGenus h L M) (h2 : SameGenus h M N) : SameGenus h L N := by
  intro p hp
  obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
  obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  rw [genusBasic_gmap_mul, e₁, e₂]

theorem sameGenus_refl (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : SameGenus h L L :=
  fun _ _ => ⟨1, one_mem _, genusBasic_gmap_one _⟩

theorem genus_eq_iff (h : V →ₗ⋆[K] V →ₗ[K] K) {L M : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hM : Submodule.IsLattice K M) :
    genus h L = genus h M ↔ L ∈ genus h M := by
  constructor
  · intro e; rw [← e]; exact ⟨hL, sameGenus_refl h L⟩
  · intro hLM
    ext N
    constructor
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h hLM.2 hs⟩
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h (genusBasic_symm h _ _ hLM.2) hs⟩

theorem mass_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : 0 ≤ mass h L := by
  unfold mass
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact le_rfl

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean
section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inv_card_eq (X : Type) [Nonempty X] :
    ((ENat.card X : ℕ∞) : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((Nat.card X : ℝ))⁻¹ := by
  rcases finite_or_infinite X with hX | hX
  · rw [ENat.card_eq_coe_natCard]
    have hp : 0 < Nat.card X := Nat.card_pos
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp), ENNReal.ofReal_natCast]
    simp
  · rw [ENat.card_eq_top_of_infinite, Nat.card_eq_zero_of_infinite]
    simp

def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    MulAction.stabilizer (isom h) M ≃ Formalism.ThetaLiftIndependence.autL h M where
  toFun g := ⟨g.1.1, g.1.2, g.2⟩
  invFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  left_inv g := rfl
  right_inv a := rfl

theorem mass_le_orbMass (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    ENNReal.ofReal (mass h L) ≤ orbMass (isom h) (genus h L) := by
  unfold mass
  split_ifs with hs
  swap
  · simp
  have hs' : Formalism.ThetaLiftIndependence.IsClassReps h L hs.choose := hs.choose_spec
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  have hrel : ∀ M : Submodule (𝓞 K) V, MulAction.orbitRel (isom h) (Submodule (𝓞 K) V)
      (Quotient.out (Quotient.mk'' M : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V))) M :=
    fun M => Quotient.exact' (Quotient.out_eq' _)
  have hq : ∀ M ∈ hs.choose, Quotient.out (Quotient.mk'' M :
      MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) ∈ genus h L := by
    intro M hM
    obtain ⟨g, hg⟩ := hrel M
    rw [← hg]
    exact GlobalTheory.Mass.Transp.genus_stable L g M (hs'.1 M hM)
  let qm : hs.choose → {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) //
      Quotient.out q ∈ genus h L} := fun M => ⟨Quotient.mk'' M.1, hq M.1 M.2⟩
  have hinj : Function.Injective qm := by
    rintro ⟨M₁, h₁⟩ ⟨M₂, h₂⟩ e
    have e' : (Quotient.mk'' M₁ : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) =
        Quotient.mk'' M₂ := congrArg Subtype.val e
    obtain ⟨g, hg⟩ := Quotient.exact' e'
    have hM₁ : M₁ ∈ genus h L := hs'.1 M₁ h₁
    have u := (hs'.2 M₁ hM₁).unique ⟨h₁, 1, one_mem _, genusBasic_gmap_one _⟩ ⟨h₂, g.1, g.2, hg⟩
    exact Subtype.ext u
  unfold orbMass orbSum
  rw [← Finset.sum_attach]
  have hterm : ∀ M : hs.choose, ENNReal.ofReal (((Nat.card (Formalism.ThetaLiftIndependence.autL h M.1) : ℕ) : ℝ))⁻¹ =
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := by
    intro M
    rw [mul_one]
    have e1 : ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) =
        ENat.card (Formalism.ThetaLiftIndependence.autL h M.1) :=
      ENat.card_congr (((MulAction.stabilizerEquivStabilizerOfOrbitRel (hrel M.1)).toEquiv).trans
        (stabEquiv h M.1))
    haveI : Nonempty (Formalism.ThetaLiftIndependence.autL h M.1) := ⟨stabEquiv h M.1 1⟩
    rw [e1, inv_card_eq]
  simp_rw [hterm]
  exact (Finset.sum_image (s := hs.choose.attach) (g := qm)
    (f := fun q : {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) // Quotient.out q ∈ genus h L} =>
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1)
    (fun a _ b _ e => hinj e)).symm.le.trans (ENNReal.sum_le_tsum _)

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean

theorem sum_le_of_classes {ι α : Type} (s : Finset ι) (L : ι → α) (G : α → Set α) (P : α → Prop)
    (hP : ∀ i ∈ s, P (L i)) (hG : ∀ a b, P a → P b → (G a = G b ↔ a ∈ G b))
    (F w : ι → ℝ≥0∞) (b : ℝ≥0∞)
    (hcl : ∀ i₀ ∈ s, ∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), F i ≤
      (∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), w i) * b) :
    ∑ i ∈ s, F i ≤ (∑ i ∈ s, w i) * b := by
  have hmap : ∀ i ∈ s, G (L i) ∈ s.image (fun i => G (L i)) := fun i hi => Finset.mem_image_of_mem _ hi
  rw [← Finset.sum_fiberwise_of_maps_to hmap F, ← Finset.sum_fiberwise_of_maps_to hmap w, Finset.sum_mul]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hy
  have e : s.filter (fun i => G (L i) = G (L i₀)) = s.filter (fun i => L i ∈ G (L i₀)) :=
    Finset.filter_congr fun i hi => hG _ _ (hP i hi) (hP i₀ hi₀)
  rw [e]
  exact hcl i₀ hi₀

end GlobalTheory.RowsMean

namespace GlobalTheory.TypeAsm
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowsMean : RowsMeanC := by
  intro D large₂ X Y u hStd W HW hEmb φ B hB hφ hbd
  have hOrb := GlobalTheory.T.rowsGenus_weightedSumComparison D large₂ X Y u hStd W HW hEmb
  have hLat := GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hStd W HW hEmb
  have hw : ∀ Λ, 0 ≤ wRow D (X.Fu u) Λ := fun Λ => by unfold wRow; positivity
  have hm : 0 ≤ massRows D (X.Fu u) (Y.what₂ u) := Finset.sum_nonneg fun Λ _ => hw Λ
  rw [ENNReal.ofReal_mul hm]
  unfold massRows
  rw [ENNReal.ofReal_sum_of_nonneg fun Λ _ => hw Λ]
  refine GlobalTheory.RowsMean.sum_le_of_classes (Y.what₂ u) (fun Λ => GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ)
    (Formalism.HermitianLatticesTheory.genus HW.B.flip) (Submodule.IsLattice D.host.E) (fun Λ hΛ => (hLat Λ hΛ).1.1)
    (fun a b ha hb => GlobalTheory.RowsMean.genus_eq_iff _ ha hb) _ _ _ ?_
  intro Λ₀ hΛ₀
  have h1 := hOrb φ hφ Λ₀ hΛ₀
  have h2 := hOrb (fun _ => 1) (fun _ _ => rfl) Λ₀ hΛ₀
  simp only [mul_one] at h2
  rw [h1, h2, mul_assoc]
  gcongr
  refine (hbd Λ₀ hΛ₀).trans ?_
  rw [ENNReal.ofReal_mul (GlobalTheory.RowsMean.mass_nonneg _ _)]
  gcongr
  exact GlobalTheory.RowsMean.mass_le_orbMass _ _

end GlobalTheory.TypeAsm
end
end

