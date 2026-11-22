import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentMulNatPowOfMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexEqLocalUnitaryIndexAtInert
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertLatIndex

open GlobalTheory.InertLoc Formalism.UG

theorem finPart_surjective (D : D7) : Function.Surjective (finPart D) := by
  intro b
  obtain ⟨a, ha⟩ := Algebra.TensorProduct.map_surjective (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    (fun b => ⟨pairA D.host.F 0 b, rfl⟩) Function.surjective_id b
  exact ⟨a, ha⟩

theorem ker_finPart_le {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} {σ : LP D P →+* LP D P}
    {π : AE D →+* LP D P} (hC : Chart e σ π) : RingHom.ker (finPart D) ≤ RingHom.ker π := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  refine (hC.2.2.1 a).2 ?_
  refine GlobalTheory.LatVac.tensor_prod_eq_zero (F := D.host.F) (A := _) (B := _) _ ?_ ?_
  · show infPart D (e * a) = 0
    rw [map_mul, hC.1.2.2, zero_mul]
  · show finPart D (e * a) = 0
    rw [map_mul, ha, mul_zero]

theorem mem_span_basisFun {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]
    (z : n → K) : z ∈ Submodule.span O (Set.range (Pi.basisFun K n)) ↔ ∀ i, z i ∈ O := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      rw [Pi.basisFun_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, Ne.symm hij]
    | zero => intro i; simp
    | add x y _ _ hx hy => intro i; exact add_mem (hx i) (hy i)
    | smul a x _ hx => intro i; exact mul_mem a.2 (hx i)
  · intro hz
    have : z = ∑ i, (⟨z i, hz i⟩ : O) • Pi.basisFun K n i := by
      conv_lhs => rw [← (Pi.basisFun K n).sum_repr z]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem finMat_apply {D : D7} {W : HSp D} (x : GA D W) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j = finPart D (Formalism.L2.Theta.mt W x i j) := rfl

theorem finMat_sub_one_eq {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x) (i j : Fin W.rank) :
    finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D e * (finMat D.sp.cm.sig W.gram x i j - (1 : Matrix (Fin W.rank) (Fin W.rank)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j) := by
  have h1ij : (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j =
      finPart D ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i j) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h1ij, finMat_apply, ← RingHom.map_sub, ← RingHom.map_mul, ← Matrix.sub_apply, hx i j]

theorem finMat_mulVec_fix {D : D7} {W : HSp D} {e : AE D} (x : GA D W) (hx : SuppF W e x)
    (y : Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig W.gram x *ᵥ (y - finPart D e • y) = y - finPart D e • y := by
  funext i
  have key : ∀ j, finMat D.sp.cm.sig W.gram x i j * (y - finPart D e • y) j =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) i j *
        (y - finPart D e • y) j := by
    intro j
    have := finMat_sub_one_eq x hx i j
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (y j) * this
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp [Matrix.one_apply]

theorem inv_mulVec_conj {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] (β g : GL n K) (w : n → K) :
    (β⁻¹).1 *ᵥ ((β.1 * g.1 * (β⁻¹).1) *ᵥ w) = g.1 *ᵥ ((β⁻¹).1 *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

set_option maxHeartbeats 1000000 in

theorem latIndex_eq_of_chart {D : D7} {W : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D}
    {σ : LP D P →+* LP D P} {π : AE D →+* LP D P} {β : GL (Fin W.rank) (LP D P)}
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hα : finPart D e = α ⊗ₜ[D.host.F] (1 : D.host.E))
    (hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F)
    (hC : Chart e σ π) (hF : Frame W e σ π β) (x : GA D W) (hx : SuppF W e x) (g : GL (Fin W.rank) (LP D P))
    (hxg : (Formalism.L2.Theta.mt W x).map π = β.1 * g.1 * (β⁻¹).1) :
    latIndex W x = ((Submodule.span (P.adicCompletionIntegers D.host.E)
        (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).map
        ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
          (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
  let πf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* LP D P :=
    (RingHom.liftOfSurjective (finPart D) (finPart_surjective D)) ⟨π, ker_finPart_le hC⟩
  have hπf : ∀ a, πf (finPart D a) = π a := fun a => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hπe : π e = 1 := by
    have h0 : e * (e - 1) = 0 := by rw [mul_sub, hC.1.1, mul_one, sub_self]
    have := (hC.2.2.1 (e - 1)).2 h0
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let T : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finMat D.sp.cm.sig W.gram x).mulVecLin.toAddMonoidHom
  let p : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+
      (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := DistribMulAction.toAddMonoidHom _ (finPart D e)
  let Φ : (Fin W.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin W.rank → LP D P) :=
    ((β⁻¹).1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.toAddMonoidHom.comp
      (πf.toAddMonoidHom.compLeft (Fin W.rank))
  let h : (Fin W.rank → LP D P) →+ (Fin W.rank → LP D P) :=
    ((g.1 : Matrix (Fin W.rank) (Fin W.rank) (LP D P)).mulVecLin.restrictScalars
      (P.adicCompletionIntegers D.host.E)).toAddMonoidHom
  have hΦ : ∀ y, Φ y = (β⁻¹).1 *ᵥ (fun k => πf (y k)) := fun y => rfl
  have h1 : ∀ y ∈ Formalism.L2.NTheta.LamHat W, p y ∈ Formalism.L2.NTheta.LamHat W := by
    have hle : Formalism.L2.NTheta.LamHat W ≤ (Formalism.L2.NTheta.LamHat W).comap p := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, z, hz, rfl⟩
      show p _ ∈ Formalism.L2.NTheta.LamHat W
      apply AddSubgroup.subset_closure
      refine ⟨α * a, hαint a ha, z, hz, ?_⟩
      funext i
      show finPart D e * (a ⊗ₜ[D.host.F] z i) = _
      rw [hα, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact fun y hy => hle hy
  have h2 : ∀ y, T (p y) = p (T y) := fun y => by
    show finMat D.sp.cm.sig W.gram x *ᵥ (finPart D e • y) = finPart D e • (finMat D.sp.cm.sig W.gram x *ᵥ y)
    exact Matrix.mulVec_smul _ _ _
  have h3 : ∀ y, T (y - p y) = y - p y := fun y => finMat_mulVec_fix x hx y
  have h4 : ∀ y, Φ y = 0 → p y = 0 := by
    intro y hy
    have h0 : ∀ k, πf (y k) = 0 := by
      intro k
      have := congrArg (fun w => β.1 *ᵥ w) hy
      simp only [hΦ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact congrFun this k
    funext k
    obtain ⟨a, ha⟩ := finPart_surjective D (y k)
    have hπa : π a = 0 := by rw [← hπf, ha]; exact h0 k
    show finPart D e * y k = 0
    rw [← ha, ← RingHom.map_mul, (hC.2.2.1 a).1 hπa, RingHom.map_zero]
  have h5 : ∀ y, Φ (T y) = h (Φ y) := by
    intro y
    have hmap : (finMat D.sp.cm.sig W.gram x).map πf = β.1 * g.1 * (β⁻¹).1 := by
      rw [← hxg]
      exact Matrix.ext fun i j => hπf _
    have hT : (fun k => πf ((finMat D.sp.cm.sig W.gram x *ᵥ y) k)) =
        (finMat D.sp.cm.sig W.gram x).map πf *ᵥ (fun k => πf (y k)) :=
      funext fun k => RingHom.map_mulVec πf _ y k
    show Φ (finMat D.sp.cm.sig W.gram x *ᵥ y) = g.1 *ᵥ Φ y
    rw [hΦ, hΦ, hT, hmap]
    exact inv_mulVec_conj β g _
  have hmapΦ : (Formalism.L2.NTheta.LamHat W).map Φ =
      (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (LP D P) (Fin W.rank)))).toAddSubgroup := by
    ext z
    rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    refine Iff.trans ?_ (mem_span_basisFun _ z).symm
    constructor
    · rintro ⟨y, hy, rfl⟩
      choose a ha using fun k => finPart_surjective D (y k)
      have hpy : (fun i => finPart D (e * a i)) ∈ Formalism.L2.NTheta.LamHat W := by
        have := h1 y hy
        convert this using 1
        funext i
        show finPart D (e * a i) = finPart D e * y i
        rw [RingHom.map_mul, ha]
      have hi := (hF.2 a).1 hpy
      have hz : Φ y = (β⁻¹).1 *ᵥ fun k => π (a k) := by
        rw [hΦ]
        congr 1
        funext k
        rw [← ha, hπf]
      rw [hz]
      exact hi
    · intro hz
      choose a ha using fun k => hC.2.1 ((β.1 *ᵥ z) k)
      have hb : (β⁻¹).1 *ᵥ (fun k => π (a k)) = z := by
        have : (fun k => π (a k)) = β.1 *ᵥ z := funext ha
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      refine ⟨fun i => finPart D (e * a i), (hF.2 a).2 ?_, ?_⟩
      · rw [hb]; exact hz
      · rw [hΦ]
        convert hb using 2
        funext k
        rw [hπf, RingHom.map_mul, hπe, one_mul]
  unfold latIndex
  rw [GlobalTheory.index_transfer_along_projection (Formalism.L2.NTheta.LamHat W) T p Φ h h1 h2 h3 h4 h5, hmapΦ,
    Submodule.map_toAddSubgroup]
  rfl

theorem latIndex_chart_eq : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  intro D W v ε hε P σ π β ι hC hF hG g
  obtain ⟨α, hεα, hα1, hα0⟩ := hε
  have hα : finPart D (algebraMap (AF D.host.F) (AE D) ε) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
    subst hεα; rfl
  have hαint : ∀ a ∈ intAf D.host.F, α * a ∈ intAf D.host.F := by
    intro a ha w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [hα1, one_mul]; exact ha w
    · rw [hα0 w hw, zero_mul]; exact zero_mem _
  exact latIndex_eq_of_chart α hα hαint hC hF (ι g) (hG.1 g) g.1 (hG.2.1 g)

end GlobalTheory.InertLatIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilTsumEnormRationalInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.SWAbsInv

open GlobalTheory.RallisCusp

variable {D : D7}

def lagSwap (W : HSp D) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (LinearEquiv.prodComm D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)).toLinearMap, by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    exact (Y.2.2 y hy y' hy').symm⟩

theorem lagSwap_lagSwap (W : HSp D) (Y : Lag W) : lagSwap W (lagSwap W Y) = Y := by
  apply Subtype.ext
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hy
    exact ⟨y.swap, ⟨y, hy, rfl⟩, rfl⟩

theorem isLagFrame_lagSwap (W : HSp D) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) : IsLagFrame W (lagSwap W Y) (C.2, C.1) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (LinearEquiv.prodComm D.host.E _ _).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

theorem lagTerm_swap {V W : HSp D} (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (f₁ f₂ : WO V W → ℂ) :
    lagTerm μ 𝓕 (C.2, C.1) f₂ f₁ = star (lagTerm μ 𝓕 C f₁ f₂) := by
  unfold lagTerm
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [mul_comm]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}

theorem tsum_comm (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₂ f₁‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let e : Lag W ≃ Lag W := ⟨lagSwap W, lagSwap W, lagSwap_lagSwap W, lagSwap_lagSwap W⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₂ f₁ h₂ h₁).1 (lagSwap W Y) _
    (isLagFrame_lagSwap W Y (fr Y) (hS.frame Y))
  change ‖lagTerm μ 𝓕 (fr (lagSwap W Y)) f₂ f₁‖ₑ = _
  rw [← h, lagTerm_swap, ← ofReal_norm_eq_enorm, norm_star, ofReal_norm_eq_enorm]

theorem tsum_left (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ) f₁) f₂‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let g : GQ W := ⟨γ, hγ⟩
  let e : Lag W ≃ Lag W := ⟨lagAct W g, lagAct W g⁻¹,
    fun Y => by rw [← lagAct_mul, inv_mul_cancel, lagAct_one],
    fun Y => by rw [← lagAct_mul, mul_inv_cancel, lagAct_one]⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ f₂ (hS.weil.om_pres (1, γ) f₁ h₁) h₂).1
    (lagAct W g Y) _ (isLagFrame_lagAct W g Y (fr Y) (hS.frame Y))
  have h' := ((Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂).2 γ hγ (gqMat W g)
    (gqMat_map W g).symm).1 (fr Y)
  change ‖lagTerm μ 𝓕 (fr (lagAct W g Y)) (om (1, γ) f₁) f₂‖ₑ = _
  rw [← h, h']

end

theorem tsum_enorm_lagTerm_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS F₁ F₂ h₁ h₂ γ₁ hγ₁ γ₂ hγ₂
  have p₂ := hS.weil.om_pres (1, γ₂) F₂ h₂
  rw [tsum_left hS h₁ p₂ hγ₁, tsum_comm hS p₂ h₁, tsum_left hS h₂ h₁ hγ₂, tsum_comm hS h₁ h₂]

end GlobalTheory.SWAbsInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChartLevels

theorem linIndep_rows_iff_map {k₁ k₂ : Type} [Field k₁] [Field k₂] (ι : k₁ →+* k₂) {m n : ℕ}
    (y : Matrix (Fin m) (Fin n) k₁) :
    LinearIndependent k₁ y.row ↔ LinearIndependent k₂ (y.map ι).row := by
  have key : ∀ {k : Type} [Field k] (y : Matrix (Fin m) (Fin n) k),
      LinearIndependent k y.row ↔ ∀ c : Fin m → k, c ᵥ* y = 0 → c = 0 := by
    intro k _ y
    rw [Fintype.linearIndependent_iff]
    have h : ∀ c : Fin m → k, ∑ i, c i • y.row i = c ᵥ* y := fun c => by
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    simp only [h]
    exact ⟨fun H c hc => funext (H c hc), fun H c hc i => congrFun (H c hc) i⟩
  have inv : ∀ {k : Type} [Field k] (y : Matrix (Fin m) (Fin n) k),
      LinearIndependent k y.row → ∃ B : Matrix (Fin n) (Fin m) k, y * B = 1 := by
    intro k _ y hy
    rw [key] at hy
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.vecMulLinear y)
      (LinearMap.ker_eq_bot.2 fun a b hab => sub_eq_zero.1 (hy _ (by
        rw [Matrix.sub_vecMul]
        exact sub_eq_zero.2 hab)))
    refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
    have hc : ∀ c : Fin m → k, c ᵥ* (y * (LinearMap.toMatrix' g)ᵀ) = c := fun c => by
      rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
      exact congrArg (fun f => f c) hg
    refine Matrix.ext fun i j => ?_
    have := congrFun (hc (Pi.single i 1)) j
    rw [Matrix.single_one_vecMul] at this
    rw [Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]
  constructor
  · intro hy
    obtain ⟨B, hB⟩ := inv y hy
    rw [key]
    intro c hc
    have : c ᵥ* ((y.map ι) * B.map ι) = c := by
      rw [← Matrix.map_mul, hB, Matrix.map_one _ ι.map_zero ι.map_one, Matrix.vecMul_one]
    rw [← Matrix.vecMul_vecMul, hc, Matrix.zero_vecMul] at this
    exact this.symm
  · intro hy
    rw [key] at hy ⊢
    intro c hc
    have h1 := hy (ι ∘ c) (funext fun j => by
      rw [← RingHom.map_vecMul, hc]
      simp)
    funext i
    exact ι.injective ((congrFun h1 i).trans ι.map_zero.symm)

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem residue_eq_zero_iff (x : GlobalTheory.SplitHecke.Ov D v) :
    IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) x = 0 ↔ Valued.v (x : Fv D.host.F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx : Valued.v (x : Fv D.host.F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx fun h1 => hnu ?_
    have h0 : (x : Fv D.host.F v) ≠ 0 := fun h => by
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    have hmem : (x : Fv D.host.F v)⁻¹ ∈ v.adicCompletionIntegers D.host.F :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, h1, inv_one])
    refine IsUnit.of_mul_eq_one (a := x) ⟨_, hmem⟩ (Subtype.ext ?_)
    show (x : Fv D.host.F v) * (x : Fv D.host.F v)⁻¹ = 1
    exact mul_inv_cancel₀ h0
  · intro hlt hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h2 := congrArg (fun t : GlobalTheory.SplitHecke.Ov D v => Valued.v (t : Fv D.host.F v)) hw
    have hw1 : Valued.v (w : Fv D.host.F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 w.2
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h2
    have : Valued.v (x : Fv D.host.F v) * Valued.v (w : Fv D.host.F v) < 1 :=
      (mul_le_of_le_one_right' hw1).trans_lt hlt
    rw [h2] at this
    exact lt_irrefl _ this

theorem resS_surjective (PP : Pl D.host.E) : Function.Surjective (resS D.host.F PP) := by
  rw [resS, RingHom.coe_comp]
  exact (RingEquiv.surjective _).comp Ideal.Quotient.mk_surjective

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem prim_map_eq {k₁ k₂ : Type} [Field k₁] [Field k₂] (ι : k₁ →+* k₂) {m n : ℕ}
    (y : Matrix (Fin m) (Fin n) k₁) : prim (y.map ι) = prim y := by
  unfold prim
  by_cases h : LinearIndependent k₁ y.row
  · rw [if_pos h, if_pos ((linIndep_rows_iff_map ι y).1 h)]
  · rw [if_neg h, if_neg (mt (linIndep_rows_iff_map ι y).2 h)]

theorem gl_map_inv_val {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (β : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.map f β)⁻¹).1 = (β⁻¹).1.map f := by
  rw [← map_inv]
  rfl

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem frame_of_baseFrame {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (φ : Datum.EAf D →+* Fv D.host.F v) (hφ : ∀ a, φ (toEAf D a) = π a)
    (hint : ∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N))
    (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hβ : Lev.IsBaseFrame V β Λ 1) : GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  intro y
  have hL := (GlobalTheory.FinAdIdent.lamHat_good hβ (f := 1) ⟨mul_one 1, 1, by simp⟩).2
  have hL' : ∀ x, x ∈ Formalism.L2.NTheta.LamHat V ↔ (fun a => Lev.swapAE D (x a)) ∈ Formalism.L2.Herm.hatL Λ :=
    fun x => by simpa only [one_smul, one_mul] using hL x
  refine (hL' _).trans ((hβ.1 _).trans (forall_congr' fun i => ?_))
  have e2 : (fun a => Lev.swapAE D (finPart D (e * y a))) = toEAf D e • (fun a => toEAf D (y a)) := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, ← RingHom.map_mul]
    rfl
  have e4 : (φ ∘ fun a => toEAf D (y a)) = fun k => π (y k) := funext fun k => hφ (y k)
  rw [e2, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hint, RingHom.map_mulVec, e4, gl_map_inv_val]

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem chart_levels : ∀ (D : D7) (e : AE D) (P : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → GlobalTheory.SplitHecke.Chart e v π → ∃ φ : Datum.EAf D →+* Fv D.host.F v, (∀ a, φ (toEAf D a) = π a) ∧ (∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N)) ∧ (∀ (m n : ℕ) (N : Matrix (Fin m) (Fin n) (Datum.EAf D)), IsIntM N → ∀ z : Matrix (Fin m) (Fin n) (GlobalTheory.SplitHecke.Ov D v), z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) = N.map φ → prim (redM P N) = prim (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Lev.IsBaseFrame V β Λ 1 → GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  intro D e P v π he hπ
  obtain ⟨φ, hφ, hres⟩ := GlobalTheory.ThetaSupport.exists_chart_levels he hπ
  obtain ⟨hi, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e P he
  have hπe : π e = 1 := hπ.map_e he.1.1
  have hint : ∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N) := by
    intro N
    obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) N
    rw [hφ, ← (hπ.2.2.2 a), ← RingHom.map_mul]
    exact ⟨GlobalTheory.PlaceDatum.finPart_mem_of_toEAf, GlobalTheory.IdemRes.toEAf_mem_of_finPart⟩
  refine ⟨φ, hφ, hint, ?_, ?_⟩
  · have hR : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ s ∈ v.adicCompletionIntegers D.host.F := fun s =>
      GlobalTheory.SplitHecke.isInt_Ov.1 ((hint s).1 (mul_mem hi s.2))
    let φR : Formalism.L2.Herm.intAf D.host.F D.host.E →+* GlobalTheory.SplitHecke.Ov D v :=
      (φ.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F) hR
    let ρ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
      (IsLocalRing.residue _).comp φR
    have hker : RingHom.ker (resS D.host.F P) ≤ RingHom.ker ρ := by
      intro s hs
      rw [RingHom.mem_ker] at hs ⊢
      exact (residue_eq_zero_iff (φR s)).2 (hres s hs)
    let ι : kP P →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
      (resS D.host.F P).liftOfRightInverse _ (Function.rightInverse_surjInv (resS_surjective P)) ⟨ρ, hker⟩
    have hι : ∀ s, ι (resS D.host.F P s) = ρ s := fun s =>
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ s
    intro m n N hN z hz
    have e1 : z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) = (redM P N).map ι := by
      ext i j
      have hzij : z i j = φR ⟨N i j, hN i j⟩ := Subtype.ext (congrFun (congrFun hz i) j)
      simp only [Matrix.map_apply, redM, dif_pos (hN i j), hι, hzij]
      rfl
    rw [e1]
    exact (prim_map_eq ι _).symm
  · exact frame_of_baseFrame φ hφ hint

end GlobalTheory.ChartLevels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremCConst25OfHypothesesStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramified_coefficient_chains_of_hypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (CR CA CB CK : ℝ), LiftingTheory.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F → CrystallineLiftingBounds.adm22 D HW F → InvariantsGenerators.LitFont D HW F → RamifiedCoefficientChains.Stmt D HW F Cm 25 CR CA CB CK := by
  first | exact @GlobalTheory.theoremC_of_admitted_inputs | exact GlobalTheory.theoremC_of_admitted_inputs | (intros; apply GlobalTheory.theoremC_of_admitted_inputs <;> assumption)
end

