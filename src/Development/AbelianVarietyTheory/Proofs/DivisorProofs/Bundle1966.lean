import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3
import Formalism.LocalToGlobal.Divisibility.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveFrameMatrixTransportIff
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport
namespace PrimFrameTr

section Fields
variable {k k' : Type} [Field k] [Field k']

theorem rank_map_le {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (f : k →+* k') (Z : Matrix A D k) :
    (Z.map f).rank ≤ Z.rank := by
  classical
  let M := LinearMap.range Z.mulVecLin
  let b := Module.finBasis k M
  have hc : ∀ y : D, (fun x => Z x y) ∈ M := fun y => ⟨Pi.single y 1, by ext x; simp⟩
  let P : Matrix A (Fin (Module.finrank k M)) k := Matrix.of fun x l => (b l : A → k) x
  let Q : Matrix (Fin (Module.finrank k M)) D k := Matrix.of fun l y => b.repr ⟨fun x => Z x y, hc y⟩ l
  have hPQ : Z = P * Q := by
    ext x y
    have h := congrArg (fun z : M => (z : A → k) x) (b.sum_repr ⟨fun x => Z x y, hc y⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply]
    simp only [P, Q, Matrix.of_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h : Z.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans ?_)
  simp [Matrix.rank, M]

theorem rank_map_equiv {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] (j : k ≃+* k') (Z : Matrix A D k) :
    (Z.map j).rank = Z.rank := by
  refine le_antisymm (rank_map_le (j : k →+* k') Z) ?_
  have := rank_map_le (j.symm : k' →+* k) (Z.map j)
  have e : (Z.map j).map (j.symm : k' →+* k) = Z := by ext; simp
  rwa [e] at this

theorem rank_trM {A D A₂ D₂ : Type} [Fintype A] [Fintype D] [DecidableEq D] [Fintype D₂]
    (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) : (trM j rA cD Z).rank = Z.rank := by
  have : trM j rA cD Z = (Z.map j).submatrix rA cD := by ext; rfl
  rw [this, Matrix.rank_submatrix, rank_map_equiv]

theorem row_trM {A D A₂ D₂ : Type} (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) (r : A₂) :
    (trM j rA cD Z).row r = fun c => j (Z.row (rA r) (cD c)) := rfl

theorem read_sum {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (c : A → k) :
    (fun d => j ((∑ a, c a • Z.row a) (cD d))) = ∑ r, j (c (rA r)) • (trM j rA cD Z).row r := by
  funext d
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, row_trM]
  exact (Fintype.sum_equiv rA _ _ fun r => rfl).symm

theorem mem_spanK_of {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (j : k ≃+* k') (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span k (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
  rw [read_sum j rA cD Z c]
  exact (Submodule.mem_span_range_iff_exists_fun k').2 ⟨_, rfl⟩

end Fields

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}

theorem isLocIso_symm (hj : IsLocIso j) : IsLocIso j.symm :=
  ⟨hj.2.1, by simpa using hj.1, fun x => by rw [← hj.2.2 (j.symm x)]; simp⟩

theorem mem_spanO_of (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) {x : D → k} (hx : x ∈ Submodule.span 𝒪[k] (Set.range Z.row)) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 hx
  have h := read_sum j rA cD Z (fun a => (c a : k))
  have e : (∑ a, c a • Z.row a) = ∑ a, (c a : k) • Z.row a := Finset.sum_congr rfl fun a _ => rfl
  rw [e, h]
  exact (Submodule.mem_span_range_iff_exists_fun 𝒪[k']).2
    ⟨fun r => ⟨j (c (rA r)), (hj.2.2 _).2 (c (rA r)).2⟩, rfl⟩

theorem read_symm {D D₂ : Type} (cD : D₂ ≃ D) (x : D → k) :
    (fun d => j.symm ((fun c => j (x (cD c))) (cD.symm d))) = x := by
  funext d; simp

theorem trM_symm {A D A₂ D₂ : Type} (rA : A₂ ≃ A) (cD : D₂ ≃ D) (Z : Matrix A D k) :
    trM j.symm rA.symm cD.symm (trM j rA cD Z) = Z := trM_symm_trM j rA cD Z

def readEquiv (j : k ≃+* k') {D D₂ : Type} (cD : D₂ ≃ D) : (D → k) ≃ (D₂ → k') where
  toFun x d := j (x (cD d))
  invFun y d := j.symm (y (cD.symm d))
  left_inv x := by funext d; simp
  right_inv y := by funext d; simp

theorem memK_iff {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span k' (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span k (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanK_of j rA cD Z⟩
  have := mem_spanK_of j.symm rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

theorem memO_iff (hj : IsLocIso j) {A D A₂ D₂ : Type} [Fintype A] [Fintype A₂] (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    (Z : Matrix A D k) (x : D → k) :
    (fun d => j (x (cD d))) ∈ Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) ↔
      x ∈ Submodule.span 𝒪[k] (Set.range Z.row) := by
  refine ⟨fun h => ?_, mem_spanO_of hj rA cD Z⟩
  have := mem_spanO_of (isLocIso_symm hj) rA.symm cD.symm _ h
  rwa [read_symm, trM_symm] at this

end PrimFrameTr

open PrimFrameTr in

theorem isPrimFrame_trM_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂]
    [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂] (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (hL : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  have hc : Fintype.card A₂ = Fintype.card A := Fintype.card_congr rA
  have hm : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
    rw [mem_matLat, mem_matLat]
    refine (forall_congr' fun r => ?_).trans (rA.forall_congr_right (q := fun a => Z.row a ∈ Λ))
    exact hL (Z.row (rA r))
  have hs : (Submodule.span 𝒪[k'] (Set.range (trM j rA cD Z).row) =
        (Submodule.span k' (Set.range (trM j rA cD Z).row)).restrictScalars 𝒪[k'] ⊓ Λ₂) ↔
      (Submodule.span 𝒪[k] (Set.range Z.row) =
        (Submodule.span k (Set.range Z.row)).restrictScalars 𝒪[k] ⊓ Λ) := by
    rw [SetLike.ext_iff, SetLike.ext_iff]
    refine ((readEquiv j cD).forall_congr_right).symm.trans (forall_congr' fun x => ?_)
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    change ((fun d => j (x (cD d))) ∈ _ ↔ (fun d => j (x (cD d))) ∈ _ ∧ (fun d => j (x (cD d))) ∈ Λ₂) ↔ _
    rw [memO_iff hj, memK_iff, hL]
  unfold IsPrimFrame
  rw [rank_trM, hc, hm, hs]
end GlobalTheory.PureMatch.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
          Formalism.IndefR.Datum.IsThetaFunO ψ S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ) := by
  first | exact @GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr | exact GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr | (intros; apply GlobalTheory.ThetaTransformTheta.isThetaFunO_thetaTr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section
namespace GlobalTheory.WeilUnitaryTransportF

theorem isUnitaryOn_transportF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ χS χT hcS hcT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have hψ := hω.std
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.T.exists_unitaryPair_partner_cmExtension F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_rationalMatrices_tower F E nS nT
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ :=
    GlobalTheory.T.darbouxCoords_transfer_haar_fundamentalDomain_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform F B.ψ hψ.1 κ μ hμ ν' hν' 𝓕' h𝓕'
  have hiso : ∀ Ψ ∈ schA F κ, ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂μ =
      c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Ψ w‖ₑ ^ 2 ∂ν := by
    intro Ψ hΨ
    rw [hc Ψ hΨ, ← heq]
    rfl
  have hth : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
    ⟨GlobalTheory.T.thetaTransform_rationalTranslate_quasiInvariant_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.continuous_thetaTransform_schwartz_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     GlobalTheory.T.contDiff_thetaTransform_archimedean_cm F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ⟩
  have ht := hom a b g h hh hg Φ hΦ
  rw [hiso _ ht.1, hiso _ hΦ, ht.2, hω.om_unit ν 𝓕 hν h𝓕 _ _ hth]

end GlobalTheory.WeilUnitaryTransportF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FibreLocality

theorem lp : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := GlobalTheory.T.vanishing_of_projection_support

theorem lw : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := GlobalTheory.T.exists_localizingWeight_equal_offPlaceMasses

theorem lc : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ b : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    (fun x => ψ (x ⬝ᵥ b) * Φ x) ∈ GlobalTheory.WeilM.schA F κ := GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace

open scoped Classical in
theorem ls_pure {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ K : Set (κ → AF F), IsCompact K ∧ ∀ x, GlobalTheory.WeilM.pureA F f g x ≠ 0 → GlobalTheory.LatVac.liftV v 1 • x ∈ K := by
  set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def
  let ι : FiniteAdeleRing (𝓞 F) F → AF F := fun a => (0, a)
  have hι : Continuous ι := continuous_const.prodMk continuous_id
  let Θ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) := fun z => e • fun i => ι (z i)
  have hΘ : Continuous Θ := by
    refine (continuous_const_smul e).comp (continuous_pi fun i => ?_)
    exact hι.comp (continuous_apply i)
  have he1 : e.1 = 0 := rfl
  refine ⟨Θ '' tsupport g, hg.2.isCompact.image hΘ, fun x hx => ⟨fun i => (x i).2, ?_, ?_⟩⟩
  · refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp only [GlobalTheory.WeilM.pureA]
    rw [h0, mul_zero]
  · funext i
    show e * ι (x i).2 = e * x i
    refine Prod.ext ?_ rfl
    show e.1 * 0 = e.1 * (x i).1
    rw [he1, zero_mul, zero_mul]

theorem ls : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∃ K : Set (κ → AF F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → GlobalTheory.LatVac.liftV v 1 • x ∈ K := by
  intro F _ _ κ _ v Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ls_pure v f g hg
  | zero => exact ⟨∅, isCompact_empty, fun x hx => (hx rfl).elim⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨K₁, hK₁, h₁⟩ := h1
    obtain ⟨K₂, hK₂, h₂⟩ := h2
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun x hx => ?_⟩
    by_cases hx1 : Φ₁ x = 0
    · exact Or.inr (h₂ x fun hx2 => hx (by simp [hx1, hx2]))
    · exact Or.inl (h₁ x hx1)
  | smul c Φ _ h =>
    obtain ⟨K, hK, hs⟩ := h
    exact ⟨K, hK, fun x hx => hs x fun h0 => hx (by simp [h0])⟩

theorem liftV_mul_self {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) * GlobalTheory.LatVac.liftV v 1 = GlobalTheory.LatVac.liftV v 1 := by
  have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (GlobalTheory.LatVac.liftV v 1 - 1)
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem at_iff {F : Type} [Field F] [NumberField F] {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (z : κ → AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z ↔ GlobalTheory.LatVac.liftV v 1 • z = z := by
  constructor
  · intro h
    have h1 := h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  · intro h u hu
    rw [← h, smul_smul]
    have := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
    rw [smul_eq_mul] at this
    rw [this, zero_smul]

theorem eq_zero_of_vanish_fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ) →
    (∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → AF F, (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ v ψ T hstd hnt hpres hiso hcomm Φ hΦ y hy
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def
  have he0 : evFin F v (1 - e) = 0 := by rw [map_sub, he_def, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self]
  let P : (κ → AF F) →+ (κ → AF F) := DistribMulAction.toAddMonoidHom _ e
  have hPc : Continuous P := continuous_const_smul e
  have hPP : ∀ x, P (P x) = P x := fun x => by
    show e • e • x = e • x
    rw [smul_smul, he_def, liftV_mul_self]
  have hTΦ := hpres Φ hΦ
  obtain ⟨K, hK, hKs⟩ := ls v Φ hΦ
  let μ : Measure (κ → AF F) := Measure.addHaar
  refine lp μ P hPc hPP Φ (T Φ) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ)
    (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hTΦ) K hK hKs y
    (fun z hz => hy z ((at_iff v z).2 hz)) ?_
  intro O hO hyO
  have htrig : ∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, e • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x‖ₑ ^ 2 ∂μ =
        ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ := by
    intro s c hs
    have hchar : ∀ b ∈ s, ∀ Ψ ∈ schA F κ,
        T (fun x => ψ (x ⬝ᵥ b) * Ψ x) = fun x => ψ (x ⬝ᵥ b) * T Ψ x := by
      intro b hb Ψ hΨ
      have h1 := hcomm (1 - e) he0 0 b Ψ hΨ
      have hb' : (1 - e) • b = b := by rw [sub_smul, one_smul, hs b hb, sub_zero]
      have hs0 : ∀ Ψ' : (κ → AF F) → ℂ,
          schr ψ ((1 - e) • (0 : κ → AF F), (1 - e) • b) Ψ' = fun x => ψ (x ⬝ᵥ b) * Ψ' x := by
        intro Ψ'; funext x; simp [schr, hb']
      rw [hs0, hs0] at h1
      exact h1
    have hsum : ∀ G : (κ → AF F) → ℂ, (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * G x) =
        ∑ b ∈ s, c b • (fun x => ψ (x ⬝ᵥ b) * G x) := by
      intro G; funext x; simp [Finset.sum_mul, mul_assoc]
    have hmem : (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) ∈ schA F κ := by
      rw [hsum]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (lc ψ hstd b Φ hΦ)
    have hT : T (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) =
        fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x := by
      rw [hsum, hsum, map_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [map_smul, hchar b hb Φ hΦ]
    have := hiso μ inferInstance _ hmem
    rw [hT] at this
    exact this
  exact lw v ψ hstd hnt μ inferInstance Φ hΦ (T Φ) hTΦ htrig y O hO hyO

end GlobalTheory.FibreLocality
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelColumnsFromTies
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

set_option maxHeartbeats 2000000 in

theorem rowsU_of_colPins : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : Formalism.L2.TiedDataSK ex) (P : RowSideFamily ex) (K : SquareIntegrableColumnsCompatible T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), ColPins K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.memberRows_of_kernelDatum_sizes CY CT hCT
  refine ⟨C0, ?_⟩
  intro D L hT Gi Gl Kc Y cX ex _ T P K W Del h0 hPins hW hKT hKS hN hNu hrk Zsc cf Cl CHl Pk hZs u lam0 c0 ce Ch Sw C1 H w e hwu hCh
  have hmu0 : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hpos : ∀ v : InfinitePlace D.what₂.LL, (((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding).PosDef :=
    fun v => Formalism.L2.DIV.BlockDat.HV_pos (ℓ := P.A3.fam3.F.lvl P.Ps P.ψs) K.ok1.ok2.conj (K.ok1.ok2.what₂ _) K.ok1.ok2.irr v
  have hlat : Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) :=
    nuLat_comap_isLattice D L hN u ⟨(hNu u).1, (hNu u).2⟩ _ e
  have ha : 0 < (K.c.face Pk.Zs).a w := by
    have h := hrk u
    change 0 < Module.finrank D.what₂.LL (Submodule.span D.what₂.LL ((D.div.Nu u).L : Set (D.div.Nu u).V)) at h
    rw [(hNu u).2, finrank_top, ← e.finrank_eq, Module.finrank_fin_fun] at h
    exact h
  have hev := GlobalTheory.T.frames_tilde_gamma_values D L hT Gi Gl Kc Y cX ex T P K hPins
  rw [← hZs] at hev
  clear hPins hrk hNu
  obtain ⟨X, e', c, Sp, colTie, kerTie, wTie, lvTie, sgTie, v0, TU, xiVal, trIv, famEq, gEq, plEq, i0Eq, tEq, muTie, ok1⟩ := K
  obtain ⟨toS, ker, crd, crd_gram, crd_lat, ker_sharp, ker_frm⟩ := T
  obtain ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, kX, seam, seam_ok, kPr, pr_ok, g_rec, kCh, ksel, kS, kword, T_rec, ktup, Q_rec, kcst, kidx, km2, kglob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩ := ker
  obtain ⟨Pr, Rk, W', Ch', sel, Sg, hX, Lv, Xg, m2, Gc, mu, cst, Li, hL, hP, Mem, wd, b, hY, Am, hK, hF, hE, ev⟩ := c
  have hXe : kX = fieldsLL D X e' := kerTie.1
  subst hXe
  have hRk : Rk = D.R := kerTie.2.1
  subst hRk
  have hPr : Pr = kPr := eq_of_heq kerTie.2.2.1
  subst hPr
  have hChE : Ch' = kCh := eq_of_heq kerTie.2.2.2.1
  subst hChE
  have hsel : sel = ksel := eq_of_heq kerTie.2.2.2.2.1
  subst hsel
  have hSg : Sg = kS := eq_of_heq kerTie.2.2.2.2.2.1
  subst hSg
  have hmu : mu = fun t => ktup (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.1
  subst hmu
  have hcst : cst = fun t => kcst (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.1
  subst hcst
  have hLi : Li = fun t => kidx (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.2.1
  subst hLi
  have hm2 : m2 = km2 := kerTie.2.2.2.2.2.2.2.2.2.1
  subst hm2
  have hGc : Gc = kglob := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.1
  subst hGc
  have hAm : Am = Formalism.L2.Ker.ambOf seam B χ cD := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.1
  subst hAm
  have hMem : Mem = D.what₂.Word := kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1
  subst hMem
  have hwd : wd = kword := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.2.2
  subst hwd
  have hW' : W' = W := eq_of_heq hW
  subst hW'
  have hLv : Lv = Formalism.L2.Col.rPsymF (R := D.R) Ch' := lvTie
  subst hLv
  have hwu' : w = u := eq_of_heq hwu
  subst hwu'
  have hmuOne : ktup (P.I.tup P.A3.fam3.base3.μ0) = 1 := by rw [hmu0]; exact hKT.mu0
  have hev' := hev hmuOne
  dsimp only at hev'
  have key := hC0 D L hT Gi Gl Kc Y cX ex
    (⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, fieldsLL D X e', seam, seam_ok, Pr, pr_ok, g_rec, Ch',
      sel, Sg, wd, T_rec, ktup, Q_rec, kcst, kidx, m2, Gc, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th,
      unf, ent, ent_lam, kf, kf_un, served⟩ : Formalism.L2.Ker.KerEntTied ex) W' Del h0 hX P.A3.fam3.base3
    (P.A3.side3 P.Ps P.ψs Pk.Zs) Xg P.I.tup hP b hY hK hF hE (ev Pk.Zs) w (Equiv.refl _) L.Nc lam0 c0 ce Ch Sw C1 H hmu0
    hKT hKS hCh hpos hev'
  dsimp only at key ha hlat ⊢
  obtain ⟨⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb⟩, hXc⟩ := key
  exact ⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb, hXc, ha, hlat⟩

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelArithmeticGroupsContainCongruenceStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevel_arithmeticGroups_contain_congruence : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (U σ)) l.M := by
  first | exact @GlobalTheory.LevGeo.hasPrinc_laws | exact GlobalTheory.LevGeo.hasPrinc_laws | (intros; apply GlobalTheory.LevGeo.hasPrinc_laws <;> assumption)
end

