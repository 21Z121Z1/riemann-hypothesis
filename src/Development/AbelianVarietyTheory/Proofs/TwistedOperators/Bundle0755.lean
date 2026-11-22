import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0726
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0748
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0732
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0746
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0747
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0723
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0009
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BidualityDepthLatticePieceBesselStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.BidualLattice

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  unfold latO
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _)]
    refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
    funext i j
    simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]
  · rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _)]
    refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
    funext i j
    simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem extY_jY_mem {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {LS : Lat S} {L₀ : Lat S₀} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (hm : ∀ v, MonoAt d LS L₀ v) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    d.extY T (u * d.jY) ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hS hT] at hu ⊢
  refine ⟨GlobalTheory.AscFinWit.mxAt_mul' (GlobalTheory.AscFinWit.mxAt_mul' hu.1 _) _, fun y hy => ?_⟩
  have e : (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from d.extY T (u * d.jY)) *ᵥ y =
      (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) *ᵥ (d.jY *ᵥ (d.pY *ᵥ y)) := by
    simp only [HypDec.extY_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  refine hu.2 _ ?_
  rw [GlobalTheory.FinPlLoc.part_lat _ _ _ _ hS.1] at hy ⊢
  refine ⟨fun i => ?_, fun v _ c hc => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _
      (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hy.1 l))
  · have hs := ((hm v) (c • y)).1 (hy.2 v trivial c hc)
    have e1 : c • (d.jY *ᵥ (d.pY *ᵥ y)) = ∑ i, GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ (c • y)) i) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e1]
    exact sum_mem fun i _ => hs.2.1 i

theorem dual_extX {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {LS : Lat S} {L₀ : Lat S₀} {LT : Lat T}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hm : ∀ v, MonoAt d LS L₀ v) {a : Mx D T.rank ρ} (ha : MxAt (fun _ => True) a) :
    d.extX T a ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
      ∀ a', d.extY T a' ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) →
        ψ (symplO S T (d.extX T a) (d.extY T a')) = 1 := by
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT _ _ (GlobalTheory.AscFinWit.mxAt_mul' ha d.pX)).trans ?_
  exact ⟨fun h _ ha' => h _ ha', fun h u hu =>
    (congrArg ψ (GlobalTheory.AscFinWit.symplO_extX d T a u)).trans (h _ (extY_jY_mem d hS hT hm hu))⟩

theorem mxAt_of_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {a' : Mx D T.rank ρ}
    (h : MxAt (fun _ => True) (d.extY T a')) : MxAt (fun _ => True) a' := by
  simpa only [HypDec.extY_apply, Matrix.mul_assoc, d.pY_jY, Matrix.mul_one] using GlobalTheory.AscFinWit.mxAt_mul' h d.jY

end GlobalTheory.AscFin.BidualLattice

namespace GlobalTheory.AscFin.BidualLattice

theorem bidual_main (hin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i) (hout : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latBig G i, e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)))) : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ := by
  have hI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting
  unfold OnStd at hI ⊢
  delta All at hI ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h a ha H
  have hJ := hI D hD T L μ0 hL sc G W M hM F hF
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hSV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by cases hj)).sd
  have hSW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (GlobalTheory.CosetRow.selfDual_chi hL G (2 * ρ + 1) hi).2
  have hbig : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0))) :=
    (hJ.1 (2 * ρ + 1) hi).2.2.2
  have hmono : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((hJ.2.1 ρ h).2.1 v).1
  have hrowO : ∀ u ∈ latRow G (2 * ρ + 1), u ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := fun u hu => by
    have h0 := hu.1
    rwa [BidualLattice.latO_negSp] at h0
  have hA2 : ∀ a', MxAt (fun _ => True) a' → (∀ b, (F.dB ρ h).extX _ b ∈ latRow G (2 * ρ + 1) →
      W.ψ (symplO _ _ ((F.dB ρ h).extX _ b) ((F.dB ρ h).extY _ a')) = 1) →
      W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1 :=
    fun a' h1 h2 => H a' (AddSubgroup.subset_closure ⟨h1, h2⟩)
  have hO : (F.dB ρ h).extX _ a ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := by
    refine (BidualLattice.dual_extX (F.dB ρ h) hψ hSV hSW hmono ha).2 fun a' ha' => ?_
    refine hA2 a' (BidualLattice.mxAt_of_extY _ (GlobalTheory.FinPl.LatMem.latO_mxAt ha')) fun b hb => ?_
    have hb' := hrowO _ hb
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hSV hSW _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hb')).1 hb' _ ha'
  refine ⟨?_, fun e he => ?_⟩
  · exact (BidualLattice.latO_negSp (G.V (.grid (2 * ρ + 2) 0)) _ _ _ _).ge hO
  · have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    have hsx : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ, (F.dB ρ h).extX _ (e • x) = e • (F.dB ρ h).extX _ x :=
      fun x => by simp only [HypDec.extX_apply, Matrix.smul_mul]
    have hsy : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ, (F.dB ρ h).extY _ (cA D e • x) =
        cA D e • (F.dB ρ h).extY _ x := fun x => by simp only [HypDec.extY_apply, Matrix.smul_mul]
    have hea : MxAt (fun _ => True) (e • a) := fun i j => Ideal.mul_mem_left _ _ (ha i j)
    have hB : (F.dB ρ h).extX _ (e • a) ∈ latBig G (2 * ρ + 1) := by
      refine (BidualLattice.dual_extX (F.dB ρ h) hψ hSV hbig hmono hea).2 fun a' ha' => ?_
      rw [hsx, GlobalTheory.SplitScalar.symplO_smul, ← hsy]
      have ha'f := BidualLattice.mxAt_of_extY _ (GlobalTheory.FinPl.LatMem.latO_mxAt ha')
      refine hA2 _ (fun i j => Ideal.mul_mem_left _ _ (ha'f i j)) fun b hb => ?_
      rw [hsy, ← GlobalTheory.SplitScalar.symplO_smul]
      have hb' := hin hL hD G (2 * ρ + 1) hi e he _ hb
      exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hSV hbig _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hb')).1 hb' _ ha'
    have h2 := hout hL hD G (2 * ρ + 1) hi e he _ hB
    rwa [hsx, smul_smul, hee] at h2

theorem bidual_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ :=
  bidual_main GlobalTheory.T.depthLatticeGridRow_smul_mem_selfDualModulusShift GlobalTheory.T.selfDualModulusShift_half_mem_completedModulusHom

end GlobalTheory.AscFin.BidualLattice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutantDepthLatticePermutesCosetVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosShift

variable {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
  {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}

theorem isHalf_sub' {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x - y) := fun i j => by
  simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]

theorem isHalf_add' {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem map_smul_sub (e : AE D) (a b : homLat Λ Λ') : e • ((a - b : homLat Λ Λ') : Matrix (Fin m) (Fin n) D.host.E).map (incA D) =
    e • (a : Matrix (Fin m) (Fin n) D.host.E).map (incA D) - e • (b : Matrix (Fin m) (Fin n) D.host.E).map (incA D) := by
  rw [Submodule.coe_sub, Matrix.map_sub _ (incA D).map_sub, smul_sub]

theorem map_smul_add (e : AE D) (a b : homLat Λ Λ') : e • ((a + b : homLat Λ Λ') : Matrix (Fin m) (Fin n) D.host.E).map (incA D) =
    e • (a : Matrix (Fin m) (Fin n) D.host.E).map (incA D) + e • (b : Matrix (Fin m) (Fin n) D.host.E).map (incA D) := by
  rw [Submodule.coe_add, Matrix.map_add _ (incA D).map_add, smul_add]

theorem mk_sub' (a b : homLat Λ Λ') : Cos.mk 𝔪 (a - b) = (Submodule.Quotient.mk a - Submodule.Quotient.mk b :
    homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
  Submodule.Quotient.mk_sub _

theorem mk_add' (a b : homLat Λ Λ') : Cos.mk 𝔪 (a + b) = (Submodule.Quotient.mk a + Submodule.Quotient.mk b :
    homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
  Submodule.Quotient.mk_add _

theorem mem_cosSet_add {e : AE D} {z : Mx D m n} (hz : IsHalf e z) (x₀ x₁ : homLat Λ Λ')
    (hx₁ : z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')) (t : Mx D m n) :
    t + z ∈ cosSet e (Cos.mk 𝔪 x₀) ↔ t ∈ cosSet e (Cos.mk 𝔪 (x₀ - x₁)) := by
  constructor
  · rintro ⟨ht, y, hy, hm⟩
    refine ⟨?_, y - x₁, ?_, ?_⟩
    · have := isHalf_sub' ht hz
      rwa [add_sub_cancel_right] at this
    · rw [mk_sub', mk_sub']
      exact congrArg (· - _) hy
    · rw [map_smul_sub]
      have h2 := sub_mem hm hx₁
      have e2 : t + z - e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) -
          (z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) =
          t - (e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) := by
        abel
      rwa [e2] at h2
  · rintro ⟨ht, y, hy, hm⟩
    refine ⟨isHalf_add' ht hz, y + x₁, ?_, ?_⟩
    · rw [mk_add']
      rw [mk_sub'] at hy
      have hy' : (Submodule.Quotient.mk y : homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) =
          Submodule.Quotient.mk x₀ - Submodule.Quotient.mk x₁ := hy
      rw [hy', sub_add_cancel]
      rfl
    · rw [map_smul_add]
      have h2 := add_mem hm hx₁
      have e2 : t - e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) +
          (z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) =
          t + z - (e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) + e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) := by
        abel
      rwa [e2] at h2

theorem cosInd_add {e : AE D} {z : Mx D m n} (hz : IsHalf e z) (x₁ : homLat Λ Λ')
    (hx₁ : z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')) (κ : Cos Λ Λ' 𝔪) :
    ∃ κ' : Cos Λ Λ' 𝔪, (fun t => cosInd e κ (t + z)) = cosInd e κ' := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Cos.mk 𝔪 x₀ = κ := Submodule.Quotient.mk_surjective _ κ
  refine ⟨Cos.mk 𝔪 (x₀ - x₁), funext fun t => ?_⟩
  have key := mem_cosSet_add hz x₀ x₁ hx₁ t
  rw [hx₀] at key
  show Set.indicator (cosSet e κ) 1 (t + z) = Set.indicator (cosSet e (Cos.mk 𝔪 (x₀ - x₁))) 1 t
  classical
  simp only [Set.indicator_apply, key, Pi.one_apply]

end GlobalTheory.CosShift

theorem GlobalTheory.CosShift.mem_hatMx_of_latO {D : D7} (hq : OffQ D) {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}
    (hL : L.Is μ₀) (G : GridData L sc) {i : ℕ} (hi : i < D.R.m) {e : AE D} (he : IsIdemSum e G.pl.W0)
    {z : WO (G.pS (.chi i 0)) (G.pT (.chi i 0))} (hz : IsHalf e z)
    (hm : z ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) :
    z ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨βS, hβS⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ (G.latS (.chi i 0)) hSD.1.1
  obtain ⟨βT, hβT⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ (G.latT (.chi i 0)) hSD.2.1
  exact GlobalTheory.RowLatChi.mem_hatMx_of_int hβS hβT he hz fun w hw a b =>
    GlobalTheory.RowLatChi.int_of_mem_latO hSD.1 hβS hβT w (GlobalTheory.DepthFix.aa_int hL hq G hw) hm a b

set_option maxHeartbeats 1000000 in
open GlobalTheory.CosShift in

theorem GlobalTheory.CosShift.epart : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → (∀ κ, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd e κ) (W.cosVec i κ)) → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∀ κ, ∃ κ', heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (W.cosVec i κ) = W.cosVec i κ' := by
  intro D hq T L μ₀ hL sc G W M hM i hi e he hθ w hw hwinf κ
  obtain ⟨⟨T₀, hT₀⟩, -⟩ := hθ κ
  have hv : ∀ κ, W.cosVec i κ = T₀ (cosInd e κ) := fun κ => (hθ κ).2 T₀ hT₀
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hz : IsHalf e (e • w) := fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)),
      e • w - e • (x₁ : Matrix _ _ D.host.E).map (incA D) ∈
        hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) :=
    GlobalTheory.T.exists_rational_hom_approx_half_mod_ideal (G.pl.modul_ne_bot sc) hSD.1.1 hSD.2.1 he (e • w) hz
      (mem_hatMx_of_latO hq hL G hi he hz (GlobalTheory.T.commutantPart_chosenPlaces_mem_completedLattice hL G W.ψ W.ψ_std i hi e he w hw hwinf))
  obtain ⟨κ', hκ'⟩ := cosInd_add hz x₁ hx₁ κ
  refine ⟨κ', ?_⟩
  rw [hv κ, hv κ', ← hκ']
  exact (hT₀.trans (cosInd e κ) (GlobalTheory.GridWeil.isSBHalf_cosInd hSD.1 hSD.2 (G.pl.modul_ne_bot sc) hee
    (GlobalTheory.PlaceDatum.infPart_idemSum he) κ) (e • w) hz).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetVectorsNonzeroDepthFockVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_vectors_nonzero_depth_fock_vacua : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ κ, W.cosVec i κ ≠ 0 ∧ Dep W (.chi i 0) (W.cosVec i κ) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0))) W.θ τ (cplxO (G.cartS W.cart (.chi i 0) τ) (G.onT W.cart (.chi i 0) τ)) (W.cosVec i κ) := by
  first | exact @GlobalTheory.CosDep.cosVec_dep | exact GlobalTheory.CosDep.cosVec_dep | (intros; apply GlobalTheory.CosDep.cosVec_dep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormApproxMultiplicityMapsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_approx_multiplicity_maps : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  first | exact @GlobalTheory.CuspPureApprox.exists_sum_approx | exact GlobalTheory.CuspPureApprox.exists_sum_approx | (intros; apply GlobalTheory.CuspPureApprox.exists_sum_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.RowBig

open scoped Pointwise

variable {D : D7}

theorem idLat_one {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    idLat (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) Λ = Λ := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    rw [algebraMap_smul]
    exact Λ.smul_mem r hy
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩

theorem conjFI_coe (I : Ideal (𝓞 D.host.E)) :
    GlobalTheory.SeeSaw.conjFI D (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((D.host.conj • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨D.host.conj • r, Ideal.smul_mem_pointwise_smul _ _ _ hr, ?_⟩
    show D.host.conj (r : D.host.E) = x
    rw [show (r : D.host.E) = D.host.conj x from hx, GlobalTheory.SeeSaw.conj_conj_host]
  · rintro ⟨r, hr, rfl⟩
    refine ⟨D.host.conj⁻¹ • r, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hr, ?_⟩
    show D.host.conj.symm (r : D.host.E) = D.host.conj (r : D.host.E)
    rw [AlgEquiv.symm_apply_eq, GlobalTheory.SeeSaw.conj_conj_host]

theorem conjFI_conjFI (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.SeeSaw.conjFI D (GlobalTheory.SeeSaw.conjFI D 𝔞) = 𝔞 := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]

theorem conjFI_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.SeeSaw.conjFI D (shiftId G) = (shiftId G)⁻¹ := by
  have hb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      GlobalTheory.SeeSaw.conjFI D (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := (conjFI_coe _).symm
  unfold shiftId
  rw [hb, map_mul, map_inv₀, conjFI_conjFI, mul_inv, inv_inv, mul_comm]

theorem shiftId_ne_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) : shiftId G ≠ 0 := by
  have hm : (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [show ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      GlobalTheory.SeeSaw.conjFI D (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) from (conjFI_coe _).symm]
    exact (RingEquiv.map_ne_zero_iff _).2 hm
  exact mul_ne_zero hm (inv_ne_zero hb)

theorem isSelfDualC_idLat_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {S : HSp D} (Λ : Lat S)
    (hΛ : IsSelfDualC S Λ) : IsSelfDualC S (idLat (shiftId G) Λ) := by
  refine GlobalTheory.ScaleSelfDual.isSelfDualC_scaleLat S Λ hΛ (shiftId_ne_zero G) fun c => ?_
  rw [← conjFI_shiftId, GlobalTheory.SeeSaw.mem_conjFI, Formalism.BasicNotions.bridge_star_holds D.R D.host c]

theorem latRow_le_latBig : All fun {D} _ _ _ {G} _ _ => ∀ i, 1 ≤ i → i < D.R.m → latRow G i ≤ latBig G i := by
  intro D hq T L μ0 hL sc G W M hM i hi1 him u hu
  have hS : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (X := .grid (i + 1) 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have hT : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
    (G.isV (X := .grid i 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have h1 := idLat_one (G.Λ (.grid i 0))
  have hsh := isSelfDualC_idLat_shiftId G _ hT
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hu' : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) ∧
      ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu
  have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (G.Λ (.grid (i + 1) 0)) 1 (G.Λ (.grid i 0)) hS (by rw [h1]; exact hT)
    (by rw [one_mul]; exact hsh) u (by rw [h1]; exact GlobalTheory.RowLoc.mem_latO_negSp.1 hu'.1) ⟨e, he, by rw [h1]; exact hu'.2 e he⟩
  rw [one_mul] at key
  exact key

end GlobalTheory.RowBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entire_eq_of_monomial_derivations_at_zero_eq : ∀ {D : D7} {N N' : ℕ} (Φ Ψ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ), Differentiable ℂ Φ → Differentiable ℂ Ψ → (∀ k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ, Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ = Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Ψ) → Φ = Ψ := by
  first | exact @GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq | exact GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq | (intros; apply GlobalTheory.EntireJetUniq.eq_of_applyAt0_monomial_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeKernelCosetFramedPointStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernel_coset_framedPoint : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∃ a ∈ Rc, ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z := by
  first | exact @GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer | exact GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer | (intros; apply GlobalTheory.HeckeExist.exists_coset_frBor_of_hkKer <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulSelfDualHomLatticeMemDepthLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nsmul_selfDual_hom_lattice_mem_depth_lattice : OnStd fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latBig G i, N • u ∈ latRow G i := by
  first | exact @GlobalTheory.BigRow.exists_nsmul_latBig_mem_latRow | exact GlobalTheory.BigRow.exists_nsmul_latBig_mem_latRow | (intros; apply GlobalTheory.BigRow.exists_nsmul_latBig_mem_latRow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantLastVertexLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_pairing_invariant_last_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) →
    t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.LastVertexInv.pairPts_last_invariant | exact GlobalTheory.LastVertexInv.pairPts_last_invariant | (intros; apply GlobalTheory.LastVertexInv.pairPts_last_invariant <;> assumption)
end

