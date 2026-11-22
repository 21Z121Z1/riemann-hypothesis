import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0167
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallPrincipalCongruenceLiftVector
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SmallEx

theorem exists_isVacO {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) : ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := Formalism.IndefR.Datum.measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩

theorem exists_small_stepVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∃ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) ∧ IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f := by
  classical
  intro D ψ θ A H χA om sA sH hθ _ hW hA hH _ β Z hP
  have dA := GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat A
  have dH := GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat H
  obtain ⟨βH, hβH⟩ := GlobalTheory.AdelicFrame.exists_isFrame (F := D.host.F) (frameLat H) dH.1.fg dH.1.span_eq_top
  obtain ⟨f₀, hf₀⟩ := exists_isVacO ψ θ hW.std hθ A H sA sH hA hH _ _ dA dH
  have hsp : ∃ e : AE D, IsIdemSum e ((prinDat A Z).Pg ∪ ∅) := by
    obtain ⟨e, he⟩ := hP.idem
    exact ⟨e, by rw [Finset.union_empty]; exact he⟩
  obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.stepVecExists D ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z)
    (fun _ => 1) ∅ (fun _ => 1) dA dH hP.frame hβH (Finset.disjoint_empty_right _) hsp f₀ hf₀
  exact ⟨βH, f₀, f, hβH, hf⟩

end GlobalTheory.Core.Rk.SmallEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLatMonoId
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem sum_pair_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) = star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

variable (d : HypDec S S₀ ρ)

theorem pair_decomp (x y : Fin S.rank → D.host.E) :
    star x ⬝ᵥ (S.gram *ᵥ y) = star (d.qY *ᵥ x) ⬝ᵥ (d.qX *ᵥ y) + star (d.q0 *ᵥ x) ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) +
      star (d.qX *ᵥ x) ⬝ᵥ (d.qY *ᵥ y) := by
  rw [gram_eq d, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, pair_mul, pair_mul, pair_mul,
    ← Matrix.mulVec_mulVec]

theorem star_single (i : Fin ρ) (b : D.host.E) : star (Pi.single i b : Fin ρ → D.host.E) = Pi.single i (star b) := by
  funext j; by_cases h : j = i <;> simp [h, Pi.single_apply]

theorem pair_e (i : Fin ρ) (b : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e *ᵥ Pi.single i b) ⬝ᵥ (S.gram *ᵥ y) = star b * (d.qY *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e, wittDecomposition_coreProj_mul_e_eq_zero, qY_e, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_e' (i : Fin ρ) (c : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e' *ᵥ Pi.single i c) ⬝ᵥ (S.gram *ᵥ y) = star c * (d.qX *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e', wittZeroProjection_mul_dualBasis_eq_zero, qY_e', Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_i₀ (x₀ : Fin S₀.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.i₀ *ᵥ x₀) ⬝ᵥ (S.gram *ᵥ y) = star x₀ ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_i₀, wittDecomposition_coreProj_mul_core_eq_one, qY_i₀, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add]

theorem decomp (y : Fin S.rank → D.host.E) : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
    d.sum_eq_one_rat, Matrix.one_mulVec]

theorem exists_ne_zero {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ b ∈ 𝔟, b ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (FractionalIdeal.eq_zero_iff.2 hc)

theorem exists_ne_zero_dualC (𝔟 : FI D) : ∃ c ∈ dualC 𝔟, c ≠ 0 := by
  obtain ⟨a, ha, hint⟩ := 𝔟.isFractional
  refine ⟨star (algebraMap (𝓞 D.host.E) D.host.E a), fun b hb => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hint b hb
    have : star b * star (algebraMap (𝓞 D.host.E) D.host.E a) = star (algebraMap (𝓞 D.host.E) D.host.E r) := by
      rw [hr, Algebra.smul_def, star_mul', mul_comm]
    rw [this]
    exact GlobalTheory.HypLattice.star_mem_int ⟨r, rfl⟩
  · rw [Ne, star_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero ha)

theorem dualC_le_span {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ γ : D.host.E, dualC 𝔟 ≤ Submodule.span (𝓞 D.host.E) {γ} := by
  obtain ⟨β, hβ, hβ0⟩ := exists_ne_zero h
  refine ⟨(star β)⁻¹, fun c hc => ?_⟩
  obtain ⟨o, ho⟩ := hc β hβ
  have hs : star β ≠ 0 := by rwa [Ne, star_eq_zero]
  refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
  rw [Algebra.smul_def, ho, mul_comm (star β), mul_assoc, mul_inv_cancel₀ hs, mul_one]

theorem mulVec_single_smul {n : ℕ} (M : Matrix (Fin S.rank) (Fin n) D.host.E) (i : Fin n) {a b : D.host.E} (hb : b ≠ 0) :
    M *ᵥ Pi.single i a = (a * b⁻¹) • (M *ᵥ Pi.single i b) := by
  rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]

variable {L₀ : Lat S₀} {𝔟 : ℕ → FI D}

theorem isLattice_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : Submodule.IsLattice D.host.E L₀) :
    Submodule.IsLattice D.host.E (splitL d L₀ 𝔟) := by
  choose γ hγ using fun i : Fin ρ => dualC_le_span (h𝔟 i)
  refine ⟨?_, ?_⟩
  · let T : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
      (⨆ i : Fin ρ, (𝔟 i : Submodule (𝓞 D.host.E) D.host.E).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))) ⊔
        L₀.map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ⊔
        ⨆ i : Fin ρ, (Submodule.span (𝓞 D.host.E) {γ i}).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e' *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))
    have hT : T.FG :=
      ((Submodule.fg_iSup _ fun i : Fin ρ => (FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔟 i)).map _).sup
        (hL₀.fg.map _)).sup (Submodule.fg_iSup _ fun i : Fin ρ => (Submodule.fg_span_singleton _).map _)
    refine hT.of_le fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    have hs : ∀ (M : Matrix (Fin S.rank) (Fin ρ) D.host.E) (w : Fin ρ → D.host.E), M *ᵥ w = ∑ i, w i • (M *ᵥ Pi.single i 1) := by
      intro M w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
    rw [decomp d y, hs d.e, hs d.e']
    refine add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
      (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, h2, rfl⟩)))
      (Submodule.mem_sup_right ?_)
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, h1 i, rfl⟩
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, hγ i (h3 i), rfl⟩
  · rw [eq_top_iff]
    intro y _
    rw [decomp d y]
    refine add_mem (add_mem ?_ ?_) ?_
    · rw [← Finset.univ_sum_single (d.qX *ᵥ y), Matrix.mulVec_sum]
      refine sum_mem fun i _ => ?_
      obtain ⟨β, hβ, hβ0⟩ := exists_ne_zero (h𝔟 i)
      rw [mulVec_single_smul d.e i hβ0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (e_mem (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hβ)))
    · have hx : d.q0 *ᵥ y ∈ Submodule.span D.host.E (L₀ : Set (Fin S₀.rank → D.host.E)) := by
        rw [hL₀.span_eq_top]; trivial
      generalize d.q0 *ᵥ y = x₀ at hx ⊢
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (i₀_mem hx)
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add x x' _ _ hx hx' => rw [Matrix.mulVec_add]; exact add_mem hx hx'
      | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx
    · rw [← Finset.univ_sum_single (d.qY *ᵥ y), Matrix.mulVec_sum]
      refine sum_mem fun i _ => ?_
      obtain ⟨c, hc, hc0⟩ := exists_ne_zero_dualC (𝔟 i)
      rw [mulVec_single_smul d.e' i hc0]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i hc)))

theorem isSelfDualC_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : IsSelfDualC S₀ L₀) : IsSelfDualC S (splitL d L₀ 𝔟) := by
  have hR : ∀ z : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = z) ↔ z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    fun z => Iff.rfl
  have h0 : ∀ y₀ : Fin S₀.rank → D.host.E, y₀ ∈ L₀ ↔ ∀ x₀ ∈ L₀, star x₀ ⬝ᵥ (S₀.gram *ᵥ y₀) ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range := fun y₀ => by
    rw [hL₀.2 y₀]
    simp only [hR, sum_pair_eq]
  refine ⟨isLattice_splitL d h𝔟 hL₀.1, fun y => ?_⟩
  simp only [hR, sum_pair_eq]
  constructor
  · intro hy x hx
    obtain ⟨hy1, hy2, hy3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    obtain ⟨hx1, hx2, hx3⟩ := (mem_splitL d L₀ 𝔟 x).1 hx
    rw [pair_decomp]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) ((h0 _).1 hy2 _ hx2)) (sum_mem fun i _ => ?_)
    · have := GlobalTheory.HypLattice.star_mem_int (hx3 i _ (hy1 i))
      rwa [star_mul', star_star, mul_comm] at this
    · exact hy3 i _ (hx1 i)
  · intro hy
    refine (mem_splitL d L₀ 𝔟 y).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
    · have hi : 𝔟 i ≠ 0 := h𝔟 i
      rw [← inv_inv (𝔟 i), FractionalIdeal.mem_inv_iff (inv_ne_zero hi)]
      intro z hz
      have hc : star z ∈ dualC (𝔟 i) := fun b hb => by
        have := GlobalTheory.HypLattice.star_mem_int (GlobalTheory.HypLattice.mem_one_iff_range.1 ((FractionalIdeal.mem_inv_iff hi).1 hz b hb))
        rwa [star_mul', mul_comm] at this
      have := hy _ (e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i hc))
      rw [pair_e', star_star, mul_comm] at this
      exact GlobalTheory.HypLattice.mem_one_iff_range.2 this
    · rw [h0]
      intro x₀ hx₀
      have := hy _ (i₀_mem (d := d) (𝔟 := 𝔟) hx₀)
      rwa [pair_i₀] at this
    · intro b hb
      have := hy _ (e_mem (L₀ := L₀) (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hb))
      rwa [pair_e] at this

end GlobalTheory.SeeSaw.SplitLat

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposi
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.HypSumWitt

open scoped ComplexOrder

theorem gramAt_hypSp (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ =
      (Matrix.fromBlocks (1 : Matrix (Fin t) (Fin t) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  unfold gramAt
  rw [GlobalTheory.Doubling.gram_hdbl]
  ext i j
  simp [GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, GlobalTheory.OrthSumSp.posSp_gram]
  generalize finSumFinEquiv.symm i = a
  generalize finSumFinEquiv.symm j = b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, apply_ite]

theorem gsq (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ * gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ = 1 := by
  rw [gramAt_hypSp, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem gct (D : D7) (t : ℕ) (τ : D.what₂.Tau) :
    (gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ)ᴴ = gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ := by
  rw [gramAt_hypSp, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  simp

theorem exists_hypSum_orthDec_hypDec : ∀ (D : D7) (W : HSp D) (t : ℕ), HSpace.SigOK W → ∃ (H B : HSp D) (_ : OrthDec B W H) (_ : HypDec B W t), HSpace.SigOK H ∧ HSpace.SigOK B ∧ H.rank = 2 * t ∧ (∀ τ, H.sig τ = (t, t)) ∧ ∃ sH : RealMat H, ∀ τ, IsCartanInv (gramAt D H τ) (sH τ) := by
  intro D W t hW
  refine ⟨GlobalTheory.OrthSumSp.hypSp D t, _, GlobalTheory.OrthSumSp.orthSumDec D W _, GlobalTheory.OrthSumSp.hypSumDec D W t,
    GlobalTheory.OrthSumSp.hypSp_sigOK D t, GlobalTheory.Doubling.sigOK_hsum hW (GlobalTheory.OrthSumSp.hypSp_sigOK D t), ?_,
    GlobalTheory.OrthSumSp.hypSp_sig D t, fun τ => gramAt D (GlobalTheory.OrthSumSp.hypSp D t) τ, fun τ => ⟨gsq D t τ, ?_, ?_⟩⟩
  · show t + t = 2 * t; omega
  · rw [gct, Matrix.mul_assoc, gsq, Matrix.mul_one]
  · rw [gsq]; exact Matrix.PosDef.one
end GlobalTheory.HypSumWitt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingOfSg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S Formalism.IndefR.Mult in

theorem GlobalTheory.SeeSaw.exists_isJ_of_par {D : D7} {u : D.what₂.Word}
    (hsg : ∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i)
    {par} (M : DSModel D.sp.X' par) (hpar : par = parB (Ptw D) D.R.m) :
    ∃ j, GlobalTheory.Core.Rk.Top.IsJ u M j := by
  subst hpar
  obtain ⟨j, hj⟩ := GlobalTheory.Core.Rk.Top.exists_isJ D u M
  exact ⟨j, hj hsg⟩

theorem GlobalTheory.SeeSaw.sg_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (τ) :
    ((((I.rec7 l Z).fm u).sg τ).w i : ℚ) =
      sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  have h2 := (TC.tup_sgHC_eq (B.hcW u τ) i).trans
    (congrArg (fun P => Formalism.L2.Col.RowPar.sgHC P i) (TC.tup_rowPar_eq B u τ))
  exact (Formalism.L2.Col.RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTranslatesOfValuesFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem isTr_unique {ι : Type} [Fintype ι] {n : ℕ} {G : ι → Matrix (Fin n) (Fin n) ℂ} {g : ι → Matrix (Fin n) (Fin n) ℂ}
    {y₁ y₂ y' : Frames G} (h₁ : IsTr g y₁ y') (h₂ : IsTr g y₂ y') : y₁.1 = y₂.1 := by
  funext τ
  have hu : IsUnit (g τ).det := by
    have h := y'.2 τ
    rw [h₁ τ, Matrix.det_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have e : g τ * y₁.1 τ = g τ * y₂.1 τ := by rw [← h₁ τ, ← h₂ τ]
  calc y₁.1 τ = (g τ)⁻¹ * (g τ * y₁.1 τ) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (g τ)⁻¹ * (g τ * y₂.1 τ) := by rw [e]
    _ = y₂.1 τ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

theorem jOf_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks), IsInfFam R.θ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), ∃ J, JOf R j J := by
  intro B X I _ _ l Z G _ _ Pl0 T F Ks _ _ _ R _ j
  refine ⟨fun v k z' => if h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
      IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' then j v ⟨h.choose.1, h.choose.2⟩ else 0, ?_⟩
  intro v k _ z z' hz
  have h : ∃ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' := ⟨z, hz⟩
  simp only [dif_pos h]
  have e := isTr_unique h.choose_spec hz
  exact congrArg (j v) (Subtype.ext e)

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChartsAll

open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

theorem exists_charts : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), (IsSplit (E := D.host.E) v → ∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ (¬ IsSplit (E := D.host.E) v → IsInertAt D.host.F D.host.E v w ∧ Odd (qV D.host.F v) ∧ ∀ c, IsConjAt D.sp.cm.sig h c → ∃ e, IsInertChart D.sp.cm.sig V.gram (frameLat V) h c e) := by
  intro D V v w h
  refine ⟨fun hs => (GlobalTheory.NoExcl.chart V h hs).1, fun hns => ?_⟩
  have hI := GlobalTheory.LFun.exists_isInertChart D.sp.cm.sig (isCMExt_host D) v
  obtain ⟨w₀, hw₀⟩ := (hI.1 (GlobalTheory.VacCoef.isUnram_host D v)).resolve_left hns
  have h₀ : w₀.under (𝓞 D.host.F) = v := GlobalTheory.LFun.under_eq_of_isInertAt hw₀
  obtain rfl : w = w₀ := ((hI.2 w₀ h₀ hw₀).2.2.1 w).1 h
  obtain ⟨-, ⟨c₀, hc₀, -⟩, -, -, H⟩ := hI.2 w h hw₀
  have hfix : Formalism.DivisionValues.conjPl w = w := GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw₀ h
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h2 => GlobalTheory.CoreThree.conj_ne_of_two w h2 hfix
  have hv2 : Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
    rw [← map_ofNat (algebraMap D.host.E (w.adicCompletion D.host.E)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 D.host.E) D.host.E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 (by exact_mod_cast h2)
  obtain ⟨⟨ϖ, hU⟩, -⟩ := H c₀ hc₀
  refine ⟨hw₀, GlobalTheory.InertLoc.odd_of_v_two hU hv2, fun c hc => ?_⟩
  obtain ⟨e, he, -⟩ := (H c hc).2 V.rank V.gram (frameLat V) (GlobalTheory.NoExcl.isHermND_gram V) (frameLat_fg V)
    (SelfDual.isLattice_frameLat V).span_eq_top (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨e, he⟩

end GlobalTheory.ChartsAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Core.Ht2

theorem family_laws : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws)
    (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).EqP I.chi ∧
      (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi := by
  intro B X I h _ l Z
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hχ : TaylorLogMetric.IsChi (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  exact ⟨GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ,
    (GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ).1⟩

end GlobalTheory.Core.Ht2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlMemGfC
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGfCImg

theorem gl_mem_GfC : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  intro D k _ _ _ _ p S n _ _ β g
  have hg := β.gl_supp g
  have he := p.split
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt S (β.gl g) - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt S (β.gl g) i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

end GlobalTheory.FrameGfCImg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfCocycleIsotropicIdempotentHalvesTrivialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfCocycle_isotropic_idempotentHalves_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ u ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ v ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplOH S T (e • u) (cA D e • v)) = 1 := by
  first | exact @GlobalTheory.HalfCocycle.char_symplOH_idem_conj | exact GlobalTheory.HalfCocycle.char_symplOH_idem_conj | (intros; apply GlobalTheory.HalfCocycle.char_symplOH_idem_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFramePropertiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceHermitianFrame_properties : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n), (∀ h : GA D S, h ∈ grpAt S (· = p.v) ↔ ∃ g, h = β.gl g) ∧ Function.Injective β.gl ∧ Continuous β.gl ∧ (∀ L : Lat S, IsSelfDualC S L → ∃ Λ : Submodule 𝒪[k] (n → k), Λ.IsLattice k ∧ β.IsLat L Λ ∧ ∀ g, InK S L (· = p.v) (β.gl g) ↔ g • Λ = Λ) ∧ (∀ (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsLattice k → ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v)) ∧ ∀ g, ∃ x : (AE D)ˣ, IsDetAt p.e S (β.gl g) x ∧ p.pr x = g.val.det := by
  first | exact @GlobalTheory.FrameAt.frame_facts | exact GlobalTheory.FrameAt.frame_facts | (intros; apply GlobalTheory.FrameAt.frame_facts <;> assumption)
end

