import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryKeepsBaseLatticeOfSplitComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.SplitStab

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_iff (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R))
    (hS : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) R (c : E) ∈ S)
    (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r))
    (y : Fin m → E ⊗[F] R) :
    y ∈ Formalism.UG.latS (F := F) R S Λ ↔ (∀ j, y j ∈ S) ∧
      ∀ j : Fin m, j.1 + 1 = m → ∃ s ∈ S, y j = Formalism.UG.inclE (F := F) R (t : E) * s := by
  constructor
  · intro hy
    unfold Formalism.UG.latS at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [SetLike.mem_coe, hΛ] at hx
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · obtain ⟨r, hr, -⟩ := hx j
        simp only [hr]; exact hS r
      · obtain ⟨r, hr, hd⟩ := hx j
        obtain ⟨c, rfl⟩ := hd hj
        refine ⟨_, hS c, ?_⟩
        simp only [hr]; push_cast; rw [map_mul]
    | zero => exact ⟨fun j => zero_mem _, fun j _ => ⟨0, zero_mem _, by simp⟩⟩
    | add a b _ _ ha hb =>
      refine ⟨fun j => add_mem (ha.1 j) (hb.1 j), fun j hj => ?_⟩
      obtain ⟨s1, hs1, e1⟩ := ha.2 j hj
      obtain ⟨s2, hs2, e2⟩ := hb.2 j hj
      exact ⟨s1 + s2, add_mem hs1 hs2, by simp [Pi.add_apply, e1, e2, mul_add]⟩
    | smul a b _ hb =>
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
        exact mul_mem a.2 (hb.1 j)
      · obtain ⟨s, hs, e⟩ := hb.2 j hj
        refine ⟨(a : E ⊗[F] R) * s, mul_mem a.2 hs, ?_⟩
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, e]
        ring
  · rintro ⟨h1, h2⟩
    have key : ∀ (j : Fin m) (r : 𝓞 E), (j.1 + 1 = m → t ∣ r) → ∀ s ∈ S,
        Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) ∈ Formalism.UG.latS (F := F) R S Λ := by
      intro j r hr s hs
      have hx : (Pi.single j (r : E) : Fin m → E) ∈ Λ := by
        rw [hΛ]; intro i
        by_cases hij : i = j
        · subst hij; exact ⟨r, by simp, hr⟩
        · exact ⟨0, by simp [hij], fun _ => dvd_zero _⟩
      have : (Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) : Fin m → E ⊗[F] R) =
          (⟨s, hs⟩ : S) • (fun i => Formalism.UG.inclE (F := F) R ((Pi.single j (r : E) : Fin m → E) i)) := by
        ext i; by_cases hij : i = j
        · subst hij; simp [Subring.smul_def]
        · simp [hij, Subring.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j.1 + 1 = m
    · obtain ⟨s, hs, e⟩ := h2 j hj
      rw [e, mul_comm]; exact key j t (fun _ => dvd_refl _) s hs
    · simpa using key j 1 (fun h => absurd h hj) (y j) (h1 j)

end GlobalTheory.SplitStab

theorem GlobalTheory.SplitStab.stab_of_split_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k),
    (∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k]) →
    ∀ (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E)),
    (∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r)) →
    ∀ q : Unif k, valuation k (φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E))) = valuation k ((q.1 : 𝒪[k]) : k) →
    valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1 →
    ∀ M : GL (Fin m) (E ⊗[F] v.adicCompletion F), M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 →
    ∀ h h' : Matrix (Fin m) (Fin m) k, M.val.map φ = h → h * h' = 1 →
    (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], u r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s) ↔
      ((∀ r, (h *ᵥ u) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (h *ᵥ u) r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s)) →
    (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔ ∀ r, (h'ᵀ *ᵥ u) r ∈ 𝒪[k]) →
    M ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ) := by
  intro F E _ _ _ _ _ σ v k _ _ _ _ φ hS m t Λ hΛ q hq hq' M hM h h' hh hhh' hA hB
  have hSO : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (c : E) ∈
      Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
  have ht : (t : E) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero, map_zero] at hq
    have h1 : ((q.1 : 𝒪[k]) : k) = 0 := (valuation k).zero_iff.mp hq.symm
    exact q.2.ne_zero (by simpa using h1)
  have hint : ∀ x : k, x ∈ 𝒪[k] ↔ valuation k x ≤ 1 := fun x => Valuation.mem_integer_iff (valuation k) x
  set σ' := Formalism.UG.sigR σ (v.adicCompletion F) with hσ'
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι

  have hchar : ∀ y : Fin m → E ⊗[F] v.adicCompletion F,
      y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ ↔
      (((∀ r, (fun j => φ (y j)) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (fun j => φ (y j)) r0 = φ (ι (t : E)) * s) ∧
        ∀ r, (fun j => φ (σ' (y j))) r ∈ 𝒪[k]) := by
    intro y
    rw [GlobalTheory.SplitStab.mem_latS_iff (F := F) (v.adicCompletion F) _ hSO m t Λ hΛ y]
    simp only [hS]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun r => (h1 r).1, fun r0 hr0 => ?_⟩, fun r => (h1 r).2⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      exact ⟨φ s, hs.1, by rw [e, map_mul]⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun r => ⟨h1 r, h3 r⟩, fun r0 hr0 => ?_⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      have hu : ι (t : E) * ι ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      refine ⟨ι ((t : E)⁻¹) * y r0, ?_, ?_⟩
      · constructor
        · have hu' : φ (ι ((t : E)⁻¹)) * φ (ι (t : E)) = 1 := by rw [← map_mul, mul_comm, hu, map_one]
          rw [map_mul, show φ (y r0) = φ (ι (t : E)) * s from e, ← mul_assoc, hu', one_mul]
          exact hs
        · have hu' : φ (σ' (ι ((t : E)⁻¹))) * φ (σ' (ι (t : E))) = 1 := by
            rw [← map_mul, ← map_mul, mul_comm, hu, map_one, map_one]
          have hv : valuation k (φ (σ' (ι ((t : E)⁻¹)))) = 1 := by
            have := congrArg (valuation k) hu'
            rw [map_mul, hq', mul_one, map_one] at this
            exact this
          rw [map_mul, map_mul]
          exact mul_mem ((hint _).2 hv.le) (h3 r0)
      · rw [← mul_assoc, hu, one_mul]

  have hU : (M.val.map (φ.comp σ'))ᵀ * h = 1 := by
    have h0 : Formalism.UG.cT σ' (M : Matrix (Fin m) (Fin m) _) * 1 * (M : Matrix (Fin m) (Fin m) _) = 1 := hM
    rw [Matrix.mul_one] at h0
    have := congrArg (fun X => X.map φ) h0
    simp only [Formalism.UG.cT] at this
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [← hh]
    simpa [Matrix.transpose_map] using this
  have hh'h : h' * h = 1 := mul_eq_one_comm.mp hhh'
  have hσM : M.val.map (φ.comp σ') = h'ᵀ := by
    have : (M.val.map (φ.comp σ'))ᵀ = h' := by
      calc (M.val.map (φ.comp σ'))ᵀ = (M.val.map (φ.comp σ'))ᵀ * (h * h') := by rw [hhh', Matrix.mul_one]
        _ = h' := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [← this, Matrix.transpose_transpose]
  intro y
  rw [hchar y, hchar]
  have e1 : (fun j => φ (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j)) = h *ᵥ (fun j => φ (y j)) := by
    funext j; rw [RingHom.map_mulVec, hh]; rfl
  have e2 : (fun j => φ (σ' (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j))) = h'ᵀ *ᵥ (fun j => φ (σ' (y j))) := by
    funext j
    have := RingHom.map_mulVec (φ.comp σ') (M : Matrix (Fin m) (Fin m) _) y j
    rw [← hσM]
    exact this
  rw [e1, e2]
  exact and_congr (hA _) (hB _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExpStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCharacter_splitDegreeOne_place_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (Formalism.L2.Col.qOf PP).Prime → ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk → ∀ (a : D.host.E) (b : ℤ) (n : ℕ), Formalism.L2.Col.IntAt PP (D.host.xi0 * a - (b : D.host.E) / (Formalism.L2.Col.qOf PP : D.host.E) ^ n) → (ψk ((ofSplit q).pr a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (Formalism.L2.Col.qOf PP : ℂ) ^ n) := by
  first | exact @GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp | exact GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp | (intros; apply GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientExternalProductEqMulOrthogonalSumStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCoefficient_externalProduct_eq_mul_orthogonalSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B W H : HSp D) (o : OrthDec B W H) (χA χW : (AE D)ˣ →* Circle) (omB : WRep A B) (omW : WRep A W) (omH : WRep A H), IsWeilDatumO ψ A B χA χW omB → IsWeilDatumO ψ A W χA χW omW → IsWeilDatumO ψ A H χA 1 omH → ∀ νB 𝓕B νW 𝓕W νH 𝓕H, IsCovolOne (ratL B A) νB 𝓕B → IsCovolOne (ratL W A) νW 𝓕W → IsCovolOne (ratL H A) νH 𝓕H → ∀ Φ Φ', IsThetaFunO ψ A W Φ → IsThetaFunO ψ A H Φ' → ∀ g, wcoef omB νB 𝓕B (o.boxT A Φ Φ') (o.boxT A Φ Φ') g = wcoef omW νW 𝓕W Φ Φ g * wcoef omH νH 𝓕H Φ' Φ' g := by
  first | exact @GlobalTheory.Core.Rk.BoxCoef.wcoef_boxT | exact GlobalTheory.Core.Rk.BoxCoef.wcoef_boxT | (intros; apply GlobalTheory.Core.Rk.BoxCoef.wcoef_boxT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientSplitsLocalFactorTwistPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistCoef

theorem conj_unit {u : ℂˣ} (h : ‖(u : ℂ)‖ = 1) : conj (u : ℂ) = ((u⁻¹ : ℂˣ) : ℂ) := by
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem datum_inv_conj (μ : kˣ →* ℂˣ) (hμ : ∀ d, ‖(μ d : ℂ)‖ = 1) (z : Matrix (A ⊕ D) (A ⊕ D') k) :
    datum μ⁻¹ z = conj (datum μ z) := by
  unfold datum
  split_ifs with h
  · have h1 : ‖(((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      simp [Units.val_inv_eq_inv_val, norm_inv, hμ]
    rw [conj_unit h1]
    simp
  · simp

theorem om_datum_inv_conj (μ : kˣ →* ℂˣ) (hμ : ∀ d, ‖(μ d : ℂ)‖ = 1) (y : GL (A ⊕ D') k)
    (z : Matrix (A ⊕ D) (A ⊕ D') k) :
    GlobalTheory.SplitWeil.om μ⁻¹ y (1 : GL (A ⊕ D) k) (datum μ⁻¹) z =
      conj (GlobalTheory.SplitWeil.om μ y (1 : GL (A ⊕ D) k) (datum μ) z) := by
  unfold GlobalTheory.SplitWeil.om
  rw [datum_inv_conj μ hμ]
  simp only [map_mul, Complex.conj_ofReal, conj_unit (hμ _), MonoidHom.inv_apply]
  simp

end Local

end GlobalTheory.TwistCoef

namespace GlobalTheory.TwistCoef

section IP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] {m n : Type} [Fintype m] [Fintype n]

theorem ip_conj (ν : Measure k) (F G : Matrix m n k → ℂ) :
    GlobalTheory.SplitWeil.ip ν (fun z => conj (F z)) (fun z => conj (G z)) = conj (GlobalTheory.SplitWeil.ip ν F G) := by
  unfold GlobalTheory.SplitWeil.ip
  rw [← integral_conj]
  congr 1
  funext z
  simp [map_mul]

end IP

theorem coef_split : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ m X, IsCovolOne (ratL s'.V s.V) m X → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s k φ ι → ∀ μT : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ cf : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ, (∀ g, cf g = GlobalTheory.SplitWeil.ip ν (GlobalTheory.SplitWeil.om μT g (1 : GL (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fv D.host.F v)) (datum μT)) (datum μT)) → ∀ P (x : GA D s.V), gAt s.V (.inl v) x = 1 → ∀ y, coefW p.ω m X (p.pt P) (x * ι y) * conj (cf 1) = coefW p.ω m X (p.pt P) x * conj (cf y) := by
  intro D hgap c w hw k hk s s' hs hs' p hp m X hX PP hPP v φ hφ ι hι μT hμT _ _ ν hν cf hcf P x hx
  obtain ⟨-, hch'⟩ := GlobalTheory.TwistChart.charts_at_twist D c w hw (k + 1) hk s' hs' PP hPP
  obtain ⟨⟨e, he⟩, -, ⟨ι', hι'⟩, hμ⟩ := hch' v φ hφ
  obtain ⟨μS, -, hμS⟩ := hμ (c.chS (k + 1))
  obtain ⟨U, hU1, -⟩ := GlobalTheory.TwistChart.unit_section φ he
  have hunit : ∀ d, ‖(μT d : ℂ)‖ = 1 := fun d => by
    rw [hμT (U d) d ⟨e, he, (hU1 d).1, (hU1 d).2⟩]
    exact Circle.norm_coe _
  have hlift : LiftsChar φ PP μT (w.ξ PP) :=
    (GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw k hk.le s hs PP hPP v φ hφ).2.2.2.1 k hk μT (Or.inr hμT)
  obtain ⟨hW, hΦ, T, hT0, -, hTω, hC⟩ :=
    GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hgap c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT μT hμS hμT hlift P m X hX
  obtain ⟨C, hC⟩ := hC ν hν x hx
  have key : ∀ y, coefW p.ω m X (p.pt P) (x * ι y) = C * conj (cf y) := by
    intro y
    have h1 : p.ω (x * ι y, 1) = p.ω (x, 1) * p.ω (ι y, ι' 1) := by
      rw [map_one, ← map_mul]
      simp
    unfold coefW
    rw [h1, ← hT0]
    simp only [Module.End.mul_apply]
    rw [hTω, hC, hcf, ← ip_conj]
    congr 2
    · funext z
      simp [GlobalTheory.ParHecke.omTwo, om_datum_inv_conj _ hunit]
    · funext z
      exact datum_inv_conj _ hunit z
  intro y
  have h0 := key 1
  rw [map_one, mul_one] at h0
  rw [key y, h0]
  ring

end GlobalTheory.TwistCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumProductCompatibility
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrKernel

variable {D : D7}

theorem continuous_ofAdj (S T : HSp D) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T) := by
  have h : Continuous fun z : Mx D S.rank T.rank => giA T ⬝ (adj z ⬝ gA S) :=
    continuous_const.matrix_mul
      ((GlobalTheory.MixModel.continuous_adj (D := D) (m := S.rank) (n := T.rank)).matrix_mul continuous_const)
  exact h.const_smul (incA D (-D.host.xi0⁻¹))

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (S : HSp D) : Continuous (l.κ S) :=
  (continuous_ofAdj B.L S).comp (continuous_const.matrix_mul continuous_id)

theorem integrable_of_cont_bdd {m n : ℕ} (μ : Measure (Mx D m n)) [IsFiniteMeasure μ] (f : Mx D m n → ℂ)
    (hc : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem symm_resS_symm {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply, add_comm]; rfl

theorem symm_resT_symm {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u : WO S B) (v : WO S A) :
    (o.symm.resT S).symm (u, v) = (o.resT S).symm (v, u) := by
  rw [OrthDec.resT_symm_apply, OrthDec.resT_symm_apply, add_comm]; rfl

theorem kernel_doubleStep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → ∀ h₀ h₁ h₂, ∫ w in vL.𝓕, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) * s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) ∂vL.μ = omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) 0 := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' hV hW hoa hoz hob hoz' Ξ₁ Ξ₂ hΞ₁ hΞ₂ h₀ h₁ h₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  have TS := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hstd B.V₀ B.A B.L B.o J.W₀
  have TT := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hstd B'.V₀ B'.A B'.L B'.o J.W₀
  have hw₁ : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s₁.χW s₁.om₀ := hV ▸ s₁.weil₀
  have hw₂ : IsWeilDatumO ψ J.W₀ B'.V₀ s₂.χV (χA' * χz) s₂.om₀ := hW ▸ s₂.weil₀
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (WO J.W₀ B'.L) := ⟨rfl⟩
  haveI : BorelSpace (WO B.L J.W₀) := ⟨rfl⟩

  have hS₁ : ∀ u, IsThetaFunO ψ B.L J.W₀ fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z)) := (TS.slice_theta Ξ₁ hΞ₁).2
  have hS₂ : ∀ v, IsThetaFunO ψ J.W₀ B'.L fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) := (TT.slice_theta Ξ₂ hΞ₂).2

  obtain ⟨Hf, hHf⟩ : ∃ Hf : WO B.A J.W₀ → WO B.L J.W₀ → ℂ,
      Hf = fun u z => omz (1, h₁) (fun z' => Ξ₁ ((B.o.resS J.W₀).symm (u, z'))) z := ⟨_, rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ Gf : WO J.W₀ B'.A → WO J.W₀ B'.L → ℂ,
      Gf = fun v w => omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) w := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁d⟩ : ∃ F₁ : WO B.V₀ J.W₀ → ℂ, F₁ = fun x => Hf (B.o.resS J.W₀ x).1 (B.o.resS J.W₀ x).2 := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂d⟩ : ∃ F₂ : WO J.W₀ B'.V₀ → ℂ, F₂ = fun x => Gf (B'.o.resT J.W₀ x).1 (B'.o.resT J.W₀ x).2 :=
    ⟨_, rfl⟩
  have hF₁s : ∀ u z, F₁ ((B.o.resS J.W₀).symm (u, z)) = Hf u z := by
    intro u z; rw [hF₁d]; simp only [AddEquiv.apply_symm_apply]
  have hF₂s : ∀ v w, F₂ ((B'.o.resT J.W₀).symm (v, w)) = Gf v w := by
    intro v w; rw [hF₂d]; simp only [AddEquiv.apply_symm_apply]

  have hF₁ : IsThetaFunO ψ B.V₀ J.W₀ F₁ := by
    have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.L B.A J.W₀ B.o.symm χz s₁.χW omz hoz Ξ₁ hΞ₁ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (1, h₁)).1
    have e : F₁ = fun x => omz (1, h₁) (fun u => Ξ₁ ((B.o.symm.resS J.W₀).symm (u, (B.o.symm.resS J.W₀ x).2)))
        (B.o.symm.resS J.W₀ x).1 := by
      funext x; rw [hF₁d, hHf]; simp only [symm_resS_symm]; rfl
    rw [e]; exact h
  have hF₂ : IsThetaFunO ψ J.W₀ B'.V₀ F₂ := by
    have h := (GlobalTheory.T.weilRep_commutes_slice_superposition_target D ψ B'.V₀ B'.L B'.A J.W₀ B'.o.symm s₂.χV χz omz' hoz' Ξ₂ hΞ₂ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (h₁, 1)).1
    have e : F₂ = fun x => omz' (h₁, 1) (fun u => Ξ₂ ((B'.o.symm.resT J.W₀).symm (u, (B'.o.symm.resT J.W₀ x).2)))
        (B'.o.symm.resT J.W₀ x).1 := by
      funext x; rw [hF₂d, hGf]; simp only [symm_resT_symm]; rfl
    rw [e]; exact h

  obtain ⟨b₁, hb₁d⟩ : ∃ b₁ : WO J.W₀ B'.L → ℂ, b₁ = fun w => oma (h₀, h₁) (fun u => Hf u (l.κ J.W₀ w)) 0 := ⟨_, rfl⟩
  have hA : ∀ w, s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = b₁ w := by
    intro w
    rw [(TS.om_slice χA χz s₁.χW s₁.om₀ oma omz hw₁ hoa hoz h₀ 1 h₁ Ξ₁ hΞ₁ (l.κ J.W₀ w)).2 0, hb₁d, hHf]
  have hB : ∀ w, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) = omb (h₁, h₂) (fun v => Gf v w) 0 := by
    intro w
    rw [(TT.om_slice s₂.χV χA' χz s₂.om₀ omb omz' hw₂ hob hoz' h₁ h₂ 1 Ξ₂ hΞ₂ w).2 0, hGf]

  have hb₁int : Integrable b₁ (vL.μ.restrict vL.𝓕) := by
    have th := hw₁.om_pres (B.o.emb (h₀, 1), h₁) Ξ₁ hΞ₁
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded B.V₀ J.W₀ ψ hstd _ th
    have e : b₁ = fun w => s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) :=
      funext fun w => (hA w).symm
    rw [e]
    exact integrable_of_cont_bdd _ _ (th.cont.comp ((B.o.continuous_resS_symm J.W₀).comp
      (continuous_const.prodMk (continuous_kappa l J.W₀)))) ⟨C, fun w => hC _⟩
  have hGint : ∀ v, Integrable (Gf v) (vL.μ.restrict vL.𝓕) := by
    intro v
    have th := hoz'.om_pres (h₁, 1) _ (hS₂ v)
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded J.W₀ B'.L ψ hstd _ th
    have e : Gf v = omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) := by rw [hGf]
    rw [e]
    exact integrable_of_cont_bdd _ _ th.cont ⟨C, hC⟩

  have hLine : ∀ u v, ∫ w, Gf v w * Hf u (l.κ J.W₀ w) ∂(vL.μ.restrict vL.𝓕) = contr l J.W₀ vL Ξ₁ Ξ₂ u v := by
    intro u v
    have hrank : B.L.rank = B'.L.rank := B.line.1.trans B'.line.1.symm
    have hgram := (GlobalTheory.T.besselLineLink_gram_similitude_bijective D (σ + 1) B B'.L B'.ζ B'.line l).1
    have CL := GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine D ψ B.L B'.L J.W₀ l.τ hrank hgram χz s₁.χW s₂.χV omz omz' hoz hoz'
      (fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z))) (hS₁ u)
    have CU := GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ J.W₀ B'.L s₂.χV χz omz' hoz' vL (h₁, 1) _ _ (hS₂ v) CL.1
    rw [CL.2 h₁] at CU
    simp only [thPair, star_star] at CU
    rw [hGf, hHf]
    exact CU

  have hInner : ∀ v, oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 =
      ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := by
    intro v
    have e : (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) =
        fun u => ∫ w, Gf v w * F₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w)) ∂(vL.μ.restrict vL.𝓕) := by
      funext u; rw [← hLine u v]; simp only [hF₁s]
    rw [e, (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa F₁ hF₁ (WO J.W₀ B'.L) (vL.μ.restrict vL.𝓕)
      (l.κ J.W₀) (Gf v) (continuous_kappa l J.W₀).measurable (hGint v) (h₀, h₁)).2 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hF₁s, hF₂s, id, hb₁d]
    exact mul_comm _ _
  have hOuter := (GlobalTheory.T.weilRep_commutes_slice_superposition_target D ψ B'.V₀ B'.A B'.L J.W₀ B'.o s₂.χV χA' omb hob F₂ hF₂ (WO J.W₀ B'.L)
    (vL.μ.restrict vL.𝓕) id b₁ measurable_id hb₁int (h₁, h₂)).2 0
  have e : (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) =
      fun v => ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := funext hInner
  rw [e, hOuter]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hA, hB, hF₂s, id]
  exact mul_comm _ _

end GlobalTheory.ContrKernel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatumStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ g : G D A.rank, mat g = blk4 0 1 (-1) 0 → ∀ Φ x, (omS g Φ).1 x = ∫ y, Φ.1 y * shift ψ lam (trA (Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  first | exact @GlobalTheory.StdUnn.WeylStd.main | exact GlobalTheory.StdUnn.WeylStd.main | (intros; apply GlobalTheory.StdUnn.WeylStd.main <;> assumption)
end

