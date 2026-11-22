import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHInt
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoveringOfTransferenceVariant
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FamilyMomentBoundOfHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def rho0 : ℝ := Real.sqrt (finrank ℚ D.host.E) * D.host.rdE

theorem one_le_rdE : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow _ (by positivity)
  have h : (NumberField.discr D.host.E) ≠ 0 := NumberField.discr_ne_zero D.host.E
  have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h1
  simpa [Int.cast_abs] using h2

theorem one_le_rho0 : 1 ≤ rho0 D := by
  unfold rho0
  have h1 : (1 : ℝ) ≤ finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
  have h2 : 1 ≤ Real.sqrt (finrank ℚ D.host.E) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1
  nlinarith [one_le_rdE D]

theorem norm_embS_eq (τ : D.what₂.Tau) (x : D.host.E) :
    ‖embS D τ x‖ = (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ) x := rfl

def boxS : Set D.host.E := {x | ∀ τ, ‖embS D τ x‖ ≤ rho0 D}

theorem boxS_cover : ∀ x : D.host.E, ∃ a ∈ intS D, x + a ∈ boxS D := by
  intro x
  have hc : ∀ w : InfinitePlace D.host.E, w.IsComplex := by
    haveI := Formalism.MainNotions.BesselShellMomentBounds.instCM D
    exact fun w => NumberField.IsTotallyComplex.isComplex w
  obtain ⟨a, ha⟩ := Formalism.HermitianLatticeCounting.P.covering_of_transference D.host.E hc (fun w => - w.embedding x)
  refine ⟨(a : D.host.E), coe_mem_intS D a, fun τ => ?_⟩
  rw [norm_embS_eq, ← InfinitePlace.norm_embedding_eq]
  have := ha (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ)
  rw [map_add, show (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ).embedding x + (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ).embedding (a : D.host.E) =
    -(-(Formalism.MainNotions.BesselShellMomentBounds.plOf D τ).embedding x - (Formalism.MainNotions.BesselShellMomentBounds.plOf D τ).embedding (a : D.host.E)) by ring, norm_neg]
  exact this

theorem mem_boxS_one : (1 : D.host.E) ∈ boxS D := fun τ => by simpa using one_le_rho0 D

theorem mem_boxS_zero : (0 : D.host.E) ∈ boxS D := fun τ => by
  simpa using le_trans zero_le_one (one_le_rho0 D)

def liftO {N : ℕ} (n : Matrix (Fin N) (Fin N) D.host.E) (h : ∀ i j, n i j ∈ intS D) :
    Matrix (Fin N) (Fin N) (𝓞 D.host.E) :=
  fun i j => ⟨n i j, h i j⟩

theorem liftO_map {N : ℕ} (n : Matrix (Fin N) (Fin N) D.host.E) (h : ∀ i j, n i j ∈ intS D) :
    (liftO D n h).map (fun x => (x : D.host.E)) = n := by
  ext i j; rfl

theorem reduce_up {N : ℕ} (U : Matrix (Fin N) (Fin N) D.host.E) (hU : IsUpUni U) :
    ∃ B : Matrix (Fin N) (Fin N) (𝓞 D.host.E), (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = 1) ∧
      ∀ i j, (U * B.map (fun x => (x : D.host.E))) i j ∈ boxS D := by
  obtain ⟨n, hn1, hn0, hnO, hnF⟩ := Formalism.HermitianLatticeCounting.P.unitriangularReduction D.host.E (intS D) (boxS D) N U
    (boxS_cover D) (fun i => (hU i i).2 rfl) (fun i j h => (hU i j).1 h)
  refine ⟨liftO D n hnO, fun a b h => Subtype.ext (hn0 a b h), fun a => Subtype.ext (hn1 a), ?_⟩
  rw [liftO_map]
  have hnU : IsUpUni n := fun i j => ⟨hn0 i j, fun h => h ▸ hn1 i⟩
  have hP := rows_upUni_mul hU hnU
  intro i j
  rcases lt_trichotomy i j with h | h | h
  · exact hnF i j h
  · rw [(hP i j).2 h]; exact mem_boxS_one D
  · rw [(hP i j).1 h]; exact mem_boxS_zero D

theorem reduce_lo {N : ℕ} (L : Matrix (Fin N) (Fin N) D.host.E) (hL : IsLoUni L) :
    ∃ A : Matrix (Fin N) (Fin N) (𝓞 D.host.E), (∀ a b, a < b → A a b = 0) ∧ (∀ a, A a a = 1) ∧
      ∀ i j, (A.map (fun x => (x : D.host.E)) * L) i j ∈ boxS D := by
  have hU : IsUpUni L.transpose := fun i j => ⟨fun h => (hL j i).1 h, fun h => h ▸ (hL i i).2 rfl⟩
  obtain ⟨B, hB0, hB1, hBF⟩ := reduce_up D L.transpose hU
  refine ⟨B.transpose, fun a b h => hB0 b a h, fun a => hB1 a, fun i j => ?_⟩
  have e : (B.transpose.map (fun x => (x : D.host.E)) * L) =
      (L.transpose * B.map (fun x => (x : D.host.E))).transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map]
  rw [e]
  exact hBF j i

end Formalism.MainNotions.S.Pv.HH

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomMain
section
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open NumberField Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge Formalism.MainNotions.LowestKTypeMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scale_turn (D : D7) :
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) * -Complex.I = cOfDpsi ((kaS D : ℝ) : ℂ) := by
  unfold cOfDpsi kaS gg
  push_cast
  ring

def LowKOneAt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → IsHCParam lam' →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) lam' σ → ∀ S S' : Submodule ℂ H,
        IsKTypeOf (epsSH D.R) σ (lowK (epsSH D.R) lam') S → IsKTypeOf (epsSH D.R) σ (lowK (epsSH D.R) lam') S' → S = S'

theorem lowKOneAt_of_mult (h : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) :
    LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  fun _ τ lam' _ hHC H _ _ σ hDS S S' h1 h2 => h _ _ _ H σ hHC hDS S S' h1 h2

theorem momNorm'_of_at (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) (hQ : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv)
    (hLN : Formalism.MainNotions.S.Pv.QuotUniq.QuotLeftNorm) :
    MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ w w' θ W hW lam' hl A hA hT hT'
  have hW' := hW
  obtain ⟨hc1, -, hz, -, hTz, -, hG, hUW, -, -, -, hN, hq, -⟩ := hW'
  have hTpos : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hT
  have hA' := hA
  obtain ⟨hHC, hDSH, hB, -, hv0s, hv0ne, ⟨PS, hPS, hv0low⟩, hcN, hl2, -, -⟩ := hA'
  obtain ⟨-, hπiso, -⟩ := rp_repOfHC _ _ W.z _ W.Wp W.π hz hTpos hc1
  have hNt : Nontrivial W.Wp := by obtain ⟨g, -, hU⟩ := hc1; exact hU.1
  have hσ : IsURepOn (UH (Hpk D.R.k D.R.rS)) A.σ := urep_of_DS hDSH
  obtain ⟨hone, hmul, hiso⟩ := Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep hDSH
  have hS : IsHaarOn (Sset D.R.k D.R.rS W.z) (muS W.μW W.μN) := Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW
  set c1 : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) with hc1def
  have hB1 : IsBesselMapSm W.z (psi D.R.k D.R.rS W.z c1) A.σ W.π A.B := hB

  have hDSH2 := hDSH
  obtain ⟨PD, hPD, hDS'⟩ := hDSH2
  obtain ⟨hκ, hκe⟩ := cayley_change hPS hPD
  have hDS : IsDS (epsSH D.R) lam' (fun g => A.σ (PS⁻¹ * g * PS)) := by
    have := dsConjK_proved _ (epsSH D.R) lam' A.H _ _ hκ hDS'
    simp only [hκe] at this
    exact this
  obtain ⟨S0, hS0⟩ := hDS.2.2.2.2.2.1
  have hset : {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (PS⁻¹ * g * PS)) (lowK (epsSH D.R) lam') S} = {S0} := by
    ext S
    constructor
    · intro h; exact hM1 hH τ lam' hl hHC A.H _ hDS S S0 h hS0
    · intro h; rw [Set.mem_singleton_iff.1 h]; exact hS0
  have hv0S : A.v0 ∈ S0 := by
    have h := hv0low
    unfold lowKSub at h
    rw [hset, sSup_singleton] at h
    exact h
  obtain ⟨hfd, hst, hirr, ⟨w0, hw0S, hw0ne, hwt⟩, -⟩ := id hS0
  have := hfd
  have hsm : ∀ u ∈ S0, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u :=
    fun u hu => hSm _ _ (epsSH D.R) lam' A.H A.σ hHC hDSH u ⟨S0, hfd, hu, kstable_Hpk hPS hst⟩
  have hS0ne : S0 ≠ ⊥ := by
    intro hb; rw [hb] at hw0S; exact hw0ne (by simpa using hw0S)

  set m : ℝ := A.cN * (Module.finrank ℂ W.Wp : ℝ) with hm
  have hm0 : 0 < m := mul_pos hcN (by exact_mod_cast Module.finrank_pos)
  set a : ℝ := ‖A.v0‖ / Real.sqrt m with ha
  have hαsq : ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 = ((‖A.v0‖₊ : ℝ≥0∞)) ^ 2 * (ENNReal.ofReal m)⁻¹ := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq, ← ENNReal.ofReal_inv_of_pos hm0,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, ha, div_pow, Real.sq_sqrt hm0.le, div_eq_mul_inv]
  have hM0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.2 hm0).ne'
  have hMt : ENNReal.ofReal m ≠ ⊤ := ENNReal.ofReal_ne_top
  have hαt : ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hN' := hN
  rw [hN'] at hS hq

  have tw : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u → ∀ Φ0 : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞, Measurable Φ0 →
      ∫⁻ x, Φ0 (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) *
          (‖(a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) (A.σ (Matrix.of x) u))‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 *
          ∫⁻ x, Φ0 (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) * (‖A.B (A.σ (Matrix.of x) u)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS := by
    intro u hu Φ0 hΦ0
    rw [← twist_lintegral hLN hσ hz hTpos c1 hπiso hB1 (kapN D θ) hG hUW hS hq hu hΦ0, ← lintegral_const_mul' _ _ hαt]
    refine lintegral_congr fun x => ?_
    rw [nnnorm_smul, ENNReal.coe_mul, mul_pow]
    ring
  refine ⟨fun v => (a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) v), PS, w0, ?_, ?_, hPS, ?_, hw0ne, ?_⟩
  · rw [← scale_turn D]
    exact bessel_smul (bessel_twist A.σ hone hmul hiso hz hB1) _
  · intro v hv
    have h1 := tw v hv (fun _ => 1) measurable_const
    simp only [one_mul] at h1
    unfold l2SG
    rw [h1]
    have h2 := hBS hH τ w w' θ W hW lam' hl A hA hT v hv
    unfold l2SG at h2 hl2
    rw [hl2] at h2
    beta_reduce at h2
    rw [hαsq]
    calc (‖A.v0‖₊ : ℝ≥0∞) ^ 2 * (ENNReal.ofReal m)⁻¹ *
          ∫⁻ x, (‖A.B (A.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS
        = (ENNReal.ofReal m)⁻¹ * ((∫⁻ x, (‖A.B (A.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS) *
            (‖A.v0‖₊ : ℝ≥0∞) ^ 2) := by ring
      _ = (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal m * (‖v‖₊ : ℝ≥0∞) ^ 2) := by rw [h2]
      _ = (‖v‖₊ : ℝ≥0∞) ^ 2 := ENNReal.inv_mul_cancel_left hM0 hMt
  · have hl0 : l1 (lowK (epsSH D.R) lam') (lowK (epsSH D.R) lam') ≤ ((0 : ℕ) : ℝ) := by simp [l1]
    exact Submodule.subset_span ⟨_, _, _, hS0, hw0S, hwt, hl0, hl0⟩
  · intro F hF
    obtain ⟨CF, hCF⟩ := kinv_form hQ laLeftS_proved laRightK_proved hPS hσ hz hTpos c1 hπiso hB1 hG
      (by rw [hN'] at *; exact hS) (by rw [hN'] at *; exact hq) S0 hS0ne hst hirr hsm hF
    have eL : ∫⁻ x, F (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ENNReal.ofReal (‖A.v0‖ ^ 2) * CF := hCF A.v0 hv0S
    rw [eL]
    unfold Emom
    have ew := tw w0 (hsm w0 hw0S) F hF
    have e2 : ∫⁻ x, (fun g => F (fun i => lA D.R.k D.R.rS W.z g i)) (Matrix.of x) *
        (‖(a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) (A.σ (Matrix.of x) w0))‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 * (ENNReal.ofReal (‖w0‖ ^ 2) * CF) := by
      rw [ew, hCF w0 hw0S]
    erw [e2]
    rw [hl2]
    have hw0p : ENNReal.ofReal (‖w0‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have key : ∀ (M Wn V CF : ℝ≥0∞), M ≠ 0 → M ≠ ⊤ → Wn ≠ 0 → Wn ≠ ⊤ →
        V * CF = M * (Wn⁻¹ * (V * M⁻¹ * (Wn * CF))) := by
      intro M Wn V CF h1 h2 h3 h4
      calc V * CF = (M * M⁻¹) * ((Wn⁻¹ * Wn) * (V * CF)) := by
            rw [ENNReal.mul_inv_cancel h1 h2, ENNReal.inv_mul_cancel h3 h4]; simp
        _ = M * (Wn⁻¹ * (V * M⁻¹ * (Wn * CF))) := by ring
    rw [hαsq, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
    exact key _ _ _ _ hM0 hMt hw0p ENNReal.ofReal_ne_top

theorem momNorm'_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) (hQ : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv)
    (hLN : Formalism.MainNotions.S.Pv.QuotUniq.QuotLeftNorm) :
    MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of_at D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS (lowKOneAt_of_mult hM1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn) hSm hQ hLN

end Formalism.MainNotions.S.Pv.Mom
end
end

