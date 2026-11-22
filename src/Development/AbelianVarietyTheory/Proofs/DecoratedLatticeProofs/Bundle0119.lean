import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdeleComponentAtFinitePlaceIntegralMemLocalTensoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  first | exact @GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | exact GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | (intros; apply GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixRealSize_le_realSymplecticPairing_sum : ∀ (D : D7) (θ : InfFam D) (T : HSp D) (ρ : ℕ), ∃ (k : ℕ) (τs : Fin k → D.what₂.Tau) (zs : Fin k → Matrix (Fin T.rank) (Fin ρ) ℂ) (C : ℝ), ∀ x : Mx D T.rank ρ, realSize θ x ≤ C * ∑ i, |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
  first | exact @GlobalTheory.RealPairBound.realSize_le_pairing | exact GlobalTheory.RealPairBound.realSize_le_pairing | (intros; apply GlobalTheory.RealPairBound.realSize_le_pairing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → IsClosed {x | InBox K x} ∧ Continuous (realSize θ : Mx D m n → ℝ) ∧ (∀ N, Measurable (maj θ K N)) ∧ ∀ R : ℝ, IsCompact {x | InBox K x ∧ realSize θ x ≤ R}) ∧ ∀ (m n k : ℕ) (x : Matrix (Fin m) (Fin n) D.host.E), LinearIndependent D.host.E x.transpose → ∀ K : Set (Mx D m k), IsCompact K → ∃ K' : Set (Mx D n k), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ u : Mx D n k, maj θ K N ((rat x : Mx D m n) ⬝ u) ≤ C * maj θ K' N u := by
  first | exact @GlobalTheory.Unf.maj_measurable_rat | exact GlobalTheory.Unf.maj_measurable_rat | (intros; apply GlobalTheory.Unf.maj_measurable_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocBesChar
open GlobalTheory.LocFrame (hA hQ besselAuxiliaryVectors IsHermitianAuxiliaryVectorSystem ent colN)
open Finset (range)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem psiE_ι {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (y : k) :
    psiE ψ (p.ι y) = ψk (y / p.xi) := by
  rw [h]
  congr 1
  have : p.ι y = p.ι (p.π (incA D D.host.xi0 * p.ι (y / p.xi))) := by
    rw [RingHom.map_mul, p.π_ι]
    change _ = p.ι (p.xi * _)
    rw [mul_div_cancel₀ _ (Witness.xi_ne p)]
  rw [this, p.ι_π, mul_left_comm, Witness.e_ι]

theorem psiE_cA (ψ : AddChar (AF D.host.F) ℂ) (x : AE D) : psiE ψ (cA D x) = psiE ψ x := by
  rw [psiE, psiE, GlobalTheory.DualPairCheck.trace_cA]

theorem psiE_supp {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) {u : AE D}
    (hu : (p.e + cA D p.e) * u = u) : psiE ψ u = ψk ((p.π u + p.π (cA D u)) / p.xi) := by
  have e : u = p.ι (p.π u) + cA D (p.ι (p.π (cA D u))) := by
    rw [p.ι_π, p.ι_π, RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA, ← add_mul, hu]
  conv_lhs => rw [e]
  rw [psiE_add, psiE_cA, psiE_ι p h, psiE_ι p h, add_div, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem hA_supp {V : HSp D} {e : AE D} {g : GA D V} (hg : SuppAt e V g) {x y : Fin V.rank → D.host.E} (h : hQ V x y = 0) :
    (e + cA D e) * hA V g x y = hA V g x y := by
  have e1 : hA V g x y = (ratV (star y) ᵥ* gA V) ⬝ᵥ (mt V g - 1) *ᵥ ratV x := by
    rw [← dotProduct_mulVec, mulVec_mulVec, mul_sub, sub_mulVec, dotProduct_sub, ← mt_one V, ← hA, ← hA,
      ← GlobalTheory.LocFrame.incA_hQ, h, map_zero, sub_zero]
  rw [e1]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hg i j
  linear_combination ((ratV (star y) ᵥ* gA V) i * ratV x j) * this

theorem π_hA (V : HSp D) (g : GA D V) (x y : Fin V.rank → D.host.E) :
    p.π (hA V g x y) = (Witness.prH p ∘ (star y ᵥ* V.gram)) ⬝ᵥ (mt V g).map p.π *ᵥ (Witness.prH p ∘ x) := by
  have h1 : ratV (star y) ᵥ* gA V = ratV (star y ᵥ* V.gram) := funext fun i => (RingHom.map_vecMul (incA D) _ _ i).symm
  rw [hA, ← mulVec_mulVec, dotProduct_mulVec, h1, GlobalTheory.LocFrame.map_dot]
  rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem map_mt_inv {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) {g : GA D V} {q : GL Y k}
    (h : (mt V g).map p.π = F.β * q.val * F.γ) : (mt V g⁻¹).map p.π = F.β * (q⁻¹).val * F.γ := by
  have h1 : (mt V g⁻¹).map p.π * (mt V g).map p.π = 1 := by
    rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * q.val * F.γ) * (F.β * (q⁻¹).val * F.γ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc F.β (q⁻¹).val, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  rw [← Matrix.mul_one ((mt V g⁻¹).map p.π), ← h2, ← Matrix.mul_assoc, ← h, h1, Matrix.one_mul]

theorem col_ne_zero {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (j : Y) {t : k} {x : Fin N → k}
    (h : ∀ r, F.β r j = t * x r) : t ≠ 0 := fun e => by
  have h1 := congrFun (congrFun F.γβ j) j
  simp [Matrix.mul_apply, h, e] at h1

section Coef
variable {V X : HSp D} {jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E} {a : ℕ → Fin V.rank → D.host.E}
  {κ : ℕ → D.host.E} {t : ℕ → k} (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) {M : Matrix (Fin X.rank) n k} {F : Frame k V.rank (n ⊕ Fin c)}
  (hl : ∀ r b, F.β r (Sum.inl b) = (jX.map p.pr * M) r b) (hr : ∀ (i : Fin c) r, F.β r (Sum.inr i) = t i * p.pr (a i r))
include H hl hr

theorem π_coef {g : GA D V} {q : GL (n ⊕ Fin c) k} (h : (mt V g).map p.π = F.β * q.val * F.γ) (i j : Fin c) :
    t j * p.π (hA V g (a j) (a (c - 1 - i))) = p.pr (κ i) * t i * q.val (.inr i) (.inr j) := by
  set u := Witness.prH p ∘ (star (a (c - 1 - i)) ᵥ* V.gram) with hu
  have e1 : t j • (Witness.prH p ∘ a j) = F.β *ᵥ Pi.single (.inr j) 1 := by
    rw [mulVec_single_one]
    exact funext fun r => (hr j r).symm
  have e2 (b : n) : (u ᵥ* F.β) (.inl b) = 0 := by
    have : (u ᵥ* (jX.map (Witness.prH p) * M)) b = 0 := by
      rw [← vecMul_vecMul, show u ᵥ* jX.map (Witness.prH p) = 0 from funext fun s => by
        rw [hu, ← RingHom.map_vecMul, H.perp _ (by omega), Pi.zero_apply, map_zero, Pi.zero_apply], zero_vecMul, Pi.zero_apply]
    rw [← this]
    change ∑ r, u r * F.β r (.inl b) = ∑ r, u r * (jX.map p.pr * M) r b
    exact Finset.sum_congr rfl fun r _ => congrArg (u r * ·) (hl r b)
  have e3 (l : Fin c) : (u ᵥ* F.β) (.inr l) = if l = i then p.pr (κ i) * t i else 0 := by
    have h3 : (u ᵥ* F.β) (.inr l) = t l * Witness.prH p (hQ V (a l) (a (c - 1 - i))) := by
      rw [hQ, dotProduct_mulVec, RingHom.map_dotProduct, dotProduct, Finset.mul_sum]
      change ∑ r, u r * F.β r (.inr l) = _
      refine Finset.sum_congr rfl fun r _ => ?_
      change u r * F.β r (.inr l) = t l * (u r * p.pr (a l r))
      rw [hr]; ring
    rw [h3, H.pair i i.2 l l.2]
    by_cases e : l = i
    · subst e; rw [if_pos rfl, if_pos rfl, mul_comm]; rfl
    · rw [if_neg (fun e' => e (Fin.ext e')), if_neg e, map_zero, mul_zero]
  rw [π_hA, h, ← smul_eq_mul, ← dotProduct_smul, ← mulVec_smul, e1, mulVec_mulVec, Matrix.mul_assoc, F.γβ, Matrix.mul_one,
    ← mulVec_mulVec, dotProduct_mulVec, mulVec_single_one, dotProduct, Fintype.sum_sum_type]
  simp [← hu, e2, e3]

theorem π_simple {g : GA D V} {q : GL (n ⊕ Fin c) k} (h : (mt V g).map p.π = F.β * q.val * F.γ) {i : ℕ} (hi : i + 1 < c)
    {x : k} (hx : p.pr (κ i) * t i = x * t (i + 1)) : p.π (hA V g (a (i + 1)) (a (c - 1 - i))) = x * ent q i := by
  have h1 := π_coef p H hl hr h ⟨i, by omega⟩ ⟨i + 1, hi⟩
  have h2 : t (i + 1) ≠ 0 := col_ne_zero F _ (hr ⟨i + 1, hi⟩)
  rw [ent, dif_pos hi]
  refine mul_left_cancel₀ h2 (h1.trans ?_)
  simp only [hx]
  ring

end Coef

def scal {ρ : ℕ} (B : BesLev D ρ) (s : k) (i : ℕ) : k :=
  if i < ρ then s * p.xi ^ (ρ - i) else if i = ρ then s else s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - i))

theorem scal_lo {ρ : ℕ} (B : BesLev D ρ) (s : k) {i : ℕ} (hi : i < ρ) :
    p.pr (if i = ρ then hQ B.L B.ζ B.ζ else 1) * scal p B s i = p.xi * scal p B s (i + 1) := by
  rw [if_neg hi.ne, show p.pr 1 = 1 from (Witness.prH p).map_one, scal, scal, if_pos hi]
  split_ifs with h1 h2
  · rw [show ρ - i = ρ - (i + 1) + 1 by omega]; ring
  · rw [show ρ - i = 1 by omega]; ring
  · omega

theorem scal_hi {ρ : ℕ} (B : BesLev D ρ) (s : k) {i : ℕ} (hi : ρ ≤ i) (hi' : i < 2 * ρ) :
    p.pr (if i = ρ then hQ B.L B.ζ B.ζ else 1) * scal p B s i = -p.xi * scal p B s (i + 1) := by
  have hx := Witness.xi_ne p
  rw [scal, scal, if_neg (show ¬ i < ρ by omega), if_neg (show ¬ i + 1 < ρ by omega), if_neg (show ¬ i + 1 = ρ by omega)]
  split_ifs with h1
  · rw [show ρ - 1 - (2 * ρ - (i + 1)) = 0 by omega]
    change p.hz B * s = _
    field_simp
  · rw [show ρ - 1 - (2 * ρ - (i + 1)) = ρ - 1 - (2 * ρ - i) + 1 by omega, show p.pr 1 = 1 from (Witness.prH p).map_one, pow_succ]
    field_simp

theorem col_eq {ρ : ℕ} {B : BesLev D ρ} {s : k} {FA : Frame k B.A.rank n} {FV : Frame k B.V.rank (n ⊕ Fin c)}
    (h : p.IsBesFrame B s FA FV) (i : Fin c) (r) :
    FV.β r (Sum.inr i) = scal p B s i * p.pr (besselAuxiliaryVectors B.d (vecB B.o B.ζ) i r) := by
  obtain ⟨hc, -, h1, h2, h3⟩ := h
  have := i.2
  unfold scal besselAuxiliaryVectors
  split_ifs with e1 e2
  · rw [h1 ⟨i, e1⟩ i rfl r, colN, dif_pos e1]
  · exact h2 i e2 r
  · have e3 : 2 * ρ - i < ρ := by omega
    rw [h3 ⟨2 * ρ - i, e3⟩ i (by simp only; omega) r, colN, dif_pos e3]

theorem psiBes_isLoc : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → psiBes ψ B.d 1 (vecB B.o B.ζ) g = (ψk (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  intro D k _ _ _ _ p ψ ψk hψ σ B s n _ _ c FA FV hF g q hq hg
  obtain rfl := hF.1
  have H := GlobalTheory.LocFrame.isHermitianAuxiliaryVectorSystem_besselVectors B.d B.o B.line
  have hx := Witness.xi_ne p
  rw [psiBes, map_one, one_mul, GlobalTheory.LocFrame.simpleSum_eq_sum_hA, psiE_supp p hψ, GlobalTheory.LocFrame.simpleSum_eq_sum_ent]
  · congr 2
    rw [div_eq_iff hx, show 2 * σ + 1 - 1 = σ + σ by omega, Finset.sum_range_add, add_mul, map_sum, map_sum, map_sum,
      Finset.sum_mul, ← Finset.sum_range_reflect (fun i => ent q (σ + i)), Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have h1 := π_simple p H hF.2.1 (col_eq p hF) hg.2 (i := i) (by omega) (scal_lo p B s hi')
      rw [show σ + σ - i = 2 * σ + 1 - 1 - i by omega, h1, mul_comm]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have h1 := π_simple p H hF.2.1 (col_eq p hF) (map_mt_inv p FV hg.2) (i := σ + (σ - 1 - i)) (by omega)
        (scal_hi p B s (by omega) (by omega))
      rw [show 2 * σ + 1 - 1 - (σ + (σ - 1 - i)) = i + 1 by omega, show σ + (σ - 1 - i) + 1 = σ + σ - i by omega,
        GlobalTheory.LocFrame.ent_inv hq] at h1
      rw [GlobalTheory.LocFrame.cA_hA, h1]
      ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => hA_supp hg.1 ?_
    have hi' := Finset.mem_range.1 hi
    rw [H.pair i (by omega) _ (by omega), if_neg (by omega)]

end GlobalTheory.LocBesChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.DoubleStep

theorem hand0_smul_snd_of_bessel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) (c : ℂ), hand0 s₁ s₂ l vL φ Ξ₁ (c • Ξ₂) = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ := by
  intro D ψ σ B J B' s₁ s₂ l vL φ Ξ₁ Ξ₂ c
  funext h₁
  simp only [hand0, handFB, pairKer, contractT, thPair, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
    MeasureTheory.integral_const_mul]

end GlobalTheory.DoubleStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepUnfoldingOfUnfoldingsAndLink
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem om_comp_one {D : D7} {S T : HSp D} (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (1, h) (om (g, 1) f) = om (g, h) f := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  ext <;> simp

theorem rTrans_liftS {D : D7} {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T))
    (G : GA D T → ℂ) (f : WO S T → ℂ) (g : GA D S) :
    rTrans g (liftS om ν 𝓕 G f) = liftS om ν 𝓕 G (om (g, 1) f) := by
  funext x
  simp only [rTrans, liftS_apply]
  congr 1
  funext h
  have e : ((x, h) : GA D S × GA D T) * (g, 1) = (x * g, h) := by simp
  rw [← e, map_mul, Module.End.mul_apply]

theorem doubleStep_of_laws : ∀ D : D7, UnfBF D → UnfFB D → LinkLaw D → HandFBLaw D → FlatLaw D → DoubleStep D := by
  intro D hBF hFB hLink hHand hFlat ψ σ B J B' s₁ s₂ l vL Φ₁ Φ₂ φ G g hΦ₁ hΦ₂ hφ hG hG'
  have hfl := GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hFlat ψ
  have hΞ₁ : ∀ h₁, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h₁) Φ₁)) := fun h₁ =>
    hfl.1 _ B J s₁ _ (s₁.weil.om_pres _ _ hΦ₁)
  have hΞ₂ : ∀ h₁ h₂, IsThetaFunO ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := fun h₁ h₂ =>
    hfl.2 _ J B' s₂ _ (s₂.weil.om_pres _ _ hΦ₂)
  have hL := fun h₁ => hLink ψ (σ + 1) B J s₁ B'.L B'.ζ B'.line l φ _ hφ (hΞ₁ h₁)
  refine ⟨fun h₁ h₂ => hHand ψ σ J B' s₂ vL _ _ (hL h₁).1 (hΞ₂ h₁ h₂), ?_⟩
  refine ⟨fun h₁ => J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)), ?_, ?_⟩
  · have := hBF ψ (σ + 1) B J s₁ φ (s₂.lift G Φ₂) (s₁.om (g, 1) Φ₁) hφ hG' (s₁.weil.om_pres _ _ hΦ₁)
    simp only [om_comp_one] at this
    convert this using 2
    exact rTrans_liftS _ _ _ _ _ _
  · intro h₁
    have := hFB ψ σ J B' s₂ vL _ G (s₂.om (h₁, 1) Φ₂) (hL h₁).1 hG (s₂.weil.om_pres _ _ hΦ₂)
    simp only [om_comp_one] at this
    convert this using 1
    · rfl
    · show J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)) = _
      rw [(hL h₁).2]
      congr 1
      exact rTrans_liftS _ _ _ _ _ _

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiNormalFramesExistSplitPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

theorem Frame.exists_of_vecMul {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (β : Matrix (Fin N) Y k) (hc : Fintype.card Y = N) (h : ∀ v, v ᵥ* β = 0 → v = 0) :
    ∃ F : GlobalTheory.LocMod.Frame k N Y, F.β = β := by
  obtain ⟨g, hg⟩ := β.vecMulLinear.exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 h)
  have h1 : β * LinearMap.toMatrixRight' g = 1 := by
    ext i j
    have := congrFun (LinearMap.congr_fun hg (Pi.single i 1)) j
    have h2 : ∀ x, g x = x ᵥ* LinearMap.toMatrixRight' g := fun x => by
      conv_lhs => rw [← LinearMap.toMatrixRight'.symm_apply_apply g]
      rfl
    rw [LinearMap.comp_apply, h2, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.single_one_vecMul] at this
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using this
  exact ⟨⟨β, _, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hc])).1 h1⟩, rfl⟩

theorem Frame.card_eq {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k N Y) : Fintype.card Y = N := by
  have h1 := Matrix.rank_mul_le_left F.β F.γ
  have h2 := Matrix.rank_mul_le_left F.γ F.β
  rw [F.βγ, Matrix.rank_one] at h1
  rw [F.γβ, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width F.β
  have h4 := Matrix.rank_le_card_width F.γ
  simp only [Fintype.card_fin] at h1 h4
  omega

theorem Frame.eq_zero {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k N Y) {v : Fin N → k} (h : v ᵥ* F.β = 0) : v = 0 := by
  rw [← Matrix.vecMul_one v, ← F.βγ, ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

theorem hyp_eq_zero {D : D7} {k : Type} [Field k] (f : D.host.E →+* k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {v : Fin S.rank → k} (h1 : v ᵥ* d.e.map f = 0) (h2 : v ᵥ* d.i₀.map f = 0) (h3 : v ᵥ* d.e'.map f = 0) : v = 0 := by
  have h := congrArg (fun M => v ᵥ* Matrix.map M f) d.sum_eq_one_rat
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f), Matrix.vecMul_add,
    ← Matrix.vecMul_vecMul, h1, h2, h3, Matrix.zero_vecMul, add_zero, Matrix.vecMul_one] at h
  exact h.symm

theorem orth_eq_zero {D : D7} {k : Type} [Field k] (f : D.host.E →+* k) {S A L : HSp D} (o : OrthDec S A L)
    {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ)
    {v : Fin S.rank → k} (h1 : v ᵥ* o.iA.map f = 0) (h2 : v ⬝ᵥ (f ∘ vecB o ζ) = 0) : v = 0 := by
  have h3 : v ᵥ* o.iB.map f = 0 := by
    funext j
    have hs : Subsingleton (Fin L.rank) := by rw [hζ.1]; infer_instance
    have hj : ζ j ≠ 0 := fun h0 => hζ.2 (by
      have : ζ = 0 := funext fun i => by rw [Subsingleton.elim i j, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero])
    have h4 : f ∘ vecB o ζ = o.iB.map f *ᵥ (f ∘ ζ) := funext fun i => RingHom.map_mulVec f o.iB ζ i
    rw [h4, Matrix.dotProduct_mulVec, dotProduct, Fintype.sum_subsingleton _ j] at h2
    exact (mul_eq_zero.1 h2).resolve_right ((map_ne_zero f).2 hj)
  have h := congrArg (fun M => v ᵥ* Matrix.map M f) o.iA_qA_add
  simp only [Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_one _ (map_zero f) (map_one f), Matrix.vecMul_add,
    ← Matrix.vecMul_vecMul, h1, h3, Matrix.zero_vecMul, add_zero, Matrix.vecMul_one] at h
  exact h.symm

theorem dot_eq_zero_of_smul {k : Type} [Field k] {N : ℕ} {v w : Fin N → k} {c : k} (hc : c ≠ 0)
    (h : v ⬝ᵥ (fun r => c * w r) = 0) : v ⬝ᵥ w = 0 := by
  have : v ⬝ᵥ (c • w) = 0 := h
  rw [dotProduct_smul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

namespace Place

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} {s : k}

theorem pr_eq : p.pr = ⇑(p.π.comp (incA D)) := rfl

theorem xi_ne_zero : p.xi ≠ 0 := (map_ne_zero (p.π.comp (incA D))).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem hz_ne_zero (B : BesLev D ρ) : p.hz B ≠ 0 := (map_ne_zero (p.π.comp (incA D))).2 B.line.2

theorem exists_isCoreFrame (hs : s ≠ 0) (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) :
    ∃ F, p.IsCoreFrame B s FA F := by
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul (N := B.V₀.rank) (Y := n ⊕ Unit)
    (Matrix.of fun r => Sum.elim (fun a => (B.o.iA.map p.pr * FA.β) r a) fun _ => s * p.pr (vecB B.o B.ζ r))
    (by rw [Fintype.card_sum, FA.card_eq, ← B.o.rank_add, B.line.1]; rfl) (fun v hv => by
      refine orth_eq_zero (p.π.comp (incA D)) B.o B.line (FA.eq_zero ?_) (dot_eq_zero_of_smul hs ?_)
      · rw [Matrix.vecMul_vecMul]; funext a; exact congrFun hv (Sum.inl a)
      · exact congrFun hv (Sum.inr ()))
  exact ⟨F, fun r a => by rw [hF]; rfl, fun r => by rw [hF]; rfl⟩

theorem exists_isJacFrame (hs : s ≠ 0) (J : JacLev D ρ) {hh : k} (hh0 : hh ≠ 0) (F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n) :
    ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F := by
  have hx := p.xi_ne_zero
  let β : Matrix (Fin J.W.rank) (n ⊕ Fin (2 * ρ)) k :=
    Matrix.of fun r => Sum.elim (fun a => (J.d.i₀.map p.pr * F₀.β) r a) fun j =>
      if h : j.val < ρ then s * p.xi ^ (ρ - j.val) * p.pr (J.d.e r ⟨j.val, h⟩)
      else s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - 1 - j.val)) * p.pr (J.d.e' r ⟨2 * ρ - 1 - j.val, by omega⟩)
  have b1 : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val = i.val → ∀ r,
      β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (rfl : j = i) r
    exact dif_pos hi
  have b2 : ∀ (i : Fin ρ) (j : Fin (2 * ρ)), j.val + i.val + 1 = 2 * ρ → ∀ r,
      β r (Sum.inr j) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : j + i + 1 = 2 * ρ) r
    obtain rfl : i = 2 * ρ - 1 - j := by omega
    exact dif_neg (show ¬ j < ρ by omega)
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul β
    (by rw [Fintype.card_sum, F₀.card_eq, ← J.d.rank_add, Fintype.card_fin]) (fun v hv => by
      refine hyp_eq_zero (p.π.comp (incA D)) J.d ?_ (F₀.eq_zero ?_) ?_
      · funext i
        have := congrFun hv (Sum.inr ⟨i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * p.xi ^ (ρ - i.val)) (mul_ne_zero hs (pow_ne_zero _ hx)) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b1 i _ rfl r).symm)
      · rw [Matrix.vecMul_vecMul]; funext a; exact congrFun hv (Sum.inl a)
      · funext i
        have := congrFun hv (Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))
          (mul_ne_zero (mul_ne_zero hs (div_ne_zero hh0 hx)) (pow_ne_zero _ (div_ne_zero (by simp) hx))) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b2 i _ (by have := i.2; dsimp only; omega) r).symm))
  exact ⟨F, rfl, fun r a => by rw [hF]; rfl, by rw [hF]; exact b1, by rw [hF]; exact b2⟩

theorem exists_isBesFrame (hs : s ≠ 0) (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) :
    ∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F := by
  have hx := p.xi_ne_zero
  let β : Matrix (Fin B.V.rank) (n ⊕ Fin (2 * ρ + 1)) k :=
    Matrix.of fun r => Sum.elim (fun a => ((B.d.i₀ * B.o.iA).map p.pr * FA.β) r a) fun j =>
      if h : j.val < ρ then s * p.xi ^ (ρ - j.val) * p.pr (B.d.e r ⟨j.val, h⟩)
      else if h' : j.val = ρ then s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r)
      else s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - j.val)) * p.pr (B.d.e' r ⟨2 * ρ - j.val, by omega⟩)
  have b1 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val = i.val → ∀ r,
      β r (Sum.inr j) = s * p.xi ^ (ρ - i.val) * p.pr (B.d.e r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (rfl : j = i) r
    exact dif_pos hi
  have b0 : ∀ j : Fin (2 * ρ + 1), j.val = ρ → ∀ r, β r (Sum.inr j) = s * p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) := by
    rintro ⟨j, hj⟩ (h : j = ρ) r
    exact (dif_neg (show ¬ j < ρ by omega)).trans (dif_pos h)
  have b2 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val + i.val = 2 * ρ → ∀ r,
      β r (Sum.inr j) = s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (B.d.e' r i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ (h : j + i = 2 * ρ) r
    obtain rfl : i = 2 * ρ - j := by omega
    exact (dif_neg (show ¬ j < ρ by omega)).trans (dif_neg (show ¬ j = ρ by omega))
  obtain ⟨F, hF⟩ := Frame.exists_of_vecMul β
    (by rw [Fintype.card_sum, FA.card_eq, ← B.d.rank_add, ← B.o.rank_add, B.line.1, Fintype.card_fin]; omega)
    (fun v hv => by
      refine hyp_eq_zero (p.π.comp (incA D)) B.d ?_
        (orth_eq_zero (p.π.comp (incA D)) B.o B.line (FA.eq_zero ?_) ?_) ?_
      · funext i
        have := congrFun hv (Sum.inr ⟨i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * p.xi ^ (ρ - i.val)) (mul_ne_zero hs (pow_ne_zero _ hx)) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b1 i _ rfl r).symm)
      · rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.map_mul]
        funext a; exact congrFun hv (Sum.inl a)
      · have := congrFun hv (Sum.inr ⟨ρ, by omega⟩)
        rw [← Matrix.dotProduct_mulVec]
        refine dot_eq_zero_of_smul hs ?_
        refine Eq.trans ?_ this
        refine congrArg (v ⬝ᵥ ·) (funext fun r => ((b0 _ rfl r).trans ?_).symm)
        exact congrArg (s * ·) (RingHom.map_mulVec (p.π.comp (incA D)) _ _ r)
      · funext i
        have := congrFun hv (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
        refine dot_eq_zero_of_smul (c := s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val))
          (mul_ne_zero (mul_ne_zero hs (div_ne_zero (neg_ne_zero.2 (p.hz_ne_zero B)) hx))
            (pow_ne_zero _ (div_ne_zero (by simp) hx))) ?_
        refine Eq.trans ?_ this
        exact congrArg (v ⬝ᵥ ·) (funext fun r => (b2 i _ (by have := i.2; dsimp only; omega) r).symm))
  exact ⟨F, rfl, fun r a => by rw [hF]; rfl, by rw [hF]; exact b1, by rw [hF]; exact b0, by rw [hF]; exact b2⟩

end Place

theorem normalFrames_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (s : k), s ≠ 0 → (∀ (B : BesLev D ρ) (FA : GlobalTheory.LocMod.Frame k B.A.rank n), (∃ F, p.IsCoreFrame B s FA F) ∧ (∃ F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ p.hz B ≠ 0) ∧ ∀ (J : JacLev D ρ) (hh : k), hh ≠ 0 → ∀ F₀ : GlobalTheory.LocMod.Frame k J.W₀.rank n, ∃ F : GlobalTheory.LocMod.Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F :=
  fun _ _ _ _ _ _ p _ _ _ _ _ hs =>
    ⟨fun B FA => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA, p.hz_ne_zero B⟩,
      fun J _ hh0 F₀ => p.exists_isJacFrame hs J hh0 F₀⟩

end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLineLink_gram_similitude_bijective : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ', l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram ∧ ∀ S : HSp D, Function.Bijective (l.κ S) ∧ ∀ w, l.κ S w ∈ ratMx D S.rank B.L.rank → w ∈ ratMx D L'.rank S.rank := by
  first | exact @GlobalTheory.Unf.LinkGram.link_gram | exact GlobalTheory.Unf.LinkGram.link_gram | (intros; apply GlobalTheory.Unf.LinkGram.link_gram <;> assumption)
end

