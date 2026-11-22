import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0368
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0366
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePo
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsDualModLevelStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_type_vectors_dual_mod_level : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) → ∀ i j, ∃ t ∈ OAd D.host.F D.host.E, hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) (bd i) (b j) - (if i = j then ιA X.ew else 0) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) * t := by
  first | exact @GlobalTheory.St.G.DualMod.dual_mod | exact GlobalTheory.St.G.DualMod.dual_mod | (intros; apply GlobalTheory.St.G.DualMod.dual_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsFixedByChosenPlacesIdempotStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_type_vectors_fixed_by_chosen_places_idempotent : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, b i = ιA X.ew • b i) ∧ ∀ i, bd i = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) • bd i := by
  first | exact @GlobalTheory.St.G.FrameEps.beps | exact GlobalTheory.St.G.FrameEps.beps | (intros; apply GlobalTheory.St.G.FrameEps.beps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurableStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), γ ∈ GG k r → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Yv k r z z' γ (Matrix.of x)) ∧ ∀ R₀ y : ℝ, MeasurableSet (Eset k r z z' γ R₀ y) := by
  first | exact @GlobalTheory.Amp.YMeas.yv_measurable | exact GlobalTheory.Amp.YMeas.yv_measurable | (intros; apply GlobalTheory.Amp.YMeas.yv_measurable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlace
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem iwasawaFormula : IwasawaFormula := by
  intro n ε p q hp hq a j hj W hW c μN μM μK hc hN hM hK0 hK1 hKinv φ hφ
  obtain ⟨κ, -, -, hκ⟩ := GlobalTheory.T.iwasawa_integration_formula_up_to_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv
  have hconst := GlobalTheory.T.iwasawa_integration_formula_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv c κ hc hκ
  rw [hκ φ hφ, ← mul_assoc, hconst]

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakPropertiesStatement
section
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRealTraceBump_peak_properties : ∀ n : ℕ, 0 < n → Continuous (GlobalTheory.KFinAvg.peak n) ∧ GlobalTheory.KFinAvg.peak n 1 = 1 ∧ (∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ GlobalTheory.KFinAvg.peak n g ∧ GlobalTheory.KFinAvg.peak n g ≤ 1) ∧ ∀ U ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ δ < 1, ∀ g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)), g ∉ U → GlobalTheory.KFinAvg.peak n g ≤ δ := by
  first | exact @GlobalTheory.KFinAvg.peak_properties | exact GlobalTheory.KFinAvg.peak_properties | (intros; apply GlobalTheory.KFinAvg.peak_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePoStatement
section
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRealTraceBump_pow_finite_translation_stable_polys : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ), (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  first | exact @GlobalTheory.KFinAvg.peak_pow_polynomial | exact GlobalTheory.KFinAvg.peak_pow_polynomial | (intros; apply GlobalTheory.KFinAvg.peak_pow_polynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WordFrameDualTupleGramIntegrality
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.FrameCrd

variable {D : D7} (X : HidaSetting D)

theorem sig_apply (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = starRingEnd D.host.E x := rfl

theorem vecOf_sum (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Equiv.sum_comp (ci X).symm]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  rw [vecOf_sum]
  simp only [crdH]
  rw [Equiv.sum_comp (ci X) (fun j => X.bas.repr y j • X.bas j)]
  exact X.bas.sum_repr y

theorem pairM_apply {α β : Type} [Fintype α] [Fintype β]
    (P : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) α D.host.E) (Q : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) β D.host.E)
    (a : α) (b : β) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) Q P a b =
      (VS D).hT (vecOf X fun i => P i a) (vecOf X fun i => Q i b) := by
  rw [vecOf_sum, vecOf_sum]
  simp only [GlobalTheory.SgAlg.pairM, GlobalTheory.SgAlg.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Jc,
    map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, sig_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply]
  ring

theorem col_last (u : D.what₂.Word) : (fun i => Pc X u i (Fin.last D.R.rS)) = crdH X (X.zu u) := by
  funext i; simp [Pc]

theorem col_cs (u : D.what₂.Word) (a : Fin D.R.rS) : (fun i => Pc X u i a.castSucc) = crdH X (X.eX a) := by
  funext i; simp [Pc]

theorem col_f (a : Fin D.R.rS) : (fun i => fc X i a) = crdH X (X.fY a) := by
  funext i; simp [fc]

theorem hT_swap_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem T_ne_zero (u : D.what₂.Word) : ((((D.mem u).A.T : ℕ) : D.host.E)) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

theorem gram_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (Pc X u) =
      GlobalTheory.SgAlg.TF D.R.rS (algebraMap D.host.F D.host.E (Tc u)) := by
  ext a b
  rw [pairM_apply]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [col_last, vecOf_crdH, X.zu_norm]; simp [GlobalTheory.SgAlg.TF, Tc]
    | cast b =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [GlobalTheory.SgAlg.TF, (Fin.castSucc_ne_last b).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).1]
      simp [GlobalTheory.SgAlg.TF, Fin.castSucc_ne_last a]
    | cast b =>
      rw [col_cs, col_cs, vecOf_crdH, vecOf_crdH, X.ee]
      simp [GlobalTheory.SgAlg.TF, Matrix.diagonal_apply, Fin.castSucc_ne_last a]

theorem free_frame (u : D.what₂.Word) : GlobalTheory.SgAlg.Free (Pc X u) := by
  have hT0 := T_ne_zero u
  let Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.of fun i c => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.fY a) i) c
  let Dg : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.diagonal fun c => Fin.lastCases (-(((D.mem u).A.T : ℕ) : D.host.E))⁻¹ (fun _ => 1) c
  refine ⟨Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X), ?_⟩
  have h : Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X) * Pc X u =
      Dg * GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) Y := by
    simp only [GlobalTheory.SgAlg.pairM, Matrix.mul_assoc]
  rw [h]
  ext c d
  rw [Matrix.diagonal_mul, pairM_apply]
  induction c using Fin.lastCases with
  | last =>
    have hy : (fun i => Y i (Fin.last D.R.rS)) = crdH X (X.zu u) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last => rw [hy, col_last, vecOf_crdH, X.zu_norm]; simp [hT0]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [(Fin.castSucc_ne_last b).symm]
  | cast a =>
    have hy : (fun i => Y i a.castSucc) = crdH X (X.fY a) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last =>
      rw [hy, col_last, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).2]
      simp [Fin.castSucc_ne_last a]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]

theorem dual_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) := by
  refine ⟨?_, ?_⟩
  · ext a b
    rw [pairM_apply, col_f, vecOf_crdH]
    induction a using Fin.lastCases with
    | last =>
      rw [col_last, vecOf_crdH, hT_swap_zero (X.zu_orth u b).2]
      simp [(Fin.castSucc_ne_last b).symm]
    | cast a =>
      rw [col_cs, vecOf_crdH, X.ef]
      simp
  · ext a b
    rw [pairM_apply, col_f, col_f, vecOf_crdH, vecOf_crdH, X.ff]
    simp

theorem aaD_eq (a : Fin D.R.rS) : aaD D a = GlobalTheory.SgGlob.dInv D.host.E (D.R.rS - a) := by
  rw [aaD, GlobalTheory.IntTerm.Conv.ddS_eq, GlobalTheory.SgGlob.dInv, ← Nat.cast_sub a.2.le, _root_.zpow_neg, _root_.zpow_natCast,
    inv_pow]

theorem tupLat_le (u : D.what₂.Word) :
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  rw [GlobalTheory.SnMass.tupLat, Submodule.span_le]
  rintro _ ⟨b, x, hx, rfl⟩
  show vecOf X (x • fun i => GlobalTheory.SnMass.sideM (Pc X u) (fc X) i b) ∈ (VS D).L0
  rw [LinearMap.map_smul, X.Lam_split]
  induction b using Fin.addCases with
  | left c =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_left]
    simp only [GlobalTheory.SnMass.id1, Fin.append_left] at hx
    induction c using Fin.lastCases with
    | last =>
      simp only [Fin.val_last, Nat.sub_self, GlobalTheory.SgGlob.dInv, pow_zero] at hx
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [col_last, vecOf_crdH, algebraMap_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.Lb.smul_mem o (X.zu_Lb u)))
    | cast a =>
      simp only [Fin.val_castSucc] at hx
      rw [← aaD_eq] at hx
      rw [col_cs, vecOf_crdH]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, rfl⟩))
  | right a =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_right]
    simp only [GlobalTheory.SnMass.id1, Fin.append_right] at hx
    rw [← aaD_eq] at hx
    rw [col_f, vecOf_crdH]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, x, hx, rfl⟩)

end GlobalTheory.CovDom.FrameCrd

namespace GlobalTheory.CovDom

open GlobalTheory.CovDom.FrameCrd in

theorem frame_dual_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X :=
  fun _ X u => ⟨⟨free_frame X u, gram_frame X u⟩, dual_frame X u, tupLat_le X u⟩

end GlobalTheory.CovDom
end
end

