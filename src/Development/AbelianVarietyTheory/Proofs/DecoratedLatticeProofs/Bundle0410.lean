import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEdge
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0260
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0235
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.FinPl.FrameLat

set_option maxHeartbeats 1000000 in

theorem sMoves_of_wComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (L L' : Lat S) (c : AE D) (g : GA D S), IsSelfDualC S L → IsSelfDualC S L' → NormOneAt p.v c → (∀ x : Fin S.rank → k, (fun i => p.sec (x i)) ∈ latV S L (· = p.v) ↔ (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i)) ∈ latV S L' (· = p.v)) → SMoves S c g L L' p.v := by
  intro D k _ _ _ _ p S L L' c g hL hL' hc hw
  have hpc : p.pr c * p.pr (cA D c) = 1 := by rw [← map_mul, hc.1, map_one]
  have hGinv : ∀ x : Fin S.rank → k,
      (Formalism.L2.Theta.mt S g).map p.pr *ᵥ ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      show Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = Formalism.L2.Theta.mt S (g * g⁻¹) from rfl, mul_inv_cancel,
      show Formalism.L2.Theta.mt S 1 = 1 from rfl, Matrix.map_one p.pr (map_zero _) (map_one _), Matrix.one_mulVec]
  have hsec : ∀ u : Fin S.rank → k, Formalism.L2.Theta.mt S g *ᵥ (fun i => p.sec (u i)) =
      fun i => p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) := by
    intro u
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]
  have hc1 : ∀ a : k, c * p.sec a = p.sec (p.pr c * a) := by
    intro a; rw [mul_comm, sec_mul_right, mul_comm]
  have hc2 : ∀ b : k, c * cA D (p.sec b) = cA D (p.sec (p.pr (cA D c) * b)) := by
    intro b
    have h : c * cA D (p.sec b) = cA D (cA D c * p.sec b) := by rw [map_mul, cA_cA]
    rw [h, mul_comm, sec_mul_right, mul_comm]
  have hB : ∀ x z : Fin S.rank → k,
      ∑ i, ∑ j, (p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x)) i * p.pr (cA D (incA D (S.gram i j))) *
          (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) j =
        ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j := by
    intro x z
    rw [← pairing_inv (p := p) g x z]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) *
      (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z) j)) * hpc
  intro y hy
  have hyd : y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
    funext i
    simp only [Pi.add_apply, p.sec_pr]
    rw [map_mul, cA_cA, ← add_mul]
    exact ((idem_iff p _).1 (hy i)).symm
  obtain ⟨u, z, rfl⟩ : ∃ u z : Fin S.rank → k, y = (fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))) :=
    ⟨_, _, hyd⟩
  have himg : c • (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) =
      (fun i => p.sec ((p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u)) i)) +
        (fun i => cA D (p.sec ((p.pr (cA D c) • ((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a)) *ᵥ z)) i))) := by
    funext i
    have h1 := congrFun (hsec u) i
    have h2 := congrFun (mt_csec (p := p) g z) i
    have h3 : (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i =
        p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [Matrix.mulVec_add, Pi.add_apply, h1, h2]
    have h4 : c * (p.sec (((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec ((((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i))) =
        p.sec (p.pr c * ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ u) i) +
          cA D (p.sec (p.pr (cA D c) * (((Formalism.L2.Theta.mt S g).map (fun a => p.pr (cA D a))) *ᵥ z) i)) := by
      rw [mul_add, hc1, hc2]
    show c * (Formalism.L2.Theta.mt S g *ᵥ ((fun i => p.sec (u i)) + (fun i => cA D (p.sec (z i))))) i = _
    refine (congrArg (c * ·) h3).trans (h4.trans ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [himg, decomp hL, decomp hL']
  refine and_congr (hw u) ?_
  rw [csec_mem_iff hL, csec_mem_iff hL']
  constructor
  · intro h x' hx'
    have hx : p.pr c • ((Formalism.L2.Theta.mt S g).map p.pr *ᵥ
        (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))) = x' := by
      rw [Matrix.mulVec_smul, smul_smul, hpc, one_smul, hGinv]
    have hmem := (hw (p.pr (cA D c) • ((Formalism.L2.Theta.mt S g⁻¹).map p.pr *ᵥ x'))).2 (by rw [hx]; exact hx')
    rw [← hx, hB]
    exact h _ hmem
  · intro h x hx
    have h5 := h _ ((hw x).1 hx)
    rwa [hB] at h5

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneMatchesIsotropicYOfMatchesIsotropicX
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

open GlobalTheory.IwaPlace in

theorem hermAt_colMul_jY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D)
    (x : Fin S.rank → AE D) : hermAt S (colMul d.jY i a) x = a * cA D ((d.pX *ᵥ x) i) := by
  have hg : ∀ j k, cA D (gA S j k) = gA S k j := fun j k => congrFun (congrFun (adj_gA S) k) j
  rw [d.pX_eq]
  simp only [hermAt, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, adj, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, cA_cA, hg, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pX_colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (b : AE D) :
    (d.pX *ᵥ colMul d.jX i b) i = b := by
  have h := congrFun (congrFun d.pX_jX i) i
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.mulVec, dotProduct, colMul]
  calc ∑ k, d.pX i k * (b * d.jX k i) = b * ∑ k, d.pX i k * d.jX k i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = b := by rw [h, mul_one]

theorem mem_idAt_of_colMul_jX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} (hL : IsSelfDualC S L)
    (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ) {b : AE D} (hb : colMul d.jX i b ∈ latV S L (· = v)) : b ∈ idAt D (· = v) := by
  rw [← pX_colMul_jX d i b]
  exact GlobalTheory.IwaPlace.mulVec_mem_idAt d.pX ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL).1 _ hb) i

theorem colMul_jY_mem_iff {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {M : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (hL : IsSelfDualC S L) (hM : MonoAt d L M v) (i : Fin ρ) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    colMul d.jY i a ∈ latV S L (· = v) ↔
      ∀ b, colMul d.jX i b ∈ latV S L (· = v) → a * cA D b ∈ intAt D (· = v) := by
  have hy : ∀ k, colMul d.jY i a k ∈ idAt D (· = v) := fun k => Ideal.mul_mem_right _ _ ha
  rw [(GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL).2.2 _ hy]
  constructor
  · intro h b hb
    have h1 := h _ hb
    rwa [hermAt_colMul_jY, pX_colMul_jX] at h1
  · intro h x hx
    rw [hermAt_colMul_jY]
    exact h _ (((hM x).1 hx).1 i)

theorem dualLine_match : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D), IsSelfDualC S L → IsSelfDualC S L' → MonoAt d L M v → MonoAt d L' M' v → NormOneAt v c → (∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v))) → ∀ i, ∀ a ∈ idAt D (· = v), (colMul d.jY i a ∈ latV S L (· = v) ↔ colMul d.jY i (c * a) ∈ latV S L' (· = v)) := by
  intro D S S₀ ρ d L L' M M' v c hL hL' hM hM' hc hX i a ha
  have hca : c * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha
  rw [colMul_jY_mem_iff d hL hM i ha, colMul_jY_mem_iff d hL' hM' i hca]
  have hcc : c * cA D c = 1 := hc.1
  constructor
  · intro h b' hb'
    have hbI : cA D c * b' ∈ idAt D (· = v) :=
      Ideal.mul_mem_left _ _ (mem_idAt_of_colMul_jX d hL' v i hb')
    have e : c * (cA D c * b') = b' := by rw [← mul_assoc, hcc, one_mul]
    have h1 : colMul d.jX i (cA D c * b') ∈ latV S L (· = v) := (hX i _ hbI).2 (by rw [e]; exact hb')
    have h2 := h _ h1
    rw [map_mul, cA_cA] at h2
    have e2 : c * a * cA D b' = a * (c * cA D b') := by ring
    rw [e2]
    exact h2
  · intro h b hb
    have h1 := (hX i b (mem_idAt_of_colMul_jX d hL v i hb)).1 hb
    have h2 := h _ h1
    have e : c * a * cA D (c * b) = a * cA D b := by
      rw [map_mul]
      calc c * a * (cA D c * cA D b) = (c * cA D c) * (a * cA D b) := by ring
        _ = a * cA D b := by rw [hcc, one_mul]
    rwa [e] at h2

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffIdempotentMemIdealTwoIntegers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemTwo
open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen

theorem exists_split {K : Type} [Field K] [NumberField K] (c d : 𝓞 K) (hc0 : c ≠ 0) (hd : d ≠ 0) :
    ∃ x y : 𝓞 K, (x : K) / c * c + (y : K) / d * d = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
        ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (x : K) / c = t * (g : K)⁻¹) ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
        ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (y : K) / d = t * (g : K)⁻¹) := by
  obtain ⟨G, hG⟩ : ∃ G : Ideal (𝓞 K), G = Ideal.span {c} ⊔ Ideal.span {d} := ⟨_, rfl⟩
  obtain ⟨I', hI'⟩ : G ∣ Ideal.span {c} := Ideal.dvd_iff_le.2 (hG ▸ le_sup_left)
  obtain ⟨D', hD'⟩ : G ∣ Ideal.span {d} := Ideal.dvd_iff_le.2 (hG ▸ le_sup_right)
  have hG0 : G ≠ 0 := by
    intro h
    have : c ∈ G := hG ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact hc0 this
  have hcop : I' ⊔ D' = ⊤ := by
    apply mul_left_cancel₀ hG0
    rw [Ideal.mul_sup, ← hI', ← hD', Ideal.mul_top, hG]
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hcop.symm ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ I' ⊔ D')
  have coe0 : ∀ w : 𝓞 K, w ≠ 0 → (w : K) ≠ 0 := fun w hw => RingOfIntegers.coe_ne_zero_iff.2 hw
  have hint : ∀ (w z : 𝓞 K), w ≠ 0 → (∀ g ∈ G, g * z ∈ Ideal.span {w}) →
      ∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
      ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (z : K) / w = t * (g : K)⁻¹ := by
    intro w z hw hz Q hQ
    have hGQ : ¬ G ≤ Q.asIdeal := fun h => hQ
      ⟨h (hG ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)),
       h (hG ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
    obtain ⟨g, hg, hgQ⟩ := Set.not_subset.1 hGQ
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hz g hg)
    have hg0 : g ≠ 0 := fun h => hgQ (h ▸ Q.asIdeal.zero_mem)
    have hgE := coe0 g hg0
    have hwE := coe0 w hw
    have htE : (t : K) * w = g * z := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      rwa [map_mul, map_mul] at this
    refine ⟨g, t, hg0, hgQ, ?_⟩
    field_simp
    linear_combination -htE
  refine ⟨x, y, ?_, hint c x hc0 fun g hg => hI' ▸ Ideal.mul_mem_mul hg hx,
    hint d y hd fun g hg => hD' ▸ Ideal.mul_mem_mul hg hy⟩
  rw [div_mul_cancel₀ _ (coe0 c hc0), div_mul_cancel₀ _ (coe0 d hd)]
  have := congrArg (algebraMap (𝓞 K) K) hxy
  rwa [map_add, map_one] at this

theorem off_comp {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D}
    {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS) :
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → Φ (1 - e - cA D e) Q = 0) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ (1 - e - cA D e) Q ∈ Q.adicCompletionIntegers D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hdl : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hdl P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]

  have hzero : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) →
      Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
    intro Q hQQ
    rw [hO]
    rcases hQQ with hQ | hQ
    · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
        rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hdl P hP).2.2 Q (Ne.symm hne))
          (fun h => absurd hQ h), (hdl Q hQ).2.1]
      have h2 := hprod Q
      rw [h1, one_mul] at h2
      rw [h1, h2, sub_self, sub_zero]
    · rw [conjP_eq_cP] at hQ
      have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
        rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
            rw [h, cP_cP])))
          (fun h => absurd hQ h)]
        have := (hdc (cP Q) hQ).2.1
        rwa [cP_cP] at this
      have h2 := hprod Q
      rw [h1, mul_one] at h2
      rw [h1, h2, sub_zero, sub_self]

  have hoint : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q ∈ Q.adicCompletionIntegers D.host.E := by
    intro Q
    rw [hO, hE, hC]
    exact sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
      (sum_mem fun P hP => delta_mem (hdl P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
  exact ⟨hzero, hoint⟩

theorem term_int {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) (o : AE D)
    (hoint : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ o Q ∈ Q.adicCompletionIntegers D.host.E) (u : D.host.E)
    (hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ o Q = 0 ∨ ∃ g t : 𝓞 D.host.E, g ≠ 0 ∧ g ∉ Q.asIdeal ∧
      u = t * (g : D.host.E)⁻¹) : finPart D (o * incA D u) ∈ intAE D := by
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  rcases hu Q with h0 | ⟨g, t, hg0, hgQ, heq⟩
  · rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · refine mul_mem (hoint Q) ?_
    have : algebraMap D.host.E (Q.adicCompletion D.host.E) u ∈ Q.adicCompletionIntegers D.host.E := by
      rw [heq, map_mul]
      exact mul_mem (Q.coe_mem_adicCompletionIntegers t) ((inv_mem_iff Q hg0).2 hgQ)
    exact this

theorem off_two : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ c : ℕ, 0 < c → ∀ d : 𝓞 D.host.E, d ≠ 0 → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (c : 𝓞 D.host.E) ∈ Q.asIdeal → d ∈ Q.asIdeal → Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → ∃ a₁ a₂ : AE D, finPart D a₁ ∈ intAE D ∧ finPart D a₂ ∈ intAE D ∧ 1 - e - cA D e = a₁ * incA D (c : D.host.E) + a₂ * incA D (d : D.host.E) := by
  intro D e SS he c hc d hd hcd
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨hzero, hoint⟩ := off_comp hΦ he
  generalize 1 - e - cA D e = o at hzero hoint ⊢
  have hc0 : (c : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_split (c : 𝓞 D.host.E) d hc0 hd
  have hcast : ((c : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) := map_natCast _ c
  rw [hcast] at hxy hx
  refine ⟨o * incA D ((x : D.host.E) / c), o * incA D ((y : D.host.E) / d),
    term_int hΦ o hoint _ fun Q => ?_, term_int hΦ o hoint _ fun Q => ?_, ?_⟩
  · by_cases h : (c : 𝓞 D.host.E) ∈ Q.asIdeal ∧ d ∈ Q.asIdeal
    · exact Or.inl (hzero Q (hcd Q h.1 h.2))
    · exact Or.inr (hx Q h)
  · by_cases h : (c : 𝓞 D.host.E) ∈ Q.asIdeal ∧ d ∈ Q.asIdeal
    · exact Or.inl (hzero Q (hcd Q h.1 h.2))
    · exact Or.inr (hy Q h)
  · have h1 := congrArg (incA D) hxy
    rw [map_add, map_mul, map_mul, map_one] at h1
    rw [mul_assoc, mul_assoc, ← mul_add, h1, mul_one]

end GlobalTheory.OffIdemTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OnePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceMatch

theorem mem_GfC_of_suppAt' {D : D7} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V}
    (hg : Formalism.L2.Theta.SuppAt e V g) : g ∈ GfC V := by
  obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, h⟩ := he
  have h0 : infPart D (e + cA D e) = 0 := by
    rw [h]; exact TensorProduct.zero_tmul _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrArg (infPart D) (hg i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at this
  refine Eq.trans this ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem suppAt_conj' {D : D7} {e : Formalism.L2.Theta.AE D} {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) (t : GA D V) :
    Formalism.L2.Theta.SuppAt e V (t⁻¹ * g * t) := by
  refine GlobalTheory.LocGrp.suppAt_of_sandwich hg (mt V t⁻¹) (mt V t) ?_
  rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.MixModel.mt_inv_mul]

theorem finE_mem_St_of_lev {D : D7} {u : D.what₂.Word} (d : GlobalTheory.SeeSaw.Dat D u) (hB : d.Base) (g : GA D (d.st 0).V)
    (hg : g ∈ d.lev 0) : finE (d.st 0).V g ∈ St (d.st 0).β := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨hr', ξ, hL⟩ := (hB.st 0 hm).lev
  have h1 : g ∈ GfC _ ∧ finE (d.st 0).V g ∈ lev D.sp.cm (d.st 0).V.gram (d.st 0).β (d.st 0).L := hg
  rw [hL, mem_lev, mem_parLev] at h1
  exact h1.2.1.2.1

theorem red_of_congr {D : D7} {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u}
    {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E} {PP : Pl D.host.E}
    (G : GlobalTheory.LocMod.GAt d τ PP) (x x' : G.S.P.J) (g : GL (Fin D.R.r) (kP PP)) (h : G.Red x' g)
    (hc : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) :
    G.Red x g := by
  intro a b a' b' ha hb z hz
  have h1 := h a b a' b' ha hb z hz
  have hI : GlobalTheory.StepData.IntM (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val :=
    GlobalTheory.StepData.intM_of_mem_KO (G.S.P.le_KO x'.2)
  have hM := hI.mul_maxM (GlobalTheory.StepData.mem_KOne.1 hc)
  have e : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val *
      (((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - 1) =
      (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val := by
    rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  rw [e] at hM
  have h2 := hM a b
  rw [Matrix.sub_apply] at h2
  have e2 : (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) =
      ((x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b) +
      ((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E)) := by ring
  rw [e2]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt h2 h1)

end GlobalTheory.PlaceMatch

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PlaceMatch.one_place : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1) (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), d.Base → IsTypePlaces d.c.Pg → GlobalTheory.LocMod.PinGBy G cG → ∀ Q : GA D (d.st 0).V → Prop, (∀ k ∈ d.lev 0, ∀ k' ∈ d.lev 0, Q k → Q k' → Q (k * k')) → (∀ (PP : d.c.Pg) (n : GA D (d.st 0).V) (q : GL (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (d.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (GlobalTheory.LocMod.ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → (d.t 0)⁻¹ * n * d.t 0 ∈ d.lev 0 → Q ((d.t 0)⁻¹ * n * d.t 0)) → (∀ b ∈ GfC (D.sp.X 0), (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0 ∈ d.lev 0 → Q ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0)) → ∀ (PP : d.c.Pg) (x : (G PP).S.P.J), ∃ m ∈ d.lev 0, Q m ∧ (∀ hr : D.R.r ≤ (d.st 0).V.rank, (G PP).Red x (upperLeftBlock hr (redFn (d.st 0).β PP.1 (finE (d.st 0).V m)))) ∧ ∀ PP' ∈ d.c.Pg, PP' ≠ PP.1 → redFn (d.st 0).β PP' (finE (d.st 0).V m) = 1 := by
  intro D u d τ G cG h0 hB _hTP hG Q hmul hN hU PP x
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hn : (d.st 0).V.rank = D.R.r := by rw [(hB.st 0 hm).rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have hst : ∀ w ∈ d.lev 0, finE (d.st 0).V w ∈ St (d.st 0).β := GlobalTheory.PlaceMatch.finE_mem_St_of_lev d hB
  have hbes := (G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)
  have hρ : (G PP).S.ρ = D.R.rS := by have := hbes.1; have := (G PP).S.odd; omega
  have hLev := GlobalTheory.T.pinned_local_groups_have_level D u d τ cG G hB hG PP 0 ((G PP).s + 1) (Nat.zero_add _)
  have hv : ∀ P : d.c.Pg, (G P).q.v = IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers D.host.F) P.1 := by
    intro P
    obtain ⟨ε, hε, hsum⟩ := (G P).q.above
    exact (GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ P.1 _ ε (G P).idem hε hsum).symm
  have horth : ∀ P P' : d.c.Pg, P ≠ P' →
      ((G P).q.e + cA D (G P).q.e) * ((G P').q.e + cA D (G P').q.e) = 0 := by
    intro P P' hne
    obtain ⟨ε, hε, hsum⟩ := (G P).q.above
    obtain ⟨ε', hε', hsum'⟩ := (G P').q.above
    have hvv : (G P).q.v ≠ (G P').q.v := by
      rw [hv P, hv P']
      intro h
      exact hne (Subtype.ext (GlobalTheory.LevelPlaces.injOn_under D d.c hB.com P.2 P'.2 h))
    rw [hsum, hsum', ← map_mul, GlobalTheory.SingleDatum.BasePair.placeIdem_mul_eq_zero hε' hε hvv, map_zero]
  have hoff : ∀ g : GA D (d.st 0).V, Formalism.L2.Theta.SuppAt (G PP).q.e (d.st 0).V g → (d.t 0)⁻¹ * g * d.t 0 ∈ d.lev 0 →
      ∀ PP' ∈ d.c.Pg, PP' ≠ PP.1 → redFn (d.st 0).β PP' (finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0)) = 1 :=
    fun g hg hl PP' hPP' hne => GlobalTheory.T.reduction_eq_one_of_supportedAt_orthogonal_splitPlace D (G ⟨PP', hPP'⟩).k (G ⟨PP', hPP'⟩).q PP' (G ⟨PP', hPP'⟩).idem (G PP).q.e
      (horth PP ⟨PP', hPP'⟩ fun h => hne (congrArg Subtype.val h).symm) _ _ _
      (GlobalTheory.PlaceMatch.suppAt_conj' hg _) (hst _ hl)
  obtain ⟨n, γ, hnN, hnJ, hγJ, hc⟩ := GlobalTheory.T.exists_N_embX_inv_mul_mem_KOne' (G PP).k (G PP).s D.R.k (G PP).S x.1 x.2
  obtain ⟨hup1, hup2⟩ := GlobalTheory.T.levelZeroUniformizerFrame_unipotent_and_embedGL (G PP).k (G PP).s D.R.k (G PP).S (Fin D.R.t)
  obtain ⟨hupN, -⟩ := hup1 ⟨n, hnJ⟩ hnN
  rw [hρ] at hupN
  obtain ⟨ν, hν⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q)
    ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) (GlobalTheory.LevZeroGen.upZero (G PP).S (Fin D.R.t) n)
  obtain ⟨η, hη⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q) ((G PP).FX 0 (Nat.zero_le _))
    (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin D.R.k) (Fin D.R.t)) γ)
  have hη' := GlobalTheory.T.besselFrame_embedding_localElement_eq_embedded_matrix D (G PP).k _ _ _ _ _ _ _ _ hbes η _ hη
  rw [← hup2] at hη'
  have hνl := hLev ν _ hν ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hnJ)
  have hηl := hLev _ _ hη' ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hγJ)
  have hQν := hN PP ν _ (GlobalTheory.LocFlag.mem_flagN D _ _ _ _ _ _ _ _ _ hbes ν _ hupN hν) hupN hν hνl
  have hQη := hU η (GlobalTheory.PlaceMatch.mem_GfC_of_suppAt' (G PP).q.split hη.1) hηl
  have hprod := GlobalTheory.LocGrp.isLoc_mul _ hν hη'
  rw [← map_mul] at hprod
  have e : (d.t 0)⁻¹ * ν * d.t 0 * ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o η * d.t 0) =
      (d.t 0)⁻¹ * (ν * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o η) * d.t 0 := by group
  have hl : (d.t 0)⁻¹ * (ν * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o η) * d.t 0 ∈ d.lev 0 :=
    hLev _ _ hprod ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 (mul_mem hnJ hγJ))
  refine ⟨_, hl, e ▸ hmul _ hνl _ hηl hQν hQη, fun hr => ?_, hoff _ hprod.1 hl⟩
  exact GlobalTheory.PlaceMatch.red_of_congr (G PP) x ⟨_, mul_mem hnJ hγJ⟩ _
    (GlobalTheory.T.local_level_zero_stabilizer_mem D u d τ PP.1 (G PP) hB hr _ ⟨_, mul_mem hnJ hγJ⟩ hprod (hst _ hl)) hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLatticeHalvesRepsFiniteIndexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLatticeHalves_reps_finite_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) ∧ Formalism.L2.Th1.H.IsReps (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) (repsOf (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) ((LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ (AC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c))) ∧ Formalism.L2.Th1.H.IsReps (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c) (repsOf (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') (BC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c)) := by
  first | exact @GlobalTheory.PeriodReps.reps_genuine | exact GlobalTheory.PeriodReps.reps_genuine | (intros; apply GlobalTheory.PeriodReps.reps_genuine <;> assumption)
end

