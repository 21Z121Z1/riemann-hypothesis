import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
import Formalism.UnipotentAdelicQuotients.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelMovesCosetVectorIntegralPoint
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.CosetMove

theorem wd_wd_norm (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ F, Wd D T a (Wd D T b F) = φ • Wd D T (a + b) F := by
  have h0 : wdPh D T (a + b) ≠ 0 := Complex.exp_ne_zero _
  have hn : ∀ x : VC D N N', ‖wdPh D T x‖ = 1 := fun x => by
    simp [wdPh, ee, Complex.norm_exp]
  have hc : Hf D T b a = (starRingEnd ℂ) (Hf D T a b) := by
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) *
    Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), ?_, fun F => ?_⟩
  · rw [norm_mul, norm_div, norm_mul, hn, hn, hn, Complex.norm_exp, hc]
    have : (((Real.pi : ℂ) * ((starRingEnd ℂ) (Hf D T a b) - Hf D T a b) / 2)).re = 0 := by
      simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.div_re]
    rw [this]; simp
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul, VacMove.hf_add_left, VacMove.hf_add_right, add_assoc]
  have : Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) =
      Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf D T z b) -
        (Real.pi : ℂ) * (Hf D T a a + (Hf D T b a + (Hf D T a b + Hf D T b b))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  field_simp
  field_simp at this
  linear_combination (wdPh D T a * wdPh D T b * F (z + (a + b))) * this

set_option maxHeartbeats 1000000 in

theorem om_cosetV_block : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ h ∈ intG D d, (∀ i j : Fin d, j.1 < a → a ≤ i.1 → ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ k ∈ intG D a, W.Om 1 h (cosetV D δ 𝔪 0 a d e0) = c • W.Om k 1 (cosetV D δ 𝔪 0 a d e0) := by
  intro D δ t0 hc a d e0 hv had W 𝔪 h𝔪 hcop _ h hh hblk
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he
  obtain ⟨G, hGdef⟩ : ∃ G, G = Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := ⟨_, rfl⟩

  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd, hcen⟩ := GlobalTheory.T.exists_skew_lattice_mover_with_determinant D 𝔪 h𝔪 hcop d
  have hsd : SD D (skewLat D 𝔪 d) := VacMove.sd_of_moves hg'm
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ, χ = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hJ : W.Om 1 g' e0 = χ • G := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔪 d) (FixKey.suppSplit_one D a) hg's
      (fun q hq hi => ⟨by simpa using FixKey.zeroAt_zero D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm, hχ, hGdef]
    rfl
  have hc0 : χ ≠ 0 := by rw [hχ]; exact Units.ne_zero _
  have hJe : G = χ⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hgT : W.Om 1 g' e0 ∈ TT D (tor0 D ⊤ δ) a d := W.maps 1 g' e0 hT
  have hJT : G ∈ TT D (tor0 D ⊤ δ) a d := by
    rw [hJe]; exact FixKey.TT_smul _ hgT

  obtain ⟨xh, -, hxh⟩ := VacInt.om_vac_right he hT W ((mem_intG h).1 hh)
  obtain ⟨uh, huh⟩ : ∃ u : ℂ, u = ((W.chV.f xh ^ W.ep : ℂˣ) : ℂ) := ⟨_, rfl⟩
  rw [← huh] at hxh
  have hhG : W.Om 1 h G = uh • G := by
    have e1 := W.mul 1 1 h g' e0 hT
    have e2 := W.mul 1 1 g' h e0 hT
    rw [mul_one] at e1 e2
    rw [hJe, W.smul _ _ _ _ hgT, ← e1, hcen, e2, hxh, W.smul _ _ _ _ hT, smul_comm]
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.T.exists_integralUnitary_blockLevel_unitBlock D 𝔪 h𝔪 hcop had h hh hblk
  obtain ⟨xk, -, hxk⟩ := VacInt.om_vac_left he hT W ((mem_intG k).1 hk)
  obtain ⟨uk, huk⟩ : ∃ u : ℂ, u = ((W.chV'.f xk ^ W.ep' : ℂˣ) : ℂ) := ⟨_, rfl⟩
  rw [← huk] at hxk
  have hkG : W.Om k 1 G = uk • G := by
    have e1 := W.mul k 1 1 g' e0 hT
    have e2 := W.mul 1 k g' 1 e0 hT
    rw [mul_one, one_mul] at e1
    rw [one_mul, mul_one] at e2
    rw [hJe, W.smul _ _ _ _ hgT, ← e1, e2, hxk, W.smul _ _ _ _ hT, smul_comm]
  have nuh : ‖uh‖ = 1 := by
    rw [huh, Units.val_zpow_eq_zpow_val, norm_zpow, W.chV.unitary, one_zpow]
  have nuk : ‖uk‖ = 1 := by
    rw [huk, Units.val_zpow_eq_zpow_val, norm_zpow, W.chV'.unitary, one_zpow]

  obtain ⟨x₀, hx₀⟩ : ∃ x, x = unitBlock D 0 a d := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁, hl₁⟩ := W.lift 1 h x₀ G hJT
  obtain ⟨m₂, hm₂, hl₂⟩ := W.lift k 1 x₀ G hJT
  obtain ⟨Y₁, hY₁⟩ : ∃ Y : Matrix (Fin d) (Fin a) (AE D), Y = ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * x₀.map (inc D) := ⟨_, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ Y : Matrix (Fin d) (Fin a) (AE D), Y =
    x₀.map (inc D) * (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) := ⟨_, rfl⟩
  have hkx' : ∀ i j, (Y₁ - Y₂) i j ∈ hatId D 𝔪 := by rw [hY₁, hY₂, hx₀]; exact hkx
  obtain ⟨z, hz⟩ := VacMove.MI_approx (cc := ⊤) top_ne_bot Y₂ (m₁ * m₂) (Nat.mul_pos hm₁ hm₂)
  obtain ⟨w, hw𝔪, hw⟩ := GlobalTheory.T.exists_ideal_matrix_congr_adelicMatrix_mod_nat D 𝔪 (Y₁ - Y₂) hkx' m₁ hm₁
  have hc2 : CloseTo D ⊤ m₂ (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) x₀ z := by
    have := hz.of_dvd (m := m₂) (dvd_mul_left _ _)
    intro i j
    obtain ⟨y, hy, e⟩ := this i j
    refine ⟨y, hy, ?_⟩
    rw [← e, hY₂]; simp
  have hc1 : CloseTo D ⊤ m₁ ((1 : GA D a) : GL (Fin a) (AE D)) (h : GL (Fin d) (AE D)) x₀ (z + w) := by
    have h3 := (hz.of_dvd (m := m₁) (dvd_mul_right _ _)).add hw
    have key : z.map (inc D) - Y₂ + (w.map (inc D) - (Y₁ - Y₂)) = (z + w).map (inc D) - Y₁ := by
      ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, map_add]; abel
    rw [key] at h3
    intro i j
    obtain ⟨y, hy, e⟩ := h3 i j
    refine ⟨y, hy, ?_⟩
    rw [← e, hY₁]; simp
  have hWh := hl₁ (z + w) hc1
  have hWk := hl₂ z hc2
  rw [hhG, FixKey.wd_smul, VacMove.pt_add] at hWh
  rw [hkG, FixKey.wd_smul] at hWk

  obtain ⟨φ, hφ1, hφ⟩ := wd_wd_norm D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hBk : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    VacMove.klat _ (VacMove.moves_one D a) hg'm
  have hJB := GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace D δ hc e0 he 𝔪 hsd
  rw [← hGdef] at hJB
  have hwB := (GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem D δ 𝔪 w hw𝔪).2
  have hfix : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ w) G = G := VacMove.wd_fix h1 hc hBk hJB hwB
  have hφ0 : φ ≠ 0 := by intro h0; rw [h0, norm_zero] at hφ1; exact zero_ne_one hφ1
  have hsum := hφ G
  rw [hfix] at hsum
  have hzw : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z + pt D (tor0 D ⊤ δ) δ w) G =
      φ⁻¹ • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) G := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hφ0, one_smul]
  have huk0 : uk ≠ 0 := by rw [huk]; exact Units.ne_zero _
  refine ⟨uh * φ⁻¹ * uk⁻¹, by rw [norm_mul, norm_mul, norm_inv, norm_inv, nuh, hφ1, nuk]; simp, k, hk, ?_⟩
  have hWT : Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G ∈ TT D (tor0 D ⊤ δ) a d :=
    GlobalTheory.FinWeil.RatTransl.wd_mem_TT D h1 ⊤ δ hc a d _ _ hJT
  unfold cosetV
  rw [← hx₀, ← hGdef]
  rw [W.smul _ _ _ _ hWT, W.smul _ _ _ _ hWT]
  change _ • W.Om 1 h (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G) = _ • _ • W.Om k 1 (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ x₀) G)
  rw [hWh, hWk, hzw, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FunObj.CosetMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelFiniteClassNumberCentraliserTorus
section
noncomputable section

open NumberField GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.TorCls.Borel

variable {N : ℕ} {S : Set (MvPolynomial (Fin N × Fin N) ℚ)} (hS : HeckeCharacterZeroLocus.IsGroupLocus S)

theorem aeval_map_entries {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R']
    (f : R →ₐ[ℚ] R') (M : Matrix (Fin N) (Fin N) R) (P : MvPolynomial (Fin N × Fin N) ℚ) :
    MvPolynomial.aeval (fun ij : Fin N × Fin N => f (M ij.1 ij.2)) P =
      f (MvPolynomial.aeval (fun ij : Fin N × Fin N => M ij.1 ij.2) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem mem_locus_map {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
    (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) :
    Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom
      (g : GL (Fin N) R) ∈ HeckeCharacterZeroLocus.locusSubgroup S hS R' := by
  intro P hP
  have h := g.2 P hP
  show MvPolynomial.aeval (fun ij : Fin N × Fin N => f (((g : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) ij.1 ij.2)) P = 0
  rw [aeval_map_entries, h, map_zero]

def locMap {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R') :
    HeckeCharacterZeroLocus.locusSubgroup S hS R →* HeckeCharacterZeroLocus.locusSubgroup S hS R' :=
  ((Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom).comp
    (HeckeCharacterZeroLocus.locusSubgroup S hS R).subtype).codRestrict _ (mem_locus_map hS f)

theorem locMap_comp {R R' R'' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R']
    [CommRing R''] [Algebra ℚ R''] (f : R' →ₐ[ℚ] R'') (f' : R →ₐ[ℚ] R') (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) :
    locMap hS f (locMap hS f' g) = locMap hS (f.comp f') g := rfl

theorem continuous_locMap {R R' : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [CommRing R']
    [Algebra ℚ R'] [TopologicalSpace R'] (f : R →ₐ[ℚ] R') (hf : Continuous f) :
    Continuous (locMap hS f) := by
  refine Continuous.subtype_mk ?_ _
  refine (Continuous.units_map _ ?_).comp continuous_subtype_val
  exact Continuous.matrix_map continuous_id hf

theorem lid_starT {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (x : ℚ ⊗[ℚ] D) :
    Algebra.TensorProduct.lid ℚ D (starT σ ℚ x).unop = (σ (Algebra.TensorProduct.lid ℚ D x)).unop := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q d =>
    rw [starT_tmul, Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.lid_tmul, map_rat_smul,
      MulOpposite.unop_smul]
  | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy]

theorem map_ofId_eq {D B : Type} [Ring D] [Algebra ℚ D] [CommRing B] [Algebra ℚ B] (x : ℚ ⊗[ℚ] D) :
    Algebra.TensorProduct.map (Algebra.ofId ℚ B) (AlgHom.id ℚ D) x =
      (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] B ⊗[ℚ] D) (Algebra.TensorProduct.lid ℚ D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q d =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.includeRight_apply,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', AlgHom.id_apply, Algebra.ofId_apply,
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tc_rat {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (z : (ℚ ⊗[ℚ] D)ˣ × ℚˣ)
    (h : GlobalTheory.TorCls.TC D σ β y ℚ z) :
    Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D) * β * (σ (Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D))).unop =
        algebraMap ℚ D (z.2 : ℚ) * β ∧
      Commute (Algebra.TensorProduct.lid ℚ D (z.1 : ℚ ⊗[ℚ] D)) y := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have := congrArg (Algebra.TensorProduct.lid ℚ D) h1
    simp only [map_mul, lid_starT] at this
    simpa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one] using this
  · have := h2.map (Algebra.TensorProduct.lid ℚ D)
    simpa using this

end GlobalTheory.TorCls.Borel

namespace GlobalTheory.TorCls.Borel

open IsDedekindDomain

theorem classes_finite : (∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R))) → HeckeCharacterZeroLocus.ClassNumberFinite → ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime],
    letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
    ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
      (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
        ∀ z ∈ O, GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) →
      ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
        ∀ z, GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 →
          ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ γ.1).unop = algebraMap ℚ D γ.2 * β ∧ Commute (γ.1 : D) y ∧
            ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u := by
  intro hbr hB D _ _ _ σ β y p _
  obtain ⟨N, S, hS, φ, hiso, hnat, hcont⟩ := hbr D σ β y
  letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
  intro U hUO
  obtain ⟨O, hO, h1O, hOU⟩ := hUO
  obtain ⟨π₁, π₂, hc₁, hc₂, hbij⟩ := GlobalTheory.CentTorus.AdelicSplit.adele_split p
  let Φ : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ) →*
      ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ) :=
    ((φ (AfP p)).comp (locMap hS π₁)).prod ((φ ℚ_[p]).comp (locMap hS π₂))
  have hφ₁ : Continuous (φ (AfP p)) := hcont (AfP p)
  have hφ₂ : Continuous (φ ℚ_[p]) := hcont ℚ_[p]
  have hΦc : Continuous Φ :=
    (hφ₁.comp (continuous_locMap hS π₁ hc₁)).prodMk (hφ₂.comp (continuous_locMap hS π₂ hc₂))
  have hTC : ∀ g, GlobalTheory.TorCls.TC D σ β y (AfP p) (Φ g).1 ∧ GlobalTheory.TorCls.TC D σ β y ℚ_[p] (Φ g).2 := fun g =>
    ⟨((hiso (AfP p)).2 _).2 ⟨_, rfl⟩, ((hiso ℚ_[p]).2 _).2 ⟨_, rfl⟩⟩

  have hsurj : ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ),
      GlobalTheory.TorCls.TC D σ β y (AfP p) z.1 → GlobalTheory.TorCls.TC D σ β y ℚ_[p] z.2 → ∃ g, Φ g = z := by
    intro z h1 h2
    obtain ⟨g₁, hg₁⟩ := ((hiso (AfP p)).2 z.1).1 h1
    obtain ⟨g₂, hg₂⟩ := ((hiso ℚ_[p]).2 z.2).1 h2
    let s := Function.surjInv hbij.2
    have hs : ∀ x, (π₁ (s x), π₂ (s x)) = x := Function.surjInv_eq hbij.2
    have hs₁ : ∀ a b, π₁ (s (a, b)) = a := fun a b => congrArg Prod.fst (hs (a, b))
    have hs₂ : ∀ a b, π₂ (s (a, b)) = b := fun a b => congrArg Prod.snd (hs (a, b))
    have hinj : ∀ a a' : FiniteAdeleRing (𝓞 ℚ) ℚ, π₁ a = π₁ a' → π₂ a = π₂ a' → a = a' :=
      fun a a' h h' => hbij.1 (Prod.ext h h')
    have hinjM : ∀ X Y : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ),
        π₁.toRingHom.mapMatrix X = π₁.toRingHom.mapMatrix Y →
        π₂.toRingHom.mapMatrix X = π₂.toRingHom.mapMatrix Y → X = Y := by
      intro X Y h h'
      refine Matrix.ext fun i j => ?_
      exact hinj _ _ (congrFun (congrFun h i) j) (congrFun (congrFun h' i) j)
    let G₁ : GL (Fin N) (AfP p) := g₁
    let G₂ : GL (Fin N) ℚ_[p] := g₂
    let M : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
      Matrix.of fun i j => s ((G₁ : Matrix (Fin N) (Fin N) (AfP p)) i j, (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) i j)
    let M' : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
      Matrix.of fun i j => s (((G₁⁻¹ : GL (Fin N) (AfP p)) : Matrix (Fin N) (Fin N) (AfP p)) i j,
        ((G₂⁻¹ : GL (Fin N) ℚ_[p]) : Matrix (Fin N) (Fin N) ℚ_[p]) i j)
    have hM₁ : π₁.toRingHom.mapMatrix M = (G₁ : Matrix (Fin N) (Fin N) (AfP p)) := by
      ext i j; exact hs₁ _ _
    have hM₂ : π₂.toRingHom.mapMatrix M = (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) := by
      ext i j; exact hs₂ _ _
    have hM'₁ : π₁.toRingHom.mapMatrix M' = ((G₁⁻¹ : GL (Fin N) (AfP p)) : Matrix (Fin N) (Fin N) (AfP p)) := by
      ext i j; exact hs₁ _ _
    have hM'₂ : π₂.toRingHom.mapMatrix M' = ((G₂⁻¹ : GL (Fin N) ℚ_[p]) : Matrix (Fin N) (Fin N) ℚ_[p]) := by
      ext i j; exact hs₂ _ _
    have hMM' : M * M' = 1 := hinjM _ _ (by rw [map_mul, map_one, hM₁, hM'₁]; simp)
      (by rw [map_mul, map_one, hM₂, hM'₂]; simp)
    have hM'M : M' * M = 1 := hinjM _ _ (by rw [map_mul, map_one, hM₁, hM'₁]; simp)
      (by rw [map_mul, map_one, hM₂, hM'₂]; simp)
    let G : GL (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ) := ⟨M, M', hMM', hM'M⟩
    have hG : G ∈ HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      intro P hP
      apply hinj
      · rw [map_zero, ← aeval_map_entries]
        have e : (fun ij : Fin N × Fin N => π₁ ((G : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2)) =
            fun ij => (G₁ : Matrix (Fin N) (Fin N) (AfP p)) ij.1 ij.2 := by
          funext ij; exact hs₁ _ _
        rw [e]; exact g₁.2 P hP
      · rw [map_zero, ← aeval_map_entries]
        have e : (fun ij : Fin N × Fin N => π₂ ((G : Matrix (Fin N) (Fin N) (FiniteAdeleRing (𝓞 ℚ) ℚ)) ij.1 ij.2)) =
            fun ij => (G₂ : Matrix (Fin N) (Fin N) ℚ_[p]) ij.1 ij.2 := by
          funext ij; exact hs₂ _ _
        rw [e]; exact g₂.2 P hP
    refine ⟨⟨G, hG⟩, Prod.ext ?_ ?_⟩
    · show φ (AfP p) (locMap hS π₁ ⟨G, hG⟩) = z.1
      rw [← hg₁]; congr 1; apply Subtype.ext; apply Units.ext; exact hM₁
    · show φ ℚ_[p] (locMap hS π₂ ⟨G, hG⟩) = z.2
      rw [← hg₂]; congr 1; apply Subtype.ext; apply Units.ext; exact hM₂

  let U' : Subgroup (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ)) := U.comap Φ
  have hU'o : IsOpen (U' : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    apply Subgroup.isOpen_of_mem_nhds U' (g := 1)
    have h1 : (1 : HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Φ ⁻¹' O := by
      show Φ 1 ∈ O; rw [map_one]; exact h1O
    refine Filter.mem_of_superset ((hO.preimage hΦc).mem_nhds h1) ?_
    intro g hg
    exact hOU _ hg (hTC g).1 (hTC g).2
  have hU'c : IsClosed (U' : Set (HeckeCharacterZeroLocus.locusSubgroup S hS (FiniteAdeleRing (𝓞 ℚ) ℚ))) :=
    U'.isClosed_of_isOpen hU'o
  obtain ⟨K, hKo, hKc⟩ := GlobalTheory.LocusOpenCompact.exists_isOpen_isCompact ℚ N S hS
  obtain ⟨T₀, hT₀⟩ := hB ℚ N S hS (U' ⊓ K) (by rw [Subgroup.coe_inf]; exact hU'o.inter hKo)
    (by
      rw [Subgroup.coe_inf]
      exact hKc.inter_left hU'c)

  classical
  refine ⟨T₀.image Φ, ?_⟩
  intro z h1 h2
  obtain ⟨g, rfl⟩ := hsurj z h1 h2
  obtain ⟨γ, hγ, s, hs, u, hu, hx⟩ := hT₀ g
  let γL : HeckeCharacterZeroLocus.locusSubgroup S hS ℚ := ⟨γ, hγ⟩
  have hg : g = locMap hS (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γL * s * u := Subtype.ext hx
  let w := φ ℚ γL
  have hw : GlobalTheory.TorCls.TC D σ β y ℚ w := ((hiso ℚ).2 w).2 ⟨γL, rfl⟩
  obtain ⟨hw1, hw2⟩ := tc_rat σ β y w hw
  let γ' : Dˣ × ℚˣ :=
    (Units.map (Algebra.TensorProduct.lid ℚ D).toAlgHom.toRingHom.toMonoidHom w.1, w.2)
  have hcomp₁ : π₁.comp (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) = Algebra.ofId ℚ (AfP p) :=
    AlgHom.ext fun q => by simp
  have hcomp₂ : π₂.comp (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) = Algebra.ofId ℚ ℚ_[p] :=
    AlgHom.ext fun q => by simp
  have hΦγ : Φ (locMap hS (Algebra.ofId ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) γL) = GlobalTheory.TorCls.dg D p γ' := by
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · show (φ (AfP p) (locMap hS π₁ (locMap hS _ γL))).1 = _
      rw [locMap_comp, hcomp₁, hnat ℚ (AfP p) (Algebra.ofId ℚ (AfP p)) γL _ rfl]
      apply Units.ext
      exact map_ofId_eq _
    · show (φ (AfP p) (locMap hS π₁ (locMap hS _ γL))).2 = _
      rw [locMap_comp, hcomp₁, hnat ℚ (AfP p) (Algebra.ofId ℚ (AfP p)) γL _ rfl]
      rfl
    · show (φ ℚ_[p] (locMap hS π₂ (locMap hS _ γL))).1 = _
      rw [locMap_comp, hcomp₂, hnat ℚ ℚ_[p] (Algebra.ofId ℚ ℚ_[p]) γL _ rfl]
      apply Units.ext
      exact map_ofId_eq _
    · show (φ ℚ_[p] (locMap hS π₂ (locMap hS _ γL))).2 = _
      rw [locMap_comp, hcomp₂, hnat ℚ ℚ_[p] (Algebra.ofId ℚ ℚ_[p]) γL _ rfl]
      rfl
  refine ⟨γ', hw1, hw2, Φ s, Finset.mem_image_of_mem _ hs, Φ u, (Subgroup.mem_inf.1 hu).1, ?_⟩
  rw [hg, map_mul, map_mul, hΦγ]

end GlobalTheory.TorCls.Borel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksArithmeticLargeGrids
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRankSize

theorem bot_arith (D : D7) (i j : ℕ) :
    Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧
      1 < SqNum.botSmall D i j := by
  have hk := D.R.k_even
  have hm := D.R.m_even
  have ht := D.R.t_odd
  have h3 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  rw [Nat.even_iff] at hk hm
  rw [Nat.odd_iff] at ht
  simp only [SqNum.botBig, SqNum.botSmall, rankV, sLen, Formalism.BasicNotions.Ranks.r]
  have e1 : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
  have e2 : (i + 1) * (D.R.k + D.R.m - 1 + 6) = i * (D.R.k + D.R.m - 1 + 6) + (D.R.k + D.R.m - 1 + 6) := by ring
  rw [e1, e2]
  generalize j * D.R.t = A
  generalize i * (D.R.k + D.R.m - 1 + 6) = B
  rw [Nat.even_iff]
  omega

theorem bottom_ranks : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro i j
  exact bot_arith D i j

end GlobalTheory.BotRankSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingArchimedeanBoundFockNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.BrPairBound

theorem pairK_one_re_nonneg {ι : Type} [Fintype ι] {m : ℕ} (w : ι → DomWeight m) (x : VV ℂ w) :
    0 ≤ (pairK w (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) x x).re := by
  by_cases h : x = 0
  · simp [h]
  · exact (Complex.lt_def.1 (GlobalTheory.CoefModel.pairK_pos w (G := fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun _ => Matrix.PosDef.one) x h)).1.le

theorem inf_bound : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N)
    (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    0 ≤ (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re ∧
    0 ≤ (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
      (GlobalTheory.CoefModel.mapVV φ _ v)).re ∧
    ‖φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v)‖ ^ 2 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) *
      (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ Λ u)).re *
      (pairK (fun τ => (σ τ).dual) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (GlobalTheory.CoefModel.mapVV φ _ v)
        (GlobalTheory.CoefModel.mapVV φ _ v)).re := by
  intro K ι _ _ _ φ n N hN Λ σ hI hS u v
  refine ⟨pairK_one_re_nonneg _ _, pairK_one_re_nonneg _ _, ?_⟩
  rw [GlobalTheory.T.branchingPairing_map_extendScalars_embedding φ hN Λ σ u v, GlobalTheory.BrPairF.brPairF_apply]
  set u' := GlobalTheory.CoefModel.mapVV φ Λ u
  set v' := GlobalTheory.CoefModel.mapVV φ _ v
  have h1 := GlobalTheory.T.bilinearFockPairing_sq_le_hermitianNorms σ (Formalism.L2.Col.Br.brStd hN Λ σ u') ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have h2 := GlobalTheory.T.branchingMap_hermitianNorm_le_prod_bounds hN Λ σ hI hS u'
  have h3 := GlobalTheory.T.hermitianFockNorm_adjugateSubst_symm_le σ v'
  have p2 := pairK_one_re_nonneg σ ((GlobalTheory.FunObj.funEquiv σ).symm v')
  have p3 := pairK_one_re_nonneg Λ u'
  calc _ ≤ _ := h1
    _ ≤ _ := mul_le_mul h2 h3 p2 (mul_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _) p3)
    _ = _ := by ring

end GlobalTheory.BrPairBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMemMultiplicitySpaceBaseLevelStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_mem_multiplicitySpace_baseLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (b : Bool) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) (levChi _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) → R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) := by
  first | exact @GlobalTheory.ThetaLevelP.thF_mem_level | exact GlobalTheory.ThetaLevelP.thF_mem_level | (intros; apply GlobalTheory.ThetaLevelP.thF_mem_level <;> assumption)
end

