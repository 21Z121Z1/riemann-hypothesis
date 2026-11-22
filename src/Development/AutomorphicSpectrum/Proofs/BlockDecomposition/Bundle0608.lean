import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0585
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0584
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionLogNormOnSheet
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem log_eq_of_frame {a ρ F G Pa Pb φ h : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hF : 0 < F) (hG : 0 < G)
    (hPa : 0 < Pa) (hPb : 0 < Pb) (hh : h = Pa / Pb * a * Real.exp (φ / 2))
    (e : a * ρ * (G / Pb) = F / Pa) : Real.log ρ - φ / 2 = Real.log (F / G / h) := by
  have hE := Real.exp_pos (φ / 2)
  have key : F / G / h = ρ / Real.exp (φ / 2) := by
    have hF' : F = a * ρ * (G / Pb) * Pa := by
      rw [e]
      field_simp
    rw [hh, hF']
    field_simp
  rw [key, Real.log_div hρ.ne' hE.ne', Real.log_exp]

theorem value_of_ne_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : GlobalTheory.HermLB (mpStr ℤ m n)) (A : HermLine (Bk n)) (X : Scheme.{0}) [IsIntegral X]
    (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (r : (M.restr i).B.ι → X.functionFieldˣ) (hr : IsRatSec (M.restr i).B r)
    (f g : Pol n), IsRatSectionOn (ptIdeal (i (genericPoint X))) A f g → RatOf M A r f g →
    ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z →
      eval z (map (Int.castRingHom ℂ) f) ≠ 0 → eval z (map (Int.castRingHom ℂ) g) ≠ 0 →
      y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) ∧
      GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r y = logNormRat A f g z := by
  intro m n M A X _ i _ r hr f g hfg hrat y z hz hf0 hg0
  obtain ⟨α, β, hf, hg, -, -, hdeg⟩ := hfg
  obtain ⟨u, hu, hcl⟩ := hrat
  obtain ⟨w, hw⟩ : ∃ w, w = PtsOver.map i rfl _ y := ⟨_, rfl⟩
  have hz' : IsUnder w z := hw ▸ hz
  have hwb := mem_pick (M.φ σ₀).isLB w
  obtain ⟨b, hb⟩ : ∃ b, b = pick (M.φ σ₀).isLB w := ⟨_, rfl⟩
  rw [← hb] at hwb
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, Bk n k, c = fun k => ptChart (w.1 (IsLocalRing.closedPoint ℂ)) k := ⟨_, rfl⟩
  have hwc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => hc ▸ mem_ptChart _ k)
  have hwbc : w ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) := mem_ptsIn_inf.2 ⟨hwb, hwc⟩
  have pre : ∀ V : (MP ℤ m n).Opens, w ∈ ptsIn (mpStr ℤ m n) σ₀ V → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ V) := by
    intro V hV
    subst hw
    exact CxPts.mem_ptsIn.2 (CxPts.mem_ptsIn.1 hV)
  have hyc := pre _ hwc
  have hybc := pre _ hwbc
  have hyb := pre _ hwb
  have hgc : genericPoint X ∈ i ⁻¹ᵁ mchart c := gen_mem (CxPts.mem_ptsIn.1 hyc)
  have hgb : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c) := gen_mem (CxPts.mem_ptsIn.1 hybc)
  have e := hcl b c hgc hgb
  have hne : ∀ a : Fin (m + 1) → ℕ, ∏ k, z ⟨k, c k⟩ ^ a k ≠ 0 := fun a =>
    Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
  have val : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      ratVal (fnAt i c hgc s) y = eval z (map (Int.castRingHom ℂ) s) / ∏ k, z ⟨k, c k⟩ ^ a k := by
    intro s a hs
    refine (ratVal_fnOf hyc hgc _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
    exact ev_dehomog_of_isUnder m n c s a hs w z hz' hwc
  have unit : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a →
      eval z (map (Int.castRingHom ℂ) s) ≠ 0 → UnitAt (under y) (fnAt i c hgc s) := by
    intro s a hs h0
    refine (unitAt_fnOf_iff (CxPts.mem_ptsIn.1 hyc) hgc _).2 (CxPts.mem_ptsIn.1 ((mem_ptsIn_basicOpen hyc _).2 ?_))
    rw [← ratVal_fnOf hyc hgc]
    change ratVal (fnAt i c hgc s) y ≠ 0
    rw [val s a hs]
    exact div_ne_zero h0 (hne a)
  have hF := unit f α hf hf0
  have hG := unit g β hg hg0
  have hU : UnitAt (under y) (fnOf _ hgb (i.app _ (u b c).val)) := by
    obtain ⟨v, hv⟩ := (u b c).isUnit.map (i.app (M.B.U b ⊓ mchart c)).hom
    have hv' : (v : Γ(X, i ⁻¹ᵁ (M.B.U b ⊓ mchart c))) = i.app _ (u b c).val := hv
    rw [← hv']
    exact unitAt_fnOf (CxPts.mem_ptsIn.1 hybc) hgb v
  have hR : UnitAt (under y) (r fun _ => b : X.functionField) := by
    have e' : (r fun _ => b : X.functionField) =
        fnAt i c hgc f * (fnOf _ hgb (i.app _ (u b c).val) * fnAt i c hgc g)⁻¹ := by
      rw [← e]
      have h1 := hU.ne_zero
      have h2 := hG.ne_zero
      field_simp
    rw [e']
    exact hF.mul (hU.mul hG).inv
  have hxb : under y ∈ (M.restr i).B.U (fun _ => b) := by
    refine Set.mem_iInter.2 fun _ => ?_
    subst hw
    exact CxPts.mem_ptsIn.1 hwb
  have hyb' : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).B.U (fun _ => b)) := CxPts.mem_ptsIn.2 hxb
  have ho : y ∈ offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) :=
    mem_offSupp.2 fun hs =>
      ((presents_divOfRatSec (M.restr i).isLB hr).isEqn (fun _ => b) _ hxb).mem_supp_iff.1 hs hR
  refine ⟨ho, ?_⟩
  have hφ : ((M.restr i).φ σ₀).φ (fun _ => b) y = (M.φ σ₀).φ b w := by
    rw [hw]
    exact GlobalTheory.Weight.pull_φ (M.φ σ₀) i rfl _ y
  have hvU : ratVal (fnOf _ hgb (i.app _ (u b c).val)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U b ⊓ mchart c) (u b c : Γ(MP ℤ m n, M.B.U b ⊓ mchart c)) w := by
    refine (ratVal_fnOf hybc hgb _).trans ((CxPts.ev_app i rfl _ _ y).trans ?_)
    rw [← hw]
  have ev' := congrArg (ratVal · y) e
  simp only at ev'
  rw [ratVal_mul (hU.mul hR).regAt hG.regAt, ratVal_mul hU.regAt hR.regAt, hvU, val g β hg, val f α hf] at ev'
  have hP : ∀ a : Fin (m + 1) → ℕ, 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := fun a => by
    have := norm_pos_iff.2 (hne a)
    simpa only [norm_prod, norm_pow] using this
  have hh := hu.2.2 b c w z hz' hwbc
  have hzp : ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ α k) / ∏ k, ‖z ⟨k, c k⟩‖ ^ β k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 : ‖z ⟨k, c k⟩‖ ≠ 0 := norm_ne_zero_iff.2 ((hz' k (c k)).1.1 (CxPts.ptsIn_mono (mchart_le c k) hwc))
    rw [← hdeg k, zpow_sub₀ h0, zpow_natCast, zpow_natCast]
  rw [hzp] at hh
  rw [logNorm_eq _ hr ho hyb', hφ, logNormRat]
  have evn := congrArg norm ev'
  simp only [norm_mul, norm_div, norm_prod, norm_pow] at evn
  exact log_eq_of_frame (norm_pos_iff.2 (ev_ne_zero hwbc (u b c).isUnit)) (norm_pos_iff.2 (ratVal_ne_zero hR))
    (norm_pos_iff.2 hf0) (norm_pos_iff.2 hg0) (hP α) (hP β) hh evn

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionTheoryHeightBound
section
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.First

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in
theorem form_eq_hE (u v : Fin n → E) :
    toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J u v = hE σ J u v := by
  simp only [toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe, hE, Formalism.UG.hform]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem hE_mulVec {m : Matrix (Fin n) (Fin n) E} (hm : cT (σ : E →+* E) m * J * m = J) (u : Fin n → E) :
    hE σ J (m *ᵥ u) (m *ᵥ u) = hE σ J u u := by
  have e : Matrix.of (fun a (_ : Fin 1) => (m *ᵥ u) a) = m * Matrix.of (fun a (_ : Fin 1) => u a) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h1 := gram_apply (σ := σ) (J := J) (s := 1) (r := 1) (Matrix.of fun a _ => (m *ᵥ u) a) (Matrix.of fun a _ => (m *ᵥ u) a) 0 0
  have h2 := gram_apply (σ := σ) (J := J) (s := 1) (r := 1) (Matrix.of fun a _ => u a) (Matrix.of fun a _ => u a) 0 0
  rw [e, pgram_unitary hm] at h1
  rw [h2] at h1
  rw [← form_eq_hE, ← form_eq_hE]
  rw [e] at *
  exact h1.symm

theorem exists_sends {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {u : Fin n → E} (hu : u ≠ 0) (hi : hE σ J u u = 0) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 ∧ Sends σ J γ u v := by
  obtain ⟨m, hm, e⟩ := hγ
  refine ⟨m.1 *ᵥ u, ?_, ?_, ?_⟩
  · intro h0
    apply hu
    have := congrArg (fun z => (m⁻¹).1 *ᵥ z) h0
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
  · rw [hE_mulVec hm, hi]
  · have e1 : (matHom _ σ J γ).1 = m.1.map (inclR (F := F) (AF F)) := by
      rw [matHom_apply]
      exact (congrArg Units.val e).symm
    unfold Sends
    rw [e1]
    funext i
    simp only [ratV]
    exact (RingHom.map_mulVec (inclR (F := F) (AF F)) m.1 u i).symm

omit [NumberField F] [NumberField E] in
theorem first_witt_vector_ne_zero {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) : Xᵀ 0 ≠ 0 := by
  intro h0
  have h1 := gram_apply (σ := σ) (J := J) X Y 0 0
  rw [hW.xy, h0] at h1
  simp at h1

omit [NumberField F] [NumberField E] in
theorem first_witt_vector_isotropic {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    hE σ J (Xᵀ 0) (Xᵀ 0) = 0 := by
  have h1 := gram_apply (σ := σ) (J := J) X X 0 0
  rw [hW.xx, form_eq_hE] at h1
  exact h1.symm

theorem exists_isotropic_le
    (hS : ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0)
    (hM : ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J,
      (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀)
    (hB : ∀ {C : Set (GAd σ J)}, IsCompact C → ∀ {v : Fin n → E}, v ≠ 0 → ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B)
    {x : Fin n → E} (hx : x ≠ 0) (hi : hE σ J x x = 0) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ g : GAd σ J, ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ hgt σ J g u ≤ C₁ := by
  obtain ⟨ε, hε, hS⟩ := hS
  obtain ⟨C₀, hC₀, hC⟩ := hM ε hε
  obtain ⟨B, hB⟩ := hB hC₀ hx
  refine ⟨max ε B, lt_max_of_lt_left hε, fun g => ?_⟩
  by_cases h : ∃ v : Fin n → E, v ≠ 0 ∧ hgt σ J g v < ε
  · obtain ⟨v, hv, hlt⟩ := h
    exact ⟨v, hv, hS g v hv hlt, hlt.le.trans (le_max_left _ _)⟩
  · push_neg at h
    obtain ⟨γ, hγ, hγC⟩ := hC g h
    obtain ⟨v, hv, hvi, hs⟩ := exists_sends hγ hx hi
    refine ⟨v, hv, hvi, ?_⟩
    rw [← hgt_mul hs.inv]
    exact (hB _ hγC).trans (le_max_right _ _)

theorem exp_neg_le_rpow {d : ℝ} (hd : 0 < d) {s D : ℝ} (h : Real.exp (-(d * s)) ≤ D) :
    Real.exp (-s) ≤ D ^ (1 / d) := by
  have e : Real.exp (-s) = Real.exp (-(d * s)) ^ (1 / d) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [e]
  exact Real.rpow_le_rpow (Real.exp_pos _).le h (by positivity)

end GlobalTheory.CompanionTheory.RedCov.First

open GlobalTheory.CompanionTheory.RedCov.First in

theorem GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin (r + 1)) E) (hW : IsWittFrame σ J X Y) (a) (ha : IsTorus σ J X Y a)
    (Ω C : Set (GAd σ J)) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X) (hC : IsCompact C) :
    ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 →
      NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → Real.exp (- s 0) ≤ M := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  obtain ⟨C₁, hC₁, hu⟩ := exists_isotropic_le (GlobalTheory.T.small_height_vector_isotropic F E σ h n J hJ) ((GlobalTheory.T.unitary_points_height_bound_finite GlobalTheory.T.unitary_points_height_bound_compact) F E σ h n J hJ)
    (fun hC _ hv => GlobalTheory.CompanionTheory.RedCov.Bridge.exists_hgt_le σ J hC hv) (first_witt_vector_ne_zero hW) (first_witt_vector_isotropic hW)
  obtain ⟨P, hP, hlow⟩ := GlobalTheory.T.torus_siegel_height_lower_bound F E σ h n J hJ r X Y hW a ha Ω C hΩ
    (hΩP.trans minParOne_subset) hC
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨(2 * P * C₁) ^ (1 / (Module.finrank ℚ F : ℝ)), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro ω hω s κ hκ e he hN
  obtain ⟨u, hu0, hui, hule⟩ := hu (ω * a s * κ)
  refine exp_neg_le_rpow hd ((hlow ω hω s κ hκ e he).trans ?_)
  calc P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) ≤ P * (2 * hgt σ J (ω * a s * κ) u) :=
        mul_le_mul_of_nonneg_left (hN.2.2 u hu0 hui) hP.le
    _ ≤ P * (2 * C₁) := by gcongr
    _ = 2 * P * C₁ := by ring
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScaledIntegralHermitianInOpenSubgroupStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_integral_hermitian_in_open_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens.exists_smul_mem_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzArchContinuousIntegrable
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple

theorem decay_of_functionals {V ι : Type} [AddCommGroup V] [TopologicalSpace V] [Fintype ι] {N : ℕ}
    (e : V ≃+ (Fin N → ℝ)) (hes : Continuous e.symm) (c : ι → V →+ ℂ) (hc : ∀ i, Continuous (c i))
    (f : SchwartzMap (Fin N → ℝ) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X : V, (∃ i, R < ‖c i X‖) → ‖f (e X)‖ ≤ C / R ^ k := by
  let L : ι → (Fin N → ℝ) →L[ℝ] ℂ := fun i =>
    ((c i).comp e.symm.toAddMonoidHom).toRealLinearMap ((hc i).comp hes)
  have hL : ∀ i X, c i X = L i (e X) := by
    intro i X
    show c i X = c i (e.symm (e X))
    rw [e.symm_apply_apply]
  set T : ℝ := ∑ i, ‖L i‖ + 1 with hT
  have hTpos : 0 < T := by
    have : 0 ≤ ∑ i, ‖L i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  obtain ⟨C0, hC0⟩ := f.decay k 0
  refine ⟨C0 * T ^ k, fun R hR X ⟨i, hi⟩ => ?_⟩
  have hRpos : 0 < R := by linarith
  set x := e X with hx
  have hb : ‖c i X‖ ≤ T * ‖x‖ := by
    rw [hL]
    refine ((L i).le_opNorm x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have : ‖L i‖ ≤ ∑ j, ‖L j‖ :=
      Finset.single_le_sum (f := fun j => ‖L j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  have hRx : R ≤ T * ‖x‖ := hi.le.trans hb
  have hd : ‖x‖ ^ k * ‖f x‖ ≤ C0 := by
    simpa [norm_iteratedFDeriv_zero] using hC0.2 x
  rw [le_div_iff₀ (pow_pos hRpos k)]
  calc ‖f x‖ * R ^ k ≤ ‖f x‖ * (T * ‖x‖) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRpos.le hRx k) (norm_nonneg _)
    _ = (‖x‖ ^ k * ‖f x‖) * T ^ k := by rw [mul_pow]; ring
    _ ≤ C0 * T ^ k := mul_le_mul_of_nonneg_right hd (pow_nonneg hTpos.le k)

theorem schwartzArch_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)), IsHomeomorph κ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Continuous φ ∧ Integrable φ (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) ∧ (∃ B : ℝ, ∀ X, ‖φ X‖ ≤ B) ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k := by
  intro F E _ _ _ _ _ σ hCM κ hκ n M d b lam hlam φ hφ
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, hsc, -, hrepr, hB, -, hgc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hB n M
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b lam hlam
  haveI := hW n M
  obtain ⟨N, e, he, hes, f, hf⟩ := hφ
  have hφe : φ = fun x => f (e x) := funext hf
  have hφc : Continuous φ := by rw [hφe]; exact f.continuous.comp he
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμ
  haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hint : Integrable φ μ := by
    have h1 : Integrable (fun x => f x) (μ.map e) := f.integrable
    rw [hφe]
    exact (integrable_map_measure h1.aestronglyMeasurable he.measurable.aemeasurable).1 h1
  refine ⟨hφc, hint, ?_, fun k => ?_⟩
  · obtain ⟨C0, hC0⟩ := f.decay 0 0
    refine ⟨C0, fun X => ?_⟩
    rw [hf]
    simpa [norm_iteratedFDeriv_zero] using hC0.2 (e X)
  · let c : (Fin n × Fin M × NumberField.InfinitePlace F) → (Fin n → Fin M → Ainf F ⊗[F] E) →+ ℂ := fun p =>
      { toFun := fun X => κ (X p.1 p.2.1) p.2.2
        map_zero' := by simp
        map_add' := fun X Y => by simp }
    have hc : ∀ p, Continuous (c p) := fun p =>
      (continuous_apply p.2.2).comp (hκ.continuous.comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1)))
    obtain ⟨C, hC⟩ := decay_of_functionals e hes c hc f k
    refine ⟨C, fun R hR X hX => ?_⟩
    rw [hf]
    refine hC R hR X ?_
    simp only [boxK, Set.mem_setOf_eq, not_forall, not_le] at hX
    obtain ⟨a, i, w, h⟩ := hX
    exact ⟨(a, i, w), h⟩

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecompositionStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_factorizable_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → ∃ (k : ℕ) (φ : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin k → (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN | exact GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN | (intros; apply GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFiniteSumOfProducts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem schwartzBruhat_eq_sum_pureTuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), IsSchwartzBruhat Φ → ∃ (N : ℕ) (φ : Fin N → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin N → (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ i, IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨k, Φinf, Φf, hinf, hf, hsum⟩ := hΦ
  choose s A S hA hAS hdec using fun i => GlobalTheory.CompanionTheory.WhitFree.DecN.exists_box_combN b (Φf i) (hf i)
  let e := Fintype.equivFin (Σ i : Fin k, (s i))
  refine ⟨Fintype.card (Σ i : Fin k, (s i)),
    fun j Z => Φinf (e.symm j).1 Z * Φf (e.symm j).1 (e.symm j).2,
    fun j => A (e.symm j).1 (e.symm j).2, Finset.univ.biUnion S, ?_, ?_, ?_, ?_⟩
  · intro j
    exact GlobalTheory.CompanionTheory.WhitFree.DecN.isSchwartzArch_const_mulN (hinf _) _
  · intro j v
    exact hA _ _ v
  · intro j v hv
    exact hAS _ _ (e.symm j).2.2 v
      (fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  · intro X
    rw [hsum X]
    symm
    refine (Equiv.sum_comp e.symm (fun p : (Σ i : Fin k, (s i)) =>
      pureN (fun Z => Φinf p.1 Z * Φf p.1 p.2) (A p.1 p.2) X)).trans ?_
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
    exact mul_assoc _ _ _

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAnyHaarStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_integrable_any_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → Integrable Φ dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt.integrable_isSchwartzBruhat_tuple | exact GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt.integrable_isSchwartzBruhat_tuple | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt.integrable_isSchwartzBruhat_tuple <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrixStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilFree_of_congruent_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (g : GL (Fin n) E) (T' : Matrix (Fin n) (Fin n) E) (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g → SWFree σ J T' hT' → SWFree σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilStabilizerIntegrableStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_stabilizer_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ T : Matrix (Fin n) (Fin n) E, Filter.Tendsto (fun S => coefS σ J ψ dx db Φ T b S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiffStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_cutoff_translate_contDiff : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {φ : XB E k}, SmV (repI E k) φ → ∀ {b : (Fin k → Cinf E) → ℝ}, ContDiff ℝ ∞ b → (∀ x ∈ tsupport b, IsUnit (lastEnt x)) → ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | exact GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | (intros; apply GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOneStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.socle_of_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | exact GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | (intros; apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceGramUnitScalingStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_gram_unit_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fv F v ⊗[F] E) (X : Fin 1 → Fin M → Fv F v ⊗[F] E), (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) X) = Algebra.norm (Fv F v) u * (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) X := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.Dilate.half_trace_dilate | exact GlobalTheory.CompanionTheory.AvgFree.Dilate.half_trace_dilate | (intros; apply GlobalTheory.CompanionTheory.AvgFree.Dilate.half_trace_dilate <;> assumption)
end

