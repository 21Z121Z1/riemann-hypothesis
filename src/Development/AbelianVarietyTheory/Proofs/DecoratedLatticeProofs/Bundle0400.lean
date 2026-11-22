import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0383
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoprimeScalingIdealValuationLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem natInv_mem_adicIntegers (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (v.adicCompletion F) ((T : F)⁻¹) ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (T : F) = 1 := by
    have : (T : F) = algebraMap (𝓞 F) F (T : 𝓞 F) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) ((T : F)⁻¹)) = v.valuation F ((T : F)⁻¹) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h2, map_inv₀, h1, inv_one]

theorem natInv_smul_mem_intAf (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) (α : Af F) (h1 : α ∈ intAf F) (h2 : ∀ w, w ≠ v → evalV F w α = 0) :
    ((T : F)⁻¹ : F) • α ∈ intAf F ∧ ∀ w, w ≠ v → evalV F w (((T : F)⁻¹ : F) • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · change evalV F w _ ∈ w.adicCompletionIntegers F
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      rw [Algebra.smul_def]
      exact mul_mem (natInv_mem_adicIntegers F T w h) (h1 w)
    · rw [h2 w hw, smul_zero]; exact zero_mem _
  · rw [map_smul, h2 w hw, smul_zero]

theorem smul_pairA_zero (F : Type) [Field F] [NumberField F] (t : F) (α : Af F) :
    t • pairA F 0 α = pairA F 0 (t • α) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact Prod.ext (mul_zero _) rfl

theorem pairA_zero_tmul_smul (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (t : F) (α : Af F) (c : E) :
    pairA F 0 α ⊗ₜ[F] (t • c) = pairA F 0 (t • α) ⊗ₜ[F] c := by
  rw [← smul_pairA_zero, TensorProduct.smul_tmul]

theorem idV_natInv_mul_le (D : D7) (𝔠 : FI D) (T : ℕ) (v : Pl D) (h : ((T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    idV (FractionalIdeal.spanSingleton _ ((T : D.host.E)⁻¹) * 𝔠) v ≤ idV 𝔠 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨c, hc, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 ha
  have e : ((T : D.host.E)⁻¹) * c = ((T : D.host.F)⁻¹ : D.host.F) • c := by
    rw [Algebra.smul_def, map_inv₀, map_natCast]
  obtain ⟨g1, g2⟩ := natInv_smul_mem_intAf D.host.F T v h α h1 h2
  refine AddSubgroup.subset_closure ⟨((T : D.host.F)⁻¹ : D.host.F) • α, g1, g2, c, hc, ?_⟩
  rw [e]
  exact pairA_zero_tmul_smul D.host.F D.host.E _ α c

end GlobalTheory.SeeSaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DetIntegralUnitIdeleOfIntegralFinitePart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DetIntUnit

theorem det_mem_subring {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

theorem det_finM (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) :
    (finM V hn g).det = toEAf D (Formalism.L2.Theta.mt V g).det := by
  unfold finM
  rw [Matrix.det_reindex_self, RingHom.map_det]
  rfl

theorem det_int_unit : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)),
    finM V hn g = k.1 → (∀ i j, k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, (k⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det →
      finPart D (d : Formalism.L2.Theta.AE D) ∈ intAE D ∧ finPart D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := by
  intro D V n hn g k hk h1 h2 d hd
  have e1 : toEAf D (d : Formalism.L2.Theta.AE D) = k.1.det := by
    rw [hd, ← det_finM D V n hn g, hk]
  have i1 : toEAf D (d : Formalism.L2.Theta.AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [e1]; exact det_mem_subring _ _ h1
  have hkk : k.1.det * (k⁻¹).1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hdd : toEAf D (d : Formalism.L2.Theta.AE D) * toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have e2 : toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = (k⁻¹).1.det := by
    rw [e1] at hdd
    calc toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)
        = ((k⁻¹).1.det * k.1.det) * toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) := by
          rw [mul_comm (k⁻¹).1.det, hkk, one_mul]
      _ = (k⁻¹).1.det := by rw [mul_assoc, hdd, mul_one]
  have i2 : toEAf D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [e2]; exact det_mem_subring _ _ h2
  exact ⟨GlobalTheory.PlaceVec.finPart_mem_intAE i1, GlobalTheory.PlaceVec.finPart_mem_intAE i2⟩

end GlobalTheory.DetIntUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowBoundFromWindowWidthThree
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem exp_add_exp_le_exp_max_succ {C₁ C₂ y : ℝ} (hy : 1 ≤ y) :
    Real.exp (C₁ * y) + Real.exp (C₂ * y) ≤ Real.exp ((max C₁ C₂ + 1) * y) := by
  have hy0 : 0 ≤ y := by linarith
  have a1 : Real.exp (C₁ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)
  have a2 : Real.exp (C₂ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hy0)
  have a3 : (2 : ℝ) ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have e : Real.exp ((max C₁ C₂ + 1) * y) = Real.exp (max C₁ C₂ * y) * Real.exp y := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hp := Real.exp_pos (max C₁ C₂ * y)
  nlinarith

theorem diagonalRow_bound_from_windowWidthThree : Formalism.L2.SG.Pf.WuDecayOfGap → On {3} VanishingGramTermsBound → On {3} CollS → OneOn {3} true →
    OneOn {3} false →
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  intro hW hG hCo h1 h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₁, hC₁, t₁, H₁⟩ := h1 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₂, _, t₂, H₂⟩ := h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨tG, HG⟩ := hG Cg cb Cu cT CT hcb hcT
  obtain ⟨tC, HC⟩ := hCo Cg cb Cu cT CT hcb hcT
  refine ⟨max C₁ C₂ + 1, max (max (max t₁ t₂) (max tG tC)) 29, max (max (max t₁ t₂) (max tG tC)) 29,
    by linarith [le_max_left C₁ C₂], ?_⟩
  intro C' Cl hC' hCl D L u hT hE hD
  obtain ⟨⟨large₂, hL, h8, h1G⟩, hR⟩ := hE
  obtain ⟨hTies, hAdm, hHL, hNW, hTF⟩ := hD
  subst hL
  have hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT := ⟨h8, hHL.2⟩
  have hD0 : StandingNumericalData D 3 := GlobalTheory.T.columnDimension_window_three_of_columnCount D hNW hR
  have hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT 3 := ⟨hS0, hD0, by norm_num⟩
  obtain ⟨S, hF, hLT⟩ := hT.trueD.sTies
  have m1 : ∀ {a b c d e : ℝ}, max (max (max a b) (max c d)) 29 ≤ e →
      a ≤ e ∧ b ≤ e ∧ c ≤ e ∧ d ≤ e ∧ 29 ≤ e := by
    intro a b c d e h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine le_trans ?_ h <;> simp
  obtain ⟨a1, a2, a3, a4, a5⟩ := m1 hC'
  obtain ⟨b1, b2, b3, b4, b5⟩ := m1 hCl
  obtain ⟨c⟩ := GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle hW D large₂ C' Cl Cg cb Cu cT CT S a5 b5 hF hLT hTF hS0
  have hAC : (c.Y.tO u u).AbsConv := kExp_absConv_tied.2 D c.X c.Y u u c.tie
  have g0 := HG 3 rfl C' Cl a3 b3 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have gc := HC 3 rfl C' Cl a4 b4 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have o1 := H₁ 3 rfl C' Cl a1 b1 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  have o2 := H₂ 3 rfl C' Cl a2 b2 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  simp only [if_true, Bool.false_eq_true, if_false] at o1 o2
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h4 : D.R.m ^ 4 ≤ D.R.f := hHL.2.2.1
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast le_trans this h4
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hL1 : 1 < large₂.sc.L := hHL.1
  have hy : 1 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ hm
    have h2' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := one_le_mul_of_one_le_of_one_le this hf
    exact one_le_mul_of_one_le_of_one_le h2' hL1.le
  have hg : ∀ C, gamL D large₂.sc.L C = Real.exp (C * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) := by
    intro C; unfold gamL; congr 1; ring
  have hsum : gamL D large₂.sc.L C₁ + gamL D large₂.sc.L C₂ ≤ gamL D large₂.sc.L (max C₁ C₂ + 1) := by
    rw [hg, hg, hg]; exact exp_add_exp_le_exp_max_succ hy
  have key := GlobalTheory.T.diagonalTheorem_of_fourPointBounds D c large₂ C' Cl Cg cb Cu cT CT 3 (gamL D large₂.sc.L C₁) (gamL D large₂.sc.L C₂)
    (gamL D large₂.sc.L (max C₁ C₂ + 1)) u a5 b5 hH0 (Real.exp_pos _).le (Real.exp_pos _).le hsum g0 gc o1 o2
  unfold SDiagAt at key
  show TwoTerm D u _ _
  unfold TwoTerm
  rw [d0_eq]
  have e1 : gamL D large₂.sc.L (max C₁ C₂ + 1) = Real.exp ((max C₁ C₂ + 1) * mfL D large₂.sc.L) := by
    rw [hg]; rfl
  have e2 : Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) = Real.exp (-(kfk D / 2)) := by
    unfold kfk; congr 1; ring
  have e3 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) = Real.exp (-kfk D) := by
    unfold kfk; rfl
  rw [e1, e2, e3] at key
  refine le_trans key (le_of_eq ?_)
  ring

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralNegligibleOrbitsEqZeroCuspForm
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
namespace GlobalTheory.Core.Rk.NegOrbit
open GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary

variable {D : D7} (V : HSp D)

def IsNeg (x : GA D (dblSp V)) : Prop := ¬ ∃ δ ∈ GQ V, x * (io V (δ, 1))⁻¹ ∈ siegel V

variable {V}

theorem isNeg_siegel_mul {p x : GA D (dblSp V)} (hp : p ∈ siegel V) : IsNeg V (p * x) ↔ IsNeg V x := by
  unfold IsNeg
  refine not_congr ⟨fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩, fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩⟩
  · have := (siegel V).mul_mem ((siegel V).inv_mem hp) h
    simpa [mul_assoc] using this
  · simpa [mul_assoc] using (siegel V).mul_mem hp h

theorem isNeg_mul_io {x : GA D (dblSp V)} {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V (x * io V (γ₁, γ₂)) → IsNeg V x := by
  intro h ⟨δ, hδ, hx⟩
  refine h ⟨γ₂⁻¹ * δ * γ₁, (GQ V).mul_mem ((GQ V).mul_mem ((GQ V).inv_mem h₂) hδ) h₁, ?_⟩
  have e : x * io V (γ₁, γ₂) * (io V (γ₂⁻¹ * δ * γ₁, 1))⁻¹ = x * (io V (δ, 1))⁻¹ * io V (γ₂, γ₂) := by
    simp only [mul_assoc, ← map_inv, ← map_mul]
    congr 2
    ext <;> simp [mul_assoc]
  rw [e]
  exact (siegel V).mul_mem hx ((io_mem_siegel V).2 rfl)

theorem isNeg_mul_io_iff {x : GA D (dblSp V)} {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V (x * io V (γ₁, γ₂)) ↔ IsNeg V x := by
  refine ⟨isNeg_mul_io h₁ h₂, fun h => isNeg_mul_io ((GQ V).inv_mem h₁) ((GQ V).inv_mem h₂) ?_⟩
  have e : ((γ₁, γ₂) * (γ₁⁻¹, γ₂⁻¹) : GA D V × GA D V) = 1 := by ext <;> simp
  rw [mul_assoc, ← map_mul, e, map_one, mul_one]
  exact h

theorem exists_out_rmul (q : SiegelCosets V) (g : GQ (dblSp V)) : ∃ p ∈ siegelQ V,
    (((rmul _ g q).out : GQ (dblSp V)) : GA D (dblSp V)) = p * (q.out : GQ (dblSp V)) * g := by
  have e : mk ((siegel V).subgroupOf (GQ (dblSp V))) (q.out * g) = mk _ (rmul _ g q).out :=
    ((rmul_mk g q.out).symm.trans (congrArg (rmul _ g) (Quotient.out_eq q))).trans (Quotient.out_eq _).symm
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  refine ⟨((p : GQ (dblSp V)) : GA D (dblSp V)), ⟨Subgroup.mem_subgroupOf.1 p.2, (p : GQ (dblSp V)).2⟩, ?_⟩
  rw [← hp]
  simp [mul_assoc]

theorem isNeg_out_rmul_iff (q : SiegelCosets V) {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) :
    IsNeg V ((rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q).out : GQ (dblSp V)) ↔ IsNeg V (q.out : GQ (dblSp V)) := by
  obtain ⟨p, hp, e⟩ := exists_out_rmul q ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩
  rw [e, mul_assoc, isNeg_siegel_mul hp.1]
  exact isNeg_mul_io_iff h₁ h₂

theorem apply_out_rmul {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ}
    {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s) (q : SiegelCosets V) (g : GQ (dblSp V)) (y : GA D (dblSp V)) :
    φ ((((rmul _ g q).out : GQ (dblSp V)) : GA D (dblSp V)) * y) = φ ((q.out : GQ (dblSp V)) * g * y) := by
  obtain ⟨p, hp, e⟩ := exists_out_rmul q g
  rw [e, mul_assoc, mul_assoc, apply_siegelQ_mul V a hμ hφ hp, mul_assoc]

abbrev NegCosets (V : HSp D) : Type := {q : SiegelCosets V // IsNeg V (q.out : GQ (dblSp V))}

def ioEquiv {γ₁ γ₂ : GA D V} (h₁ : γ₁ ∈ GQ V) (h₂ : γ₂ ∈ GQ V) : NegCosets V ≃ NegCosets V where
  toFun q := ⟨rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q.1, (isNeg_out_rmul_iff q.1 h₁ h₂).2 q.2⟩
  invFun q := ⟨rmul _ ⟨io V (γ₁⁻¹, γ₂⁻¹), io_mem_GQ V (inv_mem h₁) (inv_mem h₂)⟩ q.1,
    (isNeg_out_rmul_iff q.1 (inv_mem h₁) (inv_mem h₂)).2 q.2⟩
  left_inv q := Subtype.ext (by
    show rmul _ _ (rmul _ _ q.1) = q.1
    rw [← rmul_mul]
    convert rmul_one q.1 using 2
    ext1; simp [← map_mul]; exact map_one (io V))
  right_inv q := Subtype.ext (by
    show rmul _ _ (rmul _ _ q.1) = q.1
    rw [← rmul_mul]
    convert rmul_one q.1 using 2
    ext1; simp [← map_mul]; exact map_one (io V))

def negAction (V : HSp D) : MulAction (GQ V) (NegCosets V) where
  smul δ q := ioEquiv (inv_mem δ.2) (one_mem (GQ V)) q
  one_smul q := Subtype.ext (by
    show rmul _ _ q.1 = q.1
    convert rmul_one q.1 using 2
    ext1; simp; exact map_one (io V))
  mul_smul δ₁ δ₂ q := Subtype.ext (by
    show rmul _ _ q.1 = rmul _ _ (rmul _ _ q.1)
    rw [← rmul_mul]
    congr 1
    ext1; simp [← map_mul])

attribute [local instance] negAction

@[simp] theorem io_one_one : io V (1, 1) = 1 := map_one (io V)

theorem smul_val (δ : GQ V) (q : NegCosets V) : (δ • q).1 =
    rmul _ ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩ q.1 := rfl

theorem mem_map_stabilizer_iff (y : NegCosets V) (x : GA D V) :
    x ∈ (MulAction.stabilizer (GQ V) y).map (GQ V).subtype ↔
      x ∈ GQ V ∧ ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (x, 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ ∈ siegel V := by
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨δ.2, ?_⟩
    obtain ⟨p, hp, e⟩ := exists_out_rmul y.1 ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩
    have hv : rmul _ ⟨io V ((δ : GA D V)⁻¹, 1), io_mem_GQ V (inv_mem δ.2) (one_mem _)⟩ y.1 = y.1 :=
      (smul_val δ y).symm.trans (congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hδ))
    rw [hv] at e
    have e' : ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) =
        p * ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((δ : GA D V)⁻¹, 1) := e
    have h' : p * ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((δ : GA D V)⁻¹, 1) * io V ((δ : GA D V), 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ = p := by
      rw [mul_assoc (p * _), ← map_mul]
      simp [io_one_one]
    rw [← e'] at h'
    rw [Subgroup.coe_subtype, h']
    exact hp.1
  · rintro ⟨hx, hs⟩
    refine ⟨⟨x, hx⟩, MulAction.mem_stabilizer_iff.2 (Subtype.ext ?_), rfl⟩
    rw [smul_val]
    conv_lhs => rw [← Quotient.out_eq y.1]
    have hr : ((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (x, 1) *
        ((y.1.out : GQ (dblSp V)) : GA D (dblSp V))⁻¹ ∈ GQ (dblSp V) :=
      mul_mem (mul_mem (y.1.out).2 (io_mem_GQ V hx (one_mem _))) (inv_mem (y.1.out).2)
    refine ((rmul_mk _ _).trans (mk_eq_iff.2 ⟨⟨⟨_, hr⟩, Subgroup.mem_subgroupOf.2 hs⟩, ?_⟩)).trans (Quotient.out_eq _)
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left, ← map_mul]
    simp [io_one_one]

theorem leftInv_negIntegrand {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) {s : ℂ}
    {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s) {f₁ f₂ : GA D V → ℂ} (hf₁ : LeftInv (GQ V) f₁)
    (hf₂ : LeftInv (GQ V) f₂) : LeftInv ((GQ V).prod (GQ V))
      (dblIntegrand V μ (fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂) := by
  rintro ⟨γ₁, γ₂⟩ ⟨h₁, h₂⟩ ⟨g₁, g₂⟩
  have hE : (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((γ₁, γ₂) * (g₁, g₂)))) =
      ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂)) := by
    refine (tsum_congr fun q => ?_).trans ((ioEquiv h₁ h₂).tsum_eq
      (fun q : NegCosets V => φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂))))
    show _ = φ ((((rmul _ ⟨io V (γ₁, γ₂), io_mem_GQ V h₁ h₂⟩ q.1).out : GQ (dblSp V)) : GA D (dblSp V)) *
      io V (g₁, g₂))
    rw [apply_out_rmul hμ hφ, map_mul, mul_assoc]
  show (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V ((γ₁, γ₂) * (g₁, g₂)))) *
      conj (f₁ (γ₁ * g₁)) * f₂ (γ₂ * g₂) * (μ (detA V (γ₂ * g₂)) : ℂ)⁻¹ =
    (∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * io V (g₁, g₂))) *
      conj (f₁ g₁) * f₂ g₂ * (μ (detA V g₂) : ℂ)⁻¹
  rw [hE, hf₁ γ₁ h₁, hf₂ γ₂ h₂, map_mul, map_mul, apply_detA hμ h₂, one_mul]

theorem integral_neg_eq_zero : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = 0 := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hc
  haveI := hm
  show ∫ x, dblIntegrandQ V μ (fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)) f₁ f₂ x
    ∂(autMeasure V m).prod (autMeasure V m) = 0
  set E : GA D (dblSp V) → ℂ := fun y => ∑' q : NegCosets V, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y)
    with hEdef
  by_cases hI : Integrable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m))
  swap
  · exact integral_undef hI
  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_negIntegrand hμ hφ h₁.1 h₂.1
  have hconv : DblConv V μ m E f₁ f₂ := ⟨hli, hI⟩
  have h𝓕 : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  set 𝓕 := stdDom (GQ V)
  obtain ⟨hint, heq⟩ := hconv.dblInt_eq h𝓕
  refine (heq : dblInt V μ m E f₁ f₂ = _).trans ?_
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  rw [← Measure.prod_restrict, integral_prod_symm _ hint]
  have hφc : Continuous φ := hφ.2.1
  have hcont : ∀ q : SiegelCosets V, Continuous
      (dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂) := fun q =>
    continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous h₂.continuous
  set G : SiegelCosets V → GA D V × GA D V → ENNReal := fun q x =>
    ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ with hGdef
  have hGm : ∀ q, Measurable (G q) := fun q => (hcont q).measurable.enorm
  have hfin := (GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂).1 𝓕 h𝓕
  rw [← Measure.prod_restrict, ← lintegral_tsum fun q => (hGm q).aemeasurable,
    lintegral_prod_symm _ (Measurable.ennreal_tsum hGm).aemeasurable] at hfin
  have hae := ae_lt_top (Measurable.ennreal_tsum hGm).lintegral_prod_left' hfin
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with g₂ hg₂
  set Φ : NegCosets V → GA D V → ℂ := fun y h =>
    dblIntegrand V μ (fun x => φ (((y.1.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ (h, g₂) with hΦdef
  have hpt : ∀ g₁, dblIntegrand V μ E f₁ f₂ (g₁, g₂) = ∑' y, Φ y g₁ := fun g₁ => by
    simp only [hΦdef, dblIntegrand, hEdef]
    rw [← tsum_mul_right, ← tsum_mul_right, ← tsum_mul_right]
  have hΦm : ∀ y, Measurable (Φ y) := fun y =>
    ((hcont y.1).comp (continuous_id.prodMk continuous_const)).measurable
  have hsum : ∑' y, ∫⁻ h, ‖Φ y h‖ₑ ∂(m.restrict 𝓕) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hg₂.ne ?_
    have hl := lintegral_tsum (μ := m.restrict 𝓕) (f := fun q h => G q (h, g₂))
      fun q => ((hGm q).comp measurable_prodMk_right).aemeasurable
    rw [hl]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun q => ∫⁻ h, G q (h, g₂) ∂(m.restrict 𝓕))
  rw [integral_congr_ae (.of_forall hpt), integral_tsum (fun y => (hΦm y).aestronglyMeasurable) hsum]
  refine GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero (GA D V) m (GQ V) (NegCosets V) 𝓕 h𝓕 Φ hΦm ?_ hsum ?_
  · intro γ y h
    have e : io V ((γ : GA D V)⁻¹, 1) * io V (γ * h, g₂) = io V (h, g₂) := by
      rw [← map_mul]; simp
    simp only [hΦdef, dblIntegrand]
    rw [h₁.1 _ γ.2, smul_val, apply_out_rmul hμ hφ, mul_assoc _ _ (io V _)]
    erw [e]
  · intro y 𝓖 h𝓖 hi
    exact GlobalTheory.T.doublingNegligibleOrbit_unfoldedIntegral_eq_zero D V a μ hμ s φ hφ _ (y.1.out).2 y.2 f₁ f₂ h₁.continuous h₂.continuous h₁.1 hc g₂ _
      (mem_map_stabilizer_iff y) m hm 𝓖 h𝓖 hi

end GlobalTheory.Core.Rk.NegOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ErrXSPiAndVal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Core GlobalTheory.Core.Cls NumberField IsDedekindDomain GlobalTheory.Mem.Db Formalism.L2 Formalism.L2.Ker Formalism.L2.Forms

namespace GlobalTheory.Core.Cls

theorem errXS_pi_and_val : ∀ (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z), (Formalism.L2.Herm.toErrXS b.t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS b.t.full.1).piT = w.px.piT ∧ Formalism.L2.Host.ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
  intro K B f T w Z b
  have hc : b.t.full.1.cols = b.t.C.herm := b.t.full.2
  refine ⟨?_, ?_, ?_⟩
  · show (b.t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = _
    rw [hc, ← b.t.C.piG]
    exact (b.t.std _).gl.piG
  · funext u
    show (b.t.full.1.cols.atT u).piU = _
    rw [hc, ← b.t.C.piU u]
    exact (b.t.std u).piU
  · rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
    subst C_eq
    exact val _ _ _ _ _ _

end GlobalTheory.Core.Cls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_nhds_one_adelicMatrixCongruentOneAtPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n N : ℕ) (P : HeightOneSpectrum (𝓞 E)), letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, GlobalTheory.TwU.CongAt P N u := by
  first | exact @GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one | exact GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one | (intros; apply GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_point_carrying_lattice_and_frames : ∀ (D : D7) (V : HSp D) (Λ L₀ : Lat V) (β : GL (Fin V.rank) (Lev.EAf D)), IsSelfDualC V Λ → IsSelfDualC V L₀ → ∀ (J : Type) [Fintype J] (k : J → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ M : ∀ i, GL (Fin V.rank) (k i), ∃ t ∈ GfC V, ∃ L : Lat V, IsSelfDualC V L ∧ (∀ P, Moves V t Λ L P) ∧ (∀ v, (∀ i, v ≠ (q i).v) → latV V L (· = v) = latV V L₀ (· = v)) ∧ ∀ i, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V t β (M i).val := by
  first | exact @GlobalTheory.FinPl.BasePoint.exists_move | exact GlobalTheory.FinPl.BasePoint.exists_move | (intros; apply GlobalTheory.FinPl.BasePoint.exists_move <;> assumption)
end

