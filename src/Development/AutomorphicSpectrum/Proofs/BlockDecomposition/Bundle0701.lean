import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0688
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

section Abstract

variable {G : Type} [Group G]

def dcos (Q P : Subgroup G) (x : G) : Set G := {g | ∃ q ∈ Q, ∃ p ∈ P, g = q * x * p}

def LocSec [TopologicalSpace G] (Q P : Subgroup G) (x : G) : Prop :=
  ∀ OQ ∈ 𝓝 (1 : G), ∀ OP ∈ 𝓝 (1 : G), ∃ O ∈ 𝓝 (1 : G), ∀ u ∈ O, x * u ∈ dcos Q P x →
    ∃ s ∈ Q, s ∈ OQ ∧ ∃ p ∈ P, p ∈ OP ∧ x * u = s * x * p

variable [TopologicalSpace G] [IsTopologicalGroup G]
  {W₁ W₂ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]

def resInd {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v)) :
    smoothPart (ind Q σ) →ₗ[ℂ] smoothPart (ind H τ) where
  toFun f := ⟨⟨fun p => E (f.1.1 (x * (p : G))), by
      intro h p
      have hq := (hH h).1 h.2
      have e : x * (((h * p : P)) : G) = (⟨_, hq⟩ : Q) * (x * (p : G)) := by
        simp [mul_assoc]
      show E (f.1.1 (x * (((h : P) * p : P) : G))) = τ h (E (f.1.1 (x * (p : G))))
      rw [hE h hq, show x * (((h : P) * p : P) : G) = ((⟨_, hq⟩ : Q) : G) * (x * (p : G)) from e]
      exact congrArg E (f.1.2 _ _)⟩, by
      have hf : IsOpen {g : G | ind Q σ g f.1 = f.1} := f.2
      have hopen : IsOpen {p : P | ind Q σ (p : G) f.1 = f.1} := hf.preimage continuous_subtype_val
      refine mem_smoothPart_of_nhds ?_
      filter_upwards [hopen.mem_nhds (by simp)] with p hp
      refine Subtype.ext (funext fun y => ?_)
      have := congrArg (fun F : indSpace Q σ => F.1 (x * (y : G))) hp
      show E (f.1.1 (x * ((y * p : P) : G))) = E (f.1.1 (x * (y : G)))
      rw [show x * ((y * p : P) : G) = x * (y : G) * (p : G) by simp [mul_assoc]]
      exact congrArg E this⟩
  map_add' a b := by
    refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    exact map_add E _ _
  map_smul' c a := by
    refine Subtype.ext (Subtype.ext (funext fun p => ?_))
    exact map_smul E _ _

@[simp] theorem resInd_apply {Q P : Subgroup G} {x : G} (σ : Representation ℂ Q W₁) (H : Subgroup P)
    (hH : ∀ p : P, p ∈ H ↔ x * (p : G) * x⁻¹ ∈ Q) (τ : Representation ℂ H W₂) (E : W₁ ≃ₗ[ℂ] W₂)
    (hE : ∀ (h : H) (hq : x * ((h : P) : G) * x⁻¹ ∈ Q) (v : W₁), τ h (E v) = E (σ ⟨_, hq⟩ v))
    (f : smoothPart (ind Q σ)) (p : P) :
    (resInd σ H hH τ E hE f).1.1 p = E (f.1.1 (x * (p : G))) := rfl

end Abstract

section Concrete

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def eGPg {m j n : ℕ} (h : m + j = n) : (Σ x, Two (Fin m) (Fin (j + 1)) x) ≃ Fin (n + 1) :=
  two (stdSum (by omega))

def HGPg {m j n : ℕ} (h : m + j = n) : Subgroup (Mir k n) := (parab k (eGPg h)).comap (Mir k n).subtype

def hgpInclg {m j n : ℕ} (h : m + j = n) : HGPg k h →* parab k (eGPg h) where
  toFun g := ⟨((g : Mir k n) : GL (Fin (n + 1)) k), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hgpg_block_mem {m j n : ℕ} (h : m + j = n) (g : HGPg k h) :
    (leviProj k (eGPg h) (hgpInclg k h g) true : GL (Fin (j + 1)) k) ∈ Mir k j := by
  subst h
  exact hgp_block_mem _ _ g

def gpProjg {m j n : ℕ} (h : m + j = n) : HGPg k h →* GL (Fin m) k × Mir k j :=
  MonoidHom.prod ((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) false).comp
      ((leviProj k (eGPg h)).comp (hgpInclg k h)))
    (((Pi.evalMonoidHom (fun x => GL (Two (Fin m) (Fin (j + 1)) x) k) true).comp
      ((leviProj k (eGPg h)).comp (hgpInclg k h))).codRestrict (Mir k j) (hgpg_block_mem k h))

def wPerm {i t : ℕ} (h : (i + 1) + t = i + t + 1) : Equiv.Perm (Fin (i + t + 1)) :=
  (two (stdSum h)).symm.trans (ePG i t)

def wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) : GL (Fin (i + t + 1)) k where
  val := (1 : Matrix _ _ k).submatrix (wPerm h) id
  inv := (1 : Matrix _ _ k).submatrix id (wPerm h)
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, mul_one]
    exact Matrix.submatrix_one_equiv (wPerm h)
  inv_val := by
    rw [← Matrix.submatrix_mul _ _ _ (wPerm h) _ (wPerm h).bijective, mul_one]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

end Concrete

section Inducing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

abbrev sQ {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (parab k (two (stdSum h))) (⨂[ℂ] x, TwoT V W x) :=
  (twist (piTensor (twoRep π₁ π₂)) (deltaHalf k (Two (Fin r) (Fin t)))).comp (leviProj k (two (stdSum h)))

abbrev tE (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    (⨂[ℂ] x, TwoT V W x) ≃ₗ[ℂ] V ⊗[ℂ] W :=
  Exponents.boolTensorEquiv (X := TwoT V W)

end Inducing

section Row

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_updateRow_one {N : ℕ} (a : Fin N) (y : Fin N → k) :
    ((1 : Matrix (Fin N) (Fin N) k).updateRow a y).det = y a := by
  have h := Matrix.cramer_apply (1 : Matrix (Fin N) (Fin N) k) y a
  rw [Matrix.cramer_one] at h
  have e : ((1 : Matrix (Fin N) (Fin N) k).updateCol a y) = ((1 : Matrix (Fin N) (Fin N) k).updateRow a y)ᵀ := by
    rw [← Matrix.updateCol_transpose, Matrix.transpose_one]
  rw [e, Matrix.det_transpose] at h
  simpa using h.symm

theorem exists_rowSec {N : ℕ} (a : Fin N) : ∃ b : (Fin N → k) → GL (Fin N) k,
    ContinuousAt b (Pi.single a 1) ∧ b (Pi.single a 1) = 1 ∧
      ∀ y : Fin N → k, y a ≠ 0 → (b y : Matrix (Fin N) (Fin N) k) = (1 : Matrix (Fin N) (Fin N) k).updateRow a y := by
  classical
  let M : (Fin N → k) → Matrix (Fin N) (Fin N) k := fun y => (1 : Matrix (Fin N) (Fin N) k).updateRow a y
  have hM : Continuous M := by
    refine continuous_matrix fun c d => ?_
    by_cases h : c = a
    · subst h
      simpa [M] using continuous_apply d
    · simpa [M, Matrix.updateRow_ne h] using continuous_const
  have hdet : ∀ y, (M y).det = y a := fun y => det_updateRow_one a y
  let b : (Fin N → k) → GL (Fin N) k := fun y =>
    if h : y a ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (M y) (by rw [hdet]; exact h) else 1
  have hb : ∀ y : Fin N → k, y a ≠ 0 → (b y : Matrix (Fin N) (Fin N) k) = M y := fun y h => by
    simp only [b, dif_pos h]
    rfl
  have h0 : (Pi.single a 1 : Fin N → k) a ≠ 0 := by simp
  have hne : ∀ᶠ y : Fin N → k in 𝓝 (Pi.single a 1), y a ≠ 0 :=
    (continuous_apply a).continuousAt.eventually_ne h0
  refine ⟨b, ?_, ?_, hb⟩
  · rw [Units.isInducing_embedProduct.continuousAt_iff]
    have h1 : ContinuousAt (fun y => (b y : Matrix (Fin N) (Fin N) k)) (Pi.single a 1) :=
      hM.continuousAt.congr (hne.mono fun y h => (hb y h).symm)
    have h2 : ContinuousAt (fun y => (((b y)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) (Pi.single a 1) := by
      have h3 : ContinuousAt (fun y : Fin N → k => (y a)⁻¹ • (M y).adjugate) (Pi.single a 1) :=
        ((continuous_apply a).continuousAt.inv₀ h0).smul hM.matrix_adjugate.continuousAt
      refine h3.congr (hne.mono fun y h => ?_)
      show (y a)⁻¹ • (M y).adjugate = (((b y)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
      rw [Matrix.coe_units_inv, hb y h, Matrix.inv_def, hdet, Ring.inverse_eq_inv]
    exact h1.prodMk (MulOpposite.continuous_op.continuousAt.comp h2)
  · ext1
    rw [hb _ h0]
    show (1 : Matrix (Fin N) (Fin N) k).updateRow a (Pi.single a 1) = 1
    ext c d
    by_cases h : c = a
    · subst h
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.updateRow_ne h]

end Row

end GlobalTheory.CompanionTheory.BZRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumQuadraticCharacterBoundStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_sum_quadratic_character_bound : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ) (B : X → X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) →
    (∀ x y, q (x + y) = q x * q y * B x y) →
    (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y y', B x (y + y') = B x y * B x y') →
    ∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤
      (m (L : Set X)).toReal * (m {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1}).toReal := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_sq_compact_open | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_sq_compact_open | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.weyl_sq_compact_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralConvergenceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_zeta_integral_convergence : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4 := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.functional_equation | exact GlobalTheory.CompanionTheory.RSZeta.functional_equation | (intros; apply GlobalTheory.CompanionTheory.RSZeta.functional_equation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem continuous_lineDer_of_growth (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : GlobalTheory.UAut.IsSm σ J φ) (hc : Continuous φ)
    {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {A : ℕ} {B : ℝ}
    (hB : ∀ g, ‖lineDer γ (lineDer γ φ) g‖ ≤ B * (height σ J g : ℝ) ^ A) : Continuous (lineDer γ φ) := by
  have hpos : ∀ g, 0 < (height σ J g : ℝ) := fun g =>
    zero_lt_one.trans_le (by exact_mod_cast GlobalTheory.AdelicU.one_le_height σ J g)
  have hB0 : 0 ≤ B := (mul_nonneg_iff_of_pos_right (pow_pos (hpos 1) A)).1 ((norm_nonneg _).trans (hB 1))
  have hγc : Continuous γ := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ
  have hht : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp (GlobalTheory.AdelicU.continuous_height_GAd σ J)
  obtain ⟨c, hc'⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (hht.comp hγc)).bddAbove
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ g, ‖lineDer γ φ g - t⁻¹ • (φ (g * γ t) - φ g)‖ ≤
      B * ((height σ J g : ℝ) * c) ^ A * t := fun t t0 t1 g => by
    set q := t⁻¹ • (φ (g * γ t) - φ g) with hq
    have d1 := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hγ g
    have d2 := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := [γ]) (by simpa using hγ) hγ g
    simp only [List.foldr_cons, List.foldr_nil] at d1 d2
    have := GlobalTheory.CuspDecay.mul_norm_deriv_le (f := fun s => φ (g * γ s) - φ g - s • q)
      (f₁ := fun s => lineDer γ φ (g * γ s) - q) (f₂ := fun s => lineDer γ (lineDer γ φ) (g * γ s))
      (fun s => by simpa using ((d1 s).sub_const (φ g)).fun_sub ((hasDerivAt_id s).smul_const q))
      (fun s => (d2 s).sub_const q) t0.le (B := B * ((height σ J g : ℝ) * c) ^ A) fun s hs' => (hB _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos _).le
          ((NNReal.coe_le_coe.2 (GlobalTheory.AdelicU.height_mul_le σ J _ _)).trans (by
            rw [NNReal.coe_mul]
            exact mul_le_mul_of_nonneg_left (hc' ⟨s, ⟨hs'.1, hs'.2.trans t1⟩, rfl⟩) (hpos g).le)) A) hB0)
    rw [GlobalTheory.UAut.ConstAut.realLine_zero h hγ, mul_one, hq, smul_inv_smul₀ t0.ne', sub_self, sub_self, zero_smul, sub_self,
      norm_zero, zero_add, zero_add, mul_comm _ t] at this
    exact le_of_mul_le_mul_left this t0
  refine continuous_of_locally_uniform_approx_of_continuousAt fun x u hu => ?_
  obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.1 hu
  have hb : Continuous fun g : GAd σ J => B * ((height σ J g : ℝ) * c) ^ A :=
    continuous_const.mul ((hht.mul continuous_const).pow A)
  obtain ⟨t, t0, t1, t2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ B * ((height σ J x : ℝ) * c) ^ A * t < ε := by
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1 ∧ B * ((height σ J x : ℝ) * c) ^ A * t < ε :=
      eventually_mem_nhdsWithin.and (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((eventually_le_nhds zero_lt_one).and
          ((continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const (by simpa using hε))))
    exact this.exists
  refine ⟨_, (isOpen_lt (hb.mul (continuous_const (y := t))) (continuous_const (y := ε))).mem_nhds t2,
    fun g => t⁻¹ • (φ (g * γ t) - φ g),
    (((hc.comp (continuous_mul_right _)).sub hc).const_smul t⁻¹).continuousAt, fun y hy => hu ?_⟩
  rw [dist_eq_norm]
  exact (key t t0 t1 y).trans_lt hy

theorem lineDer_mul_fin {φ : GAd σ J → ℂ} {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) {k : GAd σ J} (hk : k ∈ finPts σ J)
    (e : ∀ g, φ (g * k) = φ g) (g : GAd σ J) : lineDer γ φ (g * k) = lineDer γ φ g := by
  have : (fun t => φ (g * k * γ t)) = fun t => φ (g * γ t) := funext fun t => by
    have hc := GlobalTheory.CompanionTheory.SiegelAssemble.commute_of_mem (GlobalTheory.RealLineInf.realLine_mem_infPts F E σ n J γ hγ t) hk
    rw [mul_assoc, ← hc.eq, ← mul_assoc, e]
  simp only [lineDer, this]

theorem isCuspidal_lineDer (h : IsCMExt F E σ) (hJ : IsHermND σ J) {φ : GAd σ J → ℂ} (hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) φ)
    (hc : Continuous φ) (hs : GlobalTheory.UAut.IsSm σ J φ) (hcu : IsCuspidal σ J φ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (hc' : Continuous (lineDer γ φ)) : IsCuspidal σ J (lineDer γ φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 x
  have hI : GlobalTheory.UAut.IsIsoCols σ J C := hC.2
  haveI := GlobalTheory.UAut.locallyCompact_unipRad h hJ hI
  have hco := GlobalTheory.UAut.cocompact_unipRad h hJ hI
  have hl' : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J) (lineDer γ φ) := GlobalTheory.UAut.ConstAut.leftInv_foldr hl [γ]
  have h0 : ∀ y, GlobalTheory.Cusp.constTermOn (ratPts σ J) (unipRad σ J C) φ y = 0 := fun y =>
    (hco.constTermOn_eq_zero_iff h𝓕 hl y).2 (hcu r C hC μ 𝓕 hμ h𝓕 y)
  have hd := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco hl hc hl' hc'
    (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ)
    (GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hγ) x
  simp only [h0] at hd
  rw [GlobalTheory.UAut.ConstAut.realLine_zero h hγ, mul_one] at hd
  exact (hco.constTermOn_eq_zero_iff h𝓕 hl' x).1 (hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))

theorem good_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  intro F E _ _ _ _ _ σ h n J hJ U A φ γ hφ hγ
  obtain ⟨B, hB⟩ := hφ.growth [γ, γ] (by simpa using hγ)
  have hcont : Continuous (lineDer γ φ) :=
    continuous_lineDer_of_growth h hφ.smooth hφ.cont hγ (A := A) (B := B) (by simpa using hB)
  refine ⟨GlobalTheory.UAut.ConstAut.leftInv_foldr hφ.left [γ], fun k hk hf => lineDer_mul_fin hγ hf (hφ.level k hk hf), hcont,
    GlobalTheory.UAut.isSm_lineDer hφ.smooth hγ, fun l hl => ?_,
    isCuspidal_lineDer h hJ hφ.left hφ.cont hφ.smooth hφ.cusp hγ hcont⟩
  have := hφ.growth (l ++ [γ]) (by
    intro δ hδ
    rcases List.mem_append.1 hδ with e | e
    · exact hl δ e
    · rw [List.mem_singleton.1 e]; exact hγ)
  simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using this

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIndicatorFormula
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.TjChar

open GlobalTheory.WeylGL (tor tor_val tor_add tor_const_comm IntM intM_tor intM_doset)

theorem sum_ite_lt (n m : ℕ) : ∑ j : Fin n, (if (j : ℕ) < m then (1 : ℤ) else 0) = min (n : ℤ) m := by
  rw [Finset.sum_boole, Fin.card_filter_val_lt]
  push_cast
  rfl

theorem antitone_eq {n k : ℕ} {a : Fin n → ℤ} (ha : Antitone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1)
    (hs : ∑ i, a i = (k : ℤ)) (i : Fin n) : a i = if (i : ℕ) < k then 1 else 0 := by
  have hi := i.2
  have hc : a i = 0 ∨ a i = 1 := by
    have := h0 i
    have := h1 i
    omega
  rcases hc with hc | hc
  · have hle : ∑ j, a j ≤ ∑ j : Fin n, (if (j : ℕ) < (i : ℕ) then (1 : ℤ) else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj
      · exact h1 j
      · have : a j ≤ a i := ha (Fin.le_def.2 (by omega))
        omega
    rw [hs, sum_ite_lt] at hle
    have : k ≤ (i : ℕ) := by omega
    rw [hc, if_neg (by omega)]
  · have hle : ∑ j : Fin n, (if (j : ℕ) < (i : ℕ) + 1 then (1 : ℤ) else 0) ≤ ∑ j, a j := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj
      · have : a i ≤ a j := ha (Fin.le_def.2 (by omega))
        omega
      · exact h0 j
    rw [hs, sum_ite_lt] at hle
    have : (i : ℕ) < k := by
      push_cast at hle
      omega
    rw [hc, if_pos this]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {ϖ : w.adicCompletion E}

theorem ordL_eq_of_v {x : w.adicCompletion E} {m : ℤ} (h : Valued.v x = WithZero.exp (-m)) : ordL x = m := by
  have hx : Valued.v x ≠ 0 := by
    rw [h]
    exact WithZero.exp_ne_zero
  have e : WithZero.unzero hx = Multiplicative.ofAdd (-m) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  unfold ordL
  rw [dif_neg hx, e]
  simp

theorem v_zpow_eq (hu : IsUnifV E w ϖ) (m : ℤ) : Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hu]
  have : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := rfl
  rw [this, ← WithZero.exp_zsmul]
  simp

theorem v_prod_zpow (hu : IsUnifV E w ϖ) (a : Fin n → ℤ) (s : Finset (Fin n)) :
    Valued.v (∏ i ∈ s, ϖ ^ a i) = WithZero.exp (-∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, map_mul, ih, v_zpow_eq hu, ← WithZero.exp_add]
    congr 1
    ring

theorem ordL_det (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    ordL (c * tor h0 a * d : GL (Fin n) (w.adicCompletion E)).val.det = ∑ i, a i := by
  apply ordL_eq_of_v
  have h1 : Valued.v c.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hc
  have h2 : Valued.v d.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hd
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, h1, h2, tor_val,
    Matrix.det_diagonal, v_prod_zpow hu]
  simp

theorem tor_inv (h0 : ϖ ≠ 0) (a : Fin n → ℤ) : (tor h0 a)⁻¹ = tor h0 (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← tor_add]
  ext1
  simp [tor_val]

theorem tor_one_val (h0 : ϖ ≠ 0) (x : GL (Fin n) (w.adicCompletion E)) :
    (tor h0 (fun _ => 1) * x : GL (Fin n) (w.adicCompletion E)).val = ϖ • x.val := by
  ext i j
  simp [tor_val, Matrix.diagonal_mul]

theorem intM_iff {c d x y : GL (Fin n) (w.adicCompletion E)} (hc : c ∈ GLint (Fin n) (Ov E w))
    (hd : d ∈ GLint (Fin n) (Ov E w)) (e : x = c * y * d) : IntM x ↔ IntM y :=
  ⟨fun h => intM_doset h ⟨c⁻¹, Subgroup.inv_mem _ hc, d⁻¹, Subgroup.inv_mem _ hd, by rw [e]; group⟩,
    fun h => intM_doset h ⟨c, hc, d, hd, e⟩⟩

theorem isInt_iff (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    IsInt w (c * tor h0 a * d : GL (Fin n) (w.adicCompletion E)).val ↔ ∀ i, 0 ≤ a i :=
  (intM_iff hc hd rfl).trans (intM_tor h0 hu a)

theorem isInt_dual_iff (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    IsInt w (ϖ • ((c * tor h0 a * d : GL (Fin n) (w.adicCompletion E))⁻¹).val) ↔ ∀ i, a i ≤ 1 := by
  rw [← tor_one_val h0]
  have e : tor h0 (fun _ => 1) * (c * tor h0 a * d)⁻¹ = d⁻¹ * tor h0 ((fun _ => 1) + -a) * c⁻¹ := by
    rw [tor_add, _root_.mul_inv_rev, _root_.mul_inv_rev, tor_inv, ← mul_assoc (tor h0 fun _ => 1) d⁻¹, tor_const_comm]
    group
  have h := (intM_iff (Subgroup.inv_mem _ hd) (Subgroup.inv_mem _ hc) e).trans (intM_tor h0 hu _)
  refine h.trans (forall_congr' fun i => ?_)
  simp

end GlobalTheory.CompanionTheory.CtS.TjChar

namespace GlobalTheory.CompanionTheory.CtS

open GlobalTheory.CompanionTheory.CtS.TjChar in

theorem Tj_eq_ite : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n k : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → k ≤ n → ∀ g : GL (Fin n) (w.adicCompletion E), Tj ℂ n (Ov E w) ϖ k g = if IsInt w g.val ∧ IsInt w (ϖ • (g⁻¹).val) ∧ ordL g.val.det = (k : ℤ) then 1 else 0 := by
  intro E _ _ w n k ϖ hu hk g
  have h0 : ϖ ≠ 0 := fun h => by simp [IsUnifV, h] at hu
  rw [GlobalTheory.WeylGL.Tj_eq h0 k]
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨a, ha, c, hc, d, hd, rfl⟩ := GlobalTheory.WeylGL.cartan h0 hu g
    have ha0 := (isInt_iff h0 hu hc hd a).1 h1
    have ha1 := (isInt_dual_iff h0 hu hc hd a).1 h2
    rw [ordL_det h0 hu hc hd] at h3
    have e : a = fun i : Fin n => if (i : ℕ) < k then 1 else 0 :=
      funext (antitone_eq ha ha0 ha1 h3)
    subst e
    exact GlobalTheory.WeylGL.dosetInd_of_mem ⟨c, hc, d, hd, rfl⟩
  · refine GlobalTheory.WeylGL.dosetInd_of_not ?_
    rintro ⟨c, hc, d, hd, rfl⟩
    refine h ⟨(isInt_iff h0 hu hc hd _).2 fun i => ?_, (isInt_dual_iff h0 hu hc hd _).2 fun i => ?_, ?_⟩
    · split_ifs <;> omega
    · split_ifs <;> omega
    · rw [ordL_det h0 hu hc hd, sum_ite_lt, min_eq_right (by exact_mod_cast hk)]

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundSiegelTorusStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_siegel_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ c : ℝ, 0 < c → ∃ b : ℕ, ∀ Ω Cm : Set (GAd σ J), IsCompact Ω → IsCompact Cm → ∃ H : ℝ, 0 ≤ H ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, (height σ J (p * a * k) : ℝ) ≤ H * rbar t ^ b := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.height_le_rbar_pow | exact GlobalTheory.CompanionTheory.RapidDecay.height_le_rbar_pow | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.height_le_rbar_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvarianceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_hermitian_invariance : PositivityTheory.SiegelWeilFormula.Gunr.HermitianLatticeInvariance := by
  first | exact @GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian | exact GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian | (intros; apply GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian <;> assumption)
end

