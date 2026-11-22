import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompFinIdemSum

variable {D : D7}

theorem compFin_tensAt_ne {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E u (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    have h0 : evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) = 0 := evalV_singleFin_ne h a
    have h1 : compFin D.host.F D.host.E u (pairA D.host.F 0 (singleFin v a) ⊗ₜ[D.host.F] x) =
        evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) ⊗ₜ[D.host.F] x :=
      Algebra.TensorProduct.map_tmul ..
    rw [h1, h0, TensorProduct.zero_tmul]
  | add y z hy hz => simp only [map_add, hy, hz, add_zero]

set_option maxHeartbeats 1000000 in
open Classical in

theorem compFin_add_cA_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z,
    compFin D.host.F D.host.E (PP.under (𝓞 D.host.F)) (e + cA D e) = 1 := by
  intro D Z e he PP hPP
  classical
  obtain ⟨⟨es, hes, rfl⟩, hcc⟩ := he
  obtain ⟨v0, τ0, -, hPP0⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes PP hPP)
  have hu : PP.under (𝓞 D.host.F) = v0 := by rw [hPP0]; exact splitPrime_under τ0
  rw [hu]
  have key : ∀ Q ∈ Z, compFin D.host.F D.host.E v0 (es Q) =
      (if Q = PP then splitIdem (isCMExt_host D) τ0 else 0) +
        (if Q = splitPrime (τ0.comp D.sp.cm.sig) then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    intro Q hQ
    obtain ⟨v, τ, hI, hQτ⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes Q hQ)
    have hQv : Q.under (𝓞 D.host.F) = v := by rw [hQτ]; exact splitPrime_under τ
    rw [GlobalTheory.SplitIdemDict.eq_idem hI, GlobalTheory.EmbChart.idem]
    by_cases hv : v = v0
    · subst hv
      rcases eq_or_eq_comp_conj (isCMExt_host D) τ0 τ with h | h <;> rw [h] at hQτ ⊢
      · rw [if_pos (hQτ.trans hPP0.symm), if_neg (by rw [hQτ]; exact (splitPrime_comp_ne (isCMExt_host D) τ0).symm),
          add_zero]
        exact GlobalTheory.EmbChart.compFin_tensAt _ _
      · rw [if_neg (by rw [hQτ, hPP0]; exact splitPrime_comp_ne (isCMExt_host D) τ0), if_pos hQτ, zero_add,
          GlobalTheory.EmbChart.compFin_tensAt, splitIdem_comp]
    · have h1 : Q ≠ PP := fun h => hv (by rw [← hQv, h, hu])
      have h2 : Q ≠ splitPrime (τ0.comp D.sp.cm.sig) := fun h => hv (by rw [← hQv, h]; exact splitPrime_under _)
      rw [if_neg h1, if_neg h2, add_zero]
      exact compFin_tensAt_ne (Ne.symm hv) _
  have hsum : compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q) = splitIdem (isCMExt_host D) τ0 +
      (if splitPrime (τ0.comp D.sp.cm.sig) ∈ Z then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    rw [map_sum, Finset.sum_congr rfl key]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos hPP]
  have hc : compFin D.host.F D.host.E v0 (cA D (∑ Q ∈ Z, es Q)) =
      sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q)) :=
    (GlobalTheory.SplitIdemDict.compFin_cA _).symm
  have h1 : ∀ a : Fv D.host.F v0 ⊗[D.host.F] D.host.E, a + (1 - a) = 1 := fun a => by abel
  rw [map_add, hc, hsum]
  by_cases hP' : splitPrime (τ0.comp D.sp.cm.sig) ∈ Z
  · exfalso
    have hz := congrArg (compFin D.host.F D.host.E v0) hcc
    rw [map_mul, hc, hsum, if_pos hP', h1, map_one, mul_one, map_zero] at hz
    have h3 := congrArg (fun y => splitProj τ0 y) hz
    simp only [map_one, map_zero] at h3
    exact one_ne_zero h3
  · rw [if_neg hP', add_zero, sigR_splitIdem, h1]

end GlobalTheory.CompFinIdemSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixAddIntegralReductionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointFrameMatrix_add_integral_reduction : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T),
  IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapAdj S T βS βT y) →
  IsIntM (frMapAdj S T βS βT (x + y)) ∧
  ∀ PP : Pl D.host.E, redM PP (frMapAdj S T βS βT (x + y)) = redM PP (frMapAdj S T βS βT x) + redM PP (frMapAdj S T βS βT y) := by
  first | exact @GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM | exact GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM | (intros; apply GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareComm

variable {D : D7}

theorem blkGL_mem (V V₁ : HSp D) (g : GA D V × GA D V₁) :
    blkGL finSumFinEquiv (g.1.1, g.2.1) ∈ HR (AF D.host.F) D.sp.cm.sig (hsum V V₁).gram := by
  have hJ : JR (F := D.host.F) (AF D.host.F) (hsum V V₁).gram =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) V.gram) (JR (F := D.host.F) (AF D.host.F) V₁.gram) := by
    unfold JR
    rw [gram_hsum]
    exact blkMat_map _ _ (map_zero _) _ _
  unfold HR
  rw [hJ]
  exact (blkGL_mem_UJ finSumFinEquiv).2 ⟨g.1.2, g.2.2⟩

def blk (V V₁ : HSp D) : GA D V × GA D V₁ →* GA D (hsum V V₁) where
  toFun g := ⟨blkGL finSumFinEquiv (g.1.1, g.2.1), blkGL_mem V V₁ g⟩
  map_one' := Subtype.ext (map_one (blkGL finSumFinEquiv))
  map_mul' g h := Subtype.ext (map_mul (blkGL finSumFinEquiv) (g.1.1, g.2.1) (h.1.1, h.2.1))

theorem mt_blk (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁) :
    Formalism.L2.Theta.mt (hsum V V₁) (blk V V₁ (g, g₁)) =
      blkMat finSumFinEquiv (Formalism.L2.Theta.mt V g) (Formalism.L2.Theta.mt V₁ g₁) := rfl

theorem continuous_blk (V V₁ : HSp D) : Continuous (blk V V₁) := by
  apply Continuous.subtype_mk
  exact (continuous_blkGL finSumFinEquiv).comp (continuous_subtype_val.prodMap continuous_subtype_val)

def frSgn (ε : Bool) {V : HSp D} (A : Fr V) : Fr (sgn ε V) where
  ε τ a := xor ε (A.ε τ a)
  fr := A.fr
  fr_unit := A.fr_unit
  fr_gram τ := by
    cases ε
    · simp only [Bool.false_xor]; exact A.fr_gram τ
    · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
      have e' : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
        ext a b
        by_cases h : a = b
        · subst h; cases h' : A.ε τ a <;> simp [Formalism.REAL.Jm, h']
        · simp [Formalism.REAL.Jm, h]
      show (A.fr τ)ᴴ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = gramAt D (neg V) τ
      rw [e, e', ← A.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

def frSum {V V₁ : HSp D} (A : Fr V) (B : Fr V₁) : Fr (hsum V V₁) where
  ε τ := Fin.append (A.ε τ) (B.ε τ)
  fr τ := blkMat finSumFinEquiv (A.fr τ) (B.fr τ)
  fr_unit τ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_blkMat]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)).mul ((Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ))
  fr_gram τ := by
    have e : gramAt D (hsum V V₁) τ = blkMat finSumFinEquiv (gramAt D V τ) (gramAt D V₁ τ) := by
      unfold gramAt
      rw [gram_hsum]; exact blkMat_map _ _ (map_zero _) _ _
    have e' : Formalism.REAL.Jm (Fin.append (A.ε τ) (B.ε τ)) =
        blkMat finSumFinEquiv (Formalism.REAL.Jm (A.ε τ)) (Formalism.REAL.Jm (B.ε τ)) := by
      refine submatrix_inj finSumFinEquiv ?_
      rw [submatrix_blkMat]
      ext (a | a) (b | b) <;> simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Fin.ext_iff] <;> omega
    have e'' : (blkMat finSumFinEquiv (A.fr τ) (B.fr τ))ᴴ = blkMat finSumFinEquiv (A.fr τ)ᴴ (B.fr τ)ᴴ := by
      simp [GlobalTheory.Doubling.blkMat, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
    rw [e, e', e'', blkMat_mul, blkMat_mul, A.fr_gram, B.fr_gram]

section Vec

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)

def IsFinF (f : WO M X → ℂ) : Prop := IsVacF ψ θ (frSgn ε A) B f

def fockF (f : WO M X → ℂ) : PolF D X.rank M.rank →ₗ[ℂ] (WO M X → ℂ) :=
  pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart A.onb B.onb f

def algF : Submodule ℂ (WO M X → ℂ) := Submodule.span ℂ {Φ | ∃ f P, IsFinF ψ θ ε A B f ∧ Φ = fockF ψ θ ε A B f P}

end Vec

def IsHaarFD (M : HSp D) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ M) 𝓕 ν

def thetaInt {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ : WO M X → ℂ) (h : GA D X) : ℂ :=
  ∫ g in 𝓕, thetaKO ω g h Φ ∂ν

def ModInt (θ : InfFam D) {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ : WO M X → ℂ) : Prop :=
  ∃ (N : ℕ) (C : ℝ), ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν ∧
    ∫ g in 𝓕, ‖thetaKO ω g h Φ‖ ∂ν ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N

def finRel {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) : Submodule ℂ (WO M X → ℂ) :=
  Submodule.span ℂ {Φ | ∃ u ∈ GfC M, ∃ Ψ ∈ S, Φ = ω (u, 1) Ψ - Ψ}

structure IsTriple (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle) : Prop where

  hecA : IsHeckeChar D α

  hecB : IsHeckeChar D β

  resA : ResEta D α W₁.rank

  resB : ResEta D β W.rank

  rank : X.rank = W.rank + W₁.rank

  even : Even X.rank

  sig : ∃ p q : ℕ, (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q ∧
      Formalism.UG.HasSignature (gramAt D X τ) (X.rank - (p + q)) (p + q)) ∧
    W₁.rank + 2 * (2 * (p + q) + 1) < W.rank ∧ 2 * (p + q) + 1 < W₁.rank

  gap : ∀ τ, ∃ a b : ℚ, HasInfExp D α τ a ∧ HasInfExp D β τ b ∧ 2 * (a - b) < -(X.rank : ℚ)

  ram : ∀ v e, IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e α ∧ GlobalTheory.WeilParts.UnramAt e β) ∨
    (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (α / β) ∧
      ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F))

structure IsMatch (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) : Prop where

  weilA : IsWeil ψ true W X β (β / α) ωA

  weilB : IsWeil ψ false W₁ X α (α / β) ωB

  irred : IsIrred X Pi rf rl

  mapA : IsCoinvMap θ ωA (algF ψ θ true A B) Pi rf rl p

  mapB : IsCoinvMap θ ωB (algF ψ θ false A₁ B) Pi rf rl p'

end GlobalTheory.SquareComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedAutomorphicRightTranslationUnitarisableBo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {V : HSp D} {ν : Measure (GA D V)} {𝓕 : Set (GA D V)}

private theorem zero_one_mem_gammaSet_one (f : bddAut V) : Continuous (f : GA D V → ℂ) ∧
    (∀ γ ∈ GQ V, ∀ g, (f : GA D V → ℂ) (γ * g) = (f : GA D V → ℂ) g) ∧
    ∃ C : ℝ, ∀ g, ‖(f : GA D V → ℂ) g‖ ≤ C := f.2

private theorem integrableOn_fundamentalDomain_of_bounded {E : Type} [NormedAddCommGroup E] (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) {φ : GA D V → E} (hφ : Continuous φ) (C : ℝ)
    (hC : ∀ g, ‖φ g‖ ≤ C) : IntegrableOn φ 𝓕 ν := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.1
  haveI := hT.2.2.2.1
  exact Measure.integrableOn_of_bounded
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕).ne hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem integrableOn_mul_conj_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f f₂ : bddAut V) :
    IntegrableOn (fun g => (f : GA D V → ℂ) g * starRingEnd ℂ ((f₂ : GA D V → ℂ) g)) 𝓕 ν := by
  obtain ⟨hc, -, C, hC⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨hc₂, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
  refine integrableOn_fundamentalDomain_of_bounded hν h𝓕 (hc.mul (Complex.continuous_conj.comp hc₂)) (C * C₂) fun g => ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC g) (hC₂ g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

theorem exists_form_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ, ∀ f f₂, B f f₂ = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f f₂ : bddAut V => l2 ν 𝓕 (f : GA D V → ℂ) f₂) ?_ ?_ ?_ ?_, fun f f₂ => rfl⟩
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a c) (integrableOn_mul_conj_bddAut hν h𝓕 b c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a b) (integrableOn_mul_conj_bddAut hν h𝓕 a c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring

theorem petersson_self_re_pos_of_ne_zero (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f : bddAut V) (hf : f ≠ 0) :
    0 < (l2 ν 𝓕 (f : GA D V → ℂ) f).re := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  obtain ⟨hc, hi, C, hC⟩ := zero_one_mem_gammaSet_one f
  have key : l2 ν 𝓕 (f : GA D V → ℂ) f =
      ((∫ x in 𝓕, Complex.normSq ((f : GA D V → ℂ) x) ∂ν : ℝ) : ℂ) := by
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Complex.mul_conj]
    exact integral_ofReal
  rw [key, Complex.ofReal_re]
  have hint : IntegrableOn (fun x => Complex.normSq ((f : GA D V → ℂ) x)) 𝓕 ν :=
    integrableOn_fundamentalDomain_of_bounded hν h𝓕 (Complex.continuous_normSq.comp hc) (C * C) fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hC g) (hC g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _) hint]
  set U : Set (GA D V) := {x | (f : GA D V → ℂ) x ≠ 0} with hUdef
  have hsupp : Function.support (fun x => Complex.normSq ((f : GA D V → ℂ) x)) = U := by
    ext x
    simp [U, Complex.normSq_eq_zero]
  rw [hsupp]
  have hU : IsOpen U := isOpen_ne_fun hc continuous_const
  have hne : U.Nonempty := by
    by_contra hE
    rw [Set.not_nonempty_iff_eq_empty] at hE
    apply hf
    apply Subtype.ext
    funext x
    by_contra hx
    have hx' : x ∈ U := hx
    rw [hE] at hx'
    exact hx'
  refine pos_iff_ne_zero.2 fun h0 => (hU.measure_pos ν hne).ne' ?_
  have hsub : U ⊆ {x | ¬ ∃ γ : GQ V, γ • x ∈ 𝓕} ∪
      ⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) := by
    intro x hx
    by_cases hx' : ∃ γ : GQ V, γ • x ∈ 𝓕
    · obtain ⟨γ, hγ⟩ := hx'
      refine Or.inr (Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩)
      show (f : GA D V → ℂ) ((γ : GA D V) * x) ≠ 0
      rw [hi γ γ.2]
      exact hx
    · exact Or.inl hx'
  refine measure_mono_null hsub (measure_union_null (ae_iff.1 h𝓕.ae_covers) ?_)
  refine measure_iUnion_null fun γ => ?_
  rw [measure_preimage_mul]
  exact h0

theorem petersson_bounded_automorphic_right_translation_invariant (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (g : GA D V) (f f₂ : bddAut V) :
    l2 ν 𝓕 (bddRep V g f : GA D V → ℂ) (bddRep V g f₂ : GA D V → ℂ) = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V ν hν).1
  obtain ⟨-, hi, -⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨-, hi₂, -⟩ := zero_one_mem_gammaSet_one f₂
  rw [coe_bddRep, coe_bddRep]
  simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
  exact GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 g
    (fun x => (f : GA D V → ℂ) x * starRingEnd ℂ ((f₂ : GA D V → ℂ) x))
    fun γ hγ x => by simp only [hi γ hγ, hi₂ γ hγ]

end

theorem bddRep_unitarisable_and_bounded : ∀ (D : D7) (V : HSp D), IsUnitarisable (bddRep V) ∧ ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∀ f₂ : bddAut V, ∃ ℓ : bddAut V →ₗ[ℂ] ℂ, (∀ f : bddAut V, ℓ f = l2 ν 𝓕 (f : GA D V → ℂ) f₂) ∧ ∀ f : bddAut V, ∃ C : ℝ, ∀ g, ‖ℓ (bddRep V g f)‖ ≤ C := by
  intro D V
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  refine ⟨?_, fun ν 𝓕 hν h𝓕 f₂ => ?_⟩
  · have hH : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
    obtain ⟨𝓕, h𝓕⟩ :=
      (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V Measure.haar hH).2
    obtain ⟨B, hB⟩ := exists_form_bddAut hH h𝓕
    unfold IsUnitarisable
    refine ⟨B, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩
    · rw [hB, hB]
      simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet]
      rw [← integral_conj]
      congr 1
      funext x
      rw [map_mul, Complex.conj_conj, mul_comm]
    · rw [hB]
      exact petersson_self_re_pos_of_ne_zero hH h𝓕 v hv
    · rw [hB, hB]
      exact petersson_bounded_automorphic_right_translation_invariant hH h𝓕 g v w
  · obtain ⟨B, hB⟩ := exists_form_bddAut hν h𝓕
    refine ⟨{ toFun := fun f => B f f₂, map_add' := fun a b => by simp, map_smul' := fun c a => by simp },
      fun f => hB f f₂, fun f => ?_⟩
    obtain ⟨-, -, C, hC⟩ := zero_one_mem_gammaSet_one f
    obtain ⟨-, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
    have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕
    refine ⟨C * C₂ * (ν 𝓕).toReal, fun g => ?_⟩
    show ‖B (bddRep V g f) f₂‖ ≤ _
    rw [hB, coe_bddRep]
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x _ => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardGLDivParabolicIndexFiniteFieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_GL_div_parabolic_index_finiteField : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ), n = r + t → (Nat.card (GL (Fin n) κ) : ℝ) / ((Nat.card (GL (Fin t) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * t)) * ((Nat.card κ : ℝ) ^ (r ^ 2 + r * t))⁻¹ = ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  first | exact @GlobalTheory.Twist.GLIndexLoc.index_loc | exact GlobalTheory.Twist.GLIndexLoc.index_loc | (intros; apply GlobalTheory.Twist.GLIndexLoc.index_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmHostFractionalIdeal_partitionOfUnity : ∀ (D : D7), ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ D.host.AA) ∧ (∀ i, ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = 1 := by
  first | exact @GlobalTheory.HostAAPartition.host_AA_partition | exact GlobalTheory.HostAAPartition.host_AA_partition | (intros; apply GlobalTheory.HostAAPartition.host_AA_partition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffContinuousOneParameterFiniteDimensionalLStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W),
    (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) → A 0 = LinearMap.id →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  first | exact @GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | exact GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | (intros; apply GlobalTheory.contDiff_toCLM_of_continuous_oneParameter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDefStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect : ∀ (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)), Continuous c → c 0 ≠ 0 → IsOpen U → (∀ s, (s, 0) ∈ U) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U → (∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  first | exact @GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | exact GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | (intros; apply GlobalTheory.FuncEqSmooth.contDiff_of_func_eq <;> assumption)
end

