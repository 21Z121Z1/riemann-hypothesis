import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0148
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0140
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PoissonReindex

open GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F]

def reidx {κ ι : Type} (e : κ ≃ ι) : (ι → AF F) ≃ₜ+ (κ → AF F) where
  toFun u i := u (e i)
  invFun x j := x (e.symm j)
  left_inv u := by funext j; simp
  right_inv x := by funext i; simp
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

theorem reidx_apply {κ ι : Type} (e : κ ≃ ι) (u : ι → AF F) (i : κ) : reidx (F := F) e u i = u (e i) := rfl

theorem dot_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (u y : ι → AF F) :
    reidx e u ⬝ᵥ reidx e y = u ⬝ᵥ y := by
  simp only [dotProduct, reidx_apply]
  exact e.sum_comp (fun j => u j * y j)

theorem Bd_half {N : ℕ} (s u : Fin N → AF F) : Bd (AF F) (fun _ : Fin N => (1 / 2 : F)) s u = s ⬝ᵥ u := by
  simp only [Bd, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (2 : F) * (1 / 2) = 1 by norm_num, map_one, one_mul]

theorem mem_schA_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) : (fun u => Φ (reidx e u)) ∈ schA F ι := by
  have h := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective Φ hΦ
  convert h using 2 with u
  congr 1
  funext i
  rw [reidx_apply]
  conv_rhs => rw [← e.symm_apply_apply i]
  exact (e.symm.injective.extend_apply u 0 (e i)).symm

end GlobalTheory.PoissonReindex

open GlobalTheory.SWQ GlobalTheory.PoissonReindex in

theorem GlobalTheory.PoissonReindex.poisson_any : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure],
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ →
      thetaSum F (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) = c * thetaSum F Φ := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  have hC1 := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hC1
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : Ctx ψ lam ν a := ⟨hF, hC1, hlam, hν, fun _ => by norm_num [a]⟩
  obtain ⟨hHaar, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have h' : r = 0 := by exact_mod_cast h
    rw [h', zero_smul] at hr
    exact (NeZero.ne μ) hr
  refine ⟨(r : ℂ), hr0, fun Φ hΦ hFΦ => ?_⟩
  set G : (κ → AF F) → ℂ := fun y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have key : ∀ y', G (T y') = (r : ℂ) * Fo ψ ν a Φ' y' := by
    intro y'
    simp only [hG]
    rw [hr, integral_smul_nnreal_measure, integral_map_equiv]
    simp only [Fo, hΦ', hTm, a, Bd_half, T, dot_reidx]
    rw [NNReal.smul_def, Complex.real_smul]
  have hΦ's : Φ' ∈ schA F (Fin N) := mem_schA_reidx e hΦ
  have hD : Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ's
  have hGs : (fun u => G (T u)) ∈ schA F (Fin N) := mem_schA_reidx e hFΦ
  have hFeq : Fo ψ ν a Φ' = (r : ℂ)⁻¹ • fun u => G (T u) := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, key u]
    rw [← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  have hFD : Decay (Fo ψ ν a Φ') := by
    rw [hFeq]
    exact GlobalTheory.SchwartzDecay.decay_smul _ (GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ hGs)
  have hP := GlobalTheory.SWQ.poisson_summation F N ψ lam ν a hC Φ' hD hFD
  let E2 : (Fin N → F) ≃ (κ → F) :=
    { toFun := fun ξ i => ξ (e i), invFun := fun η j => η (e.symm j),
      left_inv := fun ξ => by funext j; simp, right_inv := fun η => by funext i; simp }
  have hth : ∀ H : (κ → AF F) → ℂ, thetaSum F H = th (fun u => H (T u)) := by
    intro H
    simp only [thetaSum, th]
    exact ((E2.tsum_eq (fun η => H (fun i => algebraMap F (AF F) (η i))))).symm
  rw [hth G, hth Φ]
  simp only [th] at hP ⊢
  simp only [key, tsum_mul_left]
  rw [hP]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniNumberFieldOfHilbertSamuel
section
set_option autoImplicit false

namespace GlobalTheory.HSShort

theorem bertiniNF_of_bertini (h : Bertini) : BertiniNF := by
  intro F _ _ T hg hb δ f hf
  obtain ⟨hδ, Q, hQ, hs⟩ := h F T hg hb δ f hf
  exact ⟨hδ, Q, hQ, fun E _ _ _ s hsQ => hs E s hsQ⟩

theorem bertiniNumberField_of_hilbertSamuel : GlobalTheory.HSCore.Quoted → BertiniNF :=
  fun hq => bertiniNF_of_bertini (GlobalTheory.T.bertini_simple_zeros_generic_sections hq)

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.BrPairF

variable {K ι : Type} [Field K] [Fintype ι] {n N : ℕ}

def brPairF (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) :
    VV K Λ →ₗ[K] (VV K fun τ => (σ τ).dual) →ₗ[K] K :=
  (pairBK σ).compl₁₂ (Formalism.L2.Col.Br.brStd hN Λ σ) (GlobalTheory.FunObj.funEquiv σ).symm.toLinearMap

theorem brPairF_apply (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) (u : VV K Λ)
    (v : VV K fun τ => (σ τ).dual) :
    brPairF σ hN Λ u v = pairBK σ (Formalism.L2.Col.Br.brStd hN Λ σ u) ((GlobalTheory.FunObj.funEquiv σ).symm v) := rfl

end GlobalTheory.BrPairF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPrincipalCongruenceTransversalLeAbsNormPow
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

theorem GlobalTheory.card_congRep_le : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a : ℕ) (R : Finset (GA D a)), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → R.card ≤ Ideal.absNorm 𝔪 ^ (a ^ 2) := by
  intro D 𝔪 h𝔪 a R hR huniq
  classical
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 a
  let Q := intG D a ⧸ (congLev D 𝔪 a).subgroupOf (intG D a)
  haveI : Finite Q := Nat.finite_of_card_ne_zero hne
  let f : R → Q := fun r => QuotientGroup.mk (⟨(r : GA D a), hR r r.2⟩ : intG D a)
  have hf : Function.Injective f := by
    rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : r⁻¹ * r' ∈ congLev D 𝔪 a := h1
    have h3 := ((mem_congLev_iff D 𝔪 a _).1 h2).2
    have h4 : CongOne D 𝔪 (r'⁻¹ * r') := by
      rw [inv_mul_cancel]; exact congOne_one 𝔪 a
    obtain ⟨s, -, hs⟩ := huniq r' (hR r' hr')
    have e1 := hs r ⟨hr, h3⟩
    have e2 := hs r' ⟨hr', h4⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  calc R.card ≤ Nat.card Q := hc
    _ = (congLev D 𝔪 a).relIndex (intG D a) := rfl
    _ ≤ _ := hle

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartFrSgnFalseRigFr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageDict

open GlobalTheory.ChainFr Matrix

variable {D : D7}

theorem jm_eq_diag {k p : ℕ} {ε : Fin k → ℝ} (h : ∀ a : Fin k, (ε a = 1 ∧ a.val < p) ∨ (ε a = -1 ∧ p ≤ a.val)) :
    Formalism.REAL.Jm (fun a : Fin k => decide (a.val < p)) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  rcases h a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · have : ¬ a.val < p := by omega
    simp [h1, this]

theorem isUnit_of_isONBasis {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) : IsUnit B := by
  obtain ⟨ε, hε, h1, -⟩ := h
  have hd : IsUnit (Matrix.diagonal fun a => (ε a : ℂ)).det := by
    rw [Matrix.det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    rcases hε a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hd
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_right hd

def sigIdx {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : ℕ := Classical.choose (h.2.2 τ).2

theorem sigIdx_spec {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) (r.s τ) (r.B τ) (sigIdx r h τ) := Classical.choose_spec (h.2.2 τ).2

def rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) : Fr V where
  ε τ a := decide (a.val < sigIdx r h τ)
  fr τ := (r.B τ)⁻¹
  fr_unit τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    exact (Matrix.isUnit_nonsing_inv_iff).2 hu
  fr_gram τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    obtain ⟨ε, hε, h1, -⟩ := sigIdx_spec r h τ
    rw [jm_eq_diag hε, ← h1, Matrix.conjTranspose_nonsing_inv]
    have hu' : IsUnit (r.B τ)ᴴ.det := by
      rw [Matrix.det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).star
    have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu', Matrix.one_mul]

theorem onb_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).onb τ = r.B τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  simp only [Fr.onb, rigFr]
  exact Matrix.nonsing_inv_nonsing_inv _ hu0

theorem cart_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).cart τ = r.s τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  obtain ⟨ε, hε, -, h2⟩ := sigIdx_spec r h τ
  simp only [Fr.cart, rigFr]
  rw [Matrix.nonsing_inv_nonsing_inv _ hu0, jm_eq_diag hε, ← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one]

theorem cart_frSgn_true_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn true (rigFr r h)).cart τ = -r.s τ := by
  rw [← cart_rigFr r h τ]
  simp only [Fr.cart, GlobalTheory.SquareComm.frSgn]
  have e' : Formalism.REAL.Jm (fun a => xor true ((rigFr r h).ε τ a)) = -Formalism.REAL.Jm ((rigFr r h).ε τ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; cases h' : (rigFr r h).ε τ a <;> simp [Formalism.REAL.Jm, h']
    · simp [Formalism.REAL.Jm, hab]
  rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn_false_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn false (rigFr r h)).cart τ = r.s τ := by
  rw [← cart_rigFr r h τ]
  simp [Fr.cart, GlobalTheory.SquareComm.frSgn]

theorem stage_sizes (i j : Fin D.R.m) {p q a a' : ℕ} (hp : p ≤ pp D j) (hq : q ≤ qq D j)
    (ha : a + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p) (ha' : a' + 2 * qq D j = rankV D i j + 2 * q) :
    Even (a + a') ∧ a' + 2 * (2 * (p + q) + 1) < a ∧ 2 * (p + q) + 1 < a' ∧
      a + a' ≤ rankV D (i + 1) (j + 1) + rankV D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := D.R.m_even
  obtain ⟨w, hw⟩ := D.R.k_even
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have r1 : rankV D i j = D.R.r + j.1 * D.R.t + i.1 * sLen D := rfl
  have r3 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have r4 : sLen D = D.R.r + 6 := rfl
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.two_le_m
  have hj := j.2
  simp only [pp, qq] at hp hq ha ha'
  refine ⟨Nat.even_iff.2 (by omega), by omega, by omega, by omega⟩

end GlobalTheory.StageDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterCompatibilityStandardKernelDataTrueColuStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (ofRecord (I.rec7 l Z) L Del h0) t.seam W t.Ch t.glob t.sel := by
  first | exact @GlobalTheory.ColRows.charTie_stdKer | exact GlobalTheory.ColRows.charTie_stdKer | (intros; apply GlobalTheory.ColRows.charTie_stdKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulComponentDegreeLeDimension
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

namespace GlobalTheory.HSCore.CompShare

theorem share_of_data {F : Type} [Field F] [NumberField F] (X : Data F) {D δ T d : ℕ} (hD : X.D = D) (hT : X.T = T)
    (hd : X.d = d) (hδ : (δ : ℤ) = X.del) (h : (X.R : ℤ) * X.del ≤ X.d) : (T - 1).choose D * δ ≤ d := by
  subst hD hT hd
  rw [← hδ] at h
  exact_mod_cast h

theorem choose_mul_compDeg_le : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), IsNef c.F (h.data f₁ f₂ th k).LA → IsBig c.F (h.data f₁ f₂ th k).LA → (h.data f₁ f₂ th k).Birational → (P.T - 1).choose (CompHt.dimFlag Dw) * CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0) ≤ Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  intro hQ E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hn hb hB
  obtain ⟨hD, hP⟩ := GlobalTheory.CompHS.compPresents_data E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have e := GlobalTheory.HSCore.ImageDegree.imageDeg_eq_del hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _
    (h.data f₁ f₂ th k).geom hB hP
  refine share_of_data (h.data f₁ f₂ th k) hD rfl (h.d_eq f₁ f₂ th k) ?_ (GlobalTheory.T.arithHilbertSamuel_rankDegree_share_le hQ c.F _ hn hb)
  rw [← e, CompHt.compDeg, ← hD]

end GlobalTheory.HSCore.CompShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExistsMoved
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem cm_exists_moved (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : (∃ α : E, σ α ≠ α) ∧ ∀ x, σ (σ x) = x := by
  obtain ⟨_, hc, _, hconj⟩ := h
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply w.embedding.injective
    rw [hconj, hconj, star_star]
  refine ⟨?_, hinv⟩
  by_contra hne
  push_neg at hne
  have hw : w.IsComplex := hc.isComplex w
  apply NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  ext x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hx := hconj w.embedding x
  rw [hne] at hx
  exact hx.symm

theorem quad_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ v : Pl F, ∃ δ : Fv F v ⊗[F] E, IsQuad (GlobalTheory.HoweLocal.cv σ v) δ := by
  intro F E _ _ _ _ _ σ h v
  have hdim : Module.finrank F E = 2 := h.2.2.1
  obtain ⟨⟨α, hα⟩, hinv⟩ := cm_exists_moved F E σ h
  set δ₀ : E := α - σ α with hδ₀
  have hanti : σ δ₀ = -δ₀ := by
    rw [hδ₀, map_sub, hinv]; ring
  have hne : δ₀ ≠ 0 := by
    intro h0; apply hα; rw [hδ₀, sub_eq_zero] at h0; exact h0.symm
  have hli : LinearIndependent F ![(1 : E), δ₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : σ (s • (1 : E) + t • δ₀) = s • (1 : E) - t • δ₀ := by
      simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hanti]
      ring
    rw [hst, map_zero] at h2
    have ht : (2 * t) • δ₀ = 0 := by
      have : (s • (1 : E) + t • δ₀) - (s • (1 : E) - t • δ₀) = (2 * t) • δ₀ := by
        rw [mul_smul, two_smul]; abel
      rw [← this, hst, ← h2, sub_zero]
    have ht0 : t = 0 := by
      rcases smul_eq_zero.mp ht with h3 | h3
      · exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
      · exact absurd h3 hne
    refine ⟨?_, ht0⟩
    rw [ht0, zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h3 | h3
    · exact h3
    · exact absurd h3 one_ne_zero
  let b0 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : ∀ i, b0 i = ![(1 : E), δ₀] i := fun i => by
    simp [b0, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨(1 : Fv F v) ⊗ₜ[F] δ₀, ⟨?_, ?_, ?_⟩⟩
  · have hu : IsUnit δ₀ := hne.isUnit
    have := hu.map (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E)
    simpa [Algebra.TensorProduct.includeRight_apply] using this
  · simp [GlobalTheory.HoweLocal.cv, Algebra.TensorProduct.map_tmul, hanti, TensorProduct.tmul_neg]
  · refine ⟨Algebra.TensorProduct.basis (Fv F v) b0, ?_, ?_⟩
    · rw [Algebra.TensorProduct.basis_apply, hb0]; rfl
    · rw [Algebra.TensorProduct.basis_apply, hb0]; rfl

end GlobalTheory.HoweLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientFieldIsFieldOfDefinitionChainStepsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientField_isFieldOfDefinition_chainSteps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition W t.sel (t.tup a) (t.cst a) (t.word u) t.amb := by
  first | exact @GlobalTheory.ColRows.fieldOfDefinition_of_stdKer | exact GlobalTheory.ColRows.fieldOfDefinition_of_stdKer | (intros; apply GlobalTheory.ColRows.fieldOfDefinition_of_stdKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonOneSpanImageEqMapStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colon_one_span_image_eq_map_colon : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
    ∀ (A : Submodule (𝓞 E) E), A.FG → (1 : E) ∈ A →
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := by
  first | exact @GlobalTheory.colon_one_span_image_eq_map | exact GlobalTheory.colon_one_span_image_eq_map | (intros; apply GlobalTheory.colon_one_span_image_eq_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonPowMulCancelFgFractionalStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colon_pow_mul_cancel_fg_fractional : ∀ {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K), 𝔟.FG → 𝔟 ≠ ⊥ →
    ∀ (p : ℕ) (A N : Submodule (𝓞 K) K),
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := by
  first | exact @GlobalTheory.ColonPowCancel.colon_pow_mul_cancel | exact GlobalTheory.ColonPowCancel.colon_pow_mul_cancel | (intros; apply GlobalTheory.ColonPowCancel.colon_pow_mul_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatumStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (h : ℕ) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (fil : G.dual.omega ≃ₗ[O] D.Fil), (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O)) → ∃ L : (Fin h → Ainf p O) ≃ₗ[Ainf p O] latt G, ∀ r t, (L r).1 t = r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i)) := by
  first | exact @GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace | exact GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace | (intros; apply GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace <;> assumption)
end

