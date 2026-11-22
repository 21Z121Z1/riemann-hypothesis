import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjComponentIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IdemPairCpt

open GlobalTheory.StdFrames

theorem cpt_sg_eq_one_of_cP_mem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∈ P) : cpt (D := D) w (sg D (toEAf D e)) = 1 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (1 - toEAf D e) = 0 := by
    rw [map_sub, map_one, GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, sub_self]
  have h2 := cpt_sg_eq_zero h1
  rw [map_sub, map_one, map_sub, map_one] at h2
  exact (sub_eq_zero.mp h2).symm

theorem cpt_sg_eq_zero_of_cP_notMem {D : D7} {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (w : Pl D.host.E) (hw : GlobalTheory.IdemSupport.cP w ∉ P) : cpt (D := D) w (sg D (toEAf D e)) = 0 := by
  have h1 : cpt (D := D) (GlobalTheory.IdemSupport.cP w) (toEAf D e) = 0 := by
    rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw]
  exact cpt_sg_eq_zero h1

theorem cpt_add_cA_idemSum : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := by
  intro D e P he w
  have hsplit : GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) =
      cpt (D := D) w (toEAf D e) + cpt (D := D) w (sg D (toEAf D e)) := by
    rw [map_add, toEAf_cA, map_add]
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · rw [hsplit]
    by_cases hw : w ∈ P
    · have hc : GlobalTheory.IdemSupport.cP w ∉ P := fun hc => GlobalTheory.IdemSumBranch.conjPrime_ne he hc hw rfl
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_pos hw, cpt_sg_eq_zero_of_cP_notMem he w hc, add_zero]
    · have hc : GlobalTheory.IdemSupport.cP w ∈ P := h.resolve_left hw
      rw [GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg hw, cpt_sg_eq_one_of_cP_mem he w hc, zero_add]
  · rw [hsplit, GlobalTheory.OffPartLattice.cpt_idemSum he, if_neg h1, cpt_sg_eq_zero_of_cP_notMem he w h2, add_zero]

example : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := @cpt_add_cA_idemSum

end GlobalTheory.IdemPairCpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InMaxCompactOfModelFrameInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

open Matrix in

theorem GlobalTheory.CuspGK.inK_inv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GlobalTheory.CuspGK.InK M τ g) :
    GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  obtain ⟨hU, hK1, hK2⟩ := h
  set P := M.fr τ with hPdef
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set u := P * g * P⁻¹ with hu
  have huu : IsUnit u.det := Matrix.UnitaryGroup.det_isUnit ⟨u, hK1⟩
  have hg : IsUnit g.det := by
    have hdet : u.det = P.det * g.det * P⁻¹.det := by simp [hu, Matrix.det_mul]
    rw [hdet] at huu
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left huu)
  have hinv : P * g⁻¹ * P⁻¹ = u⁻¹ := by
    rw [hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc]
  have hsu : star u * u = 1 := Unitary.star_mul_self_of_mem hK1
  have hustar : u⁻¹ = star u := Matrix.inv_eq_left_inv hsu
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ huu
  have h2 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ huu
  refine ⟨⟨?_, ?_, ?_⟩, Matrix.nonsing_inv_nonsing_inv _ hg⟩
  · have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
    show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hgg]; simp
  · show P * g⁻¹ * P⁻¹ ∈ _
    rw [hinv, hustar]
    exact Unitary.star_mem hK1
  · show P * g⁻¹ * P⁻¹ * _ = _ * (P * g⁻¹ * P⁻¹)
    rw [hinv]
    clear_value u
    calc u⁻¹ * Formalism.REAL.Jm (M.ε τ) = u⁻¹ * Formalism.REAL.Jm (M.ε τ) * (u * u⁻¹) := by rw [h2, Matrix.mul_one]
      _ = u⁻¹ * (Formalism.REAL.Jm (M.ε τ) * u) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u⁻¹ * (u * Formalism.REAL.Jm (M.ε τ)) * u⁻¹ := by rw [hK2]
      _ = (u⁻¹ * u) * Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by rw [h1, Matrix.one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfield
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem integral_eq_sum_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKt : μ K ≠ ⊤) {S : Set G} (hS : IsCompact S)
    (hSK : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) (f : G → ℂ) (hf : ∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) :
    ∃ t : Finset (G ⧸ K), ∫ g in S, f g ∂μ = ∑ Q ∈ t, f Q.out * μ.real K := by
  classical
  set q : G → G ⧸ K := QuotientGroup.mk

  have hcov : S ⊆ ⋃ s ∈ S, s • (K : Set G) := fun s hs =>
    Set.mem_biUnion hs ⟨1, one_mem K, by simp⟩
  obtain ⟨b, hbS, hbf, hb⟩ := hS.elim_finite_subcover_image (fun s _ => hKo.smul s) hcov
  have hfin : (q '' S).Finite := by
    refine (hbf.image q).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, hy⟩ := Set.mem_iUnion₂.1 (hb hs)
    refine ⟨g, hg, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hy
    simp only [smul_eq_mul, q]
    exact (QuotientGroup.mk_mul_of_mem g hy).symm
  have hout : ∀ Q ∈ q '' S, Q.out ∈ S := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hh]; exact hSK s hs h h.2
  obtain ⟨T, hT⟩ : ∃ T : Finset (G ⧸ K), ∀ Q, Q ∈ T ↔ Q ∈ q '' S :=
    ⟨hfin.toFinset, fun Q => hfin.mem_toFinset⟩
  have hSeq : S = ⋃ Q ∈ T, Q.out • (K : Set G) := by
    ext g
    simp only [Set.mem_iUnion, hT, exists_prop]
    constructor
    · intro hg
      refine ⟨q g, ⟨g, hg, rfl⟩, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨h⁻¹, (h⁻¹).2, ?_⟩
      simp [q, hh, mul_assoc]
    · rintro ⟨Q, hQ, y, hy, rfl⟩
      exact hSK _ (hout Q hQ) y hy
  have hconst : ∀ Q ∈ q '' S, ∀ y ∈ Q.out • (K : Set G), f y = f Q.out := by
    rintro Q hQ _ ⟨y, hy, rfl⟩
    exact hf _ (hout Q hQ) y hy
  refine ⟨T, ?_⟩
  rw [hSeq, integral_biUnion_finset]
  · refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [hT] at hQ
    rw [setIntegral_congr_fun (hKo.smul _).measurableSet (hconst Q hQ), setIntegral_const,
      measureReal_def, measure_smul, ← measureReal_def, Complex.real_smul, mul_comm]
  · exact fun Q _ => (hKo.smul _).measurableSet
  · intro Q _ Q' _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
    apply hne
    have h1 : q (Q.out * y) = Q := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy]; exact QuotientGroup.out_eq' Q
    have h2 : q (Q'.out * y') = Q' := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy']; exact QuotientGroup.out_eq' Q'
    simp only [smul_eq_mul] at he
    rw [← h1, ← h2, he]
  · intro Q hQ
    rw [hT] at hQ
    refine (integrableOn_congr_fun (hconst Q hQ) (hKo.smul _).measurableSet).2 ?_
    refine integrableOn_const ?_
    rw [measure_smul]; exact hKt

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem measureReal_eq_inv_natCast {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] {J K : Subgroup G}
    (hJc : IsCompact (J : Set G)) (hJ1 : μ J = 1) (hKo : IsOpen (K : Set G)) (hKJ : K ≤ J) :
    ∃ n : ℕ, μ.real K = (n : ℝ)⁻¹ := by
  have hKt : μ K ≠ ⊤ := ((measure_mono (show (K : Set G) ⊆ J from hKJ)).trans_lt (by simp [hJ1])).ne
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv μ K hKo hKt hJc (fun s hs k hk => J.mul_mem hs (hKJ hk))
    (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl)
  rw [setIntegral_const, measureReal_def, hJ1, Finset.sum_const, nsmul_eq_mul, one_mul] at ht
  simp only [ENNReal.toReal_one, one_smul] at ht
  refine ⟨t.card, eq_inv_of_mul_eq_one_right ?_⟩
  exact_mod_cast ht.symm

def rightStab {G : Type} [Group G] (S : Set G) : Subgroup G where
  carrier := {k | ∀ g, g ∈ S ↔ g * k ∈ S}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [ha g, hb (g * a), mul_assoc]
  inv_mem' := fun {a} ha g => by rw [ha (g * a⁻¹), inv_mul_cancel_right]

theorem isOpen_rightStab {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {S : Set G}
    (hSc : IsCompact S) (hSo : IsOpen S) : IsOpen (rightStab S : Set G) := by
  obtain ⟨V, hV, hSV⟩ := compact_open_separated_mul_right hSc hSo subset_rfl
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem hV (inv_mem_nhds_one G hV)) ?_)
  rintro k ⟨hk, hk'⟩ g
  refine ⟨fun hg => hSV (Set.mul_mem_mul hg hk), fun hg => ?_⟩
  have := hSV (Set.mul_mem_mul hg hk')
  rwa [mul_inv_cancel_right] at this

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A' : Type} [Fintype A'] [DecidableEq A']

def matBall (x : Matrix A' A' k) (c : kˣ) : Set (Matrix A' A' k) :=
  {y | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)}

theorem matBall_eq_preimage (x : Matrix A' A' k) (c : kˣ) :
    matBall x c = ⋂ i, ⋂ j, (fun y : Matrix A' A' k => (y i j - x i j) / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  ext y
  simp only [matBall, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
    Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0]

theorem isOpen_matBall (x : Matrix A' A' k) (c : kˣ) : IsOpen (matBall x c) := by
  rw [matBall_eq_preimage]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    IsOpen.preimage (by fun_prop) Valuation.isOpen_integer

theorem isCompact_matBall (x : Matrix A' A' k) (c : kˣ) : IsCompact (matBall x c) := by
  have hc : (c : k) ≠ 0 := c.ne_zero
  have e : matBall x c = (fun A : Matrix A' A' k => (c : k) • A + x) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨fun i j => (y i j - x i j) / (c : k), fun i j => ?_, ?_⟩
      · have := (matBall_eq_preimage x c ▸ hy : y ∈ _)
        simp only [Set.mem_iInter, Set.mem_preimage] at this
        exact this i j
      · ext i j
        show (c : k) * ((y i j - x i j) / (c : k)) + x i j = y i j
        rw [mul_div_cancel₀ _ hc, sub_add_cancel]
    · rintro ⟨A, hA, rfl⟩ i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_right, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))
  rw [e]
  exact isCompact_intMatrix.image (by fun_prop)

theorem isCompact_isOpen_glBall (x : Matrix A' A' k) (c : kˣ) (hdet : ∀ y ∈ matBall x c, y.det ≠ 0) :
    IsCompact {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} ∧
    IsOpen {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
  have e : {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} =
      (fun g : GL A' k => g.val) ⁻¹' matBall x c := rfl
  rw [e]
  refine ⟨?_, (isOpen_matBall x c).preimage Units.continuous_val⟩
  rw [isEmbedding_val_GL.isInducing.isCompact_iff]
  convert isCompact_matBall x c using 1
  ext y
  refine ⟨fun ⟨g, hg, hgy⟩ => hgy ▸ hg, fun hy => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero y (hdet y hy), hy, rfl⟩⟩

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

theorem integral_glBall_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (ν : kˣ →* ℂˣ) (z : ℂ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u z ∈ F) → ∀ (c : kˣ) (x : Matrix A' A' k), (∀ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)) → y.det ≠ 0) → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
  intro k _ _ _ _ _ _ A' _ _ F J hJo hJK ν z ϖ e _ hcond hνF hapF c x hdet
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨hSc, hSo⟩ := isCompact_isOpen_glBall x c hdet
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  set K : Subgroup (GL A' k) := J ⊓ GlobalTheory.SplitFlip.glLatCong (ϖ ^ e) (stdLat k A') ⊓ rightStab S with hKdef
  have hKo : IsOpen (K : Set (GL A' k)) := by
    simp only [hKdef, Subgroup.coe_inf]
    exact (hJo.inter (GlobalTheory.FunObj.GivenAdm.isOpen_glLatCong _)).inter (isOpen_rightStab hSc hSo)
  have hKJ : K ≤ J := inf_le_left.trans inf_le_left
  have hJc : IsCompact (J : Set (GL A' k)) := isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hKt : haarVol J K ≠ ⊤ :=
    ((measure_mono (show (K : Set (GL A' k)) ⊆ J from hKJ)).trans_lt (by simp [haarVol_self hJo hJK])).ne
  have hinv : ∀ s ∈ S, ∀ k' ∈ K, ((ν (gdet (s * k')) : ℂ) * apow (gdet (s * k')) z) =
      (ν (gdet s) : ℂ) * apow (gdet s) z := by
    intro s _ k' hk
    have hu : gdet k' ∈ unitCong (ϖ ^ e) :=
      GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
    rw [gdet_mul, map_mul, Units.val_mul, apow_mul, hcond _ hu, apow_of_valuation_eq_one hu.1]
    simp
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv (haarVol J) K hKo hKt hSc
    (fun s hs k' hk => ((Subgroup.mem_inf.1 hk).2 s).1 hs) (fun g => (ν (gdet g) : ℂ) * apow (gdet g) z) hinv
  rw [ht]
  obtain ⟨n, hn⟩ := measureReal_eq_inv_natCast (haarVol J) hJc (haarVol_self hJo hJK) hKo hKJ
  refine Subfield.sum_mem _ fun Q _ => F.mul_mem (F.mul_mem (hνF _) (hapF _)) ?_
  rw [hn]
  push_cast
  exact F.inv_mem (natCast_mem F n)

end GlobalTheory.GLBallInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.CosetVanish

theorem integral_coset_singular_eq_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (μ : Measure (GL A' k)) [μ.IsMulLeftInvariant] (ν : kˣ →* ℂˣ) (z : ℂ), ¬ IsUnram ν → ∀ (c : kˣ) (x : Matrix A' A' k), x.det = 0 → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ = 0 := by
  intro k _ _ _ _ _ _ A' _ _ μ _ ν z hν c x hx
  classical
  obtain ⟨u, hu1, hνu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hν fun y hy => h y hy
  obtain ⟨w0, hw0, hw0x⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := x)).2 hx
  obtain ⟨j, hj⟩ : ∃ j, w0 j ≠ 0 := by
    by_contra h; push_neg at h; exact hw0 (funext h)
  haveI : Nonempty A' := ⟨j⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => valuation k (w0 i))
  have hwi₀ : w0 i₀ ≠ 0 := by
    intro h0
    have := hi₀ j
    rw [h0, map_zero] at this
    exact hj ((valuation k).zero_iff.1 (le_antisymm this zero_le'))
  set w : A' → k := (w0 i₀)⁻¹ • w0 with hwdef
  have hwi : w i₀ = 1 := by simp [w, hwi₀]
  have hwint : ∀ i, valuation k (w i) ≤ 1 := by
    intro i
    simp only [w, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    have hpos : valuation k (w0 i₀) ≠ 0 := by simpa using hwi₀
    calc (valuation k (w0 i₀))⁻¹ * valuation k (w0 i) ≤ (valuation k (w0 i₀))⁻¹ * valuation k (w0 i₀) :=
          by gcongr; exact hi₀ i
      _ = 1 := inv_mul_cancel₀ hpos
  have hwx : ∀ j, ∑ l, w l * x l j = 0 := by
    intro j
    have := congrFun hw0x j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    simp only [w, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  set e : A' → k := Pi.single i₀ ((u : k) - 1) with hedef
  have he : ∀ i, valuation k (e i) ≤ 1 := by
    intro i
    by_cases h : i = i₀
    · subst h
      simp only [e, Pi.single_eq_same]
      refine ((valuation k).map_sub _ _).trans ?_
      simp [hu1]
    · simp [e, Pi.single_eq_of_ne h]
  have hwe : ∑ l, w l * e l = (u : k) - 1 := by
    simp [e, Pi.single_apply, hwi]
  set M : Matrix A' A' k := 1 + Matrix.vecMulVec e w with hMdef
  have hMdet : M.det = u := by
    rw [hMdef, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [dotProduct]
    rw [hwe]; ring
  have hMne : M.det ≠ 0 := by rw [hMdet]; exact u.ne_zero
  set m : GL A' k := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMne with hmdef
  have hmdet : gdet m = u := by
    ext; simp [gdet, Matrix.GeneralLinearGroup.val_det_apply, m, hMdet]
  have hmval : (m : Matrix A' A' k) = M := rfl
  have hMG : ∀ (G : Matrix A' A' k) i j, (M * G) i j = G i j + e i * ∑ l, w l * G l j := by
    intro G i j
    rw [hMdef, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.vecMulVec_apply, mul_assoc, Finset.mul_sum]
  have hsum : ∀ (G : Matrix A' A' k) j, ∑ l, w l * G l j = ∑ l, w l * (G l j - x l j) := by
    intro G j
    simp only [mul_sub, Finset.sum_sub_distrib, hwx, sub_zero]
  have hkey : ∀ g : GL A' k, (m * g ∈ {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}) ↔
      g ∈ {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
    intro g
    simp only [Set.mem_setOf_eq, Units.val_mul, hmval, hMG]
    constructor
    · intro h i j
      set s := ∑ l, w l * (g.val l j) with hs
      have h2 : ∑ l, w l * ((g.val l j + e l * s) - x l j) = (u : k) * s := by
        have : ∀ l, w l * ((g.val l j + e l * s) - x l j) = w l * (g.val l j - x l j) + (w l * e l) * s := by
          intro l; ring
        simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, hwe, ← hsum, ← hs]
        ring
      have hsv : valuation k s ≤ valuation k (c : k) := by
        have : s = (u : k)⁻¹ * ∑ l, w l * ((g.val l j + e l * s) - x l j) := by
          rw [h2, ← mul_assoc, inv_mul_cancel₀ u.ne_zero, one_mul]
        rw [this, map_mul, map_inv₀, hu1, inv_one, one_mul]
        refine (valuation k).map_sum_le fun l _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left' (hwint l)).trans (h l j) |>.trans' (by rfl)
      have : g.val i j - x i j = ((g.val i j + e i * s) - x i j) + (-(e i * s)) := by ring
      rw [this]
      refine (valuation k).map_add_le (h i j) ?_
      rw [Valuation.map_neg, map_mul]
      exact (mul_le_of_le_one_left' (he i)).trans hsv
    · intro h i j
      have hsv : valuation k (∑ l, w l * g.val l j) ≤ valuation k (c : k) := by
        rw [hsum]
        refine (valuation k).map_sum_le fun l _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left' (hwint l)).trans (h l j)
      have : g.val i j + e i * (∑ l, w l * g.val l j) - x i j = (g.val i j - x i j) + e i * (∑ l, w l * g.val l j) := by ring
      rw [this]
      refine (valuation k).map_add_le (h i j) ?_
      rw [map_mul]
      exact (mul_le_of_le_one_left' (he i)).trans hsv
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  have hpre : (fun g => m * g) ⁻¹' S = S := Set.ext hkey
  set χ : GL A' k → ℂ := fun g => (ν (gdet g) : ℂ) * apow (gdet g) z with hχ
  have hχm : ∀ g, χ (m * g) = (ν u : ℂ) * χ g := by
    intro g
    simp only [χ, gdet, map_mul] at hmdet ⊢
    rw [hmdet, apow_mul, apow_of_valuation_eq_one hu1, Units.val_mul]
    ring
  have hmp : MeasurePreserving (fun g => m * g) μ μ := measurePreserving_mul_left μ m
  have hemb : MeasurableEmbedding (fun g => m * g) := (MeasurableEquiv.mulLeft m).measurableEmbedding
  have h1 := hmp.setIntegral_preimage_emb hemb χ S
  rw [hpre] at h1
  simp only [hχm, integral_const_mul] at h1
  change ∫ g in S, χ g ∂μ = 0
  have hne : (ν u : ℂ) ≠ 1 := by
    intro h; exact hνu (Units.ext h)
  have h3 : ((ν u : ℂ) - 1) * ∫ g in S, χ g ∂μ = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.CosetVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartzStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  first | exact @GlobalTheory.SquareAgree.isDatum_add | exact GlobalTheory.SquareAgree.isDatum_add | (intros; apply GlobalTheory.SquareAgree.isDatum_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFlipStage_isTensor_placeDepth : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (Φ : ch.G.Datum), ∀ w ∈ locPl ch.G t, ∀ k, k ≤ D.R.m ^ 2 → (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w) ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).path ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).tensor := by
  first | exact @GlobalTheory.FlipRun.isTensor_flips_take | exact GlobalTheory.FlipRun.isTensor_flips_take | (intros; apply GlobalTheory.FlipRun.isTensor_flips_take <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_grid_rational_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ (G.pS p) (G.pT p) f → ∀ γ ∈ GQ (G.V p.small), ∀ γ' ∈ GQ (G.V p.big),
    ∀ g h, W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  first | exact @GlobalTheory.RowReal.ker_rat_left | exact GlobalTheory.RowReal.ker_rat_left | (intros; apply GlobalTheory.RowReal.ker_rat_left <;> assumption)
end

