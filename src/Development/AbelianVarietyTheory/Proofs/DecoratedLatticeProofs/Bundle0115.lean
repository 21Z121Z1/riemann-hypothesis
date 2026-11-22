import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFrames
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0103
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLeOfCuspidalVariationUnipotentRadical
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspGeo

theorem norm_le_of_unipRad_variation : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → IsCuspFun V φ →
    ∀ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ → ∀ (g : GA D V) (e : ℝ),
      (∀ m ∈ NI V C₀, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  intro D V φ hφ hcusp r C₀ hC g e he
  set 𝔉 := GlobalTheory.Cusp.frameFlag hC with h𝔉
  have hc : GlobalTheory.Cusp.Cocompact (GQ V) (GlobalTheory.Cusp.NA 𝔉) := GlobalTheory.Cusp.cocompact_single _
  have hP := hc.isProbabilityMeasure
  have h0 : GlobalTheory.Cusp.constTerm 𝔉 φ g = 0 :=
    congrFun ((GlobalTheory.Cusp.isCuspFun_iff hφ.left).1 hcusp _ _) g
  have hI := hc.integrable hφ.left hφ.cont g
  have hmem : ∀ n : GlobalTheory.Cusp.NA 𝔉, (n : GA D V) ∈ NI V C₀ := fun n => by
    exact (SetLike.ext_iff.1 (GlobalTheory.Cusp.NA_frameFlag hC) _).1 n.2
  have key : φ g = ∫ q, (φ g - φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g)) ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉) := by
    rw [integral_sub (integrable_const _) hI]
    have h0' : ∫ q, φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g) ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉) = 0 := h0
    rw [h0', integral_const]
    simp
  rw [key]
  have hb := norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉))
    (f := fun q => φ g - φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g)) (C := e)
    (.of_forall fun q => by rw [norm_sub_rev]; exact he _ (hmem _))
  simpa using hb

end GlobalTheory.CuspGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedOperatorBijectiveFiniteTranslationCombin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamBij

variable {D : D7}

def contAutSub (S : HSp D) : Submodule ℂ (GA D S → ℂ) where
  carrier := {φ | IsContAut S φ}
  add_mem' ha hb := ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ h := ⟨fun γ hγ g => by simp [h.1 γ hγ g], h.2.const_smul c⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem formAt_eq (β : Frame p S n) (P : Pair k n) {φ : Form k n (GA D S → ℂ)} (hφ : φ ∈ EqForm β.rep) :
    formAt β P (φ P) = φ := by
  funext P₁
  have h := Classical.epsilon_spec (p := fun g : GL n k => g • P = P₁) (MulAction.exists_smul_eq (GL n k) P P₁)
  show β.rep _ (φ P) = φ P₁
  rw [← hφ, h]

theorem sum_single_sum (β : Frame p S n) {ι : Type} (s : Finset ι) (g : ι → GL n k) (a : ι → ℂ)
    (φ₀ : GA D S → ℂ) :
    (∑ i ∈ s, Finsupp.single (g i) (a i)).sum (fun h b => b • β.rep h φ₀) = ∑ i ∈ s, a i • β.rep (g i) φ₀ := by
  rw [← Finsupp.sum_finset_sum_index (fun h => zero_smul ℂ (β.rep h φ₀)) (fun h _ _ => add_smul _ _ (β.rep h φ₀))]
  exact Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index (zero_smul ℂ _)

section Ops

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (β : Frame p S n)

theorem isRam_diaFFStar (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (dia ε (FFStar q χ φ)) := by
  refine ⟨dia_mem_EqForm ε (FFStar_mem_EqForm q χ hφ.1), hO.dia_mem_ram ε _ (hO.FFStar_mem_ram _ hφ.2.1),
    fun P' => ?_⟩
  rw [dia_apply, FFStar_apply]
  exact (contAutSub S).sum_mem fun P₁ _ => (contAutSub S).smul_mem _ (hφ.2.2 P₁)

theorem isRam_FFdia (hO : OperatorIdentities k n (GA D S → ℂ) q χ) (c : ℂ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (c • FF q χ (dia ε⁻¹ φ)) := by
  refine ⟨(EqForm β.rep).smul_mem c (FF_mem_EqForm q χ (dia_mem_EqForm _ hφ.1)),
    (Mram k n _).smul_mem c (hO.FF_mem_ram _ (hO.dia_mem_ram _ _ hφ.2.1)), fun P' => ?_⟩
  rw [Pi.smul_apply, FF_apply]
  refine (contAutSub S).smul_mem c ((contAutSub S).sum_mem fun Q _ => (contAutSub S).smul_mem _ ?_)
  rw [dia_apply]
  exact hφ.2.2 _

theorem diaFFStar_inv (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) :
    dia ε (FFStar q χ (((resCard k : ℂ) ^ Fintype.card n)⁻¹ • FF q χ (dia ε⁻¹ φ))) = φ := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  rw [map_smul, map_smul, hO.FFStar_FF_ram _ (hO.dia_mem_ram _ _ h), map_smul, smul_smul, inv_mul_cancel₀ hqr,
    one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem diaFFStar_inj (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ φ' : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) (h' : φ' ∈ Mram k n (GA D S → ℂ))
    (he : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ')) : φ = φ' := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  have h2 : FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ))) = FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ'))) := by rw [he]
  have hd : ∀ X : Form k n (GA D S → ℂ), dia ε⁻¹ (dia ε X) = X := fun X => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hd, hd, hO.FF_FFStar_ram _ h, hO.FF_FFStar_ram _ h'] at h2
  exact smul_right_injective _ hqr h2

end Ops

theorem ramBijective_at (q : Unif k) (χ₀ : AddChar k Circle) (hχ : HasConductor χ₀ 1) (ε : 𝓀[k]ˣ)
    (β : Frame p S n) (P : Pair k n) :
    Set.BijOn (sOp β P q (resChar χ₀ hχ q) ε) {φ₀ | RamAt β P φ₀} {φ₀ | RamAt β P φ₀} ∧
      (∀ φ, IsRam β φ → IsRam β (dia ε (FFStar q (resChar χ₀ hχ q) φ)) ∧
        sOp β P q (resChar χ₀ hχ q) ε (φ P) = dia ε (FFStar q (resChar χ₀ hχ q) φ) P) ∧
      ∃ c c' : GL n k →₀ ℂ, (∀ φ₀, sOp β P q (resChar χ₀ hχ q) ε φ₀ = c.sum fun g a => a • β.rep g φ₀) ∧
        ∀ φ₀, RamAt β P φ₀ → sOp β P q (resChar χ₀ hχ q) ε (c'.sum fun g a => a • β.rep g φ₀) = φ₀ ∧
          RamAt β P (c'.sum fun g a => a • β.rep g φ₀) := by
  set χ := resChar χ₀ hχ q with hχdef
  have hO : OperatorIdentities k n (GA D S → ℂ) q χ :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ₀ hχ n).1 (GA D S → ℂ)).2
  set r : ℂ := ((resCard k : ℂ) ^ Fintype.card n)⁻¹ with hr

  have hval : ∀ φ, IsRam β φ → sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P := fun φ hφ => by
    show dia ε (FFStar q χ (formAt β P (φ P))) P = _
    rw [formAt_eq β P hφ.1]

  have hinv : ∀ φ, IsRam β φ → sOp β P q χ ε ((r • FF q χ (dia ε⁻¹ φ)) P) = φ P := fun φ hφ => by
    rw [hval _ (isRam_FFdia q χ ε β hO r hφ), diaFFStar_inv q χ ε hO hφ.2.1]
  let gch : Pair k n → GL n k := fun P₁ => Classical.epsilon fun g : GL n k => g • P = P₁
  refine ⟨⟨?_, ?_, ?_⟩, fun φ hφ => ⟨isRam_diaFFStar q χ ε β hO hφ, hval φ hφ⟩,
    ∑ P₁ ∈ withKer (ε • P).lat, Finsupp.single (gch P₁) (χ (-cross q P₁ (ε • P))),
    ∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q)), fun φ₀ => ?_, fun φ₀ hφ₀ => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, isRam_diaFFStar q χ ε β hO hφ, (hval φ hφ).symm⟩
  · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨φ', hφ', rfl⟩ he
    rw [hval φ hφ, hval φ' hφ'] at he
    have hX := isRam_diaFFStar q χ ε β hO hφ
    have hX' := isRam_diaFFStar q χ ε β hO hφ'
    have he' : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ') := by
      rw [← formAt_eq β P hX.1, ← formAt_eq β P hX'.1, he]
    rw [diaFFStar_inj q χ ε hO hφ.2.1 hφ'.2.1 he']
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, ⟨_, isRam_FFdia q χ ε β hO r hφ, rfl⟩, hinv φ hφ⟩
  · rw [sum_single_sum]
    rfl
  · obtain ⟨φ, hφ, rfl⟩ := hφ₀
    have hc : (∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q))).sum
        (fun g a => a • β.rep g (φ P)) = (r • FF q χ (dia ε⁻¹ φ)) P := by
      rw [sum_single_sum, Pi.smul_apply, FF_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [smul_smul, dia_apply]
      conv_rhs => rw [← formAt_eq β P hφ.1]
      rfl
    rw [hc]
    exact ⟨hinv φ hφ, _, isRam_FFdia q χ ε β hO r hφ, rfl⟩

end GlobalTheory.FinPl.RamBij

namespace GlobalTheory.FinPl

theorem ramBijective_holds : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  intro D k _ _ _ _ p n _ _ q χ₀ hχ χ hχeq ε S β P
  subst hχeq
  exact RamBij.ramBijective_at q χ₀ hχ ε β P

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidDecRTrans
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RTransDecay

theorem rapidDec_rTrans : ∀ (D : D7) (V : HSp D) (G : GA D V → ℂ), RapidDec V G → (∀ h, RapidDec V (rTrans h G)) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ g h, ‖G (g * h)‖ * quotHeight V g ^ N ≤ C * height V h ^ N := by
  intro D V G hG
  refine ⟨fun h => hG.mul_right h, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hG.decay N
  refine ⟨C, fun g h => ?_⟩
  have h1 : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h := by
    simpa using GlobalTheory.Grow.quotHeight_mul_le V (g * h) h⁻¹
  calc ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V g ^ N
        ≤ ‖G (g * h)‖ * (GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (GlobalTheory.Grow.quotHeight_pos V g).le h1 N) (norm_nonneg _)
    _ = ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V (g * h) ^ N * GlobalTheory.Grow.height V h ^ N := by ring
    _ ≤ C * GlobalTheory.Grow.height V h ^ N := mul_le_mul_of_nonneg_right (hC _) (pow_pos (GlobalTheory.Grow.height_pos V h) N).le

end GlobalTheory.RTransDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFlagUnipotentIsotropicBlockUnitriangular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.RatBlock

variable {D : D7}

theorem blockX_mem_UX {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    ∃ u ∈ UX D ρ, blockX d n = u.1 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D V V₀ ρ d).1 n).1 hn
  have h1 : mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  refine ⟨u, hu, ?_⟩
  rw [blockX, h1, ← Matrix.mul_assoc d.pX d.jX, d.pX_jX, Matrix.one_mul]

theorem blockX_col_of_fix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {g : GA D V} (k : Fin ρ)
    (h : g ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k)) (i : Fin ρ) :
    blockX d g i k = (1 : Mx D ρ ρ) i k := by
  have hcol : ∀ l, (mt V g ⬝ d.jX) l k = d.jX l k := fun l => by
    have := congrFun (congrFun (mem_fixer.1 h) l) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using this
  rw [← d.pX_jX, blockX, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [hcol l]

end GlobalTheory.Unf.RatBlock

open GlobalTheory.Unf.RatBlock in

theorem GlobalTheory.Unf.ratBlock_unitri : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ ∧ u * u' = 1 ∧ u' * u = 1 ∧ (∀ i, u i i = 1) ∧ (∀ i k, k < i → u i k = 0) ∧ ∀ j : Fin ρ, γ ∈ Nfix d j → ∀ i k, k ≤ j → u i k = if i = k then 1 else 0 := by
  intro D V V₀ ρ d γ hq hn
  obtain ⟨M, hM⟩ := (mem_GQ_iff V γ).1 hq
  have hM' : rat M = mt V γ := hM
  have hb : (rat (d.qX * (M * d.e)) : Mx D ρ ρ) = blockX d γ := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  obtain ⟨v, hv, hvb⟩ := blockX_mem_UX d hn
  have hent : ∀ i k, incA D ((d.qX * (M * d.e)) i k) = v.1 i k := fun i k => by
    have := congrFun (congrFun (hb.trans hvb) i) k
    exact this
  have hdiag : ∀ i, (d.qX * (M * d.e)) i i = 1 := fun i =>
    incA_injective (by rw [map_one, hent]; exact ((mem_UX.1 hv) i i).2)
  have hlow : ∀ i k, k < i → (d.qX * (M * d.e)) i k = 0 := fun i k hki =>
    incA_injective (by rw [map_zero, hent]; exact ((mem_UX.1 hv) i k).1 hki)
  have hdet : (d.qX * (M * d.e)).det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k (hki : k < i) => hlow i k hki)]
    simp [hdiag]
  have hu : IsUnit (d.qX * (M * d.e)).det := by rw [hdet]; exact isUnit_one
  refine ⟨d.qX * (M * d.e), (d.qX * (M * d.e))⁻¹, hb, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
    hdiag, hlow, fun j hj i k hkj => ?_⟩
  have hfix : γ ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k) := by
    have h2 := (Subgroup.mem_inf.1 hj).2
    exact (Subgroup.mem_iInf.1 h2) ⟨k, hkj⟩
  apply incA_injective
  have e1 := blockX_col_of_fix d k hfix i
  rw [← hb] at e1
  change incA D _ = _ at e1
  rw [e1, Matrix.one_apply]
  split_ifs <;> simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFramesSameGramOneUnitaryOrbit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.WittOrbit
variable {D : D7}

theorem isQA_sig (D : D7) : GlobalTheory.SgAlg.IsQA (D.sp.cm.sig : D.host.E →+* D.host.E) := by
  refine ⟨fun x => star_star x, ?_, inferInstance, ?_, fun x _ hx => isUnit_iff_ne_zero.2 hx⟩
  · by_contra h
    push_neg at h
    have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ :=
      eq_top_iff.2 fun x _ => Algebra.mem_bot.2 ((D.sp.cm.fixed x).1 (h x))
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
    rw [D.sp.cm.deg2] at h1
    exact absurd h1 (by norm_num)
  · exact isUnit_iff_ne_zero.2 two_ne_zero

theorem free_of_li {n ρ : ℕ} (x : Matrix (Fin n) (Fin ρ) D.host.E) (h : LinearIndependent D.host.E x.transpose) :
    GlobalTheory.SgAlg.Free x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem isUnit_of_unitary (W : HSp D) {g : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : gᴴ * W.gram * g = W.gram) : IsUnit g := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact gram_det_ne W this.symm

theorem orb_eq_orbit : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E),
    LinearIndependent D.host.E x₀.transpose →
      (∀ x ∈ Orb W x₀, ∃ γ ∈ GQ W, mt W γ ⬝ (rat x₀ : Mx D W.rank ρ) = rat x) ∧
        ∀ γ ∈ GQ W, ∀ x ∈ Orb W x₀, ∃ x' ∈ Orb W x₀, mt W γ ⬝ (rat x : Mx D W.rank ρ) = rat x' := by
  intro D W ρ x₀ h₀
  have hJ : GlobalTheory.SgAlg.IsHermU (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram :=
    ⟨gram_conjTranspose W, gram_isUnit_det W⟩
  refine ⟨fun x hx => ?_, fun γ hγ x hx => ?_⟩
  · obtain ⟨g, hg, hgx⟩ := GlobalTheory.SgAlg.witt_free_field _ (isQA_sig D) W.gram hJ x₀ x (free_of_li x₀ h₀)
      (free_of_li x hx.1) (by
        show x₀ᴴ * W.gram * x₀ = xᴴ * W.gram * x
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
        exact hx.2.symm)
    have hg' : gᴴ * W.gram * g = W.gram := hg
    have hu : adj (rat g) * (gA W * rat g) = gA W := by
      rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← Matrix.mul_assoc, hg']
    refine ⟨ofMat W (rat g) hu, (mem_GQ_iff W _).2 ⟨g, rfl⟩, ?_⟩
    rw [mt_ofMat, ← rat_mul, hgx]
  · obtain ⟨g, hg⟩ := (mem_GQ_iff W γ).1 hγ
    replace hg : rat g = mt W γ := hg
    have hu : gᴴ * W.gram * g = W.gram := rat_injective (by
      rw [rat_mul, rat_mul, rat_conjTranspose, hg]
      exact mt_rel W γ)
    have hgu := isUnit_of_unitary W hu
    refine ⟨g * x, ⟨?_, ?_⟩, by rw [← hg, ← rat_mul]⟩
    · refine Matrix.mulVec_injective_iff.1 ?_
      intro v w hvw
      simp only [← Matrix.mulVec_mulVec] at hvw
      exact Matrix.mulVec_injective_iff.2 hx.1 (Matrix.mulVec_injective_iff_isUnit.2 hgu hvw)
    · show (g * x)ᴴ * (W.gram * (g * x)) = gramQ W x₀
      rw [← hx.2, gramQ, Matrix.conjTranspose_mul]
      calc xᴴ * gᴴ * (W.gram * (g * x)) = xᴴ * ((gᴴ * W.gram * g) * x) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hu]

end GlobalTheory.WittOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDoma
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.RationalSubgroupFund

theorem countable_discrete_exists_fundamentalDomain : ∀ (D : D7) (W : HSp D) (Γ : Subgroup (GA D W)), Γ ≤ GQ W → Countable Γ ∧ DiscreteTopology Γ ∧ ∀ μ : Measure (GA D W), μ.IsHaarMeasure → ∃ 𝓑 : Set (GA D W), IsFundamentalDomain Γ 𝓑 μ := by
  intro D W Γ hΓ
  obtain ⟨_, h2, _, h4, h5, h6, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := h2; haveI := h4; haveI := h5; haveI := h6
  haveI hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨(x : GA D W), hΓ x.2⟩ : GQ W))
      (continuous_subtype_val.subtype_mk _)
      (fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy))
  obtain ⟨hc, 𝓓, h𝓓m, h𝓓⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  haveI := hc
  refine ⟨hc, hdisc, fun μ _ => ⟨𝓓, ?_⟩⟩
  exact IsFundamentalDomain.mk' h𝓓m.nullMeasurableSet (fun g => h𝓓 g)

end GlobalTheory.RationalSubgroupFund
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasures
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem sFinite_vol : ∀ (D : D7) (ρ m : ℕ) (vb : VolM D ρ m) (vU : VolU D ρ), SFinite vb.μ ∧ SFinite vU.ν := by
  intro D ρ m vb vU
  constructor
  · obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D ρ m
    haveI : IsTopologicalAddGroup (Mx D ρ m) := i1
    haveI : LocallyCompactSpace (Mx D ρ m) := i2
    haveI : SecondCountableTopology (Mx D ρ m) := i3
    haveI : vb.μ.IsAddHaarMeasure := vb.covol.1
    haveI : SigmaFinite vb.μ := Measure.IsAddHaarMeasure.sigmaFinite _
    infer_instance
  · obtain ⟨i1, i2, -⟩ := GlobalTheory.UnitU.topology D ρ
    haveI : LocallyCompactSpace (UX D ρ) := i1
    haveI : SecondCountableTopology (UX D ρ) := i2
    haveI : vU.ν.IsHaarMeasure := vU.unit.1
    haveI : SigmaFinite vU.ν := Measure.IsHaarMeasure.sigmaFinite _
    infer_instance

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixUniformlyLocallyConstantBoun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SBUnif

theorem uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (Ψ : Matrix n n' k → ℂ), Ψ ∈ SB (Matrix n n' k) → ∃ N : ℕ, 0 < N ∧ (∀ X Y : Matrix n n' k, (∀ i j, Y i j ∈ 𝒪[k]) → Ψ (X + (N : k) • Y) = Ψ X) ∧ ∀ X, Ψ X ≠ 0 → ∀ i j, (N : k) * X i j ∈ 𝒪[k] := by
  intro k _ _ _ _ n n' _ _ _ _ Ψ hΨ
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset (GlobalTheory.LocMod.Inhab.eventually_invariant hΨ)
  have hinv : ∀ X u, u ∈ GlobalTheory.LocMod.Inhab.box n n' a → Ψ (X + u) = Ψ X := fun X u hu =>
    GlobalTheory.LocMod.Inhab.invariant_of_tsupport (K := GlobalTheory.LocMod.Inhab.box n n' a) (fun u hu => ha u hu) u hu X
  obtain ⟨R, hR⟩ := GlobalTheory.LocMod.Inhab.exists_cosets hΨ a
  let F : Finset k := insert (a : k) ((R ×ˢ (Finset.univ ×ˢ Finset.univ)).image fun x => x.1 x.2.1 x.2.2)
  obtain ⟨b, -, hb⟩ := F.exists_max_image (fun x => valuation k x) ⟨_, Finset.mem_insert_self _ _⟩
  have hab : valuation k (a : k) ≤ valuation k b := hb _ (Finset.mem_insert_self _ _)
  have ha0 : valuation k (a : k) ≠ 0 := by simp
  have hb0 : valuation k b ≠ 0 := fun h => ha0 (le_antisymm (h ▸ hab) zero_le')
  have hsupp : ∀ X, Ψ X ≠ 0 → ∀ i j, valuation k (X i j) ≤ valuation k b := by
    intro X hX i j
    obtain ⟨r, hr, hXr⟩ := hR X hX
    have h1 : valuation k ((X - r) i j) ≤ valuation k (a : k) := hXr i j
    have h2 : valuation k (r i j) ≤ valuation k b :=
      hb _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(r, i, j), by simp [hr], rfl⟩))
    have e : X i j = r i j + (X - r) i j := by simp
    rw [e]
    exact Valuation.map_add_le _ h2 (h1.trans hab)
  have hq := GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one (k := k)
  obtain ⟨e₁, he₁⟩ := exists_pow_lt₀ hq (Units.mk0 _ ha0)
  obtain ⟨e₂, he₂⟩ := exists_pow_lt₀ hq (Units.mk0 _ (inv_ne_zero hb0))
  have hpos : 0 < resCard k := Nat.card_pos
  refine ⟨resCard k ^ (e₁ + e₂), pow_pos hpos _, ?_, ?_⟩
  · intro X Y hY
    refine hinv X _ fun r q => ?_
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, Nat.cast_pow, map_pow]
    have hY' : valuation k (Y r q) ≤ 1 := hY r q
    calc valuation k (resCard k : k) ^ (e₁ + e₂) * valuation k (Y r q)
        ≤ valuation k (resCard k : k) ^ e₁ * 1 :=
          mul_le_mul' (pow_le_pow_right_of_le_one' hq.le (Nat.le_add_right _ _)) hY'
      _ ≤ valuation k (a : k) := by rw [mul_one]; exact he₁.le
  · intro X hX i j
    show valuation k _ ≤ 1
    rw [map_mul, Nat.cast_pow, map_pow]
    calc valuation k (resCard k : k) ^ (e₁ + e₂) * valuation k (X i j)
        ≤ (valuation k b)⁻¹ * valuation k b :=
          mul_le_mul' ((pow_le_pow_right_of_le_one' hq.le (Nat.le_add_left _ _)).trans he₂.le) (hsupp X hX i j)
      _ = 1 := inv_mul_cancel₀ hb0

end GlobalTheory.SBUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShortVectorCuspUnipotentCoverAllInstancesStatement
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortVectorCuspUnipotentCover_all_instances : ∀ I : AutInst, ShortCusp I := by
  first | exact @GlobalTheory.CuspGeo.shortCusp_all | exact GlobalTheory.CuspGeo.shortCusp_all | (intros; apply GlobalTheory.CuspGeo.shortCusp_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAllStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_character_conductor_almost_all : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ᶠ v : Pl D in cofinite, ∀ s ∈ idAt D (· = v), (∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.Conductor.eventually_conductor | exact GlobalTheory.FinPl.Conductor.eventually_conductor | (intros; apply GlobalTheory.FinPl.Conductor.eventually_conductor <;> assumption)
end

