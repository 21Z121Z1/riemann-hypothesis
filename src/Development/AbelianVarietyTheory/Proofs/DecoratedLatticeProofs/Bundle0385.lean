import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthSumSp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def col {V W : HSpace E} {k : ℕ} (X : Matrix (Fin V.rank) (Fin k) E) (Y : Matrix (Fin W.rank) (Fin k) E) :
    Matrix (Fin (GlobalTheory.Doubling.hsum V W).rank) (Fin k) E :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem col_gram {V W : HSpace E} {k l : ℕ} (X : Matrix (Fin V.rank) (Fin k) E) (Y : Matrix (Fin W.rank) (Fin k) E)
    (X' : Matrix (Fin V.rank) (Fin l) E) (Y' : Matrix (Fin W.rank) (Fin l) E) :
    (col X Y)ᴴ * (GlobalTheory.Doubling.hsum V W).gram * col X' Y' = Xᴴ * V.gram * X' + Yᴴ * W.gram * Y' := by
  rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, col, col, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp

def orthSumDec (D : D7) (A L : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A L) A L where
  iA := col 1 0
  iB := col 0 1
  isoA := by rw [col_gram]; simp
  isoB := by rw [col_gram]; simp
  orth := by rw [col_gram]; simp
  rank_add := rfl

@[reducible] def posSp (D : D7) (ρ : ℕ) : HSp D where
  V := Fin ρ → D.host.E
  hT := Formalism.BasicNotions.Examples₂.diagForm ρ (fun _ => false)
  herm := Formalism.BasicNotions.Examples₂.diagForm_isSymm ρ _
  nondeg := Formalism.BasicNotions.Examples₂.diagForm_nondeg ρ _
  rank := ρ
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := fun _ => (ρ, 0)
  L0 := Formalism.BasicNotions.Examples₂.stdLat ρ
  standardTuple_isLattice := Formalism.BasicNotions.Examples₂.stdLat_isLattice ρ
  baseLattice_isUnimodular := Formalism.BasicNotions.Examples₂.stdLat_unimod Formalism.BasicNotions.Examples₂.star_isIntegral ρ _

theorem posSp_sigOK (D : D7) (ρ : ℕ) : (posSp D ρ).SigOK :=
  Formalism.BasicNotions.Examples₂.posSpace_sigOK (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral ρ

theorem posSp_gram (D : D7) (ρ : ℕ) : (posSp D ρ).gram = 1 := by
  funext i j
  rw [Matrix.one_apply]
  refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral ρ (fun _ => false) ρ 0 i j).trans ?_
  simp [Formalism.BasicNotions.Examples₂.sgn]

@[reducible] def hypSp (D : D7) (ρ : ℕ) : HSp D :=
  GlobalTheory.Doubling.hdbl (posSp D ρ)

theorem hypSp_sigOK (D : D7) (ρ : ℕ) : (hypSp D ρ).SigOK :=
  GlobalTheory.Doubling.sigOK_hdbl (posSp_sigOK D ρ)

theorem hypSp_sig (D : D7) (ρ : ℕ) (τ) : (hypSp D ρ).sig τ = (ρ, ρ) := by
  show (ρ, 0) + (0, ρ) = (ρ, ρ)
  simp

def hypSumDec (D : D7) (A : HSp D) (ρ : ℕ) : HypDec (GlobalTheory.Doubling.hsum A (hypSp D ρ)) A ρ where
  e := col 0 (col (1 : Matrix (Fin ρ) (Fin ρ) D.host.E) (1 : Matrix (Fin ρ) (Fin ρ) D.host.E))
  e' := col 0 (col ((2 : D.host.E)⁻¹ • (1 : Matrix (Fin ρ) (Fin ρ) D.host.E)) (-((2 : D.host.E)⁻¹ • (1 : Matrix (Fin ρ) (Fin ρ) D.host.E))))
  i₀ := col 1 0
  ee := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]; simp
  e'e' := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]; simp
  e'e := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]
    simp [Matrix.smul_eq_diagonal_mul, ← two_mul]
  iso := by rw [col_gram]; simp
  i₀e := by rw [col_gram]; simp
  i₀e' := by rw [col_gram]; simp
  rank_add := by show A.rank + 2 * ρ = A.rank + (ρ + ρ); omega

theorem exists_orthSum_hypSum : ∀ (D : D7), (∀ A L : HSp D, A.SigOK → L.SigOK → ∃ (S : HSp D) (_ : OrthDec S A L), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + L.sig τ) ∧ ∀ (A : HSp D) (ρ : ℕ), A.SigOK → ∃ (S : HSp D) (_ : HypDec S A ρ), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + (ρ, ρ) := by
  intro D
  refine ⟨fun A L hA hL => ⟨_, orthSumDec D A L, GlobalTheory.Doubling.sigOK_hsum hA hL, fun τ => rfl⟩,
    fun A ρ hA => ⟨_, hypSumDec D A ρ, GlobalTheory.Doubling.sigOK_hsum hA (hypSp_sigOK D ρ), fun τ => ?_⟩⟩
  show A.sig τ + (hypSp D ρ).sig τ = _
  rw [hypSp_sig]

end GlobalTheory.OrthSumSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField

noncomputable section

namespace GlobalTheory.FinPl.LocGen

theorem half_diff_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (half_diff_ne_bot D)
  have hc0 : ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    rw [Host.ccE, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact D.host.ccK_ne_bot
  exact mul_ne_zero hc0 (inv_ne_zero hb0)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_incA_int (q : SplitPt D k) (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D (x : D.host.E))) := (x.2).map ((q.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (q.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

theorem exists_gen : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k), ∃ a₀ ∈ (D.host.AA : Set D.host.E), q.pr (incA D a₀) ≠ 0 ∧
      ∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / q.pr (incA D a₀) ∈ 𝒪[k] := by
  intro D k _ _ _ _ q
  classical
  set π : D.host.E →+* k := q.pr.comp (incA D) with hπ
  have hinj : Function.Injective π := π.injective
  have hfg : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E)).FG :=
    FractionalIdeal.fg_unit (Units.mk0 D.host.AA (AA_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]; simp
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun x => valuation k (π x)) hsne
  have hjmem : j ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := hs ▸ Submodule.subset_span hj
  have hj0 : π j ≠ 0 := by
    intro h0
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs, Submodule.span_eq_bot]
    intro i hi
    have h1 := hmax i hi
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (h1.trans π.map_zero.symm)
  refine ⟨j, hjmem, hj0, ?_⟩
  intro a ha
  have ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E) := hs.symm ▸ ha
  change π a / π j ∈ 𝒪[k]
  clear ha
  induction ha' using Submodule.span_induction with
  | mem x hx =>
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax x hx) zero_le'
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_div]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul, mul_div_assoc]
    exact mul_mem (pr_incA_int q r) hx

end GlobalTheory.FinPl.LocGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPrimeToDvdAway
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HalfTmul

theorem exists_prime_to_dvd_away {R : Type} [CommRing R] [IsDedekindDomain R] (SS : Finset (HeightOneSpectrum R))
    (m : R) (hm : m ≠ 0) : ∃ t : R, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧
      ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t = m * w := by
  classical
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hm
  have hfac : ∀ Q : HeightOneSpectrum R, ∃ n : ℕ, ∃ J : Ideal R, ¬ Q.asIdeal ∣ J ∧ Ideal.span {m} = Q.asIdeal ^ n * J :=
    fun Q => WfDvdMonoid.max_power_factor hI Q.prime.irreducible
  choose n J hJ using hfac
  have hT := Ideal.finite_factors hI
  obtain ⟨t0, ht0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := SS ∪ hT.toFinset) (fun Q => Q.asIdeal)
    (fun Q => if Q ∈ SS then 1 else n Q) (fun Q _ => Q.prime) (fun Q _ Q' _ h e => h (HeightOneSpectrum.ext e))
    (fun Q => if (Q : HeightOneSpectrum R) ∈ SS then 1 else 0)
  have hone : ∀ Q : HeightOneSpectrum R, (1 : R) ∉ Q.asIdeal := fun Q h1 =>
    Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hSS : ∀ Q ∈ SS, t0 ∉ Q.asIdeal := by
    intro Q hQ hmem
    have h := ht0 Q (Finset.mem_union_left _ hQ)
    simp only [if_pos hQ, pow_one] at h
    exact hone Q (by simpa using Q.asIdeal.sub_mem hmem h)
  have hgood : ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t0 = m * w := by
    intro Q hQ
    by_cases hQT : Q.asIdeal ∣ Ideal.span {m}
    · have h := ht0 Q (Finset.mem_union_right _ (hT.mem_toFinset.2 hQT))
      simp only [if_neg hQ, sub_zero] at h
      obtain ⟨hnd, hEq⟩ := hJ Q
      rw [Ideal.dvd_iff_le] at hnd
      obtain ⟨u, huJ, huQ⟩ := SetLike.not_le_iff_exists.1 hnd
      refine ⟨u, huQ, ?_⟩
      have hmem : t0 * u ∈ Ideal.span {m} := by
        rw [hEq]; exact Ideal.mul_mem_mul h huJ
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 hmem
      exact ⟨w, by rw [mul_comm u, hw]⟩
    · refine ⟨m, ?_, t0, rfl⟩
      intro hmem
      exact hQT (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem))
  by_cases h0 : t0 = 0
  · refine ⟨m, hm, ?_, fun Q _ => ⟨1, hone Q, 1, by ring⟩⟩
    intro Q hQ
    exact absurd (h0 ▸ Q.asIdeal.zero_mem) (hSS Q hQ)
  · exact ⟨t0, h0, hSS, hgood⟩

theorem tmul_mem_of {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (c : ℕ) (hc : 0 < c) (y : W) (hy : y ∈ twist₂ M c (expS SS)) (t : 𝓞 E)
    (ht : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ SS → ∃ u : 𝓞 E, u ∉ Q.asIdeal ∧ ∃ w : 𝓞 E, u * t = (c : 𝓞 E) ^ 2 * w) :
    ((t : E) * (c : E)⁻¹) • y ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcast : ∀ (r : 𝓞 E) (z : W), (r : E) • z = r • z := fun r z => IsScalarTower.algebraMap_smul E r z
  have hcy : (c : E) • y ∈ M := by
    have h := (GlobalTheory.CommonReps.mem_twO_zero M c _).1 (GlobalTheory.CommonReps.natsmul_mem_twO M c _ _ (fun Q => by
      rcases expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num) hy)
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  apply Formalism.L2.Ker.mem_of_forall_locP M
  intro Q
  by_cases hQ : Q ∈ SS
  · have h1 := (Formalism.L2.Ker.mem_twO M c _ y).1 hy Q
    simp only [expS, if_pos hQ, zpow_one] at h1
    obtain ⟨s, hs, hsy⟩ := h1
    refine ⟨s, hs, ?_⟩
    have e : s • (((t : E) * (c : E)⁻¹) • y) = t • (s • ((c : E)⁻¹ • y)) := by
      rw [← hcast s, ← hcast t, ← hcast s]
      simp only [smul_smul]
      congr 1; ring
    rw [e]; exact M.smul_mem t hsy
  · obtain ⟨u, hu, w, huw⟩ := ht Q hQ
    refine ⟨u, hu, ?_⟩
    have huwE : (u : E) * (t : E) = (c : E) ^ 2 * (w : E) := by
      have := congrArg (fun r : 𝓞 E => (r : E)) huw
      simpa using this
    have e : u • (((t : E) * (c : E)⁻¹) • y) = w • ((c : E) • y) := by
      rw [← hcast u, ← hcast w]
      simp only [smul_smul]
      congr 1
      field_simp
      linear_combination huwE
    rw [e]; exact M.smul_mem w hcy

theorem exists_tmul_mem_perO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧ ((t : D.host.E) * (c : D.host.E)⁻¹) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  obtain ⟨t, ht0, hSS, hgood⟩ := exists_prime_to_dvd_away SS ((c : 𝓞 D.host.E) ^ 2)
    (pow_ne_zero _ (by exact_mod_cast hc.ne'))
  exact ⟨t, ht0, hSS, tmul_mem_of _ SS c hc y hy t hgood⟩

end GlobalTheory.HalfTmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPattern
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.SymRes

theorem exists_red_iff_isPat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] (I : Ideal O) (π : O →+* k) (h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk I) π)
    {s κ r : ℕ} (hr : r = κ + (s + 1)) (S : GlobalTheory.SymChain.SymData k s κ) (g : GL (Fin r) (O ⧸ I)) :
    (∃ x : S.P.J, ∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
      b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O, Ideal.Quotient.mk I z = g.val a' b' →
      valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - π z) < 1) ↔ IsPat S.ρ κ g := by
  subst hr
  let e : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hfree : ∀ a b, FreePos S.ρ κ (e a).val (e b).val ↔ GlobalTheory.SymChain.FreeTop S.ρ a b := by
    intro a b
    rw [he, he]
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl, Sum.elim_inr, GlobalTheory.SymChain.FreeTop, FreePos, Fin.lt_def] <;>
      have := a.2 <;> have := b.2 <;> omega
  choose l hl using fun a b => Ideal.Quotient.mk_surjective (I := I) (g.val (e a) (e b))
  have key : ∀ a b, g.val (e a) (e b) = (1 : Matrix _ _ (O ⧸ I)) (e a) (e b) ↔
      valuation k (π (l a b) - (1 : Matrix _ _ k) a b) < 1 := by
    intro a b
    have h4 := h.ker (l a b - if a = b then 1 else 0)
    rw [map_sub, map_sub, sub_eq_zero, apply_ite (Ideal.Quotient.mk I), apply_ite π, map_one, map_one, map_zero,
      map_zero, hl] at h4
    rw [Matrix.one_apply, Matrix.one_apply]
    simp only [e.apply_eq_iff_eq]
    convert h4
  constructor
  · rintro ⟨x, hx⟩ i j hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have h1 := hx a b _ _ (he a) (he b) _ (hl a b)
    have h2 := ((GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x.1).1 x.2).2 a b (fun h' => hij ((hfree a b).2 h'))
    have h3 := (valuation k).map_sub_lt h2 h1
    rw [sub_sub_sub_cancel_left] at h3
    exact (key a b).2 h3
  · intro hg
    have hM : (Matrix.of l).map (Ideal.Quotient.mk I) = g.val.submatrix e e := Matrix.ext hl
    have hu : IsUnit ((Matrix.of l).map (Ideal.Quotient.mk I)).det := by
      rw [hM, det_submatrix_equiv_self]
      convert (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    obtain ⟨x, hx1, hx2⟩ := (h.isUnit_det_iff _).1 hu
    have hx3 : ∀ a b, x.val a b = π (l a b) := fun a b => congrFun (congrFun hx2 a) b
    refine ⟨⟨x, (GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x).2 ⟨by convert hx1, fun a b hab => ?_⟩⟩, ?_⟩
    · rw [hx3]
      exact (key a b).1 (hg _ _ fun h' => hab ((hfree a b).1 h'))
    · intro a b a' b' ha hb z hz
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      change valuation k (x.val a b - π z) < 1
      rw [hx3, ← map_sub, ← h.ker, map_sub, hl, hz, sub_self]

theorem exists_red_iff : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)), (∃ x, G.Red x g) ↔ GlobalTheory.SymRes.IsPat D.R.rS D.R.k g := by
  intro D u d τ PP G g
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP G.idem
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hρ : D.R.rS = G.S.ρ := by
    have := G.hs
    have := G.S.odd
    unfold Ranks.rS
    omega
  let π : 𝓞 D.host.E →+* G.k :=
    (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).comp (oToS D.host.F D.host.E)
  have hπ : ∀ z : 𝓞 D.host.E, π z = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := fun z =>
    h1 (incA D (z : D.host.E))
  have h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk PP.asIdeal) π :=
    ⟨h2.field, fun z => h2.int _, fun z => (iff_of_eq (congrArg (· = 0) (resS_oToS (F := D.host.F) PP z).symm)).trans (h2.ker _)⟩
  have := exists_red_iff_isPat PP.asIdeal π h hr G.S g
  simp only [hπ] at this
  rw [hρ]
  exact this

end GlobalTheory.SymRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SeeSaw.LevRed

open GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem finE_val' (V : HSp D) (g : GA D V) : (Lev.finE V g).val = (mt V g).map (toEAf D) := rfl

theorem exists_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (Formalism.L2.DIV.frGL β y).val * β.val = β.val * (Formalism.L2.DIV.intGL F E n y).val := by
  have h0 : Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL F E n y := inv_mul_cancel_right _ _
  rw [← Units.val_mul, h0, Units.val_mul]

theorem eq_map_of_moved {S K n : Type} [CommRing S] [CommRing K] [Fintype n] [DecidableEq n] (π : S →+* K) (β : GL n S)
    (x y : Matrix n n S) (h1 : x * β.val = β.val * y) (T T' H N M : Matrix n n K) (hT : T' * T = 1)
    (hN : T * β.val.map π = N) (hM : H * N = N * M) (hx : T * x.map π = H * T) : M = y.map π := by
  have h2 : x.map π * β.val.map π = β.val.map π * y.map π := by rw [← Matrix.map_mul, h1, Matrix.map_mul]
  have h3 : N * M = N * y.map π := by
    rw [← hM, ← hN, Matrix.mul_assoc _ _ (y.map π), ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hx]
  have h4 : ((β⁻¹).val.map π * T') * N = 1 := by
    rw [← hN, Matrix.mul_assoc, ← Matrix.mul_assoc T', hT, Matrix.one_mul, ← Matrix.map_mul,
      Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  calc M = ((β⁻¹).val.map π * T') * (N * M) := by rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
    _ = y.map π := by rw [h3, ← Matrix.mul_assoc, h4, Matrix.one_mul]

set_option maxHeartbeats 1000000 in

theorem red_of_movedTo (q : SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k)
    (hN : MovedTo (ofSplit q) V t β N) (hM : (mt V h).map q.pr * N = N * M)
    (hx : Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β) (i j : Fin V.rank) (z : 𝓞 D.host.E)
    (hz : Ideal.Quotient.mk PP.asIdeal z = (Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j) :
    valuation k (M i j - (ofSplit q).pr (z : D.host.E)) < 1 := by
  obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP
  obtain ⟨y, hy⟩ := hx
  rw [← hy, Formalism.L2.DIV.redFn_frGL] at hz
  choose l hl using exists_lift (D := D)
  have hπ' : ∀ m : Matrix (Fin V.rank) (Fin V.rank) (AE D), (m.map (toEAf D)).map π' = m.map q.pr := fun m => by
    ext a b; exact hπ _
  have hb : (β.val.map l).map (toEAf D) = β.val := by ext a b; exact hl _
  have hN' : (mt V t).map q.pr * β.val.map π' = N := by
    rw [← hN _ hb, Matrix.map_mul]
    congr 1
    conv_lhs => rw [← hb]
    exact hπ' _
  let ψ := π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have h1 : (Lev.finE V (t⁻¹ * h * t)).val * β.val = β.val * (Formalism.L2.DIV.intGL D.host.F D.host.E _ y).val := by
    have h0 := frGL_mul β y
    rw [hy] at h0
    exact h0
  have hfin : (Lev.finE V (t⁻¹ * h * t)).val.map π' = (mt V (t⁻¹ * h * t)).map q.pr := by
    rw [finE_val', hπ']
  have h5 := eq_map_of_moved π' β _ _ h1 ((mt V t).map q.pr) ((mt V t⁻¹).map q.pr) _ N M
    (by rw [← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one', Matrix.map_one _ (map_zero _) (map_one _)]) hN' hM
    (by
      rw [hfin, ← Matrix.map_mul, ← Matrix.map_mul, ← mt_mul', ← mt_mul', mul_assoc, mul_inv_cancel_left])
  have h7 : M i j = ψ (y.val i j) := congrFun (congrFun h5 i) j
  have h6 : (ofSplit q).pr (z : D.host.E) = ψ (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
  rw [h7, h6, ← map_sub, ← hred.ker, map_sub, Formalism.L2.DIV.resS_oToS, hz]
  exact sub_self _

end GlobalTheory.SeeSaw.LevRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_data_conductor_one : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), d.c.Is → PP ∈ d.c.Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar d.c.ψ ψk → HasConductor ψk 1 → ∀ s ρ : ℕ, s = 2 * ρ → ∃ S : SymData k s D.R.k, S.ψ = ψk ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j) := by
  first | exact @GlobalTheory.LocMod.SymChainAt.exists_symData_at | exact GlobalTheory.LocMod.SymChainAt.exists_symData_at | (intros; apply GlobalTheory.LocMod.SymChainAt.exists_symData_at <;> assumption)
end

