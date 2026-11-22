import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetCharInvariantSameValueTwisted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

theorem colSub_totalDegree_le {ι : Type} [Fintype ι] {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  classical
  unfold colSub
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  have h1 : (∑ j' : Fin a, C (g i.1 j' i.2.2) * (X (i.1, i.2.1, j') : Pol ι d a)).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ h1
    _ = s i := mul_one _

theorem star_detChar_mul_detChar {ι : Type} [Fintype ι] {a : ℕ} (n : ι → ℕ) (g : ι → Matrix.unitaryGroup (Fin a) ℂ) :
    starRingEnd ℂ (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) *
      detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
  unfold detChar
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [map_pow, ← mul_pow]
  have h : starRingEnd ℂ (g τ : Matrix (Fin a) (Fin a) ℂ).det * (g τ : Matrix (Fin a) (Fin a) ℂ).det = 1 := by
    rw [starRingEnd_apply, ← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 (g τ).2,
      Matrix.det_one]
  rw [h, one_pow]

@[reducible] def fockCore {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := Formalism.L2.DIV.fockS x.1 y.1
  conj_inner_symm x y := (fockS_conj x.1 y.1).symm
  re_inner_nonneg x := by
    by_cases hx : x.1 = 0
    · simp [hx, Formalism.L2.DIV.fockS]
    · exact (fockS_self_re_pos hx).le
  add_left x y z := by
    show Formalism.L2.DIV.fockS (x.1 + y.1) z.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_add₂]
    rfl
  smul_left x y r := by
    show Formalism.L2.DIV.fockS (r • x.1) y.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  definite x hx := by
    by_contra h
    have h' : x.1 ≠ 0 := fun e => h (Subtype.ext e)
    have := fockS_self_re_pos h'
    rw [show Formalism.L2.DIV.fockS x.1 x.1 = 0 from hx] at this
    simp at this

theorem exists_mem_inv_eq_of_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  intro ι _ a d n Pr _ _ q hq P
  classical
  let S : Submodule ℂ (Pol ι d a) := restrictTotalDegree (Var ι d a) ℂ P.totalDegree
  haveI : FiniteDimensional ℂ S :=
    inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Var ι d a) ℂ P.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fockCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  have hmemS : ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (x : Pol ι d a), x ∈ S → colSub g x ∈ S := fun g x hx =>
    (mem_restrictTotalDegree _ _ _).2 ((colSub_totalDegree_le g x).trans ((mem_restrictTotalDegree _ _ _).1 hx))
  let gen : Set S := {w | ∃ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (x : S),
      (w : Pol ι d a) = colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) x.1 -
        detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • x.1}
  let K : Submodule ℂ S := Submodule.span ℂ gen
  have hK : ∀ w ∈ K, q (w : Pol ι d a) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, y, hy⟩ := hx
      rw [hy, map_sub, map_smul, hq, sub_self]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have hPS : P ∈ S := (mem_restrictTotalDegree _ _ _).2 le_rfl
  obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal (⟨P, hPS⟩ : S)
  refine ⟨z.1, ?_, ?_⟩
  · intro g
    set G := colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) z.1 with hG
    set c := detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) with hc
    let w : S := ⟨G - c • z.1, S.sub_mem (hmemS _ _ z.2) (S.smul_mem c z.2)⟩
    have hw : w ∈ K := Submodule.subset_span ⟨g, z, rfl⟩
    have h1 : Formalism.L2.DIV.fockL z.1 (G - c • z.1) = 0 := Submodule.inner_left_of_mem_orthogonal hw hz
    have h2 : Formalism.L2.DIV.fockL (G - c • z.1) z.1 = 0 := Submodule.inner_right_of_mem_orthogonal hw hz
    have hinv : Formalism.L2.DIV.fockL G G = Formalism.L2.DIV.fockL z.1 z.1 := by
      rw [Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockL_apply, hG, fockS_colSub_unitary]
    have hcc := star_detChar_mul_detChar n g
    rw [← hc] at hcc
    have e1 : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) =
        Formalism.L2.DIV.fockL (G - c • z.1) G - c * Formalism.L2.DIV.fockL (G - c • z.1) z.1 := by
      rw [map_sub, map_smul, smul_eq_mul]
    have e2 : Formalism.L2.DIV.fockL (G - c • z.1) G =
        Formalism.L2.DIV.fockL G G - starRingEnd ℂ c * Formalism.L2.DIV.fockL z.1 G := by
      rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    have h1' : Formalism.L2.DIV.fockL z.1 G - c * Formalism.L2.DIV.fockL z.1 z.1 = 0 := by
      rw [← h1, map_sub, map_smul, smul_eq_mul]
    have hWW : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) = 0 := by
      linear_combination e1 + e2 - c * h2 + hinv - starRingEnd ℂ c * h1' - Formalism.L2.DIV.fockL z.1 z.1 * hcc
    by_contra hne
    have hne' : G - c • z.1 ≠ 0 := sub_ne_zero.2 hne
    have := fockS_self_re_pos hne'
    rw [← Formalism.L2.DIV.fockL_apply, hWW] at this
    simp at this
  · have hP : P = y.1 + z.1 := congrArg Subtype.val hyz
    rw [hP, map_add, hK y hy, zero_add]

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulBlockUnitaryDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DetDecomp

open GlobalTheory.UTrans

theorem hf_single {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    hf σ M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [hf, Pi.single_apply]

theorem isU_mat {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (M γ : Matrix (Fin n) (Fin n) R)
    (h : IsU σ M γ) : γᵀ * M * γ.map σ = M := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hf_single] at this
  rw [← this]
  simp only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.col_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_aniso {K : Type} [Field K] [CharZero K] {n : ℕ} (σ : K →+* K) (hσ : ∀ a, σ (σ a) = a)
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ a b, σ (M a b) = M b a) {i j : Fin n} (hij : M i j ≠ 0) :
    ∃ x : Fin n → K, hf σ M x x ≠ 0 := by
  by_contra hno
  push_neg at hno
  set x : Fin n → K := Pi.single i 1
  set y : Fin n → K := Pi.single j 1
  have hm0 : hf σ M x y ≠ 0 := by rw [hf_single]; exact hij
  have hc := Calc.hf_conj σ M hσ hM x y
  have e : hf σ M (x + hf σ M x y • y) (x + hf σ M x y • y) = hf σ M x x + σ (hf σ M x y) * hf σ M x y
      + hf σ M x y * hf σ M y x + hf σ M x y * σ (hf σ M x y) * hf σ M y y := by
    simp only [Calc.hf_add_left, Calc.hf_add_right, Calc.hf_smul_left, Calc.hf_smul_right]
    ring
  rw [hno, hno x, hno y, ← hc] at e
  have hs : σ (hf σ M x y) ≠ 0 := (map_ne_zero σ).2 hm0
  have : (2 : K) * (σ (hf σ M x y) * hf σ M x y) = 0 := by linear_combination -e
  rcases mul_eq_zero.1 this with h2 | h2
  · exact two_ne_zero h2
  · exact mul_ne_zero hs hm0 h2

theorem refl_isU_det {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a)
    (M : Matrix (Fin n) (Fin n) R) (hM : ∀ a b, σ (M a b) = M b a) (x : Fin n → R) {Q r z : R}
    (hQ : hf σ M x x = Q) (hrQ : r * Q = 1) (hcr : σ r = r) (hz : z * σ z = 1) :
    IsU σ M (tv σ M x ((z - 1) * r)) ∧ (tv σ M x ((z - 1) * r)).det = z := by
  refine ⟨Calc.isU_tv σ M hσ hM x _ ?_, ?_⟩
  · rw [hQ, map_mul, map_sub, map_one, hcr]
    linear_combination r * hz + (z - 1) * (σ z - 1) * r * hrQ
  · rw [Calc.tv_det, hQ]
    linear_combination (z - 1) * hrQ

variable {D : D7}

theorem hf_incA (V : HSp D) (x0 : Fin V.rank → D.host.E) :
    hf (cA D) (V.gram.map (incA D))ᵀ (fun a => incA D (x0 a)) (fun a => incA D (x0 a)) =
      incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) := by
  simp only [hf, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA,
    starRingEnd_apply]

theorem exists_aniso_gram (V : HSp D) (hV : 0 < V.rank) :
    ∃ x0 : Fin V.rank → D.host.E, hf (starRingEnd D.host.E) V.gramᵀ x0 x0 ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, V.gramᵀ i j ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply GlobalTheory.LevelSubgroup.gram_det_ne_zero V
    have h0 : V.gram = 0 := Matrix.ext fun a b => hne b a
    rw [h0]
    haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
    exact Matrix.det_zero
  exact exists_aniso _ (fun a => star_star a) _ (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) hij

theorem exists_det_eq (V : HSp D) (hV : 0 < V.rank) (z : Formalism.L2.Theta.AE D) (hz : z * cA D z = 1) :
    ∃ g : GA D V, (mt V g).det = z := by
  obtain ⟨x0, hx0⟩ := exists_aniso_gram V hV
  have hqs : star (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = hf (starRingEnd D.host.E) V.gramᵀ x0 x0 :=
    Calc.hf_conj (starRingEnd D.host.E) V.gramᵀ (fun a => star_star a) (fun a b => GlobalTheory.DualPairCheck.gram_star V b a) x0 x0
  have hrQ : incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ * incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have hcr : cA D (incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹) =
      incA D (hf (starRingEnd D.host.E) V.gramᵀ x0 x0)⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, hqs]
  have hMA : ∀ a b, cA D ((V.gram.map (incA D))ᵀ a b) = (V.gram.map (incA D))ᵀ b a := fun a b => by
    simp only [Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨hU, hdet⟩ := refl_isU_det (cA D) GlobalTheory.DualPairCheck.cA_cA _ hMA _ (hf_incA V x0) hrQ hcr hz
  generalize tv (cA D) ((HSpace.gram V).map ⇑(incA D))ᵀ (fun a ↦ (incA D) (x0 a))
    ((z - 1) * (incA D) (hf (starRingEnd D.host.E) (HSpace.gram V)ᵀ x0 x0)⁻¹) = γ at hU hdet
  have hzu : IsUnit z := ⟨⟨z, cA D z, hz, by rw [mul_comm]; exact hz⟩, rfl⟩
  have hmat := congrArg Matrix.transpose (isU_mat (cA D) _ _ hU)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
    ← Matrix.mul_assoc] at hmat
  have hunit := (Matrix.isUnit_iff_isUnit_det γ).2 (by rw [hdet]; exact hzu)
  refine ⟨⟨hunit.unit, ?_⟩, ?_⟩
  · show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) hunit.unit.1 * JR (AF D.host.F) V.gram * hunit.unit.1 =
      JR (AF D.host.F) V.gram
    rw [IsUnit.unit_spec]
    exact hmat
  · show (hunit.unit.1).det = z
    rw [IsUnit.unit_spec]
    exact hdet

theorem det_blk {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (P : Matrix (Fin p) (Fin p) R)
    (Q : Matrix (Fin q) (Fin q) R) : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q).det = P.det * Q.det := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem skewGram_det_ne (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) :
    (skewGram A B e).det ≠ 0 := by
  rw [skewGram, Matrix.det_smul, det_blk, Matrix.det_transpose, Matrix.det_transpose]
  exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
    (mul_ne_zero (GlobalTheory.LevelSubgroup.gram_det_ne_zero A) (GlobalTheory.LevelSubgroup.gram_det_ne_zero B))

theorem det_mul_conj (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e) (x : UB J) : (mat x).det * cA D (mat x).det = 1 := by
  have hx : (mat x)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (mat x).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  have hd := congrArg Matrix.det hx
  have hm : ((mat x).map (cA D)).det = cA D (mat x).det := (RingHom.map_det (cA D) (mat x)).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm] at hd
  have hJ : IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).det := by
    have hm' : (J.map (incA D)).det = incA D J.det := (RingHom.map_det (incA D) J).symm
    show IsUnit (J.map (incA D)).det
    rw [hm']
    have h0 : J.det ≠ 0 := h ▸ skewGram_det_ne A B e
    refine ⟨⟨incA D J.det, incA D J.det⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    · rw [← map_mul, inv_mul_cancel₀ h0, map_one]
  apply hJ.mul_right_injective
  simp only
  rw [mul_one]
  linear_combination hd

theorem mat_blkU (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e) (g : GA D A × GA D B) :
    mat (blkU A B e h g) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (mt A g.1) (mt B g.2) := rfl

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem exists_detOne_mul_blkU : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = skewGram A B e), 0 < d → ∀ x : UB J, ∃ (s : UB J) (g : GA D A × GA D B), (mat s).det = 1 ∧ x = s * blkU A B e h g := by
  intro D A B d e J h hd x
  have hz := det_mul_conj A B e h x
  have hzu : IsUnit (mat x).det := ⟨⟨_, _, hz, by rw [mul_comm]; exact hz⟩, rfl⟩
  have hcard : A.rank + B.rank = d := by simpa using Fintype.card_congr e
  obtain ⟨g, hg⟩ : ∃ g : GA D A × GA D B, (mat (blkU A B e h g)).det = (mat x).det := by
    rcases Nat.eq_zero_or_pos A.rank with hA | hA
    · obtain ⟨g, hg⟩ := exists_det_eq B (by omega) _ hz
      exact ⟨(1, g), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, one_mul, hg]⟩
    · obtain ⟨g, hg⟩ := exists_det_eq A hA _ hz
      exact ⟨(g, 1), by rw [mat_blkU, det_blk, mt_one, Matrix.det_one, mul_one, hg]⟩
  refine ⟨x * (blkU A B e h g)⁻¹, g, ?_, (inv_mul_cancel_right x _).symm⟩
  have hm : mat x = mat (x * (blkU A B e h g)⁻¹) * mat (blkU A B e h g) := by
    conv_lhs => rw [← inv_mul_cancel_right x (blkU A B e h g)]
    rfl
  have hd2 := congrArg Matrix.det hm
  rw [Matrix.det_mul, hg] at hd2
  apply hzu.mul_left_injective
  simp only [one_mul]
  exact hd2.symm

end GlobalTheory.DetDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.LatMove

open scoped Matrix

theorem mem_hat_stdLat_iff {D : D7} {n : ℕ} (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E n : Set (Fin n → D.host.E)) ↔ IntVec z := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, r, congrArg (fun t => a ⊗ₜ[D.host.F] t) hr.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [Submodule.mem_one.2 ⟨x, rfl⟩, zero_mem _]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

theorem mem_hat_colLat_iff {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E)
    (w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) ↔
      IntVec (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) := by
  have ew : GlobalTheory.UnRep.fm D.host.F B.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.HatPullback.fm_mul', Units.mul_inv, GlobalTheory.HatPullback.fm_one', Matrix.one_mulVec]
  have h1 := GlobalTheory.HatPullback.main D.host.F D.host.E n B (Formalism.L2.DIV.colLat B) (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w)
  rw [ew, GlobalTheory.ColStd.colLat_comap_eq_stdLat] at h1
  exact h1.trans (mem_hat_stdLat_iff _)

theorem swap_mem_hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (u i)) ∈ Formalism.L2.Herm.hatL (F := F) L ↔
      u ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  rw [GlobalTheory.GenusTranslate.hatL_iff]
  simp only [AlgEquiv.symm_apply_apply]

theorem exists_move {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) :
    ∃ x ∈ GfC V, ∀ w, w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin V.rank → D.host.E)) ↔
      (finHom V x).1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨x, hx, h⟩ := GlobalTheory.GenusTranslate.exists_move_colLat D V B _ hB (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)
  refine ⟨x, hx, fun w => ?_⟩
  have h1 := h fun i => Formalism.IndefR.Lev.swapAE D (w i)
  have h2 : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (w i)) =
      fun i => Formalism.IndefR.Lev.swapAE D (((finHom V x).1 *ᵥ w) i) :=
    funext fun i => (RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) (finHom V x).1 w i).symm
  rw [h2] at h1
  exact (swap_mem_hatL_iff _ w).symm.trans (h1.trans (swap_mem_hatL_iff _ ((finHom V x).1 *ᵥ w)))

theorem exists_finite_point : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  intro D _ V M hM
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse hM)
  obtain ⟨B, rfl⟩ := hu
  obtain ⟨x, hx, h⟩ := exists_move V B hM
  refine ⟨x⁻¹, inv_mem hx, fun y => ?_⟩
  have hL : L0c D V = (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) :=
    Set.ext fun z => (GlobalTheory.PlaceModel.mem_latFrame V z).symm
  have h1 := h ((finHom V x⁻¹).1 *ᵥ y)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec,
    mem_hat_colLat_iff, Matrix.coe_units_inv] at h1
  rw [hL]
  exact h1.symm

end GlobalTheory.DefTransfer.LatMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSquaringPathWithTangentVector
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_path_tan : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R] [Algebra ℚ R], Smooth G.hom → QuasiSeparated G.hom → ∀ (b : Sp R ⟶ S) (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∃ ξ, IsPath G 2 b ξ ∧ HasTan G b ξ τ w := by
  intro S G _ R _ _ _ hsm hqs b n V τ w hbV
  set s : S := b (IsLocalRing.closedPoint R)
  set β : S.presheaf.stalk s →+* R := (Scheme.stalkClosedPointTo b).hom
  have hβ : Spec.map (CommRingCat.ofHom β) ≫ S.fromSpecStalk s = b :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk b
  obtain ⟨-, -, -, hev4, -, -, hev7⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hsV : s ∈ V := (hev4 R S b V).1 hbV
  obtain ⟨π, ε, m, hSD, hεπ, hmπ, hεm⟩ := GlobalTheory.T.exists_groupSchemeUnitStalkData S G s
  have hfs := GlobalTheory.T.formallySmooth_stalk_unit_smooth_groupScheme S G hsm s π ε m hSD
  have hm2 := GlobalTheory.T.groupSchemeSquaring_cotangent_eq_two S G hqs s π ε m hSD
  obtain ⟨δ, hδ, hδπ, hδτ⟩ := GlobalTheory.T.exists_stalkDerivation_of_lieSheafSections S G R s π ε m β n V hsV τ w hSD
  obtain ⟨ψ, hψπ, hψ0, hψ1, hψ2⟩ := GlobalTheory.T.exists_path_formallySmooth_ring _ _ R π ε m β δ hfs hεπ hmπ hεm hm2 hδ hδπ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ G.left.fromSpecStalk (unitSec G s), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← hSD.str, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψπ,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hβ]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ0, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hSD.unit, ← Category.assoc, hβ]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ2, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hSD.sq, Category.assoc]
  · intro U hU V' hV he hb f
    have hs' : s ∈ V' := (hev4 R S b V').1 hb
    have hp : unitSec G s ∈ U := he hs'
    obtain ⟨h₁, e₁⟩ := hev7 (PowerSeries R) G.left (unitSec G s) ψ U hp
    rw [show evAt _ hU f = evAt _ h₁ f from rfl, e₁, hψ1, hδτ U hp V' hV he hs' f]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    obtain ⟨h₂, e₂⟩ := hev7 R S s β V' hs'
    rw [← e₂]
    have key : ∀ {b₁ b₂ : Sp R ⟶ S} (_ : b₁ = b₂) (k₁ : ⊤ ≤ b₁ ⁻¹ᵁ V') (k₂ : ⊤ ≤ b₂ ⁻¹ᵁ V') (g : Γ(S, V')),
        evAt b₁ k₁ g = evAt b₂ k₂ g := by
      rintro _ _ rfl _ _ _; rfl
    exact key hβ h₂ hb _

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantThetaMeanSquareFormStatement
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergInvariant_thetaMeanSquare_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ M : Submodule ℂ (WOF F E nS nT → ℂ), (∀ f ∈ M, IsThetaFunOF σ JS JT ξ₀ B.ψ f) →
      ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∃ Bf : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WOF F E nS nT) (f g f' g' : M),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u f → (g' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u g →
            Bf f' g' = Bf f g) ∧
          ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (Bf f f).re := by
  first | exact @GlobalTheory.ThetaMeanSquareF.exists_invariant_form | exact GlobalTheory.ThetaMeanSquareF.exists_invariant_form | (intros; apply GlobalTheory.ThetaMeanSquareF.exists_invariant_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlockStatement
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRationalWeilOperator_leviBlock : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (g h : Matrix κ κ F), gᵀ * h = 1 →
    HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  first | exact @GlobalTheory.RatWeilOp.hasOp_levi | exact GlobalTheory.RatWeilOp.hasOp_levi | (intros; apply GlobalTheory.RatWeilOp.hasOp_levi <;> assumption)
end

