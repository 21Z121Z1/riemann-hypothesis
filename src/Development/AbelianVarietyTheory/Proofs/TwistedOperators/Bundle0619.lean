import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1722
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KapXLineDec

variable {D : D7}

theorem pre_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1 ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig X.gram := by
  have h0 : (u.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (u.1.1).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := u.2
  show ((reindex e.symm e.symm u.1.1).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram * reindex e.symm e.symm u.1.1 =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
  generalize u.1.1 = M at h0 ⊢
  clear u
  subst hJ
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h0
  have h1 := congrArg (fun A => incA D D.host.xi0⁻¹ • A) h0
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul] at h1
  have h2 := congrArg (fun A => Aᵀ.submatrix e e) h1
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ))ᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e.symm e.symm := rfl
  simp only [transpose_mul, transpose_transpose, e1] at h2
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram = ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e.symm e.symm).submatrix e e := by simp
  have e3 : ((reindex e.symm e.symm M).map (cA D))ᵀ = ((M.map (cA D))ᵀ).submatrix e e := rfl
  rw [e2, e3, reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
  exact h2

def pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : GA D X :=
  ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1, pre_mem X e hJ u⟩

theorem kapX_pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : kapX X e hJ (pre X e hJ u) = u := by
  apply Subtype.ext
  apply Units.ext
  show reindex e e (reindex e.symm e.symm u.1.1) = u.1.1
  simp

theorem pre_mul (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (u v : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    pre X e hJ (u * v) = pre X e hJ u * pre X e hJ v := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom (u.1 * v.1) =
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom u.1 *
      Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom v.1
  exact map_mul _ _ _

theorem continuous_pre (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : Continuous (pre X e hJ) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp continuous_subtype_val).matrix_reindex e.symm e.symm
  · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_reindex e.symm e.symm

theorem pre_mem_GinfC (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) {u : UA D.sp.cm.sig Wd.J}
    (hu : u ∈ UAt D.sp.cm.sig Wd (evI D.host.F)) : pre X e hJ u ∈ GinfC X := by
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  show (Formalism.L2.Theta.mt X (pre X e hJ u)).map (finPart D) = 1
  ext i j
  have h1 : At (evI D.host.F) (mat u (e i) (e j) - (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j)) :=
    fun w hw => congrFun (congrFun (hu w hw) (e i)) (e j)
  have h2 := GlobalTheory.ConjInfExp.finPart_eq_one (mat u (e i) (e j) - (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j) + 1)
    (by rwa [add_sub_cancel_right])
  rw [RingHom.map_add, RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at h2
  show finPart D (mat u (e i) (e j)) = (1 : Matrix (Fin X.rank) (Fin X.rank) _) i j
  rw [h2]
  by_cases c : i = j
  · subst c; simp
  · have c' : e i ≠ e j := fun k => c (e.injective k)
    simp [Matrix.one_apply_ne c, Matrix.one_apply_ne c']

theorem lie_of {n : Type} [Fintype n] [DecidableEq n] (G Y : Matrix n n ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ * G * NormedSpace.exp (t • Y) = G) : Yᴴ * G + G * Y = 0 := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have e1 : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ = NormedSpace.exp (t • Yᴴ) := fun t => by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]
  have h1 := ((hasDerivAt_exp_smul_const (Yᴴ) (0:ℝ)).mul_const G).mul (hasDerivAt_exp_smul_const Y (0:ℝ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  have hc : ((fun y : ℝ => NormedSpace.exp (y • Yᴴ) * G) * fun u : ℝ => NormedSpace.exp (u • Y)) = fun _ => G :=
    funext fun t => by
      show NormedSpace.exp (t • Yᴴ) * G * NormedSpace.exp (t • Y) = G
      rw [← e1]; exact h t
  have h2 : HasDerivAt (fun _ : ℝ => G) (Yᴴ * G * 1 + G * Y) 0 :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun hc t).symm)
  have h3 := h2.unique (hasDerivAt_const (0:ℝ) G)
  simpa only [mul_one] using h3

end GlobalTheory.KapXLineDec

open GlobalTheory.KapXLineDec in

theorem GlobalTheory.KapXLineDec.line_dec : ∀ (D : D7) (θ : InfFam D) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ), IsInfFam θ →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod) := by
  intro D θ X d e Wd hJ hθ γ hγ
  classical
  let h : ℝ → GA D X := fun t => pre X e hJ (γ (Multiplicative.ofAdd t))
  have hc : Continuous h := (continuous_pre X e hJ).comp (hγ.1.comp continuous_ofAdd)
  have hadd : ∀ s t, h (s + t) = h s * h t := fun s t => by
    show pre X e hJ (γ (Multiplicative.ofAdd (s + t))) = _
    rw [ofAdd_add, map_mul, pre_mul]
  have h0 : h 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hfin : ∀ t, h t ∈ GinfC X := fun t => pre_mem_GinfC X e Wd hJ (hγ.2 _)
  let N : D.what₂.Tau → ℝ → Matrix (Fin X.rank) (Fin X.rank) ℂ := fun τ t => infMat D.sp.cm.sig X.gram (θ τ) (h t)
  have hNc : ∀ τ, Continuous (N τ) := fun τ => (GlobalTheory.Mem.VolExists.continuous_infMat X.gram (hθ τ)).comp hc
  have hN0 : ∀ τ, N τ 0 = 1 := fun τ => by
    show infMat D.sp.cm.sig X.gram (θ τ) (h 0) = 1
    rw [h0]; exact GlobalTheory.PointAtPlaceHom.infMat_one X _
  have hNm : ∀ τ s t, N τ (s + t) = N τ s * N τ t := fun τ s t => by
    show infMat D.sp.cm.sig X.gram (θ τ) (h (s + t)) = _
    rw [hadd]; exact GlobalTheory.PointAtPlaceHom.infMat_mul X _ _ _
  choose Y hY using fun τ => GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous (N τ) (hNc τ) (hN0 τ) (hNm τ)
  have hYl : ∀ τ, Y τ ∈ lieAt X τ := fun τ =>
    lie_of _ _ fun t => (hY τ t) ▸ GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ X (h t) τ
  let L : List D.what₂.Tau := (Finset.univ : Finset D.what₂.Tau).toList
  refine ⟨L.map fun τ => (τ, Y τ), ?_, fun t => ?_⟩
  · intro q hq
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hq
    exact hYl τ
  · have hP : ((L.map fun τ => (τ, Y τ)).map fun q => oneP θ X q.1 q.2 t).prod = h t := by
      refine GlobalTheory.RowReal.IsRealAll.unique hθ (M := fun τ => N τ t) ⟨?_, fun σ => ?_⟩ ⟨hfin t, fun σ => rfl⟩
      · refine Subgroup.list_prod_mem (GinfC X) fun x hx => ?_
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hq
        exact (GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hYl τ) t).1
      · have e1 : GlobalTheory.RowReal.infMatHom X (θ σ) ((L.map fun τ => (τ, Y τ)).map fun q => oneP θ X q.1 q.2 t).prod =
            (L.map fun ρ => if ρ = σ then N σ t else 1).prod := by
          rw [map_list_prod, List.map_map, List.map_map]
          congr 1
          refine List.map_congr_left fun ρ _ => ?_
          show infMat D.sp.cm.sig X.gram (θ σ) (oneP θ X ρ (Y ρ) t) = _
          have hs := GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hYl ρ) t
          by_cases hρ : ρ = σ
          · subst hρ
            rw [if_pos rfl]
            exact hs.2.1.trans (hY ρ t).symm
          · rw [if_neg hρ]
            exact hs.2.2 σ (Ne.symm hρ)
        exact e1.trans (GlobalTheory.RowReal.list_prod_map_ite _ _ L (Finset.nodup_toList _)
          (Finset.mem_toList.2 (Finset.mem_univ _)))
    rw [hP]
    exact (kapX_pre X e hJ _).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumFirstBlockBlockDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.BlockSubst

def firstCols (D₁ D₂ : Type) [Fintype D₁] [Fintype D₂] : D₁ ≃ ↥(Assignment.one.block D₁ D₂) where
  toFun j := ⟨Sum.inl j, by simp [Assignment.block]⟩
  invFun x := Sum.getLeft x.1 (by simpa [Assignment.block] using x.2)
  left_inv j := rfl
  right_inv x := by
    obtain ⟨x | x, hx⟩ := x
    · rfl
    · simp [Assignment.block] at hx

theorem forall_mem_block_one {D₁ D₂ : Type} [Fintype D₁] [Fintype D₂] (p : D₁ ⊕ D₂ → Prop) :
    (∀ j ∈ Assignment.one.block D₁ D₂, p j) ↔ ∀ j : D₁, p (Sum.inl j) := by
  constructor
  · intro h j; exact h _ (by simp [Assignment.block])
  · rintro h (j | j) hj
    · exact h j
    · simp [Assignment.block] at hj

theorem sum_mul_eq_trace {A D : Type} [Fintype A] [Fintype D] {k : Type} [Field k] (X Z : Matrix A D k) :
    ∑ i, ∑ j, X i j * Z i j = trace (X * Zᵀ) := by
  simp [trace, Matrix.mul_apply]

end GlobalTheory.BlockSubst

open GlobalTheory.BlockSubst in
theorem GlobalTheory.BlockSubst.fourierSum_blockDiag_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ Y : Matrix A (D₁ ⊕ D₂) k,
      fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) Y =
        fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) := by
  intro k _ _ _ _ A D₁ D₂ _ _ _ _ _ _ ψ ϖ e hϖ hψ Φ hΦ M₁ hM₁ M₂ hM₂ Y
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  set P := Assignment.one.block D₁ D₂ with hP
  set E := firstCols D₁ D₂ with hE
  set c : k := ((ϖ ^ e : kˣ) : k) with hc
  obtain ⟨hM1, hM1'⟩ := (mem_KO_iff M₁).1 hM₁
  obtain ⟨hT1, hT1'⟩ := (mem_KO_iff _).1 (invT_mem_KO hM₁)
  have hsumP : ∀ f : ↥P → k, ∑ j : ↥P, f j = ∑ j : D₁, f (E j) := fun f =>
    (Fintype.sum_equiv E _ _ fun _ => rfl).symm
  have hX1 : ∀ (X : Matrix A (D₁ ⊕ D₂) k) (a : Matrix D₁ D₁ k) (b : Matrix D₂ D₂ k) i j,
      (X * fromBlocks a 0 0 b) i (Sum.inl j) = ∑ l, X i (Sum.inl l) * a l j := by
    intro X a b i j; simp [Matrix.mul_apply, Fintype.sum_sum_type]
  have hX2 : ∀ (X : Matrix A (D₁ ⊕ D₂) k) (a : Matrix D₁ D₁ k) (b : Matrix D₂ D₂ k) i j,
      (X * fromBlocks a 0 0 b) i (Sum.inr j) = ∑ l, X i (Sum.inr l) * b l j := by
    intro X a b i j; simp [Matrix.mul_apply, Fintype.sum_sum_type]
  set Y₁ : Matrix A D₁ k := Matrix.of fun i j => Y i (Sum.inl j) with hY₁
  have hYH : ∀ i j, (Y * fromBlocks (invT M₁).val 0 0 M₂.val) i (Sum.inl j) = (Y₁ * (invT M₁).val) i j := by
    intro i j; rw [hX1]; simp [Y₁, Matrix.mul_apply]
  have hinv : (invT M₁).val * M₁.valᵀ = 1 := by
    rw [invT_val, ← transpose_mul, Units.mul_inv, transpose_one]
  have hinv' : M₁.val * ((invT M₁).val)ᵀ = 1 := by
    rw [invT_val, transpose_transpose, Units.mul_inv]
  have hint : ∀ (X : Matrix A D₁ k) (B : Matrix D₁ D₁ k), (∀ i j, B i j ∈ 𝒪[k]) →
      (∀ i j, c * X i j ∈ 𝒪[k]) → ∀ i j, c * (X * B) i j ∈ 𝒪[k] := by
    intro X B hB hX i j
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Subring.sum_mem _ fun l _ => by rw [← mul_assoc]; exact mul_mem (hX i l) (hB l j)
  have hcond : (∀ i, ∀ j ∈ P, c * Y i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ P, c * (Y * fromBlocks (invT M₁).val 0 0 M₂.val) i j ∈ 𝒪[k]) := by
    simp only [hP, forall_mem_block_one, hYH]
    constructor
    · intro h; exact hint Y₁ _ hT1 h
    · intro h i j
      have := hint _ M₁.valᵀ (fun i j => by simpa using hM1 j i) h i j
      rwa [Matrix.mul_assoc, hinv, Matrix.mul_one] at this
  set YH := Y * fromBlocks (invT M₁).val 0 0 M₂.val with hYHdef
  have hset : ∀ T' : Matrix A ↥P k, setCols P YH (T' * M₁.val.submatrix E.symm E.symm) =
      setCols P Y T' * fromBlocks M₁.val 0 0 M₂.val := by
    intro T'
    ext i (j | j)
    · rw [hX1]
      simp only [setCols, Matrix.of_apply]
      rw [dif_pos (by simp [hP, Assignment.block]), Matrix.mul_apply, hsumP]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dif_pos (by simp [hP, Assignment.block])]
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
      rfl
    · rw [hX2]
      simp only [setCols, Matrix.of_apply]
      rw [dif_neg (by simp [hP, Assignment.block]), hYHdef, hX2]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dif_neg (by simp [hP, Assignment.block])]
  have hpc : ∀ (Z : Matrix A (D₁ ⊕ D₂) k) (S : Matrix A ↥P k),
      pairCols P Z S = ∑ i, ∑ j : D₁, S i (E j) * Z i (Sum.inl j) := by
    intro Z S; simp only [pairCols]; exact Finset.sum_congr rfl fun i _ => hsumP _
  have hpair : ∀ T' : Matrix A ↥P k, pairCols P YH (T' * M₁.val.submatrix E.symm E.symm) = pairCols P Y T' := by
    intro T'
    set T₁ : Matrix A D₁ k := Matrix.of fun i j => T' i (E j) with hT₁
    have hTN : ∀ i j, (T' * M₁.val.submatrix E.symm E.symm) i (E j) = (T₁ * M₁.val) i j := by
      intro i j; rw [Matrix.mul_apply, hsumP]; simp [T₁, Matrix.mul_apply]
    rw [hpc, hpc]
    simp only [hTN, hYH]
    calc ∑ i, ∑ j, (T₁ * M₁.val) i j * (Y₁ * (invT M₁).val) i j
        = trace ((T₁ * M₁.val) * (Y₁ * (invT M₁).val)ᵀ) := sum_mul_eq_trace _ _
      _ = trace (T₁ * Y₁ᵀ) := by
          rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc M₁.val, hinv', Matrix.one_mul]
      _ = ∑ i, ∑ j, T' i (E j) * Y i (Sum.inl j) := (sum_mul_eq_trace T₁ Y₁).symm
  rw [fourierSum_apply, fourierSum_apply]
  beta_reduce
  split_ifs with h1 h2 h2
  · congr 1
    obtain ⟨u, hu⟩ := hM₁
    let N : Matrix ↥P ↥P 𝒪[k] := u.val.submatrix E.symm E.symm
    let N' : Matrix ↥P ↥P 𝒪[k] := (u⁻¹).val.submatrix E.symm E.symm
    have hN : N * N' = 1 := by
      simp only [N, N', submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]
    have hNk : N.map (fun x => (x : k)) = M₁.val.submatrix E.symm E.symm := by
      rw [← hu]; rfl
    have hF : ∀ T Z : Matrix A ↥P k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) →
        Φ (setCols P YH (T + Z)) * (ψ (pairCols P YH (T + Z)) : ℂ) =
          Φ (setCols P YH T) * (ψ (pairCols P YH T) : ℂ) := by
      intro T Z hZ
      have e1 : setCols P YH (T + Z) = setCols P YH T + setCols P 0 Z := by
        ext i j; by_cases hj : j ∈ P <;> simp [setCols, hj]
      have e2 : pairCols P YH (T + Z) = pairCols P YH T + pairCols P YH Z := by
        simp [pairCols, add_mul, Finset.sum_add_distrib]
      rw [e1, e2, hΦ.2, AddChar.map_add_eq_mul, triv (pairCols P YH Z), mul_one]
      · refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        have h3 := (Valuation.mem_integer_iff _ _).1 (h2 i j j.2)
        rw [map_mul] at h3
        rw [Valuation.mem_integer_iff, map_mul]
        exact (show valuation k (Z i j) * valuation k (YH i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) * valuation k (YH i j) by
          gcongr; exact hZ i j).trans h3
      · refine FourierDepth.mem_matLat_smul_stdLat.2 fun i j => ?_
        by_cases hj : j ∈ P
        · simpa [setCols, hj] using hZ i ⟨j, hj⟩
        · simp [setCols, hj]
    have key : ∑ T : A → ↥P → Res k e, Φ (setCols P YH (liftRes T * N.map (fun x => (x : k)))) *
          (ψ (pairCols P YH (liftRes T * N.map (fun x => (x : k)))) : ℂ) =
        ∑ T : A → ↥P → Res k e, Φ (setCols P YH (liftRes T)) * (ψ (pairCols P YH (liftRes T)) : ℂ) :=
      GlobalTheory.ColSubst.sum_liftRes_mul hϖ e N N' hN (fun T' => Φ (setCols P YH T') * (ψ (pairCols P YH T') : ℂ)) hF
    rw [← key, hNk]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [hset, hpair]
  · exact absurd (hcond.1 h1) h2
  · exact absurd (hcond.2 h2) h1
  · rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodStepInvMulPointShape
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

section Shape
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem basePt_eq_zero_of_stepVar (y : Matrix n n' k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) : basePt c y r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp only [Free, Kept, or_false, false_or] at h <;>
    simp only [basePt, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, of_apply]
  rw [if_neg (by omega)]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem stepVar_fixed_of_ordL_lt (y : Matrix n n' k) {r t : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hv : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) (hlt : GlobalTheory.DiagVol.ordL c r < GlobalTheory.DiagVol.ordL c t) :
    ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) ∧ basePt c y t s = 0 := by
  rcases r with r | r <;> rcases t with t | t <;> rcases s with s | s <;>
    simp only [Free, Kept, GlobalTheory.DiagVol.ordL, Sum.elim_inl, Sum.elim_inr, basePt, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, of_apply, not_or,
      Nat.even_iff, Nat.odd_iff, not_and, true_and, and_true, not_false_eq_true, not_true_eq_false] at hv hlt ⊢
  all_goals first | omega | (refine ⟨⟨by omega, by omega⟩, ?_⟩; rw [if_neg (by omega)]) | (refine ⟨by omega, ?_⟩; rw [if_neg (by omega)]) | skip

end Shape

section Shape2
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n'] [DecidableEq n'] in

theorem unipSub_mul_fixed {u : GL (n ⊕ Fin c) k} (hu : u ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c))
    (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → (u.val * M) r s = basePt c y r s := by
  intro r s hv
  have hu' : ∀ r t, GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r →
      u.val r t = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t := hu
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · rw [hu' r r le_rfl, Matrix.one_apply_eq, one_mul, hM r s hv]
  · intro t _ htr
    by_cases h : GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r
    · rw [hu' r t h, Matrix.one_apply_ne (Ne.symm htr), zero_mul]
    · obtain ⟨h1, h2⟩ := stepVar_fixed_of_ordL_lt y hv (not_le.1 h)
      rw [hM t s h1, h2, mul_zero]
  · simp

omit [Fintype n'] [DecidableEq n'] in

theorem embX_mul_fixed (κ : GL n k) (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) →
      ((embX c κ).val * M) r s = basePt c (κ.val * y) r s := by
  intro r s hv
  have hE : (embX c κ).val = (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) := rfl
  rw [hE, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases r with a | l
  · simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have hb : ∀ b, M (Sum.inl b) s = basePt c y (Sum.inl b) s := fun b =>
      hM _ _ (by rcases s with s | s <;> simpa only [Free, Kept] using hv)
    simp only [hb]
    rcases s with s | s <;> simp [basePt, Matrix.mul_apply]
  · simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single l (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), zero_mul]) (by simp),
      Matrix.one_apply_eq, one_mul, hM _ _ hv]
    rcases s with s | s <;> simp [basePt]

end Shape2

theorem inv_mul_stepPt_shape : ∀ {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (v : GL (n ⊕ Fin c) k), v ∈ symN k n c → ∀ (κ : GL n k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k), ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (fun a => (((v * embX c κ)⁻¹).val * stepPt x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2) := by
  intro k _ n n' _ _ _ _ c v hv κ x₀ e
  have hg : ((v * embX c κ)⁻¹).val = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [_root_.mul_inv_rev, map_inv, Units.val_mul]
  have hu : v⁻¹ ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c) := GlobalTheory.DiagVol.symN_le_unipSub (inv_mem hv)
  have hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → stepPt x₀ e r s = basePt c x₀ r s :=
    fun r s h => by rw [stepPt, Matrix.add_apply, of_apply, dif_neg h, add_zero]
  have hA := embX_mul_fixed κ⁻¹ x₀ _ (unipSub_mul_fixed hu x₀ _ hM)
  have hR : ∀ (y : Matrix n n' k) (e' : StepVar n c n' → k) r s, stepPt y e' r s =
      basePt c y r s + (if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e' ⟨(r, s), h⟩ else 0) :=
    fun _ _ _ _ => rfl
  ext r s
  by_cases h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)
  · conv_rhs => rw [hR, dif_pos h, basePt_eq_zero_of_stepVar _ h, zero_add]
  · conv_rhs => rw [hR, dif_neg h, add_zero]
    rw [hg, Matrix.mul_assoc, hA r s h]

end GlobalTheory.StepLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicDStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∀ f : WO S X → ℂ, IsDatum M ψ cS ΦD f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
        ∃ ΦD' ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD' (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  first | exact @GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD | exact GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD | (intros; apply GlobalTheory.SquareAgree.HeisDeriv.heisDeriv_algD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingAbsoluteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_unfolding_absolute : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ), f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @GlobalTheory.SquareAgree.KerPFin.kerPD_fin | exact GlobalTheory.SquareAgree.KerPFin.kerPD_fin | (intros; apply GlobalTheory.SquareAgree.KerPFin.kerPD_fin <;> assumption)
end

