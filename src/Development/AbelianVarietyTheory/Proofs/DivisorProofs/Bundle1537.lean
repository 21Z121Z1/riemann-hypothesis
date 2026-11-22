import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingUnipotentMemFlagUnipotentRadical
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix GlobalTheory.StdPar
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.CuspUnip

theorem sub_mem_span {A : Type} [CommRing A] {n r d : ℕ} {X Y : Matrix (Fin n) (Fin r) A} {L K : Matrix (Fin r) (Fin n) A}
    (e : Fin d → Fin r) (P Q : Matrix (Fin d) (Fin d) A) (r' : ℕ)
    (hP : ∀ a b : Fin d, ¬ (a.val < r' ∧ r' ≤ b.val) → P a b = 0) {I : Set (Fin r)} {y : Fin n → A}
    (hL : ∀ a, (L *ᵥ y) (e a) = 0)
    (hI : (∀ b : Fin d, r' ≤ b.val → (K *ᵥ y) (e b) = 0) ∨ ∀ a : Fin d, a.val < r' → e a ∈ I) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y - y ∈
      Submodule.span A ((fun i => Xᵀ i) '' I) := by
  have h1 : (fun a => (L *ᵥ y) (e a)) = 0 := funext hL
  rw [GlobalTheory.BlockForms.Norm.blk_mulVec, h1, mulVec_zero, mulVec_zero, add_zero, add_sub_cancel_left]
  rcases hI with hI | hI
  · have h2 : P *ᵥ (fun a => (K *ᵥ y) (e a)) = 0 := funext fun a => by
      simp only [mulVec, dotProduct, Pi.zero_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : r' ≤ b.val
      · change P a b * (K *ᵥ y) (e b) = 0
        rw [hI b hb, mul_zero]
      · rw [hP a b (fun h' => hb h'.2), zero_mul]
    rw [h2, mulVec_zero]
    exact zero_mem _
  · rw [mulVec_eq_sum]
    refine sum_mem fun a _ => ?_
    rw [op_smul_eq_smul]
    by_cases ha : a.val < r'
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e a, hI a ha, rfl⟩)
    · have : (P *ᵥ fun a => (K *ᵥ y) (e a)) a = 0 := by
        simp only [mulVec, dotProduct]
        exact Finset.sum_eq_zero fun b _ => by rw [hP a b (fun h' => ha h'.1), zero_mul]
      rw [this, zero_smul]
      exact zero_mem _

theorem blockEmb_unip_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∀ x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E, ι (GlobalTheory.CuspRep.unip x) ∈ GlobalTheory.StdPar.unip σ J Xf (insert k S) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, _, _, _, hΦ, hι⟩ hS hk0 _ r' hr0 hrd k hk x
  let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
  obtain ⟨k0, hk0S, hk0⟩ := hk0
  have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
  have hLX : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [hm, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [hm, GlobalTheory.StdPar.yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hP : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) (a b : Fin d), ¬ (a.val < r' ∧ r' ≤ b.val) →
      ((GlobalTheory.CuspRep.unip x).1.map Φ.symm - 1) a b = 0 := by
    intro x a b hab
    rw [Matrix.sub_apply, Matrix.map_apply]
    change Φ.symm ((1 + GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) _) a b) - _ = 0
    rw [Matrix.add_apply, map_add, GlobalTheory.CuspRep.nilM, Matrix.of_apply, dif_neg hab, map_zero, add_zero]
    by_cases hab' : a = b <;> simp [Matrix.one_apply, hab']
  have core : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) {I : Set (Fin r)} {y : Fin n → AF F ⊗[F] E},
      (∀ a, (adMat F (cT (σ : E →+* E) X * J) *ᵥ y) (e a) = 0) →
      ((∀ b : Fin d, r' ≤ b.val → (adMat F (cT (σ : E →+* E) Y * J) *ᵥ y) (e b) = 0) ∨ ∀ a : Fin d, a.val < r' → e a ∈ I) →
      (matHom _ σ J (ι (GlobalTheory.CuspRep.unip x))).1 *ᵥ y - y ∈ colSpan F X I := fun x I y h1 h2 => by
    rw [hι]
    exact sub_mem_span (X := adMat F X) (Y := adMat F Y) (L := adMat F (cT (σ : E →+* E) X * J))
      (K := adMat F (cT (σ : E →+* E) Y * J)) e _ _ r' (hP x) h1 h2
  have spL : ∀ {I : Set (Fin r)}, ∀ y ∈ colSpan F X I, ∀ a, (adMat F (cT (σ : E →+* E) X * J) *ᵥ y) (e a) = 0 :=
    fun y hy a => GlobalTheory.BlockForms.Norm.row_span (fun i _ => by rw [hLX]; rfl) hy
  have spK : ∀ {I : Set (Fin r)}, ∀ y ∈ colSpan F X I, ∀ b, e b ∉ I →
      (adMat F (cT (σ : E →+* E) Y * J) *ᵥ y) (e b) = 0 :=
    fun y hy b hb => GlobalTheory.BlockForms.Norm.row_span (fun i hi => by
      rw [hKX, Matrix.one_apply_ne]; rintro rfl; exact hb hi) hy
  have pres : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) {I : Set (Fin r)},
      ((∀ b : Fin d, r' ≤ b.val → e b ∉ I) ∨ ∀ a : Fin d, a.val < r' → e a ∈ I) →
      ∀ y ∈ colSpan F X I, (matHom _ σ J (ι (GlobalTheory.CuspRep.unip x))).1 *ᵥ y ∈ colSpan F X I := fun x I hI y hy => by
    have := add_mem (core x (spL y hy) (hI.imp (fun h b hb => spK y hy b (h b hb)) id)) hy
    rwa [sub_add_cancel] at this
  have u0 : GlobalTheory.CuspRep.unip (0 : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) = 1 := by
    refine Units.ext ?_
    change (1 + GlobalTheory.CuspRep.nilM 0 : Matrix (Fin d) (Fin d) _) = 1
    rw [show GlobalTheory.CuspRep.nilM (0 : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) = 0 from
      Matrix.ext fun i j => by simp [GlobalTheory.CuspRep.nilM], add_zero]
  have hinv : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) y,
      (matHom _ σ J (ι (GlobalTheory.CuspRep.unip (-x)))).1 *ᵥ (matHom _ σ J (ι (GlobalTheory.CuspRep.unip x))).1 *ᵥ y = y := fun x y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, ← map_mul ι, ← GlobalTheory.CuspRep.unip_add, neg_add_cancel, u0, map_one,
      map_one, Units.val_one, one_mulVec]
  have hiff : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) {I : Set (Fin r)},
      ((∀ b : Fin d, r' ≤ b.val → e b ∉ I) ∨ ∀ a : Fin d, a.val < r' → e a ∈ I) →
      ∀ y, y ∈ colSpan F X I ↔ (matHom _ σ J (ι (GlobalTheory.CuspRep.unip x))).1 *ᵥ y ∈ colSpan F X I :=
    fun x I hI y => ⟨pres x hI y, fun hy => by have := pres (-x) hI _ hy; rwa [hinv x y] at this⟩
  have cJ : ∀ j : Fin r, k < j → ∀ a : Fin d, a.val < r' → e a ∈ {i | ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j} :=
    fun j hj a ha => ⟨k, Finset.mem_insert_self _ _, by change l + a.val ≤ k.val; omega, hj⟩
  have cN : ∀ j : Fin r, ¬ k < j → ∀ b : Fin d, r' ≤ b.val → e b ∉ {i | ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j} := by
    rintro j hj b hb ⟨k', hk', h1, h2⟩
    have h1' : l + b.val ≤ k'.val := h1
    have h2' : k'.val < j.val := h2
    rcases Finset.mem_insert.1 hk' with hk'' | hk''
    · rw [hk''] at h1'; omega
    · have h3 : ¬ k'.val + 1 < l + d := fun h' => hS k' (by omega) h' hk''
      exact hj (Fin.lt_def.2 (by omega))
  have cA : ∀ a : Fin d, e a ∈ {i | ∃ k' ∈ insert k S, i ≤ k'} :=
    fun a => ⟨k0, Finset.mem_insert_of_mem hk0S, by change l + a.val ≤ k0.val; omega⟩
  refine ⟨Subgroup.mem_iInf.2 fun j => ?_, hiff x (Or.inr fun a _ => cA a), fun y hy => ?_⟩
  · by_cases hj : k < j
    · exact ⟨hiff x (Or.inr (cJ j hj)), fun y hy => core x (spL y hy) (Or.inr (cJ j hj))⟩
    · refine ⟨hiff x (Or.inl (cN j hj)), fun y hy => core x (spL y hy) (Or.inl fun b hb => spK y hy b ?_)⟩
      intro hb'
      have hjv : j.val = l + b.val := by rw [← Set.mem_singleton_iff.1 hb']
      exact hj (Fin.lt_def.2 (by omega))
  · refine core x (fun a => ?_) (Or.inr fun a _ => cA a)
    simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    exact hy (e a) (cA a)

end GlobalTheory.BlockForms.CuspUnip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

namespace GlobalTheory.LeviHC

section Alg

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def FinMod (K : Submodule ℂ M) (A : Subalgebra ℂ (Module.End ℂ M)) (v : M) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ A, y = K.mkQ (a v)})

def MonicFactorFinite : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (p q : ℂ → Module.End ℂ N),
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∃ (d : ℕ) (c : ℕ → Module.End ℂ N), c d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    ∀ v : N, FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range fun u => p u * q u), y = a v}) →
      FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ a ∈ Algebra.adjoin ℂ (Set.range p), y = a v})

def RelativeCentre : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X → ∀ B : Subalgebra ℂ A,
    (∀ b ∈ B, ∀ i j, X i j * b = b * X i j) →
    ∀ z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) ⊔ B, (∀ i j, X i j * z = z * X i j) →
      z ∈ Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA X)) ⊔ B

def MonicFactorFiniteMod : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
    (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) →
    (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K ∧ q u x ∈ K) →
    (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
    ∀ v ∈ M', FinMod K (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v

theorem coeff_mem_span {d : ℕ} {a : ℕ → M} {p : ℂ → M} (hp : ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i)
    {i : ℕ} (hi : i < d + 1) : a i ∈ Submodule.span ℂ (Set.range p) := by
  set W := Submodule.span ℂ (Set.range p)
  have hdual : ∀ f : Module.Dual ℂ (M ⧸ W), f (W.mkQ (a i)) = 0 := by
    intro f
    let P : Polynomial ℂ :=
      ∑ j ∈ Finset.range (d + 1), Polynomial.C (f (W.mkQ (a j))) * Polynomial.X ^ j
    have hP : P = 0 := by
      apply Polynomial.funext
      intro u
      have h0 : W.mkQ (p u) = 0 :=
        (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span ⟨u, rfl⟩)
      have h1 : f (W.mkQ (p u)) = ∑ j ∈ Finset.range (d + 1), u ^ j * f (W.mkQ (a j)) := by
        rw [hp u, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, smul_eq_mul]
      rw [h0, map_zero] at h1
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
      rw [h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hc := congrArg (fun q : Polynomial ℂ => q.coeff i) hP
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_ite_eq] at hc
    simpa [Finset.mem_range.2 hi] using hc
  have hq : W.mkQ (a i) = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ _).1 hdual
  exact (Submodule.Quotient.mk_eq_zero W).1 hq

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def SmG : Submodule ℂ (GAd σ J → ℂ) where
  carrier := {f | IsSm σ J f}
  add_mem' := isSm_add
  zero_mem' := fun _ _ _ _ => contDiff_const
  smul_mem' := fun a _ h => isSm_smul a h

theorem mem_SmG {f : GAd σ J → ℂ} : f ∈ SmG σ J ↔ IsSm σ J f := Iff.rfl

variable (σ J) in

def IsLineOf {w : InfinitePlace F} (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J) : Prop :=
  ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z)

variable (σ J) in

def IsDer {w : InfinitePlace F} (τ : EmbOver E w)
    (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)) : Prop :=
  (∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) ∧
    ∀ Z γ, IsLineOf σ J τ Z γ → ∀ f : SmG σ J, (D Z f).1 = lineDer γ f.1

variable {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → GAd σ J}

theorem IsLineOf.skew (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 := by
  apply GlobalTheory.LineDerSum.skew_of_exp_unitary
  intro t
  obtain ⟨y, -, hy⟩ := hγ t
  rw [← hy, GlobalTheory.Orb.archMat_eq_archEquiv J h τ y]
  exact (archEquiv J h τ y).2

theorem IsLineOf.isRealLine (h : IsCMExt F E σ) (hγ : IsLineOf σ J τ Z γ) : IsRealLine σ J γ := ⟨w, τ, Z, hγ.skew h, hγ⟩

theorem IsLineOf.unique (h : IsCMExt F E σ) {δ : ℝ → GAd σ J} (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ Z δ) :
    γ = δ := by
  funext t
  obtain ⟨y, hy1, hy2⟩ := hγ t
  obtain ⟨y', hy1', hy2'⟩ := hδ t
  have hyy : y = y' := by
    apply (archEquiv J h τ).injective
    apply Subtype.ext
    apply Units.ext
    rw [← GlobalTheory.Orb.archMat_eq_archEquiv J h τ y, ← GlobalTheory.Orb.archMat_eq_archEquiv J h τ y', hy2, hy2']
  rw [hy1, hy1', hyy]

theorem IsLineOf.smul (hγ : IsLineOf σ J τ Z γ) (c : ℝ) : IsLineOf σ J τ (c • Z) fun t => γ (t * c) := by
  intro t
  obtain ⟨y, h1, h2⟩ := hγ (t * c)
  exact ⟨y, h1, by rw [h2, smul_smul]⟩

private theorem conjTranspose_map_eq_of_isHermND (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) :
    (J.map τ)ᴴ = J.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← h.2.2.2 τ, hJ.1 i j]

private theorem isUnit_det_map_of_det_ne_zero {K : Type} [Field K] {m : ℕ} {M : Matrix (Fin m) (Fin m) K}
    (hM : M.det ≠ 0) (τ : K →+* ℂ) : IsUnit (M.map τ).det := by
  have hd : (M.map τ).det = τ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [isUnit_iff_ne_zero, hd]
  exact (map_ne_zero τ).2 hM

theorem exists_isLineOf (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hZ : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0) :
    ∃ γ, IsLineOf σ J τ Z γ := by
  set A := J.map τ.1 with hAdef
  have hA : Aᴴ = A := conjTranspose_map_eq_of_isHermND h hJ τ.1
  have hd : IsUnit A.det := isUnit_det_map_of_det_ne_zero hJ.2 τ.1
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hd
  have hZ' : Zᴴ = -(A * Z * A⁻¹) := by
    have hz : Zᴴ * A = -(A * Z) := eq_neg_of_add_eq_zero_left hZ
    calc Zᴴ = Zᴴ * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hd, Matrix.mul_one]
      _ = -(A * Z * A⁻¹) := by rw [hz, Matrix.neg_mul]
  have hunit : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * A * NormedSpace.exp (t • Z) = A := by
    intro t
    have hconj : t • -(A * Z * A⁻¹) = A * (-(t • Z)) * A⁻¹ := by
      rw [Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.mul_smul, Matrix.smul_mul]
    have hc : NormedSpace.exp (-(t • Z)) * NormedSpace.exp (t • Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • Z)).neg_left), neg_add_cancel,
        NormedSpace.exp_zero]
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial, hZ', hconj,
      Matrix.exp_conj A _ hAu]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left A _ hd]
    rw [hc, Matrix.mul_one]
  have hmem : ∀ t : ℝ, (Matrix.isUnit_exp (t • Z)).unit ∈ Formalism.UG.UJ (starRingEnd ℂ) A :=
    fun t => hunit t
  refine ⟨fun t => embArch σ J w ((archEquiv J h τ).symm ⟨_, hmem t⟩), fun t => ⟨_, rfl, ?_⟩⟩
  rw [GlobalTheory.Orb.archMat_eq_archEquiv J h τ, MulEquiv.apply_symm_apply]
  rfl

theorem conjTranspose_map (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := conjTranspose_map_eq_of_isHermND h hJ τ

omit [NumberField F] [NumberField E] in
theorem isUnit_det_map (hJ : IsHermND σ J) (τ : E →+* ℂ) : IsUnit (J.map τ).det := isUnit_det_map_of_det_ne_zero hJ.2 τ

def adj (A X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := A⁻¹ * Xᴴ * A

theorem skew_parts {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hd : IsUnit A.det) (X : Matrix (Fin n) (Fin n) ℂ) :
    (((1 / 2 : ℂ) • (X - adj A X))ᴴ * A + A * ((1 / 2 : ℂ) • (X - adj A X)) = 0) ∧
    (((-Complex.I / 2 : ℂ) • (X + adj A X))ᴴ * A + A * ((-Complex.I / 2 : ℂ) • (X + adj A X)) = 0) ∧
    X = (1 / 2 : ℂ) • (X - adj A X) + Complex.I • ((-Complex.I / 2 : ℂ) • (X + adj A X)) := by
  have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hd
  have h2 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hd
  have e1 : (adj A X)ᴴ * A = A * X := by
    simp only [adj, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hA, Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : A * adj A X = Xᴴ * A := by
    simp only [adj, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have s1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have s2 : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by
    rw [Complex.star_def, map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  have s3 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul, e1,
      Matrix.mul_smul, Matrix.mul_sub, e2, s1]
    module
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul, e1,
      Matrix.mul_smul, Matrix.mul_add, e2, s2]
    have : (-Complex.I / 2 : ℂ) = -(Complex.I / 2) := by ring
    rw [this, neg_smul]
    module
  · rw [smul_smul, s3]
    module

theorem exists_lines (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : EmbOver E w) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ γ₁ γ₂, IsLineOf σ J τ ((1 / 2 : ℂ) • (X - adj (J.map τ.1) X)) γ₁ ∧
      IsLineOf σ J τ ((-Complex.I / 2 : ℂ) • (X + adj (J.map τ.1) X)) γ₂ ∧
      X = (1 / 2 : ℂ) • (X - adj (J.map τ.1) X) + Complex.I • ((-Complex.I / 2 : ℂ) • (X + adj (J.map τ.1) X)) := by
  obtain ⟨s1, s2, s3⟩ := skew_parts (conjTranspose_map h hJ τ.1) (isUnit_det_map hJ τ.1) X
  obtain ⟨γ₁, h1⟩ := exists_isLineOf (τ := τ) h hJ s1
  obtain ⟨γ₂, h2⟩ := exists_isLineOf (τ := τ) h hJ s2
  exact ⟨γ₁, γ₂, h1, h2, s3⟩

variable {n₁ : ℕ}

def frame (H : Plane E n n₁) : Matrix (Fin n) (Fin (1 + n₁ + 1)) E :=
  Matrix.of fun r => Fin.addCases (Fin.addCases (fun _ => H.x r) fun k => H.ι r k) fun _ => H.y r

def mid (k : Fin n₁) : Fin (1 + n₁ + 1) := Fin.castAdd 1 (Fin.natAdd 1 k)

def blk (n₁ : ℕ) : Fin (1 + n₁ + 1) → ℕ := Fin.addCases (Fin.addCases (fun _ => 0) fun _ => 1) fun _ => 2

omit [NumberField E] in
theorem frame_alt (H : Plane E n n₁) (r : Fin n) (a : Fin 1) : frame H r (Fin.castAdd 1 (Fin.castAdd n₁ a)) = H.x r := by simp [frame]

omit [NumberField E] in
theorem frame_mid (H : Plane E n n₁) (r : Fin n) (k : Fin n₁) : frame H r (mid k) = H.ι r k := by simp [frame, mid]

omit [NumberField E] in
theorem frame_y (H : Plane E n n₁) (r : Fin n) (a : Fin 1) : frame H r (Fin.natAdd (1 + n₁) a) = H.y r := by simp [frame]

theorem block_matrix_mulVec_basis (a : Fin 1) : blk n₁ (Fin.castAdd 1 (Fin.castAdd n₁ a)) = 0 := by simp [blk]

theorem blk_mid (k : Fin n₁) : blk n₁ (mid k) = 1 := by simp [blk, mid]

theorem blk_y (a : Fin 1) : blk n₁ (Fin.natAdd (1 + n₁) a) = 2 := by simp [blk]

end GlobalTheory.LeviHC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.FDim

theorem fromSpecStalk_comp_spec {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem isClosed_origin (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (p : Sp K) :
    IsClosed ({(η[A]).left.base p} : Set A.left) := by
  have hr : Set.range (η[A]).left.base = {(η[A]).left.base p} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      have hs : Subsingleton (Sp K) := inferInstance
      obtain rfl : q = p := hs.elim q p
      rfl
    · rintro rfl
      exact ⟨p, rfl⟩
  rw [← hr]
  exact (η[A]).left.isClosedEmbedding.isClosed_range

theorem cechLB_triv_finrank_one_two : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, Module.Finite K ((cechLB A.hom (LB.triv A.left) D).homology i)) ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 1) = g ∧ Module.finrank K ((cechLB A.hom (LB.triv A.left) D).homology 2) ≤ g.choose 2 := by
  intro K _ _ A _ g hA hsm κ _ _ D hD hcov
  obtain ⟨L, H, _, j, hL, hproj, hgen, hj, hci, hfin, hK⟩ := GlobalTheory.T.exists_ample_kernel_finite_subgroupScheme K A hA
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hx₀ : (η[A]).left.base p ∈ Set.range (η[A]).left.base := ⟨p, rfl⟩
  obtain ⟨J, C, φ, hJ, hφ, hfree, hbdd, hcok, hfib, hiso⟩ :=
    GlobalTheory.T.exists_free_complex_structureSheaf_cech_origin K A g hA hsm L H j hL hproj hgen hj hci hfin hK _ hx₀
  obtain ⟨f, hf⟩ := GlobalTheory.T.finiteSubgroupScheme_ideal_generated_by_dim_elements K A g hA hsm H j hj hci hfin _ hx₀ J hJ
  obtain ⟨hJt, hart⟩ := GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion K A H j hj hci hfin _ hx₀ J hJ
  subst hf
  let σ : K →+* A.left.presheaf.stalk ((η[A]).left.base p) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ A.hom.appTop ≫
      A.left.presheaf.germ ⊤ ((η[A]).left.base p) trivial).hom
  have hσ : A.left.fromSpecStalk ((η[A]).left.base p) ≫ A.hom = Spec.map (CommRingCat.ofHom σ) := by
    rw [fromSpecStalk_comp_spec]
    rfl
  have hloc : IsLocalHom σ := ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩
  obtain ⟨-, -, hreg, hdim⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth K A.left A.hom g hsm _ (isClosed_origin K A p) σ hσ hloc
  have hbot : (IsLocalRing.maximalIdeal K).map σ = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  let e := (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot (A.left.presheaf.stalk ((η[A]).left.base p)))
  haveI : IsRegularLocalRing (A.left.presheaf.stalk ((η[A]).left.base p)) :=
    IsRegularLocalRing.of_ringEquiv e
  have hdim' : ringKrullDim (A.left.presheaf.stalk ((η[A]).left.base p)) = g := by
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact hdim
  have hex := GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres _ g hdim' C hfree hbdd hfib
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_homology_one_two_dualResolution _ g hdim' f hJt hart C hfree hex hcok K φ hφ
  haveI := hA.proper
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K A.left A.hom (LB.triv A.left) κ D
      (LB.isLB_triv _) inferInstance hproj hD hcov i
  · obtain ⟨e1⟩ := hiso κ D hD hcov 1
    rw [← e1.finrank_eq]
    exact h1
  · obtain ⟨e2⟩ := hiso κ D hD hcov 2
    rw [← e2.finrank_eq]
    exact h2

end GlobalTheory.AbCoh.FDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryGLBlockEmbeddingPolynomialEntriStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  first | exact @GlobalTheory.BlockForms.isBlockEmb_continuous | exact GlobalTheory.BlockForms.isBlockEmb_continuous | (intros; apply GlobalTheory.BlockForms.isBlockEmb_continuous <;> assumption)
end

