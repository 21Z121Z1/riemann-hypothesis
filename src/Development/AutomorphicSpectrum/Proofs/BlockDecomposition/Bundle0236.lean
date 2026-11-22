import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0180
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0229
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0177
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0228
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0213
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0232
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFacts
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg TensorProduct

namespace GlobalTheory.CompanionTheory.ACrisMod

variable {l : ℕ} [Fact l.Prime]

variable (l) in

abbrev Qt : Type := Ob l ⧸ Ideal.span {pFlat l ^ l}

variable (l) in

abbrev Nm : Type := ℕ →₀ Qt l

@[reducible] def modAcr (A : PAlg l) : Module (Ob l) (A.Acr 1) := Module.compHom _ (A.aTo1.comp A.s)

attribute [local instance] modAcr

theorem smul_acr (A : PAlg l) (c : Ob l) (y : A.Acr 1) : c • y = A.aTo1 (A.s c) * y := rfl

def mulDxi (A : PAlg l) (k : ℕ) : A.A →ₗ[Ob l] A.Acr 1 where
  toFun a := A.aTo1 a * A.dxi 1 (l * k)
  map_add' x y := by rw [map_add, add_mul]
  map_smul' c a := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, smul_acr, mul_assoc]; rfl

theorem mulDxi_apply (A : PAlg l) (k : ℕ) (a : A.A) : mulDxi A k a = A.aTo1 a * A.dxi 1 (l * k) := rfl

theorem pow_smul_mulDxi (A : PAlg l) (k : ℕ) : pFlat l ^ l • mulDxi A k = 0 := by
  ext a
  have h := (GlobalTheory.T.expansion_surjective_additive_linear A).2.2.2 (l * k)
  rw [LinearMap.smul_apply, smul_acr, mulDxi_apply, LinearMap.zero_apply, map_pow, mul_left_comm]
  have e : A.aTo1 (A.s (pFlat l) ^ l) * A.dxi 1 (l * k) = 0 := h
  rw [e, mul_zero]

def tk (A : PAlg l) (k : ℕ) : Qt l →ₗ[Ob l] (A.A →ₗ[Ob l] A.Acr 1) :=
  (Ideal.span {pFlat l ^ l}).liftQ (LinearMap.toSpanSingleton (Ob l) _ (mulDxi A k)) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, mul_smul, pow_smul_mulDxi, smul_zero])

def tauL (A : PAlg l) : Nm l ⊗[Ob l] A.A →ₗ[Ob l] A.Acr 1 :=
  TensorProduct.lift (Finsupp.lsum ℕ (tk A))

theorem tauL_one (A : PAlg l) (k : ℕ) (a : A.A) :
    tauL A (Finsupp.single k 1 ⊗ₜ a) = A.aTo1 a * A.dxi 1 (l * k) := by
  have : (1 : Qt l) = Submodule.Quotient.mk (1 : Ob l) := rfl
  rw [tauL, TensorProduct.lift.tmul, Finsupp.lsum_single, this, tk, Submodule.liftQ_apply,
    LinearMap.toSpanSingleton_apply, one_smul, mulDxi_apply]

theorem smul_one_Qt (r : Ob l) : r • (1 : Qt l) = Submodule.Quotient.mk r := by
  change r • (Submodule.Quotient.mk (1 : Ob l) : Qt l) = _
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

theorem pow_smul_Qt (q : Qt l) : pFlat l ^ l • q = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gen (A : PAlg l) (c : ℕ →₀ A.A) : Nm l ⊗[Ob l] A.A := c.sum fun k a => Finsupp.single k 1 ⊗ₜ a

theorem gen_zero (A : PAlg l) : gen A 0 = 0 := Finsupp.sum_zero_index

theorem gen_add (A : PAlg l) (c d : ℕ →₀ A.A) : gen A (c + d) = gen A c + gen A d :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)

theorem gen_single (A : PAlg l) (k : ℕ) (a : A.A) : gen A (Finsupp.single k a) = Finsupp.single k 1 ⊗ₜ a :=
  Finsupp.sum_single_index (TensorProduct.tmul_zero _ _)

theorem tauL_gen (A : PAlg l) (c : ℕ →₀ A.A) : tauL A (gen A c) = A.expand c := by
  rw [gen, map_finsuppSum, expand]
  exact Finsupp.sum_congr fun k _ => tauL_one A k (c k)

theorem exists_gen (A : PAlg l) (x : Nm l ⊗[Ob l] A.A) : ∃ c, gen A c = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, gen_zero A⟩
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, gen_add A c d⟩
  | tmul n a =>
    induction n using Finsupp.induction_linear with
    | zero => exact ⟨0, by rw [gen_zero, TensorProduct.zero_tmul]⟩
    | add f g hf hg =>
      obtain ⟨c, hc⟩ := hf
      obtain ⟨d, hd⟩ := hg
      exact ⟨c + d, by rw [gen_add, hc, hd, TensorProduct.add_tmul]⟩
    | single k q =>
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨Finsupp.single k (r • a), ?_⟩
      rw [gen_single, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Finsupp.smul_single]
      congr 2
      exact smul_one_Qt r

theorem gen_eq_zero (A : PAlg l) (c : ℕ →₀ A.A) (h : ∀ k, c k ∈ Ideal.span {A.pi ^ l}) : gen A c = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h k)
  have e : c k = pFlat l ^ l • b := by
    rw [Algebra.smul_def, ← hb, mul_comm]
    congr 1
    exact (map_pow A.s _ _).symm
  have z : pFlat l ^ l • (Finsupp.single k 1 : Nm l) = 0 := by
    rw [Finsupp.smul_single, pow_smul_Qt, Finsupp.single_zero]
  change Finsupp.single k 1 ⊗ₜ[Ob l] (c k) = 0
  rw [e, ← TensorProduct.smul_tmul, z, TensorProduct.zero_tmul]

theorem tauL_bijective (A : PAlg l) : Function.Bijective (tauL A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_gen A x
    rw [tauL_gen] at hx
    exact gen_eq_zero A c ((GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem A c).1 hx)
  · obtain ⟨c, rfl⟩ := (GlobalTheory.T.expansion_surjective_additive_linear A).1 y
    exact ⟨gen A c, tauL_gen A c⟩

def tau (A : PAlg l) : Nm l ⊗[Ob l] A.A ≃+ A.Acr 1 :=
  { Equiv.ofBijective (tauL A) (tauL_bijective A) with map_add' := map_add (tauL A) }

theorem tau_apply (A : PAlg l) (x : Nm l ⊗[Ob l] A.A) : tau A x = tauL A x := rfl

theorem map_gen {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    ((D.toPf l ⋙ D.tensF l (Ob l) (Nm l)).map f).hom (gen A c) =
      gen B (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [gen, map_finsuppSum, gen, Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
  rfl

theorem pow_smul_Nm (x : Nm l) : pFlat l ^ l • x = 0 :=
  Finsupp.ext fun k => (Finsupp.smul_apply _ _ _).trans (pow_smul_Qt (x k))

theorem algebraMap_eq (A : PAlg l) (a : Ainf l) (y : A.Acr 1) :
    algebraMap (Ainf l) (A.Acr 1) a * y = a.coeff 0 • y := by
  rw [(GlobalTheory.T.functoriality_of_period_ring_maps A A (𝟙 A)).2.2.2.2.2 a]
  rfl

theorem tau_smul (A : PAlg l) (a : Ainf l) (x : Nm l ⊗[Ob l] A.A) :
    tau A (a.coeff 0 • x) = algebraMap (Ainf l) (A.Acr 1) a * tau A x :=
  ((tauL A).map_smul (a.coeff 0) x).trans (algebraMap_eq A a (tauL A x)).symm

theorem tau_map (A B : PAlg l) (f : A ⟶ B) (x : Nm l ⊗[Ob l] A.A) :
    tau B (((D.toPf l ⋙ D.tensF l (Ob l) (Nm l)).map f).hom x) = mapAcr f 1 (tau A x) := by
  obtain ⟨c, rfl⟩ := exists_gen A x
  rw [tau_apply, tau_apply, map_gen, tauL_gen, tauL_gen]
  exact ((GlobalTheory.T.functoriality_of_period_ring_maps A B f).2.1 c).symm

theorem acr1 (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcr1 l :=
  ⟨Nm l, inferInstance, inferInstance, l, tau, pow_smul_Nm, tau_smul, tau_map⟩

end GlobalTheory.CompanionTheory.ACrisMod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFiniteStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_cohomology_finite : ∀ {O : Type} [CommRing O] [IsNoetherianRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : (⨆ α, U α) = ⊤) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (K : Cos.{1} O) (V : VB (fun W => ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ W le_top).hom) U K) (p : ℕ),
    Module.Finite O (K.cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.VBGlue.finite_H_cx | exact GlobalTheory.CompanionTheory.VBGlue.finite_H_cx | (intros; apply GlobalTheory.CompanionTheory.VBGlue.finite_H_cx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityExistsStatement
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximate_identity_exists : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ φ : ℕ → Mat n → ℝ, (∀ k, IsTest (φ k)) ∧ (∀ k y, 0 ≤ φ k y) ∧ (∀ k, ∫ y : G n, φ k y.val ∂μ = 1) ∧ ∀ N ∈ 𝓝 (1 : G n), ∀ᶠ k in atTop, ∀ y : G n, φ k y.val ≠ 0 → y ∈ N := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers | exact GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers | (intros; apply GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CMEqZeroOfNe
section
open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent

section Algebra

variable {F : Type} [Field F] {n : ℕ}

theorem cM_eq_zero_of_ne {k : ℕ} (x : Fin (k + 1) → F) {i j : Fin n}
    (h : ¬ ((j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1)) : cM n k x i j = 0 := by
  simp only [cM, Matrix.of_apply]
  rw [dif_neg h]

theorem cM_eq_of {k : ℕ} (x : Fin (k + 1) → F) {i j : Fin n} (hj : (j : ℕ) = k + 1)
    (hi : (i : ℕ) < k + 1) : cM n k x i j = x ⟨i, hi⟩ := by
  simp only [cM, Matrix.of_apply]
  rw [dif_pos ⟨hj, hi⟩]

theorem col_val (k : ℕ) (x : Fin (k + 1) → F) :
    ((col n k x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + cM n k x := rfl

theorem col_inv_val (k : ℕ) (x : Fin (k + 1) → F) :
    (((col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 - cM n k x := rfl

theorem col_mem (k : ℕ) (x : Fin (k + 1) → F) : col n k x ∈ unipotent F n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : (j : ℕ) < i := hij
    rw [col_val, Matrix.add_apply, Matrix.one_apply_ne (by intro e; subst e; omega),
      cM_eq_zero_of_ne x (by omega), add_zero]
  · rw [col_val, Matrix.add_apply, Matrix.one_apply_eq, cM_eq_zero_of_ne x (by omega), add_zero]

theorem superdiagSum_cM {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.superdiagSum (cM n k x) = x (Fin.last k) := by
  unfold Whittaker.superdiagSum
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin n), Finset.sum_eq_single (⟨k + 1, hk⟩ : Fin n)]
  · rw [if_pos rfl, cM_eq_of x rfl (by simp)]
    rfl
  · intro j _ hj
    rw [if_neg]
    intro e
    exact hj (Fin.ext (by simpa using e))
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · refine cM_eq_zero_of_ne x fun h' => hi (Fin.ext ?_)
      simp only
      omega
    · rfl
  · simp

theorem psiN_col (ψ : AddChar F ℂ) {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.psiN ψ (col n k x) = ψ (x (Fin.last k)) := by
  rw [Whittaker.psiN, col_val, Whittaker.superdiagSum_add, Whittaker.superdiagSum_one, zero_add,
    superdiagSum_cM hk]

theorem mul_cM {k : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j : Fin n, (j : ℕ) ≤ k → M i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (x : Fin (k + 1) → F) : M * cM n k x = cM n k x := by
  have h : M * cM n k x = 1 * cM n k x := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : (l : ℕ) ≤ k
    · rw [hM i l hl]
    · rw [cM_eq_zero_of_ne x (i := l) (j := j) (by omega), mul_zero, mul_zero]
  rw [h, one_mul]

theorem conj_expand {M C : Matrix (Fin n) (Fin n) F} (hMC : M * C = C) (hCC : C * C = 0) :
    (1 + C) * M * (1 - C) = M + C * M - C := by
  calc (1 + C) * M * (1 - C) = M + C * M - M * C - C * (M * C) := by noncomm_ring
    _ = M + C * M - C := by rw [hMC, hCC, sub_zero]

end Algebra

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem inU_split (ψ : AddChar F ℂ) {k : ℕ} (hk : k + 1 < n) (g : GL (Fin n) F) (hg : inU k g) :
    ∃ (g' : GL (Fin n) F) (x : Fin (k + 1) → F), inU (k + 1) g' ∧ g = g' * col n k x ∧
      Whittaker.psiN ψ g = Whittaker.psiN ψ g' * ψ (x (Fin.last k)) := by
  obtain ⟨hu, hc⟩ := hg
  let x : Fin (k + 1) → F := fun i => (g : Matrix (Fin n) (Fin n) F) ⟨i, by omega⟩ ⟨k + 1, hk⟩
  have hv : ((g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) - cM n k x := by
    rw [Units.val_mul, col_inv_val, mul_sub, mul_one, mul_cM hc]
  have hm : g * (col n k x)⁻¹ ∈ unipotent F n :=
    (unipotent F n).mul_mem hu ((unipotent F n).inv_mem (col_mem k x))
  refine ⟨g * (col n k x)⁻¹, x, ⟨hm, fun i j hj => ?_⟩, (inv_mul_cancel_right _ _).symm, ?_⟩
  · rw [hv, Matrix.sub_apply]
    by_cases hjk : (j : ℕ) ≤ k
    · rw [cM_eq_zero_of_ne x (by omega), sub_zero, hc i j hjk]
    · have hj' : (j : ℕ) = k + 1 := by omega
      by_cases hi : (i : ℕ) < k + 1
      · have hx : x ⟨i, hi⟩ = (g : Matrix (Fin n) (Fin n) F) i j := by
          have e : j = ⟨k + 1, hk⟩ := Fin.ext hj'
          subst e
          rfl
        rw [cM_eq_of x hj' hi, hx, sub_self, Matrix.one_apply_ne (by intro e; subst e; omega)]
      · rw [cM_eq_zero_of_ne x (by omega), sub_zero]
        by_cases e : i = j
        · subst e
          rw [hu.2, Matrix.one_apply_eq]
        · have hlt : id j < id i := by
            have : (j : ℕ) < i := by
              have : (i : ℕ) ≠ j := fun h => e (Fin.ext h)
              omega
            exact this
          rw [hu.1 hlt, Matrix.one_apply_ne e]
  · have h : Whittaker.psiN ψ g = Whittaker.psiN ψ (g * (col n k x)⁻¹ * col n k x) := by
      rw [inv_mul_cancel_right]
    rw [h, Whittaker.psiN_mul ψ hm (col_mem k x), psiN_col ψ hk]

theorem inU_conj (ψ : AddChar F ℂ) {k : ℕ} (g : GL (Fin n) F) (hg : inU (k + 1) g)
    (x : Fin (k + 1) → F) :
    ∃ g' : GL (Fin n) F, inU (k + 1) g' ∧ col n k x * g = g' * col n k x ∧
      Whittaker.psiN ψ g' = Whittaker.psiN ψ g := by
  obtain ⟨hu, hc⟩ := hg
  have hcol : col n k x ∈ unipotent F n := col_mem k x
  have hcg := (unipotent F n).mul_mem hcol hu
  have hinv := (unipotent F n).inv_mem hcol
  have hv : ((col n k x * g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) + cM n k x * (g : Matrix (Fin n) (Fin n) F) - cM n k x := by
    rw [Units.val_mul, Units.val_mul, col_val, col_inv_val]
    exact conj_expand (mul_cM (fun i j hj => hc i j (by omega)) x) (cM_mul k x x)
  refine ⟨col n k x * g * (col n k x)⁻¹, ⟨(unipotent F n).mul_mem hcg hinv, fun i j hj => ?_⟩,
    (inv_mul_cancel_right _ _).symm, ?_⟩
  · have hC : (cM n k x * (g : Matrix (Fin n) (Fin n) F)) i j = cM n k x i j := by
      rw [Matrix.mul_apply, Finset.sum_congr rfl fun l _ => by rw [hc l j hj], ← Matrix.mul_apply,
        mul_one]
    rw [hv, Matrix.sub_apply, Matrix.add_apply, hC, hc i j hj, add_sub_cancel_right]
  · have h0 := Whittaker.psiN_ne_zero ψ (col n k x)
    rw [Whittaker.psiN_mul ψ hcg hinv, Whittaker.psiN_mul ψ hcol hu, Whittaker.psiN_inv ψ hcol]
    field_simp

end Local

theorem main : ColumnsUnipotent := by
  intro F _ _ _ _ _ _ μ _ ψ _ n k hk
  exact ⟨fun g hg => inU_split ψ hk g hg, fun g hg x => inU_conj ψ g hg x⟩

end GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormula
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem sk_skew {n : ℕ} (p : Ix n) : (sk p)ᴴ = -sk p := by
  obtain ⟨b, i, j⟩ := p
  have hc : ∀ (a b : Fin n) (c : ℂ), (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
    intro a b c
    ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]
  cases b
  · simp [sk, Matrix.conjTranspose_add, hc, Matrix.single_neg, add_comm]
  · simp [sk, Matrix.conjTranspose_sub, hc]

theorem Rd_Rd_of_act {n : ℕ} (E : KMod n) (Y : Mat n) (B : E.V →L[ℂ] E.V)
    (hB : ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g)) (f : Mat n → E.V) (hf : f ∈ CE E)
    (g : Mat n) (hg : g ∈ GLs n) : Rd Y (Rd Y f) g = B (B (f g)) := by
  have hnhds : GLs n ∈ nhds g := isOpen_GLs.mem_nhds hg
  have hev : Rd Y f =ᶠ[nhds g] (B.restrictScalars ℝ) ∘ f := by
    filter_upwards [hnhds] with y hy
    simpa using hB f hf y hy
  have hd : DifferentiableAt ℝ f g :=
    (hf.1.contDiffAt hnhds).differentiableAt (by simp)
  have hfd : fderiv ℝ (Rd Y f) g = (B.restrictScalars ℝ).comp (fderiv ℝ f g) := by
    rw [hev.fderiv_eq]
    exact ((B.restrictScalars ℝ).hasFDerivAt.comp g hd.hasFDerivAt).fderiv
  have h1 : Rd Y (Rd Y f) g = B (Rd Y f g) := by
    change fderiv ℝ (Rd Y f) g (g * Y) = B (fderiv ℝ f g (g * Y))
    rw [hfd]
    rfl
  rw [h1, hB f hf g hg]

theorem om_section {n : ℕ} (E : KMod n) : ∃ A : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g) := by
  choose B hB using fun p : Ix n => rd_skew_eq_const E (sk p) (sk_skew p)
  refine ⟨-(1 / 4 : ℂ) • ∑ p, B p * B p, fun f hf g hg => ?_⟩
  rw [OmDec.Om_eq_squares f hf.1 g hg, sub_eq_add_neg]
  congr 1
  have h : ∀ p, Rd (sk p) (Rd (sk p) f) g = B p (B p (f g)) := fun p =>
    Rd_Rd_of_act E (sk p) (B p) (hB p) f hf g hg
  simp only [h, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.neg_apply, neg_smul]
  rfl

end GlobalTheory.CompanionTheory.WaveSpd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffEqPowOfMulOneSub
section
open PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

open PowerSeries Filter Topology

theorem tendsto_coeff_mul_one_sub (G : ℂ⟦X⟧) (b : ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * (1 - C b * X))) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have e : ∀ j : ℕ, coeff (j + 1) (G * (1 - C b * X)) = coeff (j + 1) G - b * coeff j G := by
    intro j
    have : G * (1 - C b * X) = G - C b * (G * X) := by ring
    rw [this, map_sub, coeff_C_mul, coeff_succ_mul_X]
  simp only [e]
  have h1 := (tendsto_add_atTop_iff_nat 1).2 h
  simpa using h1.sub (h.const_mul b)

theorem tendsto_coeff_mul_prod (G : ℂ⟦X⟧) {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * ∏ k ∈ s, (1 - C (β k) * X))) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have : G * ((1 - C (β a) * X) * ∏ k ∈ s, (1 - C (β k) * X)) =
        (G * ∏ k ∈ s, (1 - C (β k) * X)) * (1 - C (β a) * X) := by ring
    rw [this]
    exact tendsto_coeff_mul_one_sub _ _ ih

theorem coeff_eq_pow_of_mul_one_sub (H : ℂ⟦X⟧) (b : ℂ) (h : H * (1 - C b * X) = 1) (j : ℕ) :
    coeff j H = b ^ j := by
  have e : H = 1 + C b * (H * X) := by
    calc H = H * (1 - C b * X) + C b * (H * X) := by ring
      _ = 1 + C b * (H * X) := by rw [h]
  induction j with
  | zero =>
    rw [e]; simp
  | succ j ih =>
    rw [e, map_add, coeff_C_mul, coeff_succ_mul_X, ih, pow_succ]
    simp [coeff_one, mul_comm]

theorem coeff_prod_one_sub {n : ℕ} (β : Fin n → ℂ) (r : ℕ) :
    coeff r (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) =
      (-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i := by
  classical
  have e : ∀ t : Finset (Fin n), ∏ i ∈ t, (-(C (β i) * X) : ℂ⟦X⟧) =
      C ((-1) ^ t.card * ∏ i ∈ t, β i) * X ^ t.card := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
  have e2 : (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) = ∏ i, (1 + -(C (β i) * X)) := by
    simp only [sub_eq_add_neg]
  rw [e2, Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [e, coeff_C_mul, coeff_X_pow]
  by_cases h : r = t.card
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp

theorem mk_mul_prod_eq_one {n : ℕ} (β : Fin n → ℂ) (g : ℕ → ℂ) (h0 : g 0 = 1)
    (hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1),
      ((-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i) * g (j - r) = 0) :
    (PowerSeries.mk g : ℂ⟦X⟧) * ∏ i, (1 - C (β i) * X) = 1 := by
  ext j
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_sub, coeff_mk]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [h0, coeff_one]
  · rw [hrec j hj, coeff_one, if_neg (by omega)]

end GlobalTheory.CompanionTheory.SatakeBound

theorem GlobalTheory.CompanionTheory.SatakeBound.norm_lt_one : liftZP_newton := by
  intro n β g h0 hrec hg i
  classical
  have hG := GlobalTheory.CompanionTheory.SatakeBound.mk_mul_prod_eq_one β g h0 hrec
  have hc : Filter.Tendsto (fun j => PowerSeries.coeff j (PowerSeries.mk g : PowerSeries ℂ))
      Filter.atTop (nhds 0) := by
    simpa [PowerSeries.coeff_mk] using hg
  have hH := GlobalTheory.CompanionTheory.SatakeBound.tendsto_coeff_mul_prod _ (Finset.univ.erase i) β hc
  have hone : ((PowerSeries.mk g : PowerSeries ℂ) *
      ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) *
      (1 - PowerSeries.C (β i) * PowerSeries.X) = 1 := by
    have hs := Finset.mul_prod_erase Finset.univ
      (fun k => (1 - PowerSeries.C (β k) * PowerSeries.X : PowerSeries ℂ)) (Finset.mem_univ i)
    calc _ = (PowerSeries.mk g : PowerSeries ℂ) * ((1 - PowerSeries.C (β i) * PowerSeries.X) *
          ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) := by ring
      _ = 1 := by rw [hs, hG]
  have hp := GlobalTheory.CompanionTheory.SatakeBound.coeff_eq_pow_of_mul_one_sub _ _ hone
  simp only [hp] at hH
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 hH
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryRootMapStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitary_root_map : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n), Continuous (uR σ hU.1 a h : L → GU σ n) := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.continuous_uR | exact GlobalTheory.CompanionTheory.SwapRoot.continuous_uR | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.continuous_uR <;> assumption)
end

