import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPointedEtaleNeighbourhoodEqMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSandwichTraceEq
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_eq_of_intertwined_by_quasi_inverse (A : Type) [CommRing A] [IsDomain A] (h : ℕ) (μ : A)
    (F G X Y : Matrix (Fin h) (Fin h) A) (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) (hFX : F * X = Y * F) :
    F * G = μ • (1 : Matrix (Fin h) (Fin h) A) ∧ X * G = G * Y ∧ Y.trace = X.trace := by
  have hdet : G.det * F.det = μ ^ h := by
    rw [← Matrix.det_mul, hGF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hF : F.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero h hμ hdet.symm
  have hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A) := by
    have h1 : (F * G - μ • (1 : Matrix (Fin h) (Fin h) A)) * F = 0 := by
      rw [sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : F.det • (F * G - μ • (1 : Matrix (Fin h) (Fin h) A)) = 0 := by
      have := congrArg (· * F.adjugate) h1
      simp only [Matrix.zero_mul] at this
      rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at this
      exact this
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hF
    · exact sub_eq_zero.mp h3
  have hXG : X * G = G * Y := by
    have e : μ • (X * G) = μ • (G * Y) := by
      calc μ • (X * G) = (G * F) * X * G := by
              rw [hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
        _ = G * (Y * (F * G)) := by
              rw [Matrix.mul_assoc G F X, hFX, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
                Matrix.mul_assoc (G * Y)]
        _ = μ • (G * Y) := by
              rw [hFG, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
    exact smul_right_injective _ hμ e
  refine ⟨hFG, hXG, ?_⟩
  have e : μ * Y.trace = μ * X.trace := by
    calc μ * Y.trace = (μ • Y).trace := by rw [Matrix.trace_smul, smul_eq_mul]
      _ = ((F * G) * Y).trace := by rw [hFG, Matrix.smul_mul, Matrix.one_mul]
      _ = (G * (Y * F)).trace := by
            rw [Matrix.mul_assoc, Matrix.trace_mul_comm F (G * Y), Matrix.mul_assoc]
      _ = ((G * F) * X).trace := by rw [← hFX, Matrix.mul_assoc]
      _ = (μ • X).trace := by rw [hGF, Matrix.smul_mul, Matrix.one_mul]
      _ = μ * X.trace := by rw [Matrix.trace_smul, smul_eq_mul]
  exact mul_left_cancel₀ hμ e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealEqJointEigen
section
open MvPolynomial Matrix

namespace GlobalTheory.MaxIdealJointEigen

theorem iSupIndep_of_joint_eigen {K E I : Type} [Field K] [AddCommGroup E] [Module K E]
    (h : I → Module.End K E) (V : (I → K) → Submodule K E)
    (hV : ∀ x, ∀ v ∈ V x, ∀ i, h i v = x i • v) : iSupIndep V := by
  classical
  have stab : ∀ (s : Finset (I → K)) (i : I), ∀ u ∈ ⨆ y ∈ s, V y, h i u ∈ ⨆ y ∈ s, V y := by
    intro s i
    have : (⨆ y ∈ s, V y) ≤ (⨆ y ∈ s, V y).comap (h i) := by
      refine iSup₂_le fun y hy v hv => ?_
      rw [Submodule.mem_comap, hV y v hv i]
      exact Submodule.smul_mem _ _ ((le_iSup₂_of_le (f := fun y (_ : y ∈ s) => V y) y hy le_rfl) hv)
    exact fun u hu => this hu
  have key : ∀ (x : I → K) (s : Finset (I → K)), x ∉ s → ∀ v ∈ V x, v ∈ (⨆ y ∈ s, V y) → v = 0 := by
    intro x s
    induction s using Finset.induction_on with
    | empty => intro _ v _ hv; simpa using hv
    | insert y s hy ih =>
      intro hx v hvx hv
      rw [Finset.mem_insert, not_or] at hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hv
      obtain ⟨w, hw, u, hu, hsum⟩ := hv
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx.1
      have e : (x i - y i) • v = h i u - y i • u := by
        rw [sub_smul, ← hV x v hvx i, ← hsum, map_add, hV y w hw i, smul_add]; abel
      have h0 := ih hx.2 ((x i - y i) • v) (Submodule.smul_mem _ _ hvx)
        (e ▸ Submodule.sub_mem _ (stab s i u hu) (Submodule.smul_mem _ _ hu))
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hi)
  intro x
  rw [Submodule.disjoint_def]
  intro v hvx hv
  replace hv : v ∈ ⨆ y : {y : I → K // y ≠ x}, V y.1 := by rwa [iSup_subtype]
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv
  refine key x (s.image Subtype.val) ?_ v hvx ?_
  · intro hx
    obtain ⟨⟨y, hy⟩, -, e⟩ := Finset.mem_image.mp hx
    exact hy e
  · refine (iSup₂_le fun y hy => ?_ : (⨆ y ∈ s, V y.1) ≤ _) hs
    exact le_iSup₂_of_le (f := fun y (_ : y ∈ s.image Subtype.val) => V y) y.1
      (Finset.mem_image_of_mem _ hy) le_rfl

theorem finite_joint_eigen {K I : Type} [Field K] {n : ℕ} (T : I → Matrix (Fin n) (Fin n) K) :
    {θ : I → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}.Finite := by
  classical
  let V : (I → K) → Submodule K (Fin n → K) := fun θ =>
    ⨅ i, Module.End.eigenspace (Matrix.toLin' (T i)) (θ i)
  have hV : ∀ x, ∀ v ∈ V x, ∀ i, Matrix.toLin' (T i) v = x i • v := by
    intro x v hv i
    have := (Submodule.mem_iInf _).mp hv i
    exact Module.End.mem_eigenspace_iff.mp this
  have hind := iSupIndep_of_joint_eigen (fun i => Matrix.toLin' (T i)) V hV
  have hfin : Finite {θ // V θ ≠ ⊥} := by
    haveI := hind.fintypeNeBotOfFiniteDimensional
    infer_instance
  refine (Set.finite_coe_iff.mp hfin).subset ?_
  rintro θ ⟨c, hc0, hc⟩
  show V θ ≠ ⊥
  rw [Submodule.ne_bot_iff]
  refine ⟨c, (Submodule.mem_iInf _).mpr fun i => ?_, hc0⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact hc i

theorem mulVec_eval₂ {O K I : Type} [CommRing O] [Field K] (emb : O →+* K) {n : ℕ}
    (ρ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (θ : I → K) (c : Fin n → K)
    (hc : ∀ i, ((ρ (X i)).map emb).mulVec c = θ i • c) (p : MvPolynomial I O) :
    ((ρ p).map emb).mulVec c = eval₂ emb θ p • c := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
    ext j
    simp [Matrix.mulVec_diagonal]
  | add p q hp hq =>
    rw [map_add, Matrix.map_add _ (map_add emb), Matrix.add_mulVec, hp, hq, eval₂_add, add_smul]
  | mul_X p i hp =>
    rw [map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hp, eval₂_mul,
      eval₂_X, smul_smul, mul_comm]

end GlobalTheory.MaxIdealJointEigen

namespace GlobalTheory

open MvPolynomial Matrix GlobalTheory.MaxIdealJointEigen

theorem maximal_ideal_eq_joint_eigen : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    (emb : O →+* PadicAlgCl l), (∀ c, ‖emb c‖ ≤ 1) → (∀ c, ‖emb c‖ = 1 → IsUnit c) →
    ∀ (I : Type) (n : ℕ) (ρ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O)
    (m : Ideal (MvPolynomial I O)), m.IsMaximal → RingHom.ker ρ ≤ m →
    ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧
      ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧
        ∀ i, ((ρ (MvPolynomial.X i)).map emb).mulVec c = θ i • c := by
  intro l _ O _ emb h1 hu I n ρ m hm hker
  classical
  set K := PadicAlgCl l
  let T : I → Matrix (Fin n) (Fin n) K := fun i => (ρ (X i)).map emb
  let Θ : Set (I → K) := {θ | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}
  have hfin : Θ.Finite := finite_joint_eigen T
  have hint : ∀ θ ∈ Θ, ∀ p, ‖eval₂ emb θ p‖ ≤ 1 := by
    rintro θ ⟨c, hc0, hc⟩ p
    exact GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric O K emb h1 n (ρ p) _ c hc0 (mulVec_eval₂ emb ρ θ c hc p)

  let J : (I → K) → Ideal (MvPolynomial I O) := fun θ =>
    { carrier := {p | ∀ r, ‖eval₂ emb θ (r * p)‖ < 1}
      add_mem' := by
        intro a b ha hb r
        simp only [Set.mem_setOf_eq, mul_add, eval₂_add] at *
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ha r) (hb r))
      zero_mem' := by intro r; simp
      smul_mem' := by
        intro a b hb r
        simp only [Set.mem_setOf_eq, smul_eq_mul, ← mul_assoc] at *
        exact hb (r * a) }
  have hJmem : ∀ θ ∈ Θ, ∀ p, p ∈ J θ ↔ ‖eval₂ emb θ p‖ < 1 := by
    intro θ hθ p
    constructor
    · intro h; simpa using h 1
    · intro h r
      show ‖eval₂ emb θ (r * p)‖ < 1
      rw [eval₂_mul, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hint θ hθ r)) h
  have hJprime : ∀ θ ∈ Θ, (J θ).IsPrime := by
    intro θ hθ
    refine ⟨?_, ?_⟩
    · intro htop
      have := (hJmem θ hθ 1).mp (htop ▸ Submodule.mem_top)
      simp at this
    · intro a b hab
      rw [hJmem θ hθ, eval₂_mul, norm_mul] at hab
      rw [hJmem θ hθ, hJmem θ hθ]
      by_contra hc
      push_neg at hc
      have := mul_le_mul hc.1 hc.2 zero_le_one (norm_nonneg _)
      linarith
  by_cases hex : ∃ θ ∈ Θ, m ≤ J θ
  · obtain ⟨θ, hθ, hle⟩ := hex
    have heq : m = J θ := hm.eq_of_le (hJprime θ hθ).ne_top hle
    obtain ⟨c, hc0, hc⟩ := hθ
    refine ⟨θ, fun i => ?_, fun p => ?_, c, hc0, hc⟩
    · simpa using hint θ ⟨c, hc0, hc⟩ (X i)
    · rw [heq]; exact hJmem θ ⟨c, hc0, hc⟩ p
  · exfalso
    push_neg at hex
    have hnot : ¬ ((m : Set (MvPolynomial I O)) ⊆ ⋃ θ ∈ (hfin.toFinset : Set (I → K)), (J θ : Set _)) := by
      rw [Ideal.subset_union_prime (0 : I → K) (0 : I → K)
        (fun θ hθ _ _ => hJprime θ (by simpa using hθ))]
      rintro ⟨θ, hθ, hle⟩
      exact hex θ (by simpa using hθ) hle
    obtain ⟨q, hqm, hq⟩ := Set.not_subset.mp hnot
    have hq1 : ∀ θ ∈ Θ, ‖eval₂ emb θ q‖ = 1 := by
      intro θ hθ
      refine le_antisymm (hint θ hθ q) (not_lt.mp fun h => hq ?_)
      exact Set.mem_biUnion (x := θ) (by simpa using hθ) ((hJmem θ hθ q).mpr h)
    let B : Matrix (Fin n) (Fin n) K := (ρ q).map emb
    have hcomm : ∀ p p', ((ρ p).map emb) * ((ρ p').map emb) = ((ρ p').map emb) * ((ρ p).map emb) := by
      intro p p'
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul, mul_comm]
    have hroot : ∀ μ ∈ B.charpoly.roots, ‖μ‖ = 1 := by
      intro μ hμ
      have hdet0 : (Matrix.scalar (Fin n) μ - B).det = 0 := by
        rw [← Matrix.eval_charpoly]
        exact (Polynomial.mem_roots'.mp hμ).2
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      have hsc : ∀ w : Fin n → K, (Matrix.scalar (Fin n) μ) *ᵥ w = μ • w := by
        intro w; ext j; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
      have hBv : B *ᵥ v = μ • v := by
        rw [Matrix.sub_mulVec, sub_eq_zero, hsc] at hv
        exact hv.symm
      let W : Submodule K (Fin n → K) := Module.End.eigenspace (Matrix.toLin' B) μ
      have hW0 : W ≠ ⊥ := by
        rw [Submodule.ne_bot_iff]
        refine ⟨v, ?_, hv0⟩
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact hBv
      have hWs : ∀ i, ∀ w ∈ W, Matrix.toLin' (T i) w ∈ W := by
        intro i w hw
        rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
        rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
        change ((ρ q).map emb * (ρ (X i)).map emb) *ᵥ w = μ • ((ρ (X i)).map emb *ᵥ w)
        rw [hcomm, ← Matrix.mulVec_mulVec]
        change (ρ (X i)).map emb *ᵥ (B *ᵥ w) = _
        rw [hw, Matrix.mulVec_smul]
      obtain ⟨c, hcW, hc0, hc⟩ := GlobalTheory.exists_common_eigenvector_mem
        (fun i => Matrix.toLin' (T i))
        (fun i j w => by
          simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
          exact congrArg (· *ᵥ w) (hcomm (X i) (X j))) W hW0 hWs
      choose θ hθ using hc
      have hθ' : ∀ i, (T i) *ᵥ c = θ i • c := fun i => by simpa [Matrix.toLin'_apply] using hθ i
      have hθΘ : θ ∈ Θ := ⟨c, hc0, hθ'⟩
      have h2 := mulVec_eval₂ emb ρ θ c hθ' q
      have h3 : B *ᵥ c = μ • c := by
        have := Module.End.mem_eigenspace_iff.mp hcW
        rwa [Matrix.toLin'_apply] at this
      have hμ : μ = eval₂ emb θ q := by
        have e : (μ - eval₂ emb θ q) • c = 0 := by
          rw [sub_smul, ← h3, ← h2]
          exact sub_self _
        exact sub_eq_zero.mp ((smul_eq_zero.mp e).resolve_right hc0)
      rw [hμ]
      exact hq1 θ hθΘ
    have hdetB : ‖emb (ρ q).det‖ = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_eq_prod_roots_charpoly]
      exact Multiset.prod_induction (fun x => ‖x‖ = 1) _
        (fun a b ha hb => by rw [norm_mul, ha, hb, one_mul]) norm_one hroot
    have hunit : IsUnit (ρ q).det := hu _ hdetB
    set P := (ρ q).charpoly with hPdef
    have hP : Polynomial.aeval q P ∈ m := by
      apply hker
      rw [RingHom.mem_ker]
      rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]
    have hC : MvPolynomial.C (P.coeff 0) ∈ m := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hP ⊢
      have hq0 : Ideal.Quotient.mkₐ O m q = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hqm
      have e := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O m) q P
      rw [hq0, ← Polynomial.coeff_zero_eq_aeval_zero'] at e
      calc Ideal.Quotient.mk m (C (P.coeff 0))
          = algebraMap O (MvPolynomial I O ⧸ m) (P.coeff 0) := by
            rw [← MvPolynomial.algebraMap_eq]
            first
              | exact Ideal.Quotient.mk_algebraMap _ _ _
              | rfl
        _ = Ideal.Quotient.mkₐ O m (Polynomial.aeval q P) := e
        _ = 0 := by rw [Ideal.Quotient.mkₐ_eq_mk]; exact hP
    have hu0 : IsUnit (P.coeff 0) := by
      rw [Matrix.det_eq_sign_charpoly_coeff] at hunit
      exact isUnit_of_mul_isUnit_right hunit
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hC (hu0.map MvPolynomial.C))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPointedEtaleNeighbourhoodEqMapStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalIdeal_pointedEtaleNeighbourhood_eq_map : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), maximalIdeal i.B = (maximalIdeal R).map (algebraMap R i.B) := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map | exact GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map | (intros; apply GlobalTheory.Henselisation.EtNbhd.maximalIdeal_B_eq_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdjoinRestrictedSectionsOfLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adjoin_restricted_sections_of_local : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W)), (∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V), (F.map (homOfLE hW).op).hom b ∈ gen F α hV T) → ∀ W' : X.Opens, IsAffineOpen W' → ∀ (hW : W' ≤ W) (hV : W' ≤ V), (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by
  first | exact @GlobalTheory.QcSub.Local.mem_gen_of_local | exact GlobalTheory.QcSub.Local.mem_gen_of_local | (intros; apply GlobalTheory.QcSub.Local.mem_gen_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureWideGaussianMulSchwartzStatement
section
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : SchwartzMap E ℂ),
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  first | exact @GlobalTheory.GaussCutoff.mem_closure_gauss_mul | exact GlobalTheory.GaussCutoff.mem_closure_gauss_mul | (intros; apply GlobalTheory.GaussCutoff.mem_closure_gauss_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationOfComponentsMemEigenSpan
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem mem_of_components : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S]
    [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N,
    (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F := by
  intro C _ w S _ _ a N F ha hF x hx hc
  have hle : ∀ s, filSpace F s ≤ clearDen F s := fun s => by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨diffGen a s, diffGen_ne_zero a ha s, single_mem_of_mem a F hF.stable s y hy⟩
  choose b hb hbx using fun s => hle s (hc s)
  have hB : (∏ s, b s) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => hb s
  refine hF.saturated x hx (∏ s, b s) hB ?_
  have key : (∏ s, b s) • x = ∑ s, (∏ t ∈ Finset.univ.erase s, b t) •
      (Pi.single s (b s • x s) : S → Fin N → C) := by
    funext s' i
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single s']
    · simp only [smul_pi_apply, Pi.single_eq_same, smul_vec_apply]
      rw [← mul_assoc, ← Subring.coe_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ s')]
    · intro s _ e
      simp [smul_pi_apply, Pi.single_apply, Ne.symm e]
    · simp
  rw [key]
  exact sum_mem fun s _ => F.smul_mem _ (hbx s)

end GlobalTheory.Div.KerFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationPreimageIffEvalMem
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.FilPreMem

theorem poly_mem (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C))
    (hF : ∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) (f : Polynomial (Int0 v)) :
    ∀ y ∈ F, (fun s i => ((f.eval (liftA hv a s) : Int0 v) : C) * y s i) ∈ F := by
  induction f using Polynomial.induction_on with
  | C c =>
    intro y hy
    have := F.smul_mem (⟨(c : C), (hv _).1 c.2⟩ : w.valuationSubring) hy
    convert this using 1
    funext s i
    simp only [Polynomial.eval_C]
    rfl
  | add p q hp hq =>
    intro y hy
    have := F.add_mem (hp y hy) (hq y hy)
    convert this using 1
    funext s i
    simp only [Polynomial.eval_add, Subring.coe_add, Pi.add_apply, add_mul]
  | monomial n c h =>
    intro y hy
    have := hF _ (h y hy)
    convert this using 1
    funext s i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif, Pi.smul_apply, smul_eq_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Subring.coe_mul,
      Subring.coe_pow, pow_succ, liftA]
    ring

theorem filPre_mem_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), (∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) → ∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F := by
  intro C _ w v hv S _ _ a N F hF x
  let T : Submodule (RS (liftA hv a)) (Fin N → RS (liftA hv a)) :=
    { carrier := {x | evalVec (liftA hv a) N x ∈ F}
      zero_mem' := by
        show evalVec (liftA hv a) N 0 ∈ F
        have : evalVec (liftA hv a) N 0 = 0 := by
          funext s i; simp [evalVec]
        rw [this]; exact F.zero_mem
      add_mem' := by
        intro x y hx hy
        show evalVec (liftA hv a) N (x + y) ∈ F
        rw [evalVec_add]; exact F.add_mem hx hy
      smul_mem' := by
        intro r x hx
        show evalVec (liftA hv a) N (r • x) ∈ F
        induction r using AdjoinRoot.induction_on with
        | ih f =>
          have := poly_mem C w v hv S a N F hF f _ hx
          convert this using 1
          funext s i
          simp [evalVec, ev] }
  constructor
  · intro hx
    have : filPre (liftA hv a) F ≤ T := Submodule.span_le.2 (fun y hy => hy)
    exact this hx
  · intro hx
    exact Submodule.subset_span hx

end GlobalTheory.FilPreMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintIffMatrixImageStandardLatticeEqStatement
section
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq : ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  first | exact @GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | exact GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | (intros; apply GlobalTheory.LatOrb.mem_GLint_iff_matLat_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealTransformOfForallSmulMem
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

def idealTransform (S : Type) [CommRing S] (I : Ideal S) (A : Type) [CommRing A] [Algebra S A] :
    Subalgebra S (FractionRing S ⊗[S] A) where
  carrier := {z | ∃ k : ℕ, ∀ a ∈ I ^ k,
    a • z ∈ (Algebra.TensorProduct.includeRight : A →ₐ[S] FractionRing S ⊗[S] A).range}
  mul_mem' := by
    rintro z w ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, fun a ha => ?_⟩
    rw [pow_add] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun u v hu hv => ?_)
    · rw [← smul_mul_smul_comm]
      exact mul_mem (hk b hb) (hl c hc)
    · rw [add_smul]; exact add_mem hu hv
  add_mem' := by
    rintro z w ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨max k l, fun a ha => ?_⟩
    rw [smul_add]
    exact add_mem (hk a (Ideal.pow_le_pow_right (le_max_left _ _) ha))
      (hl a (Ideal.pow_le_pow_right (le_max_right _ _) ha))
  algebraMap_mem' := by
    intro r
    refine ⟨0, fun a _ => ?_⟩
    exact ⟨algebraMap S A (a * r), by simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul', mul_smul]⟩

theorem mem_idealTransform_of_forall_smul_mem {S : Type} [CommRing S] [IsNoetherianRing S]
    {I : Ideal S} {A : Type} [CommRing A] [Algebra S A] (z : FractionRing S ⊗[S] A)
    (h : ∀ a ∈ I, a • z ∈ idealTransform S I A) : z ∈ idealTransform S I A := by
  let R := (Algebra.TensorProduct.includeRight : A →ₐ[S] FractionRing S ⊗[S] A).range
  let Q : Ideal S := Submodule.comap (LinearMap.toSpanSingleton S _ z) (Subalgebra.toSubmodule R)
  have hQ : ∀ a, a ∈ Q ↔ a • z ∈ R := fun a => by simp [Q]
  have hrad : I ≤ Q.radical := by
    intro a ha
    obtain ⟨k, hk⟩ := h a ha
    refine ⟨k + 1, ?_⟩
    rw [hQ, pow_succ, mul_smul]
    exact hk _ (Ideal.pow_mem_pow ha k)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  exact ⟨n, fun a ha => (hQ a).1 (hn ha)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientSpanIffOfIsPushoutStatement
section
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_support_quotient_span_iff_of_isPushout' : ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'), IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'), ((letI := qa'.hom.toAlgebra; p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔ (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first | (exact @GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (exact GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout) | (intros; apply GlobalTheory.SupportBC.mem_support_quotient_span_iff_of_isPushout  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticQuadraticOperatorEqSumSymplecticDualStatement
section
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual : ∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i)) := by
  first | exact @GlobalTheory.quad_eq_sum_symplDual | exact GlobalTheory.quad_eq_sum_symplDual | (intros; apply GlobalTheory.quad_eq_sum_symplDual <;> assumption)
end

