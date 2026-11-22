import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0522
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDict

open GlobalTheory.InertLocField GlobalTheory.InertSelfDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem nonempty_emb {σ : E →ₐ[F] E} (h : IsCMExt F E σ) [Algebra.Unramified (𝓞 F) (𝓞 E)] (v : Pl F)
    (hv : ∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) : Nonempty (E →ₐ[F] Fv F v) := by
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split F E h.2.2.1 v).1 (fun w _ => inferInstance) with hp | hp
  · refine (hv ⟨_, hp, fun h0 => v.ne_bot ?_⟩ rfl).elim
    exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).1 h0
  · exact (nonempty_split_iff h).2 hp

omit [NumberField E] in
theorem piW_apply {v : Pl F} (τ : E →ₐ[F] Fv F v) (z : AE F E) : piW τ z = splitProj τ (evT E v z) := rfl

omit [NumberField E] in
theorem piW_cA {v : Pl F} (τ : E →ₐ[F] Fv F v) (σ : E →ₐ[F] E) (z : AE F E) :
    piW τ (cA σ z) = piW (τ.comp σ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem piW_algebraMap {v : Pl F} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    piW τ (algebraMap (AF F) (AE F E) a) = evFin F v a := by
  show evFin F v a * τ 1 = _
  rw [map_one, mul_one]

omit [NumberField E] in
theorem piW_inclR {v : Pl F} (τ : E →ₐ[F] Fv F v) (e : E) : piW τ (inclR (F := F) (AF F) e) = τ e := by
  show evFin F v 1 * τ e = _
  rw [map_one, one_mul]

theorem mem_latAt_iff {d : ℕ} (W : Spc F E d) (v : Pl F) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧ (fun i => evT E v (z i)) ∈ latLoc F W.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, haO, y, hy, rfl⟩ := hz
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      · convert tmul_mem_latLoc haO hy using 1
        funext i
        rw [Pi.smul_apply, GlobalTheory.InertSphLat.smul_inclR]
        rfl
    | zero => exact ⟨fun u _ => smul_zero u, by
        convert zero_mem (latLoc F W.L v) using 1
        funext i; simp⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], ?_⟩
      convert add_mem hx.2 hy.2 using 1
      funext i; simp
    | neg x _ hx =>
      refine ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], ?_⟩
      convert neg_mem hx.2 using 1
      funext i; simp
  · rintro ⟨hz, hm⟩
    have key : ∀ y ∈ latLoc F W.L v, (fun i => liftT E v (y i)) ∈ GlobalTheory.InertSph.latAt W v := fun y hy => by
      refine latLoc_induction (p := fun y => (fun i => liftT E v (y i)) ∈ GlobalTheory.InertSph.latAt W v)
        (fun a ha x hx => GlobalTheory.InertSphLat.gen_mem W ha hx) ?_ (fun p q hp hq => ?_) (fun p hp => ?_) hy
      · convert zero_mem (GlobalTheory.InertSph.latAt W v) using 1
        funext i; simp
      · convert add_mem hp hq using 1
        funext i; simp
      · convert neg_mem hp using 1
        funext i; simp
    convert key _ hm using 1
    funext i
    obtain ⟨y, hy⟩ := (at_iff v (z i)).1 fun u hu => congrFun (hz u hu) i
    rw [← hy, evT_liftT]

theorem mem_of_trace_int {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hu : PsiUnr ψ v) (t : F)
    (ht : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * t) = k) :
    algebraMap F (Fv F v) t ∈ v.adicCompletionIntegers F := by
  refine (hu _).1 fun y hy => ?_
  have h := GlobalTheory.LatVacArith.psi_int hψ t ht (singleFin v y) fun w => by
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleFin_self]
      exact hy
    · rw [evalV_singleFin_ne hw]
      exact zero_mem _
  rw [mul_comm, ← Algebra.smul_def, ← LinearMap.map_smul, Algebra.smul_def] at h
  exact h

theorem form_mem {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d r s : ℕ} {W : Spc F E d}
    (hW : W.IsSkew σ B r s) {v : Pl F} (hu : PsiUnr B.ψ v) (τ : E →ₐ[F] Fv F v) {x y : Fin d → E}
    (hx : x ∈ W.L) (hy : y ∈ W.L) : τ (form σ W.J x y) ∈ v.adicCompletionIntegers F := by
  haveI := hB.unram
  obtain ⟨m, p, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
  rw [← hsc (form σ W.J x y), map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_smul, Algebra.smul_def]
  refine mul_mem (mem_of_trace_int hB.std hu _ fun a => ?_) (apply_coe_mem τ _)
  have h := (hW.dual x).1 hx y hy (algebraMap (𝓞 F) (𝓞 E) a * c i)
  have e : (a : F) * Algebra.trace F E ((c i : E) * form σ W.J x y) =
      Algebra.trace F E (((algebraMap (𝓞 F) (𝓞 E) a * c i : 𝓞 E) : E) * form σ W.J x y) := by
    rw [← smul_eq_mul, ← LinearMap.map_smul, Algebra.smul_def, ← mul_assoc]
    rfl
  rw [e, Algebra.trace_trace]
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨k, by rw [← hk]; simp⟩

omit [NumberField E] in
theorem splitLat_induction {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl F} {τ : E →ₐ[F] Fv F v}
    (N : Submodule (v.adicCompletionIntegers F) (Fin d → Fv F v)) (hN : ∀ x ∈ L, (fun i => τ (x i)) ∈ N)
    {u : Fin d → Fv F v} (hu : u ∈ splitLat τ L) : u ∈ N := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => splitVec τ y ∈ N) (fun a ha x hx => ?_) ?_ (fun p q hp hq => ?_)
    (fun p hp => ?_) hy
  · exact N.smul_mem ⟨a, ha⟩ (hN x hx)
  · convert N.zero_mem using 1
    funext i; simp [splitVec]
  · rw [splitVec_add]; exact N.add_mem hp hq
  · convert N.neg_mem hp using 1
    funext i; simp [splitVec]

omit [NumberField E] in
theorem apply_mem_splitLat {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl F} (τ : E →ₐ[F] Fv F v)
    {x : Fin d → E} (hx : x ∈ L) : (fun i => τ (x i)) ∈ splitLat τ L :=
  ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => by simp [splitVec]⟩

theorem pairing_mem {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d r s : ℕ} {W : Spc F E d}
    (hW : W.IsSkew σ B r s) {v : Pl F} (hu : PsiUnr B.ψ v) (τ : E →ₐ[F] Fv F v) {u₁ u₂ : Fin d → Fv F v}
    (h₁ : u₁ ∈ splitLat τ W.L) (h₂ : u₂ ∈ splitLat (τ.comp σ) W.L) :
    u₁ ⬝ᵥ W.J.map τ *ᵥ u₂ ∈ v.adicCompletionIntegers F := by
  let O : Submodule (v.adicCompletionIntegers F) (Fv F v) :=
    { carrier := v.adicCompletionIntegers F
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := fun c _ hx => mul_mem c.2 hx }
  let β : (Fin d → Fv F v) →ₗ[Fv F v] (Fin d → Fv F v) →ₗ[Fv F v] Fv F v := Matrix.toLinearMap₂' (Fv F v) (W.J.map τ)
  have hβ : ∀ a b, β a b = a ⬝ᵥ W.J.map τ *ᵥ b := fun a b => Matrix.toLinearMap₂'_apply' _ a b
  rw [← hβ]
  refine splitLat_induction (O.comap ((β.flip u₂).restrictScalars _)) (fun x hx => ?_) h₁
  refine splitLat_induction (O.comap ((β fun i => τ (x i)).restrictScalars _)) (fun y hy => ?_) h₂
  show β _ _ ∈ v.adicCompletionIntegers F
  rw [hβ]
  convert form_mem hB hW hu τ hx hy using 1
  simp [form, dotProduct, Matrix.mulVec, map_sum]

omit [NumberField E] in
theorem col_mem {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl F} {τ : E →ₐ[F] Fv F v}
    {b : GL (Fin d) (Fv F v)} (hb : IsSplitBasis τ L b) (j : Fin d) : (fun i => b.1 i j) ∈ splitLat τ L := by
  have := (hb (Pi.single j 1)).1 fun i => by
    by_cases e : i = j
    · subst e; simp
    · simp [e]
  rwa [Matrix.mulVec_single_one] at this

theorem exists_gram {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d r s : ℕ} {W : Spc F E d}
    (hW : W.IsSkew σ B r s) {v : Pl F} (hu : PsiUnr B.ψ v) (τ : E →ₐ[F] Fv F v) {b₁ b₂ : GL (Fin d) (Fv F v)}
    (h₁ : IsSplitBasis τ W.L b₁) (h₂ : IsSplitBasis (τ.comp σ) W.L b₂) :
    ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
      S.map (fun x => (x : Fv F v)) = b₁.1ᵀ * W.J.map τ * b₂.1 := by
  obtain ⟨k, S, T, hS, hT, hTS⟩ := exists_formFrame σ W.J (det_ne_zero_of_skew σ B hW) W.L hW.lat
    (fun y hy => (hW.dual y).2 fun x hx o => by
      obtain ⟨r, hr⟩ := hy x hx
      rw [← hr]
      exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
  have hG : ∀ i j, (b₁.1ᵀ * W.J.map τ * b₂.1) i j ∈ v.adicCompletionIntegers F := fun i j => by
    rw [Matrix.mul_assoc]
    exact pairing_mem hB hW hu τ (col_mem h₁ i) (col_mem h₂ j)
  have hA : ∀ i j, ((b₂⁻¹).1 * S.map (τ.comp σ)) i j ∈ v.adicCompletionIntegers F := fun i j =>
    h₂.mem_iff.1 (apply_mem_splitLat _ (hS j)) i
  have hC : ∀ i j, ((b₁⁻¹).1 * T.map τ) i j ∈ v.adicCompletionIntegers F := fun i j =>
    h₁.mem_iff.1 (apply_mem_splitLat _ (hT j)) i
  have hH : ∀ i j, (((b₂⁻¹).1 * S.map (τ.comp σ)) * ((b₁⁻¹).1 * T.map τ)ᵀ) i j ∈ v.adicCompletionIntegers F :=
    fun i j => sum_mem fun l _ => mul_mem (hA i l) (hC j l)
  have e1 : W.J.map τ * S.map (τ.comp σ) * (T.map τ)ᵀ = 1 := by
    have e0 : W.J * S.map σ * Tᵀ = 1 := by
      rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_transpose, hTS, Matrix.transpose_one]
    have := congrArg (fun M => Matrix.map M (τ : E →+* Fv F v)) e0
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have e2 : (b₁.1ᵀ * W.J.map τ * b₂.1) * (((b₂⁻¹).1 * S.map (τ.comp σ)) * ((b₁⁻¹).1 * T.map τ)ᵀ) = 1 := by
    calc _ = b₁.1ᵀ * (W.J.map τ * (b₂.1 * (b₂⁻¹).1) * S.map (τ.comp σ) * (T.map τ)ᵀ) * ((b₁⁻¹).1)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [Units.mul_inv, Matrix.mul_one, e1, Matrix.mul_one, ← Matrix.transpose_mul, Units.inv_mul,
            Matrix.transpose_one]
  refine ⟨Matrix.of fun i j => ⟨_, hG i j⟩, ?_, rfl⟩
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i j => ⟨_, hH i j⟩) ?_
  refine Matrix.map_injective (v.adicCompletionIntegers F).subtype_injective ?_
  simp only
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  exact e2

end GlobalTheory.SplitDict

namespace GlobalTheory.SplitDict

open GlobalTheory.InertLocField

theorem exists_split_dictionary : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v hv hu
  haveI := hB.unram
  haveI := hW.lat
  have h := hB.cm
  obtain ⟨τ⟩ := nonempty_emb h v hv
  obtain ⟨b₁, h₁⟩ := exists_isSplitBasis τ W.L h
  obtain ⟨b₂, h₂⟩ := exists_isSplitBasis (τ.comp σ) W.L h
  refine ⟨piW τ, piW (τ.comp σ), b₁, b₂, ⟨piW_cA τ σ, fun z => ?_, piW_algebraMap τ, piW_algebraMap _,
    fun z hz e₁ e₂ => ?_, fun x₁ x₂ => ?_, fun z => ?_⟩, ?_⟩
  · rw [piW_cA, comp_conj_conj h]
  · obtain ⟨y, rfl⟩ := (at_iff v z).1 hz
    rw [piW_apply, evT_liftT] at e₁ e₂
    rw [split_ext h τ (y := y) (z := 0) (by rw [e₁, map_zero]) (by rw [e₂, map_zero]), map_zero]
  · refine ⟨liftT E v ((splitAlgEquiv h τ).symm (x₁, x₂)), at_liftT v _, ?_, ?_⟩
    · rw [piW_apply, evT_liftT, splitProj_symm]
    · rw [piW_apply, evT_liftT, splitProj_comp_symm]
  · rw [mem_latAt_iff, mem_latLoc_iff_split τ h, h₁.mem_iff, h₂.mem_iff]
    rfl
  · have e : (incM F W.J).map (piW τ) = W.J.map τ := Matrix.ext fun i j => piW_inclR τ (W.J i j)
    rw [e]
    exact exists_gram hB hW hu τ h₁ h₂

end GlobalTheory.SplitDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ArrowMultilinear

section General

variable {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

theorem chainTo_congr {k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)} : ∀ n, (∀ j < n, k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n (Nat.lt_succ_self n), chainTo_congr n fun j hj => h j (Nat.lt_succ_of_lt hj)]

theorem chain_multilinear : ∀ (m : ℕ) (A : Fin m → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    (k : ∀ j : Fin m, A j →ₗ[ℂ] (V j →ₗ[ℂ] V (j + 1))),
    ∃ M : MultilinearMap ℂ A (V 0 →ₗ[ℂ] V m), ∀ fs,
      M fs = chainTo (fun j => if h : j < m then k ⟨j, h⟩ (fs ⟨j, h⟩) else 0) m := by
  intro m
  induction m with
  | zero =>
    intro A _ _ k
    exact ⟨MultilinearMap.constOfIsEmpty ℂ A LinearMap.id, fun _ => rfl⟩
  | succ m ih =>
    intro A _ _ k
    obtain ⟨M, hM⟩ := ih (fun j => A j.castSucc) (fun j => k j.castSucc)
    let kl : A (Fin.last m) →ₗ[ℂ] (V m →ₗ[ℂ] V (m + 1)) := k (Fin.last m)
    refine ⟨MultilinearMap.uncurryRight
      (((LinearMap.llcomp ℂ (V 0) (V m) (V (m + 1)) ∘ₗ kl).flip).compMultilinearMap M), fun fs => ?_⟩
    show kl (fs (Fin.last m)) ∘ₗ M (Fin.init fs) = _ ∘ₗ chainTo _ m
    rw [hM]
    beta_reduce
    rw [dif_pos (Nat.lt_succ_self m)]
    congr 1
    refine chainTo_congr m fun j hj => ?_
    rw [dif_pos hj, dif_pos (Nat.lt_succ_of_lt hj)]
    rfl

theorem pair_multilinear {ι κ X Y : Type} {A : ι → Type} {B : κ → Type} [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (Ma : MultilinearMap ℂ A X) (Mb : MultilinearMap ℂ B Y) :
    ∃ M : MultilinearMap ℂ A (MultilinearMap ℂ B ℂ), ∀ a b, M a b = β (Ma a) (Mb b) := by
  let L : X →ₗ[ℂ] MultilinearMap ℂ B ℂ :=
    { toFun := fun x => (β x).compMultilinearMap Mb
      map_add' := fun x x' => by ext b; simp
      map_smul' := fun c x => by ext b; simp }
  exact ⟨L.compMultilinearMap Ma, fun _ _ => rfl⟩

theorem compl_multilinear {ι κ X Y P Q : Type} {A : ι → Type} {B : κ → Type} [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (c : (∀ j, A j) → P →ₗ[ℂ] X) (r : (∀ j, B j) → Q →ₗ[ℂ] Y) (u : P) (v : Q)
    (hc : ∃ M : MultilinearMap ℂ A X, ∀ a, M a = c a u) (hr : ∃ M : MultilinearMap ℂ B Y, ∀ b, M b = r b v) :
    ∃ M : MultilinearMap ℂ A (MultilinearMap ℂ B ℂ), ∀ a b, M a b = β.compl₁₂ (c a) (r b) u v := by
  obtain ⟨Ma, ha⟩ := hc
  obtain ⟨Mb, hb⟩ := hr
  obtain ⟨M, hM⟩ := pair_multilinear β Ma Mb
  exact ⟨M, fun a b => by rw [hM, ha, hb, LinearMap.compl₁₂_apply]⟩

end General

section Jet

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetLin_add (J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) :
    Formalism.L2.Ker.jetLin (J + J') = Formalism.L2.Ker.jetLin J + Formalism.L2.Ker.jetLin J' := by
  refine (MvPolynomial.basisMonomials _ ℂ).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add]

theorem jetLin_smul (c : ℂ) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) :
    Formalism.L2.Ker.jetLin (c • J) = c • Formalism.L2.Ker.jetLin J := by
  refine (MvPolynomial.basisMonomials _ ℂ).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, Pi.smul_apply, map_smul]

end Jet

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem jetTab_add (W : G.Weil) (B : VertexFrames G) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ}
    (hf : IsThetaFunO W.ψ _ _ f) (hf' : IsThetaFunO W.ψ _ _ f') (x : FinPt G p.small) (y : FinPt G p.big) :
    jetTab W B p (f + f') x y = jetTab W B p f x y + jetTab W B p f' x y := by
  funext k
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO, Pi.add_apply]
  rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ hf hf', map_add, Pi.add_apply]

theorem jetTab_smul (W : G.Weil) (B : VertexFrames G) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ)
    (x : FinPt G p.small) (y : FinPt G p.big) :
    jetTab W B p (c • f) x y = c • jetTab W B p f x y := by
  funext k
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO, Pi.smul_apply]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply]

def fockLin (W : G.Weil) (B : VertexFrames G) (p : Pair T) (x : FinPt G p.small) (y : FinPt G p.big) :
    thSub W p →ₗ[ℂ] (VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big)) where
  toFun f := fockComp W B p f x y
  map_add' f f' := by
    ext1 v
    simp only [fockComp, Submodule.coe_add]
    rw [jetTab_add W B p f.2 f'.2]
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_add, LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' c f := by
    ext1 v
    simp only [fockComp, Submodule.coe_smul]
    rw [jetTab_smul]
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_smul, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

variable {W : G.Weil} {U : Set T}

theorem col_multilinear (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (Ψ₀ : VV ℂ (wt G (.top 0))) :
    ∃ M : MultilinearMap ℂ (fun j : Fin D.R.m => thSub W (.top t j)) (VV ℂ (wt G (.top D.R.m))),
      ∀ fs, M fs = colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x Ψ₀ := by
  obtain ⟨Mc, hc⟩ := chain_multilinear (V := fun j => VV ℂ (wt G (.top j))) D.R.m
    (fun j : Fin D.R.m => thSub W (.top t j))
    (fun j => S.Z.scal 1 (.top t j) • fockLin W S.N.frC (.top t j) (x j * S.N.u _) (x (j + 1) * S.N.u _))
  refine ⟨(LinearMap.applyₗ (R := ℂ) (rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ Ψ₀)).compMultilinearMap Mc, fun fs => ?_⟩
  show Mc fs _ = _
  rw [hc]
  refine LinearMap.congr_fun (chainTo_congr (V := fun j => VV ℂ (wt G (.top j))) D.R.m fun j hj => ?_) _
  exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem row_multilinear (S : GridChoice W U) (y : ∀ i, FinPt G (.grid i D.R.m))
    (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    ∃ M : MultilinearMap ℂ (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) (VV ℂ (wt G (.grid D.R.m D.R.m))),
      ∀ gs, M gs =
        rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y F₀ := by
  obtain ⟨Mr, hr⟩ := chain_multilinear (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m
    (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T))
    (fun i => S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockLin W S.N.frC (.chi i D.R.m : Pair T) (y i * S.N.u _) (y (i + 1) * S.N.u _))
  refine ⟨(LinearMap.applyₗ (R := ℂ)
    (rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) F₀))).compMultilinearMap Mr,
    fun gs => ?_⟩
  show Mr gs _ = _
  rw [hr]
  refine LinearMap.congr_fun (chainTo_congr (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m fun j hj => ?_) _
  exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem pairing_multilinear {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (Ψ₀ : VV ℂ (wt G (.top 0))) (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    ∃ M : MultilinearMap ℂ (fun j : Fin D.R.m => thSub W (.top t j))
        (MultilinearMap ℂ (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ),
      ∀ fs gs, M fs gs = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
        (colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
        (rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀ := by
  exact compl_multilinear (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)))
    (fun fs : ∀ j : Fin D.R.m, thSub W (.top t j) =>
      colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
    (fun gs : ∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T) =>
      rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀
    (col_multilinear S t x Ψ₀) (row_multilinear S y F₀)

end GlobalTheory.ArrowMultilinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompMulFin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.KerTrans

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_fin (p : Pair T) (k : FinPt G p.small) :
    (G.toPair p k.1 1).1 ∈ GfC (G.pS p) ∧ (G.toPair p k.1 1).2 ∈ GfC (G.pT p) := by
  cases p <;> simp [GridData.toPair]

theorem ker_mul_fin (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h : GA D (G.V p.big)) : W.ker p F (g * k) h = W.ker p (W.om p (G.toPair p k 1) F) g h := by
  have e : G.toPair p (g * k) h = G.toPair p g h * G.toPair p k 1 := by
    rw [← GlobalTheory.RowClaim.toPair_mul, mul_one]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem fockComp_mul_fin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G)
    {p : Pair T}, p.InRange D.R.m → ∀ (f : WO (G.pS p) (G.pT p) → ℂ), IsThetaFunO W.ψ (G.pS p) (G.pT p) f →
    ∀ (g k : FinPt G p.small) (h : FinPt G p.big),
      fockComp W B p f (g * k) h = fockComp W B p (W.om p (G.toPair p k.1 1) f) g h := by
  intro D T L sc G W B p hp f hf g k h
  have hk := toPair_fin p k
  unfold fockComp
  congr 1
  funext m
  unfold jetTab kerFin
  rw [Subgroup.coe_mul, ker_mul_fin]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om p) (W.om_is p hp) W.θ W.θ_is _ hk.1 _ hk.2 _ _ _ _ f _ hf

end GlobalTheory.KerTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiVertexLattice_splitsAlongWitt_at_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v := by
  first | exact @GlobalTheory.AscFin.MonoJac.monoAt_jac | exact GlobalTheory.AscFin.MonoJac.monoAt_jac | (intros; apply GlobalTheory.AscFin.MonoJac.monoAt_jac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenOppositeGridPathsAndDeterminedByEdgesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges : ∀ {T : Type} (m : ℕ) (t : T), (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.givenPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.givenPath t m) = GlobalTheory.SplitFlip.givenPath m) ∧ (GlobalTheory.FlipRun.OnGrid m t (GlobalTheory.FunObj.oppPath t m) ∧ GlobalTheory.FlipRun.edges (GlobalTheory.FunObj.oppPath t m) = GlobalTheory.SplitFlip.oppositePath m) ∧ ∀ {X Y : Node} (p q : Path T X Y), GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.FlipRun.OnGrid m t q → GlobalTheory.FlipRun.edges p = GlobalTheory.FlipRun.edges q → p = q := by
  first | exact @GlobalTheory.FlipPaths.given_opp_paths | exact GlobalTheory.FlipPaths.given_opp_paths | (intros; apply GlobalTheory.FlipPaths.given_opp_paths <;> assumption)
end

