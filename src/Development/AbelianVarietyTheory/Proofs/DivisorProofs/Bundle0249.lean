import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0200
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0198
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Formalism.SatakeDualWeyl.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import GroundTheory.LocalFields.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTermStatement
section
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_leading_term : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (j : ι), alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k))) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (j : ι) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V), IsPhi p f h Φ → IsGamma p (f j) γ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, Φ x {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • γ x := by
  first | exact @GlobalTheory.DI.PhiLead.leading_term | exact GlobalTheory.DI.PhiLead.leading_term | (intros; apply GlobalTheory.DI.PhiLead.leading_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegreeStatement
section
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  first | exact @GlobalTheory.DI.alt_and_phi_vanish_above_degree | exact GlobalTheory.DI.alt_and_phi_vanish_above_degree | (intros; apply GlobalTheory.DI.alt_and_phi_vanish_above_degree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkImageOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem charZero_stalk_genPt : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK
    CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ hY hK
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hL : CharZero Y.functionField :=
    charZero_of_injective_ringHom (f := (Y.germToFunctionField ⊤).hom) (Y.germToFunctionField_injective ⊤)
  have h0 : CharZero (Z.presheaf.stalk (genPt π)) := (π.stalkMap (genericPoint Y)).hom.charZero
  exact h0

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDvdOfAevalEqZero
section
open Polynomial Matrix Formalism.UG

namespace GlobalTheory.SepCharpoly

theorem charpoly_dvd_of_aeval_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]),
      M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by
  intro R _ _ n M p hs hp
  classical
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  rw [← Polynomial.map_dvd_map f hf M.charpoly_monic, ← Matrix.charpoly_map]
  refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval (M.map f) ?_ (p.map f) ?_
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [show M.map f = (f.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) M from rfl]
    have := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId R K)) hp
    rw [← aeval_algHom_apply, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this

end GlobalTheory.SepCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfIntertwined
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem charpoly_eq_of_intertwined :
    ∀ (A : Type) [CommRing A] [IsDomain A] (h : ℕ) (μ : A) (F G X Y : Matrix (Fin h) (Fin h) A),
      μ ≠ 0 → G * F = μ • (1 : Matrix (Fin h) (Fin h) A) → F * X = Y * F →
        Y.charpoly = X.charpoly := by
  intro A _ _ h μ F G X Y hμ hGF hFX
  have hdet : F.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hGF
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hμ h1.symm
  have hmap : (F.map Polynomial.C) * (X.map Polynomial.C)
      = (Y.map Polynomial.C) * (F.map Polynomial.C) := by
    have := congrArg (fun M => Polynomial.C.mapMatrix M) hFX
    simpa [map_mul] using this
  have hcomm : (F.map Polynomial.C) * Matrix.scalar (Fin h) (Polynomial.X : Polynomial A)
      = Matrix.scalar (Fin h) (Polynomial.X : Polynomial A) * (F.map Polynomial.C) :=
    ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq).symm
  have key : (F.map Polynomial.C) * charmatrix X = charmatrix Y * (F.map Polynomial.C) := by
    simp only [charmatrix, RingHom.mapMatrix_apply, mul_sub, sub_mul]
    rw [hmap, hcomm]
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  have hC : (F.map Polynomial.C).det ≠ 0 := by
    have : (F.map Polynomial.C).det = Polynomial.C F.det := by
      simpa using (RingHom.map_det (Polynomial.C : A →+* Polynomial A) F).symm
    rw [this]
    exact Polynomial.C_ne_zero.mpr hdet
  have := mul_right_cancel₀ hC hd
  simpa [Matrix.charpoly] using this.symm

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqQuotientCharpolyPowStatement
section
open scoped TensorProduct nonZeroDivisors
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_quotient_charpoly_pow : ∀ (K : Type) [Field K] (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (t T : Module.End K X) (_ : Commute t T) (e : ℕ) (_ : 0 < e) (_ : t ^ e = 0)
    (_ : ∀ x, t x = 0 → x ∈ LinearMap.range (t ^ (e - 1)))
    (hT : LinearMap.range t ≤ (LinearMap.range t).comap T),
    LinearMap.charpoly T = (LinearMap.charpoly ((LinearMap.range t).mapQ (LinearMap.range t) T hT)) ^ e := by
  first | exact @GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow | exact GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow | (intros; apply GlobalTheory.NilpFiltration.charpoly_eq_charpoly_mapQ_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
section
open Matrix Complex ComplexConjugate Filter Topology

noncomputable section

namespace GlobalTheory.HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}

theorem del_finsetProd {ι : Type*} [DecidableEq ι] (t : Finset ι) {f : ι → E → ℂ} {z : E}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (f i) z) (ξ : E) :
    del (fun x => ∏ i ∈ t, f i x) z ξ = ∑ i ∈ t, (∏ j ∈ t.erase i, f j z) * del (f i) z ξ := by
  have h1 := (HasFDerivAt.finsetProd (u := t) (g := f) (fun i hi => (h i hi).hasFDerivAt)).fderiv
  simp only [del_apply, h1, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

section Det

variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}

theorem trace_adjugate_mul_eq_sum (A B : Matrix n n ℂ) :
    (A.adjugate * B).trace = ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * B (σ i) i := by
  have h1 : ∀ i, (A.adjugate * B) i i = (A.updateCol i (fun k => B k i)).det := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.trace, Matrix.diag, h1, det_apply']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [updateCol_apply]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (Finset.ne_of_mem_erase hj)]

theorem del_det (h : MContDiffAt 1 H z) (ξ : E) :
    del (fun x => (H x).det) z ξ = ((H z).adjugate * mdel H z ξ).trace := by
  have hp : ∀ σ : Equiv.Perm n, DifferentiableAt ℝ (fun x => ∏ i, H x (σ i) i) z := fun σ =>
    (contDiffAt_prod fun c _ => h (σ c) c).differentiableAt one_ne_zero
  simp only [det_apply']
  rw [del_sum fun σ _ => (differentiableAt_const _).fun_mul (hp σ), trace_adjugate_mul_eq_sum,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [del_mul (differentiableAt_const _) (hp σ),
    del_finsetProd _ (f := fun i x => H x (σ i) i) fun i _ => h.diff _ _]
  simp

theorem trace_conn (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det) (ξ : E) :
    (conn H z ξ).trace = (H z).det⁻¹ * del (fun x => (H x).det) z ξ := by
  have _ := hu
  rw [del_det h, conn, ← transpose_nonsing_inv, ← transpose_mul, trace_transpose, trace_mul_comm,
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, trace_smul, smul_eq_mul]

theorem trace_curv_eq_neg_dbar (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    (curv H z ξ η).trace = -dbar (fun x => (conn H x ξ).trace) z η := by
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  simp only [curv, trace, diag_apply, Matrix.neg_apply, mdbar_apply, Finset.sum_neg_distrib]
  rw [dbar_sum fun a _ => hc.diff a a, ContinuousLinearMap.sum_apply]

theorem trace_curv_eq_curv_det (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : E) :
    (curv H z ξ η).trace =
      curv (fun x => (of fun _ _ => (H x).det : Matrix Unit Unit ℂ)) z ξ η () () := by
  have he : (fun x => (conn H x ξ).trace) =ᶠ[𝓝 z]
      fun x => conn (fun x => (of fun _ _ => (H x).det : Matrix Unit Unit ℂ)) x ξ () () := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu] with x h1 h2
    rw [trace_conn (h1.of_le one_le_two) h2]
    simp [conn, Matrix.mul_apply]
  rw [trace_curv_eq_neg_dbar h hu, dbar_congr he]
  rfl

theorem ofReal_re_det {M : Matrix n n ℂ} (hM : M.IsHermitian) : (M.det.re : ℂ) = M.det := by
  refine conj_eq_iff_re.1 ?_
  rw [← star_def, ← det_conjTranspose, hM.eq]

theorem trace_curv (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (ξ η : E) :
    (curv H z ξ η).trace = -leviForm (fun x => Real.log (H x).det.re) z ξ η := by
  rw [trace_curv_eq_curv_det h hu]
  refine curv_line (f := fun x => (H x).det.re) (reCLM.contDiff.contDiffAt.comp z h.det) ?_
    (hh.mono fun x hx => (ofReal_re_det hx).symm) ξ η () ()
  intro h0
  apply hu.ne_zero
  rw [← ofReal_re_det hh.self_of_nhds, ofReal_eq_zero]
  exact h0

theorem chernOne_eq_neg_ddc_log_det (h : MContDiffAt 2 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det) (ξ η : E) :
    chernOne H z ξ η = -ddc (fun x => Real.log (H x).det.re) z ξ η := by
  rw [chernOne, trace_curv h hh hu, ddc, mul_neg]

end Det

section Sub

variable [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem trace_conn_eq_sub_add_quot (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) : (conn H z ξ).trace =
      (conn (fun x => subGram (H x)) z ξ).trace + (conn (fun x => quotGram (H x)) z ξ).trace := by
  have hq := isUnit_det_quotGram hu hs
  have he : (fun x => (H x).det) =ᶠ[𝓝 z] fun x => (subGram (H x)).det * (quotGram (H x)).det :=
    (h.subGram.eventually_isUnit hs).mono fun x hx => det_eq_det_subGram_mul hx
  rw [trace_conn h hu, trace_conn h.subGram hs, trace_conn (h.quotGram hs) hq, del_congr he,
    del_mul (h.subGram.det.differentiableAt one_ne_zero)
      ((h.quotGram hs).det.differentiableAt one_ne_zero), det_eq_det_subGram_mul hs]
  have h1 := hs.ne_zero
  have h2 := hq.ne_zero
  field_simp
  ring

theorem trace_curv_eq_sub_add_quot (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ η : E) : (curv H z ξ η).trace =
      (curv (fun x => subGram (H x)) z ξ η).trace +
        (curv (fun x => quotGram (H x)) z ξ η).trace := by
  have hq := isUnit_det_quotGram hu hs
  have he : (fun x => (conn H x ξ).trace) =ᶠ[𝓝 z] fun x =>
      (conn (fun x => subGram (H x)) x ξ).trace + (conn (fun x => quotGram (H x)) x ξ).trace := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, h.subGram.eventually_isUnit hs]
      with x h1 h2 h3
    exact trace_conn_eq_sub_add_quot (h1.of_le one_le_two) h2 h3 ξ
  have hS : MContDiffAt 1 (fun x => conn (fun x => subGram (H x)) x ξ) z :=
    h.subGram.conn hs (by norm_num) ξ
  have hQ : MContDiffAt 1 (fun x => conn (fun x => quotGram (H x)) x ξ) z :=
    (h.quotGram hs).conn hq (by norm_num) ξ
  rw [trace_curv_eq_neg_dbar h hu, trace_curv_eq_neg_dbar h.subGram hs,
    trace_curv_eq_neg_dbar (h.quotGram hs) hq, dbar_congr he, dbar_add,
    ContinuousLinearMap.add_apply, neg_add]
  · exact DifferentiableAt.fun_sum fun a _ => hS.diff a a
  · exact DifferentiableAt.fun_sum fun a _ => hQ.diff a a

end Sub

end GlobalTheory.HermFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChevalleyExistsLeSupMaximalIdealPowOfAntitone
section
open IsLocalRing

namespace GlobalTheory.Chevalley

theorem exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion (A : Type) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (F : AdicCompletion (maximalIdeal A) A) (n : ℕ) :
    ∃ a : A, F - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal A) A n F)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal A).fg_of_isNoetherianRing,
    LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
  first
  | rw [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply, ← ha, sub_self]
  | simp [← ha]

theorem exists_le_sup_maximalIdeal_pow_of_antitone :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A),
      Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) →
      (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A),
        (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈
          maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) →
        (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) →
      ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  intro A _ _ _ K J hK hmK hJ k
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : Module.Flat A B := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let f := algebraMap A B
  have hmB : ∀ n, maximalIdeal B ^ n = (maximalIdeal A ^ n).map f := fun n ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]
  let K' : ℕ → Ideal B := fun e ↦ (K e).map f
  have hK' : Antitone K' := fun i j hij ↦ Ideal.map_mono (hK hij)
  have hmK' : ∀ e, maximalIdeal B ^ e ≤ K' e := fun e ↦ by
    rw [hmB]; exact Ideal.map_mono (hmK e)
  let N : Ideal B := ⨅ e, K' e
  have hNK : ∀ e, N ≤ K' e := fun e ↦ iInf_le _ e
  have hNJ : N ≤ J.map f := by
    intro F hF
    choose a ha using exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion A F
    refine hJ F a ha fun n ↦ ?_
    have h1 : f (a n) ∈ K' n := by
      have : f (a n) = F - (F - f (a n)) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hNK n hF) (hmK' n (ha n))
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (K n)]
    exact h1
  let P : ℕ → Submodule B (B ⧸ N) := fun e ↦ Submodule.map (Submodule.mkQ N) (K' e : Submodule B B)
  have hdir : Directed (· ≥ ·) P := fun i j ↦
    ⟨max i j, Submodule.map_mono (hK' (le_max_left i j)), Submodule.map_mono (hK' (le_max_right i j))⟩
  have hbot : (⨅ e, P e) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N x
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submodule.mem_iInf] at hx ⊢
    intro e
    have := Submodule.mem_comap.2 (hx e)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (hNK e)] at this
    exact this
  obtain ⟨e, he⟩ := exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ N) ℕ P ⟨0⟩ hdir hbot k
  refine ⟨e, ?_⟩
  have hsm : (maximalIdeal B ^ k • (⊤ : Submodule B (B ⧸ N))) =
      Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B) := by
    have hI : (maximalIdeal B ^ k • (⊤ : Submodule B B)) = (maximalIdeal B ^ k : Submodule B B) := by
      rw [smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ N, LinearMap.range_eq_map, ← Submodule.map_smul'', hI]
  have h2 : K' e ≤ maximalIdeal B ^ k ⊔ N := by
    intro y hy
    have h := he (Submodule.mem_map_of_mem (f := Submodule.mkQ N) hy)
    rw [hsm] at h
    have h' : y ∈ Submodule.comap (Submodule.mkQ N)
        (Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B)) := h
    rw [Submodule.comap_map_mkQ] at h'
    rw [sup_comm]; exact h'
  have h3 : K' e ≤ (J ⊔ maximalIdeal A ^ k).map f := by
    rw [Ideal.map_sup, ← hmB]
    exact h2.trans (sup_le le_sup_right (hNJ.trans le_sup_left))
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J ⊔ maximalIdeal A ^ k)]
  exact Ideal.map_le_iff_le_comap.1 h3

end GlobalTheory.Chevalley
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginNoeth

def baseHom (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : R →+* D :=
  (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R))

def closure (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Subring D :=
  letI := (baseHom A R D).toAlgebra
  (integralClosure R D).toSubring

def closureAlg (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Algebra R (closure A R D) :=
  ((baseHom A R D).codRestrict (closure A R D) (fun r => by
    letI := (baseHom A R D).toAlgebra
    exact isIntegral_algebraMap (R := R) (A := D) (x := r))).toAlgebra

def ClosureFiniteEtale (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] : Prop :=
  letI := closureAlg A R D
  Module.Finite R (closure A R D) ∧ Algebra.Etale R (closure A R D) ∧ Nontrivial (closure A R D)

def Good (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) : Prop :=
  letI := closureAlg A R D
  (∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] closure A R D)) ∧
    ∃ s : closure A R D →+* FractionRing A,
      s.comp (algebraMap R (closure A R D)) = (algebraMap A (FractionRing A)).comp ρ

end GlobalTheory.KeyOriginNoeth

example (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (r : R) :
    GlobalTheory.KeyOriginNoeth.baseHom A R (GlobalTheory.LocAcyc.GenFib A R) r ∈
      GlobalTheory.KeyOriginNoeth.closure A R (GlobalTheory.LocAcyc.GenFib A R) := by
  letI := (GlobalTheory.KeyOriginNoeth.baseHom A R (GlobalTheory.LocAcyc.GenFib A R)).toAlgebra
  exact isIntegral_algebraMap (R := R) (A := GlobalTheory.LocAcyc.GenFib A R) (x := r)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureGenericFibreClopenSplit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.closure_generic_fibre_clopen_split : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  intro R A _ _ _ _ _ hsm C C' hU hd1 hd2
  let K := FractionRing R
  let f : A →+* A ⊗[R] K := (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] K).toRingHom
  let φ := PrimeSpectrum.comap f
  have hφc : Continuous φ := PrimeSpectrum.continuous_comap f

  have hF : {r : PrimeSpectrum A | r.asIdeal.comap (algebraMap R A) = ⊥} = Set.range φ := by
    have h1 := GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker R A K
    have hker : RingHom.ker (algebraMap R K) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
    rw [hker] at h1
    rw [← h1]
    let e := (Algebra.TensorProduct.comm R A K).toRingEquiv
    have hg : (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom = e.toRingHom.comp f := by
      ext a
      simp [f, e]
    rw [hg, PrimeSpectrum.comap_comp, Set.range_comp]
    have hsurj : Set.range (PrimeSpectrum.comap e.toRingHom) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ⟨PrimeSpectrum.comap e.symm.toRingHom y, ?_⟩
      rw [← PrimeSpectrum.comap_comp_apply, RingEquiv.symm_toRingHom_comp_toRingHom]
      rfl
    rw [hsurj, Set.image_univ]

  have hinj : Function.Injective f := by
    have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R K)
      (IsFractionRing.injective R K)
    intro x y hxy
    have : (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm x) =
        (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm y) := by
      simpa [f] using hxy
    exact (TensorProduct.rid R A).symm.injective (hl this)
  have hdense : DenseRange φ :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2
      (by rw [(RingHom.injective_iff_ker_eq_bot f).1 hinj]; exact bot_le)
  have hCC' : Disjoint C C' := hd1.mono_right subset_closure
  have hunion : φ ⁻¹' C ∪ φ ⁻¹' C' = Set.univ := by
    rw [← Set.preimage_union, hU, hF, Set.preimage_range]
  have hcompl : IsCompl (φ ⁻¹' C) (φ ⁻¹' C') :=
    ⟨hCC'.preimage φ, codisjoint_iff.2 hunion⟩
  have hS1 : φ ⁻¹' closure C = φ ⁻¹' C := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hd2 hx)
  have hclosed : IsClosed (φ ⁻¹' C) := hS1 ▸ isClosed_closure.preimage hφc
  have hS2 : φ ⁻¹' closure C' = φ ⁻¹' C' := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact absurd hx (Set.disjoint_left.1 hd1 h)
    · exact h
  have hclosed' : IsClosed (φ ⁻¹' C') := hS2 ▸ isClosed_closure.preimage hφc
  have hopen : IsOpen (φ ⁻¹' C) := by
    rw [← isClosed_compl_iff, hcompl.compl_eq]; exact hclosed'
  obtain ⟨ε, hε, hεS⟩ := PrimeSpectrum.isClopen_iff.1 ⟨hclosed, hopen⟩
  obtain ⟨a, ha, haε⟩ := GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra R A hsm ε hε
  have hfa : f a = ε := by simp [f, haε]
  have hpre : φ ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) = φ ⁻¹' C := by
    rw [hεS, ← hfa]
    ext x
    simp [φ, PrimeSpectrum.mem_basicOpen]
  have hCa : C ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inl hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ φ ⁻¹' C := hx
    rw [← hpre] at hy
    exact hy
  have hC'a : C' ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))ᶜ := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inr hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ (φ ⁻¹' C)ᶜ := hcompl.compl_eq ▸ hx
    rw [← hpre] at hy
    exact hy
  have hclo : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · exact (disjoint_compl_right (a := (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)))).mono
      (closure_minimal hCa hclo.isClosed) (closure_minimal hC'a hclo.isOpen.isClosed_compl)
  · rw [← closure_union, hU, hF]
    exact hdense.closure_range
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelTorsionOfFiniteLengthModElementStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_torsion_of_finiteLength_mod_element : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  first | exact @GlobalTheory.cokernel_torsion_of_finiteLength_mod | exact GlobalTheory.cokernel_torsion_of_finiteLength_mod | (intros; apply GlobalTheory.cokernel_torsion_of_finiteLength_mod <;> assumption)
end

