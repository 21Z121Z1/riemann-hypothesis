import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import GroundTheory.GlobalFields.LocalAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianSkewHermitianCompletionTensor
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewLagr

open Matrix

theorem det_hyp {L : Type*} [CommRing L] (m : ℕ) :
    (fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0).det = (-1) ^ m := by
  have h : fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0 =
      (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    simp [fromBlocks_multiply]
  rw [h, det_mul, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp [det_neg]

theorem exists_isLagr_of_local (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {L : Type} [Field L] [Algebra (v.adicCompletion F) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion F) L]
    (c : L →ₐ[v.adicCompletion F] L) (hc : ∀ x, c (c x) = x) {δ : L} (hδ : δ ≠ 0) (hcδ : c δ = -δ)
    (m : ℕ) (J : Matrix (Fin (m + m)) (Fin (m + m)) L) (hJ : ∀ i j, c (J j i) = -J i j)
    (hd : J.det ≠ 0) (hx : ∃ x, J.det = x * c x) :
    ∃ Cy : Matrix (Fin (m + m)) (Fin m) L, GlobalTheory.WeilM.IsLagr c J Cy := by
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨x, hx⟩ := hx
  let σ : L ≃ₐ[v.adicCompletion F] L := AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)
  have hσc : ∀ y, σ y = c y := fun _ => rfl
  have h2 : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap (v.adicCompletion F) L) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hσ : σ ≠ 1 := by
    intro h
    have h1 : c δ = δ := by rw [← hσc, h]; rfl
    apply hδ
    have : (2 : L) * δ = 0 := by linear_combination hcδ - h1
    exact (mul_eq_zero.1 this).resolve_left h2
  let e : Fin m ⊕ Fin m ≃ Fin (m + m) := finSumFinEquiv
  let Hyp : Matrix (Fin (m + m)) (Fin (m + m)) L :=
    (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).submatrix e.symm e.symm
  let H : Matrix (Fin (m + m)) (Fin (m + m)) L := δ • J
  have hH : ∀ a b, σ (H a b) = H b a := by
    intro a b
    simp only [H, Matrix.smul_apply, smul_eq_mul, hσc, map_mul, hcδ, hJ]
    ring
  have hHyp : ∀ a b, σ (Hyp a b) = Hyp b a := by
    intro a b
    simp only [Hyp, submatrix_apply]
    rcases e.symm a with i | i <;> rcases e.symm b with j | j <;>
      by_cases hij : i = j <;> simp [fromBlocks, one_apply, hij, eq_comm]
  have hdH : H.det = δ ^ (m + m) * J.det := by simp [H, det_smul]
  have hdHyp : Hyp.det = (-1) ^ m := by simp [Hyp, det_submatrix_equiv_self, det_hyp]
  have hs : ((-1 : L) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  obtain ⟨P, hP, hPeq⟩ := (GlobalTheory.HermLocal.congr_iff_adicCompletion F v L σ hσ hH hHyp
    (by rw [hdH]; exact mul_ne_zero (pow_ne_zero _ hδ) hd) (by rw [hdHyp]; simp)).2 ⟨δ ^ m * x, by
      rw [hdH, hdHyp, div_eq_iff (by simp), hx, hσc, map_mul, map_pow, hcδ, neg_pow]
      linear_combination (-(δ ^ (m + m) * x * c x)) * hs⟩
  have hQ : ∀ a b, δ * (Pᵀ * J * P.map c) a b = Hyp a b := by
    intro a b
    rw [hPeq]
    simp only [H, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    rfl
  have hiso : ∀ (f : Fin m → Fin m ⊕ Fin m), (∀ a b, Hyp (e (f a)) (e (f b)) = 0) →
      (P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c = 0 := by
    intro f hf
    ext a b
    have h1 : ((P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c) a b =
        (Pᵀ * J * P.map c) (e (f a)) (e (f b)) := rfl
    rw [h1, Matrix.zero_apply]
    have h3 := hQ (e (f a)) (e (f b))
    rw [hf] at h3
    exact (mul_eq_zero.1 h3).resolve_left hδ
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hcols : fromCols (P.submatrix id (fun j => e (Sum.inl j))) (P.submatrix id (fun j => e (Sum.inr j))) =
      P.submatrix id e := by
    ext i (j | j) <;> rfl
  refine ⟨P.submatrix id (fun j => e (Sum.inl j)), hiso Sum.inl (fun a b => by simp [Hyp]),
    P.submatrix id (fun j => e (Sum.inr j)), P⁻¹.submatrix e id, hiso Sum.inr (fun a b => by simp [Hyp]), ?_, ?_⟩
  · rw [hcols, submatrix_mul_equiv, mul_nonsing_inv P hPu, submatrix_id_id]
  · rw [hcols, show (P⁻¹.submatrix e id) = P⁻¹.submatrix e (Equiv.refl _) from rfl,
      show P.submatrix id e = P.submatrix (Equiv.refl _) e from rfl, submatrix_mul_equiv,
      nonsing_inv_mul P hPu, submatrix_one_equiv]

end GlobalTheory.SkewLagr

namespace GlobalTheory.SkewLagr

open Matrix

theorem exists_isLagr_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F), IsField (Fv F v ⊗[F] E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Even n → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    (∃ x : Fv F v ⊗[F] E, (1 : Fv F v) ⊗ₜ[F] J.det = x * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ x) →
    ∃ Cy : Matrix (Fin n) (Fin (n / 2)) (Fv F v ⊗[F] E),
      IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) J) Cy := by
  intro F E _ _ _ _ _ σ hcm v hF n J hn hJ hd hx
  obtain ⟨m, rfl⟩ := hn
  rw [show (m + m) / 2 = m by omega]
  letI : Field (Fv F v ⊗[F] E) := hF.toField
  haveI : Algebra.IsQuadraticExtension (Fv F v) (Fv F v ⊗[F] E) :=
    { finrank_eq_two' := by rw [Module.finrank_baseChange]; exact hcm.2.2.1 }
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  obtain ⟨t, ht⟩ : ∃ t, σ t ≠ t := by
    by_contra h
    push_neg at h
    have hw := hcm.2.1.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hw
    apply hw
    ext y
    have hy := hcm.2.2.2 τ y
    rw [h] at hy
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [starRingEnd_apply]
    exact hy.symm
  set c := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ with hcdef
  have hct : ∀ y : E, c ((1 : Fv F v) ⊗ₜ[F] y) = (1 : Fv F v) ⊗ₜ[F] σ y := fun y => by
    simp [c, Algebra.TensorProduct.map_tmul]
  have hc : ∀ z, c (c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [c, Algebra.TensorProduct.map_tmul, hσσ]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hinj : Function.Injective (inclR (Fv F v) : E →+* Fv F v ⊗[F] E) := RingHom.injective _
  have hincl : ∀ y : E, inclR (Fv F v) y = (1 : Fv F v) ⊗ₜ[F] y := fun _ => rfl
  have hδ : (1 : Fv F v) ⊗ₜ[F] (t - σ t) ≠ 0 := by
    rw [← hincl]
    exact (map_ne_zero_iff _ hinj).2 (sub_ne_zero.2 (Ne.symm ht))
  have hcδ : c ((1 : Fv F v) ⊗ₜ[F] (t - σ t)) = -((1 : Fv F v) ⊗ₜ[F] (t - σ t)) := by
    rw [hct, map_sub, hσσ, ← TensorProduct.tmul_neg, neg_sub]
  have hdet : (JR (Fv F v) J).det = (1 : Fv F v) ⊗ₜ[F] J.det := by
    rw [← hincl, RingHom.map_det]
    rfl
  refine exists_isLagr_of_local F v c hc hδ hcδ m (JR (Fv F v) J) (fun i j => ?_) ?_ ?_
  · change c (inclR (Fv F v) (J j i)) = -inclR (Fv F v) (J i j)
    rw [hincl, hincl, hct, hJ, TensorProduct.tmul_neg]
  · rw [hdet, ← hincl]
    exact (map_ne_zero_iff _ hinj).2 hd
  · rw [hdet]
    exact hx

end GlobalTheory.SkewLagr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open Formalism.BasicNotions.TH

namespace GlobalTheory.FockQuot

variable (P Q R S : ℕ)

def rel (x : ℚ) : Submodule ℂ (Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Pol P Q R S), g = fockAct1 P Q R S X f - ((x : ℂ) * X.trace) • f}

def act2 (t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S) :=
  fockAct2 P Q R S + (Matrix.traceLinearMap (Ix R S) ℂ ℂ).smulRight ((t : ℂ) • (1 : Module.End ℂ (Pol P Q R S)))

theorem fockSecondActionTraceShift_apply (t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    act2 P Q R S t Y f = fockAct2 P Q R S Y f + ((t : ℂ) * Y.trace) • f := by
  simp [act2, mul_comm, smul_smul]

theorem fockTraceCharacterRelations_le_comap_secondAction (x t : ℚ) (Y : Mat R S) : rel P Q R S x ≤ (rel P Q R S x).comap (act2 P Q R S t Y) := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨X, f, rfl⟩
  have hc : fockAct2 P Q R S Y (fockAct1 P Q R S X f) = fockAct1 P Q R S X (fockAct2 P Q R S Y f) :=
    (LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Y) f).symm
  refine Submodule.subset_span ⟨X, act2 P Q R S t Y f, ?_⟩
  simp only [fockSecondActionTraceShift_apply, map_sub, map_add, map_smul, hc]

theorem isLieAct_fockSecondActionTraceShift (t : ℚ) : IsLieAct (act2 P Q R S t) := by
  intro X Y
  refine LinearMap.ext fun f => ?_
  have h := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.1 X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, fockSecondActionTraceShift_apply, map_add, map_smul, h, Matrix.trace_sub,
    Matrix.trace_mul_comm X Y, sub_self, mul_zero, zero_smul, add_zero]
  module

def actQ (x t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S ⧸ rel P Q R S x) where
  toFun Y := (rel P Q R S x).mapQ (rel P Q R S x) (act2 P Q R S t Y) (fockTraceCharacterRelations_le_comap_secondAction P Q R S x t Y)
  map_add' Y Z := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]
  map_smul' c Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]

theorem actQ_mk (x t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    actQ P Q R S x t Y (Submodule.Quotient.mk f) = Submodule.Quotient.mk (act2 P Q R S t Y f) := rfl

theorem actQ_lie (x t : ℚ) : IsLieAct (actQ P Q R S x t) := by
  intro X Y
  refine LinearMap.ext fun v => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have h := LinearMap.congr_fun (isLieAct_fockSecondActionTraceShift P Q R S t X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h ⊢
  simp only [actQ_mk, h, Submodule.Quotient.mk_sub]

theorem actQ_kfin (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    ∃ W : Submodule ℂ (Pol P Q R S ⧸ rel P Q R S x), FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (actQ P Q R S x t) W := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨W₀, hW₀, hf, hst⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  refine ⟨W₀.map (rel P Q R S x).mkQ, inferInstance, ⟨f, hf, rfl⟩, ?_⟩
  rintro X hX _ ⟨w, hw, rfl⟩
  refine ⟨act2 P Q R S t X w, ?_, rfl⟩
  rw [fockSecondActionTraceShift_apply]
  exact W₀.add_mem (hst X hX w hw) (W₀.smul_mem _ hw)

theorem actQ_wt (x t : ℚ) (μ : Ix R S → ℚ) (g : Pol P Q R S) (hg : g ∈ wtSub (fockAct2 P Q R S) μ) :
    (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈ wtSub (actQ P Q R S x t) (fun a => μ a + t) := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hg ⊢
  intro a
  rw [actQ_mk, fockSecondActionTraceShift_apply, hg a]
  simp [Eab, Matrix.trace_single_eq_same, add_smul]

theorem actQ_wts (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    v ∈ ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hf := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).2
  refine Submodule.iSup_induction (fun μ => wtSub (fockAct2 P Q R S) μ)
    (motive := fun g => (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈
      ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ) hf ?_ ?_ ?_
  · intro μ g hg
    exact Submodule.mem_iSup_of_mem _ (actQ_wt P Q R S x t μ g hg)
  · simp
  · intro g h hg hh
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ hg hh

def gkQ (x t : ℚ) : GKMod R S where
  V := Pol P Q R S ⧸ rel P Q R S x
  act := actQ P Q R S x t
  lie := actQ_lie P Q R S x t
  kfin := actQ_kfin P Q R S x t
  wts := actQ_wts P Q R S x t

theorem mk_fockFirstAction_eq_trace_smul (x : ℚ) (X : Mat P Q) (f : Pol P Q R S) :
    (Submodule.Quotient.mk (fockAct1 P Q R S X f) : Pol P Q R S ⧸ rel P Q R S x) =
      ((x : ℂ) * X.trace) • Submodule.Quotient.mk f := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨X, f, rfl⟩

theorem nontrivial_of_form (x : ℚ) (l : Pol P Q R S →ₗ[ℂ] ℂ) (hl : l ≠ 0)
    (hlX : ∀ X f, l (fockAct1 P Q R S X f) = (x : ℂ) * X.trace * l f) : Nontrivial (Pol P Q R S ⧸ rel P Q R S x) := by
  have hK : rel P Q R S x ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro g ⟨X, f, rfl⟩
    simp [hlX]
  obtain ⟨f, hf⟩ : ∃ f, l f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl (LinearMap.ext fun f => by simpa using h f)
  refine ⟨⟨Submodule.Quotient.mk f, 0, ?_⟩⟩
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  exact fun hm => hf (hK hm)

theorem exists_lift : ∀ (P Q R S : ℕ) (x t : ℚ), GlobalTheory.RealLift.HasForm P Q R S x →
    ∃ (M : Formalism.BasicNotions.TH.GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V),
      GlobalTheory.RealLift.IsLift x t M pr ∧ Nontrivial M.V := by
  intro P Q R S x t ⟨l, hl, hlX⟩
  refine ⟨gkQ P Q R S x t, (rel P Q R S x).mkQ, ⟨Submodule.mkQ_surjective _, ?_, ?_⟩, ?_⟩
  · intro X f
    exact mk_fockFirstAction_eq_trace_smul P Q R S x X f
  · intro Y f
    show actQ P Q R S x t Y (Submodule.Quotient.mk f) = _
    rw [actQ_mk, fockSecondActionTraceShift_apply]
    rfl
  · exact nontrivial_of_form P Q R S x l hl hlX

end GlobalTheory.FockQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneMulCompactOfTwistedNormCompact
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.Tw.NormOneCore

theorem exists_normOne_mul_compact : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) K), GlobalTheory.Tw.Reg δ → ∀ C : Set (GL (Fin n) K), IsCompact C → ∃ D : Set (GL (Fin n) K), IsCompact D ∧ ∀ z : GL (Fin n) K, (z : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} → ∀ u ∈ C, (u : Matrix (Fin n) (Fin n) K) = (z : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (z : Matrix (Fin n) (Fin n) K) → ∃ t : GL (Fin n) K, (t : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} ∧ (t : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (t : Matrix (Fin n) (Fin n) K) = 1 ∧ ∃ d ∈ D, z = t * d := by
  intro K _ _ _ hK n δ hδ C hC
  have hu := hδ.1
  set N := GlobalTheory.Tw.nrm δ with hNdef
  set A := Algebra.adjoin K {N} with hAdef
  letI : CommRing A := Algebra.adjoinCommRingOfComm K (by
    intro a ha b hb; rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb])
  have hA := GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hu
  have hmul := GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hu
  have hsemi := GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ
  have hone := GlobalTheory.Tw.CentralizerAdjoin.adj_one' hu
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) K, GlobalTheory.Tw.adj δ (x + y) = GlobalTheory.Tw.adj δ x + GlobalTheory.Tw.adj δ y :=
    fun x y => by simpa using hsemi 1 x y
  have hzero : GlobalTheory.Tw.adj δ 0 = 0 := by simp [GlobalTheory.Tw.adj]
  let σ : A →+* A :=
    { toFun := fun x => ⟨GlobalTheory.Tw.adj δ x, (hA x x.2).1⟩
      map_one' := Subtype.ext hone
      map_mul' := fun x y => by
        apply Subtype.ext
        change GlobalTheory.Tw.adj δ (x.1 * y.1) = _
        rw [hmul]
        exact congrArg Subtype.val (mul_comm (⟨_, (hA y y.2).1⟩ : A) ⟨_, (hA x x.2).1⟩)
      map_zero' := Subtype.ext hzero
      map_add' := fun x y => Subtype.ext (hadd x.1 y.1) }
  have hσv : ∀ x : A, (σ x : Matrix (Fin n) (Fin n) K) = GlobalTheory.Tw.adj δ x := fun x => rfl
  have hσσ : ∀ x : A, σ (σ x) = x := fun x => Subtype.ext (hA x x.2).2
  haveI : IsReduced A := ⟨fun x ⟨m, hm⟩ => Subtype.ext
    (GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable K n N hδ.2 x x.2 m (by simpa using congrArg Subtype.val hm))⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨e, f, he, hf, hes, hsum, hnull⟩ := GlobalTheory.T.reduced_artinian_involution_idempotent_split A σ hσσ

  have hse : σ e * f = 0 := by
    have h1 : σ e * σ e = σ e := by rw [← map_mul, he.eq]
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination (-1 : A) * h1 + (-1 : A) * hes
  have hef : e * f = 0 := by
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination -he.eq - hes
  have hσf : σ f = f := by
    have h := congrArg σ hsum
    rw [map_add, map_add, hσσ, map_one] at h
    linear_combination h - hsum
  letI : ContinuousStar K := ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, hK]).continuous⟩
  have hqc : Continuous fun w : Matrix (Fin n) (Fin n) K => w * GlobalTheory.Tw.adj δ w := by
    unfold GlobalTheory.Tw.adj
    fun_prop
  have hss : σ e * σ e = σ e := by rw [← map_mul, he.eq]
  let S : Submodule K (Matrix (Fin n) (Fin n) K) :=
    Submodule.map (LinearMap.mulRight K (f : Matrix (Fin n) (Fin n) K)) (Subalgebra.toSubmodule A)
  have hhom : ∀ (c : K) (w : Matrix (Fin n) (Fin n) K),
      (c • w) * GlobalTheory.Tw.adj δ (c • w) = (c * star c) • (w * GlobalTheory.Tw.adj δ w) := by
    intro c w
    have : GlobalTheory.Tw.adj δ (c • w) = star c • GlobalTheory.Tw.adj δ w := by simpa [hzero] using hsemi c w 0
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hnullS : ∀ w ∈ S, w * GlobalTheory.Tw.adj δ w = 0 → w = 0 := by
    intro w hw h0
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hw
    have hx : (⟨a, ha⟩ * f : A) * σ (⟨a, ha⟩ * f) = 0 := Subtype.ext h0
    have h1 := hnull _ hx
    rw [mul_assoc, hf.eq] at h1
    exact congrArg Subtype.val h1
  obtain ⟨B1, hB1, hB1m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * u) '' C)
    (hC.image (continuous_const.mul Units.continuous_val))
  obtain ⟨B2, hB2, hB2m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) '' C)
    (hC.image (continuous_const.mul (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K))))
  let φ : GL (Fin n) K × Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K →
      Matrix (Fin n) (Fin n) K × (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ := fun p =>
    ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * p.1 + p.2.1,
      MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + p.2.2))
  have hφ : Continuous φ :=
    ((continuous_const.add (continuous_const.mul (Units.continuous_val.comp continuous_fst))).add
      (continuous_fst.comp continuous_snd)).prodMk
      (MulOpposite.continuous_op.comp ((continuous_const.add
        (continuous_const.mul ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K)).comp continuous_fst))).add
          (continuous_snd.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (φ '' (C ×ˢ (B1 ×ˢ B2))),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage ((hC.prod (hB1.prod hB2)).image hφ), ?_⟩
  intro z hz u hu' huz
  have hzi : ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ A := by
    rw [Matrix.coe_units_inv]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hz) (GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit z.isUnit)
  set z' : A := ⟨z, hz⟩ with hz'
  set zi : A := ⟨_, hzi⟩ with hzi'
  have hz1 : z' * zi = 1 := Subtype.ext (Units.mul_inv z)
  have hsz1 : σ z' * σ zi = 1 := by rw [← map_mul, hz1, map_one]
  set tA : A := e * z' + σ e * σ zi + f with htA
  set tiA : A := e * zi + σ e * σ z' + f with htiA
  have hprod : tA * tiA = 1 := by
    rw [htA, htiA]
    linear_combination (z' * zi) * he.eq + e * hz1 + (z' * σ z' + σ zi * zi) * hes + (z' + zi) * hef +
      (σ zi * σ z') * hss + σ e * hsz1 + (σ zi + σ z') * hse + hf.eq + hsum
  have hprod' : tiA * tA = 1 := by rw [mul_comm]; exact hprod
  have hσt : σ tA = tiA := by
    rw [htA, htiA]; simp only [map_add, map_mul, hσσ, hσf]; ring
  let t : GL (Fin n) K := ⟨tA, tiA, congrArg Subtype.val hprod, congrArg Subtype.val hprod'⟩
  have hinvu : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * σ zi : A) : Matrix (Fin n) (Fin n) K) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [huz]
    exact congrArg Subtype.val (show (z' * σ z') * (zi * σ zi) = 1 by
      linear_combination (σ z' * σ zi) * hz1 + hsz1)
  refine ⟨t, tA.2, ?_, t⁻¹ * z, ?_, by simp⟩
  · show (tA : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ tA = 1
    rw [← hσv, hσt]; exact congrArg Subtype.val hprod
  refine ⟨(u, (z : Matrix (Fin n) (Fin n) K) * f, ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f),
    ⟨hu', hB1m _ (Submodule.mem_map.mpr ⟨z, hz, rfl⟩) ⟨u, hu', ?_⟩,
      hB2m _ (Submodule.mem_map.mpr ⟨_, hzi, rfl⟩) ⟨u, hu', ?_⟩⟩, ?_⟩
  · show (f : Matrix (Fin n) (Fin n) K) * u = ((z' * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (z' * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [huz]
    exact congrArg Subtype.val (show f * (z' * σ z') = (z' * f) * σ (z' * f) by
      rw [map_mul, hσf]; linear_combination (-(z' * σ z')) * hf.eq)
  · show (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (zi * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [hinvu]
    exact congrArg Subtype.val (show f * (zi * σ zi) = (zi * f) * σ (zi * f) by
      rw [map_mul, hσf]; linear_combination (-(zi * σ zi)) * hf.eq)
  · apply Prod.ext
    · show (e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K) + (z : Matrix (Fin n) (Fin n) K) * f = ((t⁻¹ * z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [huz]
      exact congrArg Subtype.val (show e + σ e * (z' * σ z') + z' * f = tiA * z' by
        rw [htiA]; linear_combination (-e) * hz1)
    · show MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f) = MulOpposite.op (((t⁻¹ * z)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [hinvu, _root_.mul_inv_rev, inv_inv, Units.val_mul]
      exact congrArg MulOpposite.op (congrArg Subtype.val (show e + σ e * (zi * σ zi) + zi * f = zi * tA by
        rw [htA]; linear_combination (-e) * hz1))
end GlobalTheory.Tw.NormOneCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealSubfieldNegativeTwoPlacesNormEverywherStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realSubfield_negative_twoPlaces_normEverywhere : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : M →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (ε a).re < 0 ∧ (ε' a).re < 0 ∧ (∀ φ : M →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  first | (exact @GlobalTheory.NormSign.exists_neg_two_norm_away) | (exact GlobalTheory.NormSign.exists_neg_two_norm_away) | (intros; apply GlobalTheory.NormSign.exists_neg_two_norm_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictedProductHaarGivenFiniteFactorsStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → (∃ μa, IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) ∧ ∃ ν, IsFinMeas V μf ν := by
  first | exact @GlobalTheory.ProdMeas.exists_prod_of_haar | exact GlobalTheory.ProdMeas.exists_prod_of_haar | (intros; apply GlobalTheory.ProdMeas.exists_prod_of_haar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRightInvOfSpan
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem exists_rightInv_of_span {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  refine GlobalTheory.ZeroCycleHt.exists_rightInv fun v => ?_
  have hv : v ∈ Submodule.span F (Set.range w.col) := hw ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
  refine ⟨c, ?_⟩
  rw [← hc]
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem htMul : HtMul := by
  intro F _ _ B N n w A Λ hL
  obtain ⟨P, hP⟩ := exists_rightInv_of_span hL.spans
  refine ⟨fun a a' G G' hG hG' ha ha' => ?_, fun c hc => ?_⟩
  · exact GlobalTheory.ZeroCycleHt.formHeight_mul 0 0 hP hL.det hG hG' ha ha'
  · have h1 : IsMultiHomogeneous (fun _ : Fin B => 0) (1 : MvPolynomial (Fin B × Fin N) F) := by
      intro t ht b
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at ht
      split_ifs at ht with h
      · subst h; simp
      · exact absurd rfl ht
    have := GlobalTheory.HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det one_ne_zero h1 hc
    rw [mul_one, GlobalTheory.ZeroCycleHt.formHeight_one] at this
    exact this

end GlobalTheory.HSShort
end
end

