import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHomFrameConjugationAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame.HomW

section Idem

variable {R L : Type} [CommRing R] [Field L] {n : ℕ} (ι : L →+ R) (hm : ∀ x y, ι (x * y) = ι x * ι y)
include hm

theorem map_mul_map (X Y : Matrix (Fin n) (Fin n) L) : X.map ι * Y.map ι = (X * Y).map ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hm]

theorem e_mul (t : L) : ι 1 * ι t = ι t := by rw [← hm, one_mul]

theorem f_mul (t : L) : (1 - ι 1) * ι t = 0 := by rw [sub_mul, one_mul, e_mul ι hm, sub_self]

theorem ff : (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
  have := e_mul ι hm 1
  linear_combination this

theorem ef : ι 1 * (1 - ι 1) = 0 := by
  have := e_mul ι hm 1
  linear_combination -this

theorem f_smul_map (X : Matrix (Fin n) (Fin n) L) : (1 - ι 1) • X.map ι = 0 := by
  ext i j
  simp [Matrix.smul_apply, f_mul ι hm]

theorem f_smul_mul_map (Y : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin n) L) :
    (1 - ι 1) • (Y * X.map ι) = 0 := by
  rw [← Matrix.mul_smul, f_smul_map ι hm, Matrix.mul_zero]

theorem f_smul_map_mul (Y : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin n) L) :
    (1 - ι 1) • (X.map ι * Y) = 0 := by
  rw [← Matrix.smul_mul, f_smul_map ι hm, Matrix.zero_mul]

theorem map_one' : (1 : Matrix (Fin n) (Fin n) L).map ι = ι 1 • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

def Mm (K : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) R := (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) R) + K.map ι

omit hm in
theorem Mm_def (K : Matrix (Fin n) (Fin n) L) : Mm ι K = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) R) + K.map ι := rfl

theorem Mm_mul (K K' : Matrix (Fin n) (Fin n) L) : Mm ι K * Mm ι K' = Mm ι (K * K') := by
  simp only [Mm_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ff ι hm,
    Matrix.one_mul, Matrix.mul_one, f_smul_map ι hm, map_mul_map ι hm, add_zero, zero_add]

theorem Mm_one : Mm ι (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  rw [Mm_def, map_one' ι hm, ← add_smul, sub_add_cancel, one_smul]

theorem sandwich (Y : Matrix (Fin n) (Fin n) R) (K1 K2 K3 : Matrix (Fin n) (Fin n) L) :
    Mm ι K1 * ((1 - ι 1) • Y + K2.map ι) * Mm ι K3 = (1 - ι 1) • Y + (K1 * K2 * K3).map ι := by
  simp only [Mm_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ff ι hm,
    Matrix.one_mul, Matrix.mul_one, f_smul_map ι hm, map_mul_map ι hm, f_smul_mul_map ι hm, f_smul_map_mul ι hm,
    add_zero, zero_add]

def toGL : GL (Fin n) L →* GL (Fin n) R where
  toFun g := ⟨Mm ι (g : Matrix (Fin n) (Fin n) L), Mm ι ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    by rw [Mm_mul ι hm, Units.mul_inv, Mm_one ι hm], by rw [Mm_mul ι hm, Units.inv_mul, Mm_one ι hm]⟩
  map_one' := Units.ext (by show Mm ι ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1; rw [Units.val_one, Mm_one ι hm])
  map_mul' g g' := Units.ext (by
    show Mm ι ((g * g' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Mm ι (g : Matrix (Fin n) (Fin n) L) * Mm ι (g' : Matrix (Fin n) (Fin n) L)
    rw [Units.val_mul, Mm_mul ι hm])

omit hm in
theorem Mm_transpose (K : Matrix (Fin n) (Fin n) L) : (Mm ι K)ᵀ = Mm ι Kᵀ := by
  simp only [Mm_def, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_map]

end Idem

section Core

variable {L : Type} [Field L] {n : ℕ}

theorem unit_core (σL : L →+* L) (δ : L) (hδ : δ ≠ 0) (T : Matrix (Fin n) (Fin n) L) (P : GL (Fin n) L)
    (JT h : Matrix (Fin n) (Fin n) L)
    (hJT : JT = -δ⁻¹ • ((P : Matrix (Fin n) (Fin n) L)ᵀ * T * (P : Matrix (Fin n) (Fin n) L).map σL)ᵀ)
    (hh : (h.map σL)ᵀ * JT * h = JT) :
    ((P : Matrix (Fin n) (Fin n) L) * h * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))ᵀ * T *
      ((P : Matrix (Fin n) (Fin n) L) * h * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map σL = T := by
  set Pm : Matrix (Fin n) (Fin n) L := (P : Matrix (Fin n) (Fin n) L)
  set Pi : Matrix (Fin n) (Fin n) L := ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  set G := Pmᵀ * T * Pm.map σL with hGdef
  have hPP : Pm * Pi = 1 := Units.mul_inv P
  have h1 : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have h2 : Pm.map σL * Pi.map σL = 1 := by rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σL) (map_one σL)]
  have hGt : (h.map σL)ᵀ * Gᵀ * h = Gᵀ := by
    rw [hJT, Matrix.mul_smul, Matrix.smul_mul] at hh
    have := congrArg (fun M : Matrix (Fin n) (Fin n) L => (-δ) • M) hh
    simpa only [smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ, one_smul] using this
  have hG : hᵀ * G * h.map σL = G := by
    have := congrArg Matrix.transpose hGt
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at this
    exact this
  calc (Pm * h * Pi)ᵀ * T * (Pm * h * Pi).map σL
      = Piᵀ * (hᵀ * (Pmᵀ * T * Pm.map σL) * h.map σL) * Pi.map σL := by
        simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = Piᵀ * (Pmᵀ * T * Pm.map σL) * Pi.map σL := by rw [← hGdef, hG]
    _ = (Piᵀ * Pmᵀ) * T * (Pm.map σL * Pi.map σL) := by simp only [Matrix.mul_assoc]
    _ = T := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end Core

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L] {n : ℕ}

theorem e_smul_incM (v : Pl F) (ι : L →+ AE F E) (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (J : Matrix (Fin n) (Fin n) E) : ι 1 • incM F J = (tJ ι J).map ι := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, incM, tJ, smul_eq_mul]
  rw [pre_spec]
  apply (hAt _).1
  intro u hu
  have h1 : u • ι 1 = 0 := (hAt (ι 1)).2 ⟨1, rfl⟩ u hu
  rw [← smul_mul_assoc, h1, zero_mul]

theorem incM_split (v : Pl F) (ι : L →+ AE F E) (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (J : Matrix (Fin n) (Fin n) E) : incM F J = (1 - ι 1) • incM F J + (tJ ι J).map ι := by
  rw [← e_smul_incM v ι hAt, ← add_smul, sub_add_cancel, one_smul]

theorem Mm_cA (σ : E →ₐ[F] E) (σL : L →+* L) (ι : L →+ AE F E) (hσ : ∀ x, ι (σL x) = cA σ (ι x))
    (K : Matrix (Fin n) (Fin n) L) : (Mm ι K).map (cA σ) = Mm ι (K.map σL) := by
  have he : cA σ (ι 1) = ι 1 := by rw [← hσ, map_one]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Mm_def, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_sub, he, hσ]
  · simp [Mm_def, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, hσ]

end Adelic

theorem homW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] (σL : L →+* L) (δ : L)
    (ι : L →+ AE F E), δ ≠ 0 → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      ∀ (P JT : GL (Fin n) L), (JT : Matrix (Fin n) (Fin n) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι P X.J)ᵀ →
      ∃ iW : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* UA σ X.J, ∀ h,
        mat (iW h) = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) +
          ((P : Matrix (Fin n) (Fin n) L) * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι := by
  intro F E _ _ _ _ _ σ v n X L _ σL δ ι hδ hAt hm hσ P JT hJT
  let φ : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* GL (Fin n) L :=
    (MulAut.conj P).toMonoidHom.comp (Subgroup.subtype _)
  have hφ : ∀ h, ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (P : Matrix (Fin n) (Fin n) L) *
      ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro h
    simp [φ, MulAut.conj_apply, Units.val_mul]
  have hmem : ∀ h, (toGL ι hm).comp φ h ∈ UG (cA σ) (incM F X.J) := by
    intro h
    have hh : (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JT : Matrix (Fin n) (Fin n) L) *
        ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n) (Fin n) L) := h.2
    show (Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))ᵀ * incM F X.J *
      (Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map (cA σ) = incM F X.J
    rw [Mm_transpose, Mm_cA σ σL ι hσ]
    conv_lhs => rw [incM_split v ι hAt X.J]
    rw [sandwich ι hm, hφ, unit_core σL δ hδ (tJ ι X.J) P JT _ hJT hh, ← incM_split v ι hAt X.J]
  refine ⟨((toGL ι hm).comp φ).codRestrict _ hmem, fun h => ?_⟩
  show Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = _
  rw [hφ, Mm_def]

end GlobalTheory.InertLocFrame.HomW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEi
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.FinEig

open Polynomial

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem fd_inf_ker_mul (N : Submodule ℂ M) (f g : Module.End ℂ M) (hf : ∀ v ∈ N, f v ∈ N)
    (h1 : FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker f)) (h2 : FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker g)) :
    FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (g * f)) := by
  rw [← Submodule.fg_iff_finiteDimensional]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker f
  · have hle : (N ⊓ LinearMap.ker (g * f)).map f ≤ N ⊓ LinearMap.ker g := by
      rintro _ ⟨v, ⟨hvN, hv⟩, rfl⟩
      exact ⟨hf v hvN, by simpa [LinearMap.mem_ker] using hv⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  · have hle : N ⊓ LinearMap.ker (g * f) ⊓ LinearMap.ker f ≤ N ⊓ LinearMap.ker f :=
      fun v hv => ⟨hv.1.1, hv.2⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance

theorem adjoin_preserves (N : Submodule ℂ M) (s : Set (Module.End ℂ M)) (hs : ∀ u ∈ s, ∀ v ∈ N, u v ∈ N)
    {b : Module.End ℂ M} (hb : b ∈ Algebra.adjoin ℂ s) : ∀ v ∈ N, b v ∈ N := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r => intro v hv; simpa [Module.algebraMap_end_apply] using N.smul_mem r hv
  | add x y _ _ hx hy => intro v hv; exact N.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy => intro v hv; exact hx _ (hy v hv)

theorem fd_inf_ker_aeval (N : Submodule ℂ M) (t : Module.End ℂ M) (ht : ∀ v ∈ N, t v ∈ N)
    (h : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ))) :
    ∀ n : ℕ, ∀ q : ℂ[X], q.natDegree = n → q ≠ 0 → FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (aeval t q)) := by
  intro n
  induction n with
  | zero =>
    intro q hq hq0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hq] at hq0 ⊢
    have ha : q.coeff 0 ≠ 0 := fun e => hq0 (by rw [e, map_zero])
    have hle : N ⊓ LinearMap.ker (aeval t (C (q.coeff 0))) ≤ ⊥ := by
      intro v hv
      have h2 := hv.2
      simp only [LinearMap.mem_ker, aeval_C, Module.algebraMap_end_apply] at h2
      simpa [Submodule.mem_bot] using (smul_eq_zero.1 h2).resolve_left ha
    exact Submodule.finiteDimensional_of_le hle
  | succ n ih =>
    intro q hq hq0
    have hdeg : 0 < q.degree := by
      rw [Polynomial.degree_eq_natDegree hq0, hq]; exact_mod_cast Nat.succ_pos n
    obtain ⟨μ, hμ⟩ := Complex.exists_root hdeg
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot (a := μ) (p := q)).2 hμ
    set q' := q /ₘ (X - C μ) with hq'
    have hq'0 : q' ≠ 0 := by
      intro e; apply hq0; rw [← hfac, e, mul_zero]
    have hq'deg : q'.natDegree = n := by
      rw [hq', Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C μ), hq, Polynomial.natDegree_X_sub_C]; rfl
    have hmul : aeval t q = (t - algebraMap ℂ (Module.End ℂ M) μ) * aeval t q' := by
      conv_lhs => rw [← hfac]
      simp [map_mul, map_sub, aeval_X, aeval_C]
    rw [hmul]
    apply fd_inf_ker_mul N _ _ _ (ih q' hq'deg hq'0) (h μ)
    exact adjoin_preserves N {t} (by simpa using ht) (Polynomial.aeval_mem_adjoin_singleton ℂ t)

theorem fd_of_finset (T : Finset (Module.End ℂ M)) (hc : ∀ u ∈ T, ∀ w ∈ T, u * w = w * u)
    (ha : ∀ u ∈ T, ∃ q : ℂ[X], q ≠ 0 ∧ aeval u q = 0) :
    ∀ N : Submodule ℂ M, (∀ u ∈ T, ∀ v ∈ N, u v ∈ N) →
      (∀ c : Module.End ℂ M → ℂ,
        FiniteDimensional ℂ ↥(N ⊓ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u)))) →
      FiniteDimensional ℂ ↥N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro N _ h
    haveI := h 0
    refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ (∅ : Finset (Module.End ℂ M)),
      LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) ((0 : Module.End ℂ M → ℂ) u))) ?_
    intro v hv
    refine ⟨hv, ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_iInf]
    intro u
    rw [Submodule.mem_iInf]
    intro hu
    simp at hu
  | insert t T htT ih =>
    intro N hN h
    obtain ⟨q, hq0, hq⟩ := ha t (Finset.mem_insert_self t T)
    have key : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ)) := by
      intro μ
      apply ih (fun u hu w hw => hc u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw))
        (fun u hu => ha u (Finset.mem_insert_of_mem hu))
      · intro u hu v hv
        refine ⟨hN u (Finset.mem_insert_of_mem hu) v hv.1, ?_⟩
        have h2 : (t - algebraMap ℂ (Module.End ℂ M) μ) v = 0 := hv.2
        have hcom := hc t (Finset.mem_insert_self t T) u (Finset.mem_insert_of_mem hu)
        show (t - algebraMap ℂ (Module.End ℂ M) μ) (u v) = 0
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply] at h2 ⊢
        rw [← Module.End.mul_apply, hcom, Module.End.mul_apply, ← map_smul, ← map_sub, h2, map_zero]
      · intro c
        haveI := h (Function.update c t μ)
        refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ insert t T,
          LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (Function.update c t μ u))) ?_
        intro v hv
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
        obtain ⟨⟨hvN, hvt⟩, hvT⟩ := hv
        refine ⟨hvN, fun u hu => ?_⟩
        rcases Finset.mem_insert.1 hu with rfl | hu'
        · simpa using hvt
        · have hne : u ≠ t := fun e => htT (e ▸ hu')
          rw [Function.update_of_ne hne]
          exact hvT u hu'
    have := fd_inf_ker_aeval N t (hN t (Finset.mem_insert_self t T)) key _ q rfl hq0
    rwa [hq, LinearMap.ker_zero, inf_top_eq] at this

end GlobalTheory.FinEig

namespace GlobalTheory.AutGrowth

theorem finiteDimensional_of_commuting_finite_eigen :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) →
      FiniteDimensional ℂ (Algebra.adjoin ℂ S) →
      (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) →
      FiniteDimensional ℂ M := by
  intro M _ _ S hS hB hE
  classical
  letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hS
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ S, ∀ y ∈ Algebra.adjoin ℂ S, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Algebra.adjoin ℂ S) ⟨y, hy⟩)
  obtain ⟨T, hT⟩ : (Algebra.adjoin ℂ S).FG :=
    Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hB)
  have hTA : ∀ u ∈ T, u ∈ Algebra.adjoin ℂ S := fun u hu => hT ▸ Algebra.subset_adjoin hu
  have key := GlobalTheory.FinEig.fd_of_finset T (fun u hu w hw => hcomm u (hTA u hu) w (hTA w hw))
    (fun u hu => ((IsIntegral.of_finite ℂ (⟨u, hTA u hu⟩ : Algebra.adjoin ℂ S)).map
      (Algebra.adjoin ℂ S).val).isAlgebraic) ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_
  · exact Module.Finite.equiv Submodule.topEquiv
  intro c
  have scal : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ v ∈ (⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u))), b v = μ • v := by
    intro b hb
    rw [← hT] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      refine ⟨c x, fun v hv => ?_⟩
      rw [Submodule.mem_iInf] at hv
      have h3 := hv x
      rw [Submodule.mem_iInf] at h3
      have h4 := h3 hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h4
      exact h4
    | algebraMap r => exact ⟨r, fun v _ => by simp [Module.algebraMap_end_apply]⟩
    | add x y _ _ hx hy =>
      obtain ⟨μ₁, h₁⟩ := hx; obtain ⟨μ₂, h₂⟩ := hy
      exact ⟨μ₁ + μ₂, fun v hv => by rw [LinearMap.add_apply, h₁ v hv, h₂ v hv, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨μ₁, h₁⟩ := hx; obtain ⟨μ₂, h₂⟩ := hy
      exact ⟨μ₁ * μ₂, fun v hv => by
        rw [Module.End.mul_apply, h₂ v hv, map_smul, h₁ v hv, smul_smul, mul_comm]⟩
  let c' : Module.End ℂ M → ℂ := fun s => if h : s ∈ Algebra.adjoin ℂ S then Classical.choose (scal s h) else 0
  haveI := hE c'
  refine Submodule.finiteDimensional_of_le
    (S₂ := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c' s))) ?_
  intro v hv
  replace hv := hv.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]
  intro s hs
  have hsA : s ∈ Algebra.adjoin ℂ S := Algebra.subset_adjoin hs
  simp only [c', dif_pos hsA]
  exact Classical.choose_spec (scal s hsA) v hv

end GlobalTheory.AutGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumPiTensorHeisenbergFactorwiseSignature
section
noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD

namespace GlobalTheory.FockVacD

theorem sumPl_heisOp_vacuum_dep {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))
        (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun w : ι => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))
        (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [GlobalTheory.FockVac.atPl_tprod, GlobalTheory.FockVac.atPl_tprod, GlobalTheory.FockVac.heisOp_one,
    MultilinearMap.map_update_smul]

end GlobalTheory.FockVacD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoordinatesActionOfIdentityOffPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem frame_mul_map (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) L) (Y : Matrix (Fin m) (Fin k) L) :
    ((1 - ι 1) • (1 : Matrix (Fin m) (Fin m) (AE F E)) + A.map ι) * Y.map ι = (A * Y).map ι := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
    zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, hmul]

theorem map_mul_frame_transpose (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (C : Matrix (Fin k) (Fin k) L) (Y : Matrix (Fin m) (Fin k) L) :
    Y.map ι * ((1 - ι 1) • (1 : Matrix (Fin k) (Fin k) (AE F E)) + C.map ι)ᵀ = (Y * Cᵀ).map ι := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
    zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, Matrix.transpose_apply, hmul]

theorem actAB_xm_frame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
    (g : UA σ X.J) (h : UA σ W.J)
    (hg : mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + A.map ι)
    (hh : mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (AE F E)) + C.map ι) (x : Matrix (Fin d) (Fin n) L) :
    actAB (cA σ) (g, h) (xm ι PV PW x) =
      (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι := by
  change mat g * xm ι PV PW x * (mat h)ᵀ = _
  rw [xm_apply, hg, hh, frame_mul_map ι hmul, map_mul_frame_transpose ι hmul]
  simp only [Matrix.mul_assoc]

example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ AE F E), (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
        (g : UA σ X.J) (h : UA σ W.J),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + A.map ι →
        mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (AE F E)) + C.map ι →
        ∀ x, actAB (cA σ) (g, h) (GlobalTheory.InertLocFrame.xm ι PV PW x) =
          (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι :=
  actAB_xm_frame

end GlobalTheory.InertLocFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionRankLowerBoundOfHilbertSamuel
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore.RankBound

theorem topologicalKrullDim_le_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp k) (D : ℕ)
    (h : SmoothOfRelativeDimension D p) : topologicalKrullDim Y ≤ D := by
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x)
  replace hU : IsAffineOpen (X := Y) U := hU
  refine ⟨U, U.isOpen, hx, le_of_eq ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, U))).trans
    (SmoothDim.ringKrullDim_affineOpen k _ p _ h U hU ⟨x, hx⟩)

theorem rankLow : Quoted → RankLow := by
  intro Q F _ _ G hnef hbig T
  have hV := G.geom.alg.variety
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · rw [Nat.zero_sub, Nat.choose_eq_zero_of_lt hV.one_le, Nat.cast_zero, zero_mul]
    exact Int.natCast_nonneg _
  have hstr : strHom F G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F G.Y) := hstr ▸ hV.proj
  have hdim := topologicalKrullDim_le_of_smooth G.str G.D hV.smooth
  have hM : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  let e : twist (GlobalTheory.structureModule G.Y) (tens G.K.bundle G.LA) ≅ LB.toMod (tens G.K.bundle G.LA) :=
    Twist.unitTwistIso _
  have hq := Twist.isFiniteQC_twist (F := GlobalTheory.structureModule G.Y) hM
  have hvan : VanishFrom G.L (twist (GlobalTheory.structureModule G.Y) (tens G.K.bundle G.LA)) 1 := fun j hj q hq =>
    (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q ((twistFunctor (lbZPow G.L j)).mapIso e)).toEquiv.subsingleton_congr.2
      (GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist Q F G hnef hbig j (by omega) q hq)
  have key := GlobalTheory.T.choose_mul_intersectionNumber_le_sectionDim F G.Y hproj G.L G.isLB G.N G.b
    (fun y => TopologicalSpace.Opens.mem_iSup.1 (G.geom.alg.bpf.ge (Set.mem_univ y))) G.D _
    ((suppDim_le _).trans hdim) 1 hvan (T - 1)
  rw [(diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom F G.Y) (GlobalTheory.structureModule G.Y) hproj
    ((suppDim_le _).trans hdim)).interNum_twist (by simp) (fun _ => G.isLB) hM] at key
  have hT' : (1 : ℤ) + ((T - 1 : ℕ) : ℤ) = T := by omega
  rw [hT'] at key
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule G.Y) hM (Twist.isLB_lbZPow G.isLB T)
    (G.isLB_adj T) rfl
  rw [G.finrank_global, lbH0, ← hdim_congr F 0 i]
  exact key

end GlobalTheory.HSCore.RankBound
end

