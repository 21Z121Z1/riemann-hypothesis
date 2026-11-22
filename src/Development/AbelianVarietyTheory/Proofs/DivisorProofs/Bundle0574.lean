import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Formalism.LocalToGlobal.Columns.PolyFn

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionQuotientKerEq
section
open Ideal WittVector

namespace GlobalTheory.PadicComplQuot

theorem mem_map_iff_evalOne {A : Type} [CommRing A] (I : Ideal A) (hI : I.FG) (x : AdicCompletion I A) :
    x ∈ I.map (algebraMap A (AdicCompletion I A)) ↔ AdicCompletion.evalOneₐ I x = 0 := by
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hI, RingHom.mem_ker]
  rfl

theorem quot_completion (p : ℕ) (A : Type) [CommRing A] (_hp : IsSMulRegular A (p : A)) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp
        (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) ∧
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp
        (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) = Ideal.span {(p : A)} := by
  set I : Ideal A := Ideal.span {(p : A)} with hIdef
  have hfg : I.FG := Submodule.fg_span_singleton _
  have hspan : Ideal.span {(p : AdicCompletion I A)} = I.map (algebraMap A (AdicCompletion I A)) := by
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  have hcomm : ∀ a : A, AdicCompletion.evalOneₐ I (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk I a :=
    fun a => (AdicCompletion.evalOneₐ I).commutes a
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I r)
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hspan, mem_map_iff_evalOne I hfg, map_sub, hcomm, ha, sub_self]
  · ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, mem_map_iff_evalOne I hfg, hcomm,
      Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.PadicComplQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfCoefficientPsiProperty
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section

namespace GlobalTheory.LemYR

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def phiT : RL p O Λ →+* RL p O Λ :=
  (Algebra.TensorProduct.map (PsiPhi.frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom

theorem phiT_tmul (a : Ainf p O) (l : Λ) : phiT (a ⊗ₜ l) = WittVector.frobenius a ⊗ₜ l := rfl

theorem phiT_psi {ψ : RL p O Λ →+* RL p O Λ} (hψ : IsPsi ψ) (r : RL p O Λ) : phiT (ψ r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [hψ, phiT_tmul, PsiPhi.frobenius_phiInv']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem phiT_inA (a : Ainf p O) : phiT (inA a : RL p O Λ) = inA (WittVector.frobenius a) := by
  show phiT (a ⊗ₜ 1) = WittVector.frobenius a ⊗ₜ 1
  rfl

theorem repr_phiT {ι : Type} (b : Module.Basis ι ℤ_[p] Λ) (r : RL p O Λ) (i : ι) :
    (Algebra.TensorProduct.basis (Ainf p O) b).repr (phiT r) i =
      WittVector.frobenius ((Algebra.TensorProduct.basis (Ainf p O) b).repr r i) := by
  have hc : ∀ c : ℤ_[p], WittVector.frobenius (algebraMap ℤ_[p] (Ainf p O) c) =
      algebraMap ℤ_[p] (Ainf p O) c := PsiPhi.frobenius_ofPadic
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [phiT_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, hc]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end GlobalTheory.LemYR

open GlobalTheory.LemYR in

theorem GlobalTheory.LemYR.lemY_tensor : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ m : Ainf p O, m.coeff 0 ≠ 0 → ∀ z w : RL p O Λ, z * ψ (inA m) = inA m * w * ψ z → (inA m : RL p O Λ) ∣ z := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ ψ hψ m hm z w hzw
  obtain ⟨hD, hV⟩ := GlobalTheory.TiltValuation.tilt_isDomain_valuationRing p C v O hv
  haveI : Module.IsTorsionFree ℤ_[p] Λ := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  set b := Module.finBasis ℤ_[p] Λ
  set B := Algebra.TensorProduct.basis (Ainf p O) b
  have h1 : phiT z * inA m = inA (WittVector.frobenius m) * phiT w * z := by
    have := congrArg phiT hzw
    simpa only [map_mul, phiT_psi hψ, phiT_inA] using this
  have hA : ∀ (a : Ainf p O) (r : RL p O Λ) i, B.repr (inA a * r) i = a * B.repr r i := by
    intro a r i
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have key : ∀ i, m * WittVector.frobenius (B.repr z i) =
      WittVector.frobenius m * (Algebra.leftMulMatrix B (phiT w) *ᵥ fun j => B.repr z j) i := by
    intro i
    have := congrArg (fun r => B.repr r i) h1
    rw [mul_comm, hA, repr_phiT, mul_assoc, hA] at this
    rw [this]
    congr 1
    exact congrFun (Algebra.leftMulMatrix_mulVec_repr B (phiT w) z) i |>.symm
  have hdiv := GlobalTheory.T.frobenius_twisted_divisibility p (PreTilt O p) (Module.finrank ℤ_[p] Λ) m
    (Algebra.leftMulMatrix B (phiT w)) (fun j => B.repr z j) hm key
  choose c hc using hdiv
  refine ⟨∑ i, c i • B i, ?_⟩
  conv_lhs => rw [← B.sum_repr z]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, Algebra.smul_def (m : Ainf p O) (c i • B i)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomExtLocalization
section
open IsLocalRing

namespace GlobalTheory.IndEtaleHensel

theorem algHom_ext_localization {R A P : Type} [CommRing R] [CommRing A] [CommRing P]
    [Algebra R A] [Algebra R P] (q : Ideal A) [q.IsPrime]
    (φ₁ φ₂ : Localization.AtPrime q →ₐ[R] P)
    (h : φ₁.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)) =
      φ₂.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))) : φ₁ = φ₂ := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext q.primeCompl
  exact RingHom.ext fun a => DFunLike.congr_fun h a

theorem bijective_of_algEquiv {R X Y T : Type} [CommRing R] [CommRing X] [CommRing Y] [CommRing T]
    [Algebra R X] [Algebra R Y] [Algebra R T] [IsLocalRing T] (e : X ≃ₐ[R] Y)
    (h : Function.Bijective
      (fun φ : X →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective
      (fun φ : Y →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  constructor
  · intro φ₁ φ₂ hφ
    have hc : φ₁.comp (e : X →ₐ[R] Y) = φ₂.comp (e : X →ₐ[R] Y) := by
      apply h.1
      simp only at hφ ⊢
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
    ext y
    have := DFunLike.congr_fun hc (e.symm y)
    simpa using this
  · intro ψ
    obtain ⟨φ, hφ⟩ := h.2 (ψ.comp (e : X →ₐ[R] Y))
    refine ⟨φ.comp (e.symm : Y →ₐ[R] X), ?_⟩
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, hφ]
    ext y; simp

theorem bijective_localization {R A T : Type} [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T] [IsLocalRing T] (q : Ideal A) [q.IsPrime]
    (hA : Function.Bijective
      (fun φ : A →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ)) :
    Function.Bijective (fun φ : Localization.AtPrime q →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  set π := IsScalarTower.toAlgHom R T (ResidueField T)
  set ι := IsScalarTower.toAlgHom R A (Localization.AtPrime q)
  constructor
  · intro φ₁ φ₂ hφ
    apply algHom_ext_localization q
    apply hA.1
    simp only at hφ ⊢
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hφ]
  · intro ψ
    obtain ⟨φ, hφ⟩ := hA.2 (ψ.comp ι)
    simp only at hφ
    have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
      intro y
      have h1 : IsUnit (ψ (algebraMap A (Localization.AtPrime q) y)) :=
        (IsLocalization.map_units (Localization.AtPrime q) y).map ψ
      have h2 : π (φ y) = ψ (algebraMap A (Localization.AtPrime q) y) := DFunLike.congr_fun hφ (y : A)
      rw [← h2] at h1
      have h3 : π (φ y) = residue T (φ y) := by
        simp [π, IsScalarTower.toAlgHom_apply, ResidueField.algebraMap_eq]
      rw [h3] at h1
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp h1.ne_zero
    refine ⟨IsLocalization.liftAlgHom (M := q.primeCompl) (S := Localization.AtPrime q) hu, ?_⟩
    apply algHom_ext_localization q
    ext a
    have := DFunLike.congr_fun hφ a
    simp only [AlgHom.comp_apply] at this ⊢
    rw [← this]
    congr 1
    simp [ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

theorem bijective_residue_comp : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [HenselianLocalRing T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → Function.Bijective (fun φ : S →ₐ[R] T => (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
  intro R S T _ _ _ _ _ _ hS
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := hS
  have hbij : ∀ i, Function.Bijective (fun φ : Si i →ₐ[R] T =>
      (IsScalarTower.toAlgHom R T (ResidueField T)).comp φ) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    exact bijective_of_algEquiv e (bijective_localization q (GlobalTheory.T.bijective_residue_comp_etale_henselian R A T))
  have dir : Directed (· ≤ ·) Si := hmono.directed_le
  have htop : (⊤ : Subalgebra R S) ≤ iSup Si := fun s _ => by
    obtain ⟨i, hi⟩ := hcov s
    exact le_iSup Si i hi
  constructor
  · intro φ₁ φ₂ h
    simp only at h
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have hc : φ₁.comp (Si i).val = φ₂.comp (Si i).val := by
      apply (hbij i).1
      simp only
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, h]
    exact DFunLike.congr_fun hc ⟨s, hi⟩
  · intro ψ
    choose f hf using fun i => (hbij i).2 (ψ.comp (Si i).val)
    simp only at hf
    have compat : ∀ i j (h : Si i ≤ Si j), f i = (f j).comp (Subalgebra.inclusion h) := by
      intro i j h
      apply (hbij i).1
      simp only
      rw [hf i, ← AlgHom.comp_assoc, hf j]
      ext x; rfl
    refine ⟨(Subalgebra.iSupLift Si dir f compat ⊤ htop).comp
      (Subalgebra.topEquiv.symm : S ≃ₐ[R] (⊤ : Subalgebra R S)).toAlgHom, ?_⟩
    ext s
    obtain ⟨i, hi⟩ := hcov s
    have h1 := DFunLike.congr_fun (hf i) ⟨s, hi⟩
    simp only [AlgHom.comp_apply] at h1 ⊢
    refine Eq.trans ?_ h1
    congr 1
    exact Subalgebra.iSupLift_of_mem (K := Si) (dir := dir) (f := f) (hf := compat)
      (T := ⊤) (hT := htop) ⟨s, trivial⟩ hi

end GlobalTheory.IndEtaleHensel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocal
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.AzumayaLocal

theorem mem_left {A Λ : Type} [CommRing A] [Ring Λ] [Algebra A Λ] {I : Ideal A} (w : Λ) {z : Λ}
    (hz : z ∈ I • (⊤ : Submodule A Λ)) : w * z ∈ I • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun a ha t _ => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]; exact Submodule.smul_mem_smul ha trivial
  · rw [mul_add]; exact Submodule.add_mem _ hx hy

theorem mem_right {A Λ : Type} [CommRing A] [Ring Λ] [Algebra A Λ] {I : Ideal A} (w : Λ) {z : Λ}
    (hz : z ∈ I • (⊤ : Submodule A Λ)) : z * w ∈ I • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun a ha t _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_mul_assoc]; exact Submodule.smul_mem_smul ha trivial
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

end GlobalTheory.AzumayaLocal

theorem GlobalTheory.AzumayaLocal.finite_residueField : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], Finite (IsLocalRing.ResidueField A) := by
  intro ℓ _ A _ _ _ _
  have hmax : (maximalIdeal A).comap (algebraMap ℤ_[ℓ] A) = maximalIdeal ℤ_[ℓ] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal A))
  haveI : IsLocalHom (algebraMap ℤ_[ℓ] A) := ⟨fun x hx => by
    by_contra h
    have : x ∈ (maximalIdeal A).comap (algebraMap ℤ_[ℓ] A) := by rw [hmax]; exact h
    exact (mem_maximalIdeal _).1 this hx⟩
  have : Finite (IsLocalRing.ResidueField ℤ_[ℓ]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[ℓ])

theorem GlobalTheory.AzumayaLocal.exists_right_inverse : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Finite A Λ] (u : Λ), u - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) → ∃ v : Λ, u * v = 1 := by
  intro A _ _ Λ _ _ _ u hu
  let f : Λ →ₗ[A] Λ := LinearMap.mulLeft A u
  have hle : (⊤ : Submodule A Λ) ≤ LinearMap.range f ⊔ (maximalIdeal A) • (⊤ : Submodule A Λ) := by
    intro y _
    have hy : y = u * y - (u - 1) * y := by noncomm_ring
    rw [hy]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
      (Submodule.mem_sup_right (GlobalTheory.AzumayaLocal.mem_right y hu))
  have htop : LinearMap.range f = ⊤ :=
    top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle)
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop 1
  exact ⟨v, hv⟩

theorem GlobalTheory.AzumayaLocal.corner_eq_smul : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Finite A Λ] (e : Λ), IsIdempotentElem e → (∀ y : Λ, ∃ c : A, e * y * e - c • e ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) → ∀ y : Λ, ∃ c : A, e * y * e = c • e := by
  intro A _ _ Λ _ _ _ e he h y
  let g : Λ →ₗ[A] Λ := (LinearMap.mulRight A e).comp (LinearMap.mulLeft A e)
  have hg : ∀ z, g z = e * z * e := fun z => rfl
  have hge : g e = e := by rw [hg, he.eq, he.eq]
  have hgg : ∀ z, g (e * z * e) = e * z * e := by
    intro z
    rw [hg, ← mul_assoc, ← mul_assoc, he.eq, mul_assoc (e * z) e e, he.eq]
  have hS : LinearMap.range g ≤ A ∙ e := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (by rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map g)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨c, hc⟩ := h z
    have key : g z - c • e = g (e * z * e - c • e) := by
      rw [map_sub, map_smul, hgg, hge, hg]
    have hmem : g z - c • e ∈ (maximalIdeal A) • LinearMap.range g := by
      rw [key, LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem hc
    rw [show g z = c • e + (g z - c • e) by abel]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)) hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hS ⟨y, rfl⟩)
  exact ⟨c, hc.symm⟩

namespace GlobalTheory.AzumayaLocal

theorem azumaya_local_matrix : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro ℓ _ A _ _ _ _ Λ _ _ _ _ n hn
  haveI : IsAdicComplete (maximalIdeal A) A :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[ℓ] A
  haveI : Finite (ResidueField A) := GlobalTheory.AzumayaLocal.finite_residueField ℓ A
  haveI : Nontrivial Λ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact zero_ne_one (FaithfulSMul.algebraMap_injective A Λ
      (Subsingleton.elim (algebraMap A Λ 0) (algebraMap A Λ 1)))
  set M := (maximalIdeal A) • (⊤ : Submodule A Λ) with hM
  obtain ⟨x, h1, h2, N, a, b, h3⟩ := GlobalTheory.T.exists_residue_idempotent' A Λ
  obtain ⟨e, he, hex⟩ := GlobalTheory.T.exists_idempotent_lift_adicComplete_free_algebra A (maximalIdeal A) Λ x h1
  have hcorner : ∀ y : Λ, ∃ c : A, e * y * e - c • e ∈ M := by
    intro y
    obtain ⟨c, hc⟩ := h2 y
    refine ⟨c, ?_⟩
    have : e * y * e - c • e = (x * y * x - c • x) + ((e - x) * (y * e) + x * y * (e - x) - c • (e - x)) := by
      simp only [sub_mul, mul_sub, smul_sub, mul_assoc]; abel
    rw [this]
    exact M.add_mem hc (M.sub_mem (M.add_mem (mem_right _ hex) (mem_left _ hex)) (M.smul_mem c hex))
  have hu : ∑ i, a i * e * b i - 1 ∈ M := by
    have : ∑ i, a i * e * b i - 1 = (∑ i, a i * x * b i - 1) + ∑ i, a i * (e - x) * b i := by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]; abel
    rw [this]
    exact M.add_mem h3 (M.sum_mem fun i _ => mem_right _ (mem_left _ hex))
  obtain ⟨v, hv⟩ := GlobalTheory.AzumayaLocal.exists_right_inverse A Λ _ hu
  exact GlobalTheory.T.nonempty_algEquiv_matrix_of_isAzumaya_of_full_idempotent A Λ n hn e he (GlobalTheory.AzumayaLocal.corner_eq_smul A Λ e he hcorner) ⟨N, a, fun i => b i * v, by
    rw [← hv, Finset.sum_mul]; simp only [mul_assoc]⟩

end GlobalTheory.AzumayaLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulFinrankCharacterSpaceOfFreePermutedSummanStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_finrank_characterSpace_of_free_permuted_summands : ∀ (K Γ V X : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype X] [DecidableEq X] (ρ : Representation K Γ V) (H : Subgroup Γ) [MulAction H X], (∀ (h : H) (x : X), h • x = x → h = 1) → ∀ (A : X → Submodule K V), DirectSum.IsInternal A → (∀ (h : H) (x : X), ∀ v ∈ A x, ρ h v ∈ A (h • x)) → ∀ (Hb : Subgroup Γ), Hb ≤ H → ∀ lam : Hb →* Kˣ, Nat.card Hb * finrank K (eig ρ Hb lam) = finrank K V := by
  first | exact @GlobalTheory.BadCount.card_mul_finrank_eig_of_free | exact GlobalTheory.BadCount.card_mul_finrank_eig_of_free | (intros; apply GlobalTheory.BadCount.card_mul_finrank_eig_of_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeightStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_central_and_on_highestWeight : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → (∀ Z, casimir act * act Z = act Z * casimir act) ∧ ∀ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ → (∑ a, ∑ b, if sameBlock a b then act (Eab a b) (act (Eab b a) v) else 0) = ((∑ a, μ a ^ 2 + (∑ i : Fin p, μ (.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ))) + (∑ j : Fin q, μ (.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • v := by
  first | exact @GlobalTheory.CasimirHighest.casimir_central_and_highest | exact GlobalTheory.CasimirHighest.casimir_central_and_highest | (intros; apply GlobalTheory.CasimirHighest.casimir_central_and_highest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2Statement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_fockAct1_sub_casimir_fockAct2_eq_smul_one : ∀ (p q r s : ℕ), casimir (fockAct1 p q r s) - casimir (fockAct2 p q r s) = ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) • (1 : Module.End ℂ (Pol p q r s)) := by
  first | exact @GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 | exact GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 | (intros; apply GlobalTheory.FockCasimir.casimir_fockAct1_sub_casimir_fockAct2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem preservesColimitsOfShape_spec_yoneda (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op) := by
  have h1 : PreservesColimitsOfShape J Scheme.Spec.{0}.rightOp := preservesColimitsOfShape_rightOp J _
  have h2 : PreservesColimitsOfShape J (yoneda (C := Scheme.{0})).op := preservesColimitsOfShape_op J _
  infer_instance

theorem hyp_spec_coAug_of_etFF : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  intro R _ A B g hg k
  obtain ⟨h1, h2⟩ := (etFF_basic.2.1 A B g).1 hg
  exact GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R CommRingCat.{0} (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op)
    (fun n => preservesColimitsOfShape_spec_yoneda _) A B g
    (locallySurjective_etale_section_baseChange.1 _ _ (Spec.map g) h1 h2)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

def colDer {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (Pol ι d a) :=
  ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a,
    S k j • (LinearMap.mulLeft ℂ (X (τ, i, k) : Pol ι d a) ∘ₗ (pderiv (τ, i, j)).toLinearMap)

def atPl {a : ℕ} (τ : ι) (g : Matrix (Fin a) (Fin a) ℂ) : ι → Matrix (Fin a) (Fin a) ℂ :=
  Function.update 1 τ g

theorem colDer_apply {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colDer τ S P = ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a, S k j • (X (τ, i, k) * pderiv (τ, i, j) P) := by
  simp [colDer, LinearMap.sum_apply]

theorem colDer_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (v : Var ι d a) :
    colDer (d := d) τ S (X v) = if v.1 = τ then ∑ k, S k v.2.2 • (X (τ, v.2.1, k) : Pol ι d a) else 0 := by
  obtain ⟨σ, i₀, j₀⟩ := v
  rw [colDer_apply]
  simp only [pderiv_X, Pi.single_apply, Prod.ext_iff]
  by_cases h : σ = τ
  · subst h
    simp only [if_true]
    rw [Finset.sum_eq_single i₀, Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  · simp [h, Ne.symm h]

end GlobalTheory.ColLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSubEqDetCharSmulOfMemInv
section
open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

variable {ι : Type} [Fintype ι]

def genColSub (d a : ℕ) : Pol ι d a →ₐ[ℂ] MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
  aeval fun y => ∑ j' : Fin a, C (X (y.1, j', y.2.2)) * X (y.1, y.2.1, j')

theorem map_eval_genColSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genColSub d a P) = colSub g P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [genColSub, colSub, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p y hp =>
    simp only [map_mul, hp]
    simp [genColSub, colSub, map_sum]

def genDetChar (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_genDetChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) (genDetChar a n) = detChar n g := by
  rw [genDetChar, map_prod, detChar]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem colSub_eq_detChar_smul_of_mem_inv {a d : ℕ} (n : ι → ℕ) (P : Pol ι d a) (hP : P ∈ inv a d n)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) : colSub g P = detChar n g • P := by
  set D : MvPolynomial (Var ι d a) (MvPolynomial (ι × Fin a × Fin a) ℂ) :=
    genColSub d a P - C (genDetChar a n) * map C P with hDdef
  have hD : ∀ g : ι → Matrix (Fin a) (Fin a) ℂ,
      map (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2) D = colSub g P - detChar n g • P := by
    intro g
    rw [hDdef, map_sub, map_mul, map_C, map_eval_genColSub, eval_genDetChar, map_map, smul_eq_C_mul]
    congr 2
    have : (eval fun x : ι × Fin a × Fin a => g x.1 x.2.1 x.2.2).comp (C : ℂ →+* MvPolynomial (ι × Fin a × Fin a) ℂ) =
        RingHom.id ℂ := by ext; simp
    rw [this, map_id]
  have hD0 : D = 0 := by
    refine MvPolynomial.ext _ _ fun m => ?_
    rw [coeff_zero]
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := ι) (n := a) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
    simp only [Matrix.one_mul]
    rw [← coeff_map, hD u]
    have hu' : ∀ τ, u τ ∈ Matrix.unitaryGroup (Fin a) ℂ := fun τ =>
      Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)
    have := hP (fun τ => ⟨u τ, hu' τ⟩)
    simp only at this
    rw [this, sub_self, coeff_zero]
  have := hD g
  rw [hD0, _root_.map_zero] at this
  exact (sub_eq_zero.mp this.symm)

end GlobalTheory.MinorFrame
end
end

