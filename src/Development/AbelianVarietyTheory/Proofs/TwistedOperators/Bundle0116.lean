import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0112
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0756
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0110
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0113
import Formalism.LocalToGlobal.KernelLattices.ThDistC

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquiv
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

noncomputable section

namespace GlobalTheory.PolyTensor

theorem curry_sum_mapDomain {ι β : Type} [Fintype ι] (v : ι → (β →₀ ℕ)) (τ : ι) :
    (∑ σ, Finsupp.mapDomain (fun x => (σ, x)) (v σ)).curry τ = v τ := by
  classical
  ext x
  rw [Finsupp.curry_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (fun a b h => (Prod.mk.inj h).2) (v τ) x
  · intro σ _ hσ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hσ (congrArg Prod.fst hy)
  · intro h
    exact absurd (Finset.mem_univ τ) h

def expEquiv (ι σ : Type) [Fintype ι] : (ι → (σ →₀ ℕ)) ≃ (ι × σ →₀ ℕ) :=
  Equiv.ofBijective (fun v => ∑ τ, Finsupp.mapDomain (fun x => (τ, x)) (v τ)) <| by
    classical
    refine ⟨fun v w h => funext fun τ => ?_, fun m => ⟨fun τ => m.curry τ, ?_⟩⟩
    · rw [← curry_sum_mapDomain v τ, ← curry_sum_mapDomain w τ]
      exact congrArg (fun m : ι × σ →₀ ℕ => m.curry τ) h
    · ext ⟨τ, x⟩
      have := DFunLike.congr_fun (curry_sum_mapDomain (fun τ => m.curry τ) τ) x
      simpa only [Finsupp.curry_apply] using this

theorem exists_piTensor_equiv : ∀ (ι σ : Type) [Fintype ι],
    ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ,
      ∀ f : ι → MvPolynomial σ ℂ,
        e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  intro ι σ _
  classical
  let bT := Basis.piTensorProduct (fun _ : ι => MvPolynomial.basisMonomials σ ℂ)
  let e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
    bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

  have key : e.toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ) =
      (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
        (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap) := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials σ ℂ) fun v => ?_
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, ← Basis.piTensorProduct_apply]
    change bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ) (bT v) = _
    rw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      MvPolynomial.rename_monomial, expEquiv, Equiv.ofBijective_apply]
    exact MvPolynomial.monomial_sum_one _ _
  refine ⟨e, fun f => ?_⟩
  simpa using congrArg (fun F : MultilinearMap ℂ (fun _ : ι => MvPolynomial σ ℂ) _ => F f) key

end GlobalTheory.PolyTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorShuffleEquiv
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_piTensor_shuffle_equiv (ι : Type) [Fintype ι] (F V : ι → Type)
    [∀ τ, AddCommGroup (F τ)] [∀ τ, Module ℂ (F τ)] [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] :
    ∃ e : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) ≃ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)),
      ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ),
        e (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v)
          = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
  classical

  let bF := fun τ => Module.Basis.ofVectorSpace ℂ (F τ)
  let bV := fun τ => Module.Basis.ofVectorSpace ℂ (V τ)
  let b₁ := (Basis.piTensorProduct bF).tensorProduct (Basis.piTensorProduct bV)
  let b₂ := Basis.piTensorProduct (fun τ => (bF τ).tensorProduct (bV τ))

  let Φ : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) →ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)) :=
    TensorProduct.lift (PiTensorProduct.map₂ (fun τ => TensorProduct.mk ℂ (F τ) (V τ)))
  have hΦ : ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ),
      Φ (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v)
        = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
    intro f v
    simp only [Φ, TensorProduct.lift.tmul, PiTensorProduct.map₂_tprod_tprod, TensorProduct.mk_apply]

  let e := b₁.equiv b₂ (Equiv.arrowProdEquivProdArrow ι _ _).symm

  have he : (e : _ →ₗ[ℂ] _) = Φ := by
    refine b₁.ext (fun i => ?_)
    obtain ⟨p, q⟩ := i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp only [b₁, b₂, Module.Basis.tensorProduct_apply, Basis.piTensorProduct_apply, hΦ]
    congr 1
    funext τ
    exact Module.Basis.tensorProduct_apply' (bF τ) (bV τ) (p τ, q τ)
  exact ⟨e, fun f v => (LinearMap.congr_fun he _).trans (hΦ f v)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockAlg

theorem fock_structure : ∀ X : ProvA, admH2 X := by
  intro X p q r s
  refine ⟨fun d μ P hP hw => (GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector p q r s).1 d μ P hP hw.1 hw.2.1,
    fun d μ P hP hw => (GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector p q r s).2 d μ P hP hw.1 hw.2.1,
    fun μ P h0 ht hh => (GlobalTheory.T.fockHarmonic_homogeneous_of_KType p q r s).1 μ P h0 ht hh,
    fun μ P h0 ht hh => (GlobalTheory.T.fockHarmonic_homogeneous_of_KType p q r s).2 μ P h0 ht hh,
    fun μ μ' => ⟨GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape p q r s μ μ', GlobalTheory.T.fockJointHarmonics_highestWeight_eq_bot_of_not_shape p q r s μ μ'⟩, ?_⟩
  intro u1 u2 hu d
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.fischerDecomposition_fockNoncompactParts p q r s d
  cases u1 <;> cases u2
  · simp at hu
  · have e1 : lowKer X (X.fock p q r s) false true = harm1 p q r s := by
      ext P; simp [lowKer, harm1, FockData.act2]
    have e2 : raised X (X.fock p q r s) false true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act2]
    rw [e1, e2]; exact h2
  · have e1 : lowKer X (X.fock p q r s) true false = harm2 p q r s := by
      ext P; simp [lowKer, harm2, FockData.act1]
    have e2 : raised X (X.fock p q r s) true false d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1]
    rw [e1, e2]; exact h1
  · have e1 : lowKer X (X.fock p q r s) true true = jointHarm p q r s := by
      ext P; simp [lowKer, jointHarm, harm1, harm2, FockData.act1, FockData.act2]
    have e2 : raised X (X.fock p q r s) true true d = {R | ∃ Q ∈ homog (Ix p q × Ix r s) d,
        (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨
          ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q} := by
      ext P; simp [raised, FockData.act1, FockData.act2]
    rw [e1, e2]; exact h3

end GlobalTheory.FockAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleOfIsAtom
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.MaschkeForms

open Representation

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_isAtom {π : Representation ℂ G V} {U : Subrepresentation π}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  have hne : U.toSubmodule ≠ ⊥ := fun h => hU.1 (Subrepresentation.toSubmodule_injective h)
  have hnt : Nontrivial (Subrepresentation U.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h' : (⊥ : Submodule ℂ U.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← U.toSubmodule.map_subtype_top, ← h', Submodule.map_bot]
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation π := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, S.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hT : T ≤ U := U.toSubmodule.map_subtype_le S.toSubmodule
  have hinj := Submodule.map_injective_of_injective U.toSubmodule.injective_subtype
  rcases hU.le_iff.mp hT with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans (Submodule.map_bot _).symm
  · right
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans U.toSubmodule.map_subtype_top.symm

def orbitSpan (π : Representation ℂ G V) (x : V) : Subrepresentation π where
  toSubmodule := Submodule.span ℂ (Set.range fun h : G => π h x)
  apply_mem_toSubmodule g v hv := by
    have : Submodule.span ℂ (Set.range fun h : G => π h x) ≤
        (Submodule.span ℂ (Set.range fun h : G => π h x)).comap (π g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by show π (g * h) x = π g (π h x); rw [map_mul]; rfl⟩
    exact this hv

theorem isCompl_toSubmodule {π : Representation ℂ G V} {S T : Subrepresentation π} (h : IsCompl S T) :
    IsCompl S.toSubmodule T.toSubmodule := by
  constructor
  · rw [disjoint_iff]; exact congrArg Subrepresentation.toSubmodule h.inf_eq_bot
  · rw [codisjoint_iff]; exact congrArg Subrepresentation.toSubmodule h.sup_eq_top

theorem proj_left {π : Representation ℂ G V} {S T : Subrepresentation π} (h : IsCompl S T) (v : V)
    (hv : v ∈ S.toSubmodule) :
    S.toSubmodule.projectionOnto T.toSubmodule (isCompl_toSubmodule h) v = ⟨v, hv⟩ :=
  Submodule.projectionOnto_apply_left (isCompl_toSubmodule h) ⟨v, hv⟩

theorem proj_right {π : Representation ℂ G V} {S T : Subrepresentation π} (h : IsCompl S T) (v : V)
    (hv : v ∈ T.toSubmodule) :
    S.toSubmodule.projectionOnto T.toSubmodule (isCompl_toSubmodule h) v = 0 :=
  Submodule.projectionOnto_apply_right (isCompl_toSubmodule h) ⟨v, hv⟩

def proj {π : Representation ℂ G V} {S T : Subrepresentation π} (h : IsCompl S T) :
    π.IntertwiningMap S.toRepresentation :=
  (S.toSubmodule.projectionOnto T.toSubmodule (isCompl_toSubmodule h)).intertwiningMap_of_isIntertwiningMap
    π S.toRepresentation (by
      intro g v
      have hv : v ∈ S.toSubmodule ⊔ T.toSubmodule := by
        rw [(isCompl_toSubmodule h).sup_eq_top]; exact Submodule.mem_top
      obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add, map_add, map_add, proj_left h _ (S.apply_mem_toSubmodule g hs),
        proj_right h _ (T.apply_mem_toSubmodule g ht), proj_left h s hs, proj_right h t ht, add_zero, add_zero]
      rfl)

end GlobalTheory.MaschkeForms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoTwistDetIrrShift
section
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

private lemma detShift_eq_add_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c)
    (hn : 0 < n) : lam'.detShift = lam.detShift + c := by
  simp only [DomWeight.detShift, dif_pos hn, h]

private lemma natW_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    lam'.natW = lam.natW := by
  funext i
  simp only [DomWeight.natW, detShift_eq_add_of_weight_shift n c lam lam' h (Fin.pos i), h]
  congr 1
  ring

private lemma nablaSq_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    nablaSq ℂ n lam' = nablaSq ℂ n lam := by
  simp only [nablaSq, natW_eq_of_weight_shift n c lam lam' h]

private lemma detPow_detShift_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) (g : U n) :
    detPow ℂ n (unitaryIncl n g) lam'.detShift =
      ((detU n g ^ c : ℂˣ) : ℂ) * detPow ℂ n (unitaryIncl n g) lam.detShift := by
  have hdet : Matrix.GeneralLinearGroup.det (unitaryIncl n g) = detU n g := by
    ext
    simp [detU, unitaryIncl_coe]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : detU 0 g = 1 := by
      ext
      simp [detU]
    simp [h1, DomWeight.detShift, detPow]
  · simp only [detPow, detShift_eq_add_of_weight_shift n c lam lam' h hn, hdet, zpow_add, Units.val_mul]
    ring

theorem iso_twist_det_irr_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  refine ⟨LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm, fun g x => ?_⟩
  apply Subtype.ext
  change ((detU n ^ c) g : ℂ) • (sqRep ℂ n lam (unitaryIncl n g) x : MvPolynomial (Fin n × Fin n) ℂ) =
    (sqRep ℂ n lam' (unitaryIncl n g) (LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm x) :
      MvPolynomial (Fin n × Fin n) ℂ)
  have hz : (detU n ^ c) g = detU n g ^ c := rfl
  rw [sqRep_coe, sqRep_coe, hz]
  simp only [sqAct, LinearEquiv.coe_ofEq_apply, detPow_detShift_of_weight_shift n c lam lam' h g, mul_smul]

end GlobalTheory.OneFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDual
section
noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching Formalism.GradedWeylDivisibility Formalism.REAL
open scoped TensorProduct DirectSum Matrix

namespace GlobalTheory.ConjDual

theorem map_rowAct {r n : ℕ} (φ : ℂ →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    map φ (rowAct ℂ A f) = rowAct ℂ (A.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct]

def bil (σ : Type) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f f' => fockF f (map (starRingEnd ℂ) f'))
    (fun _ _ _ => fischerInner_add_left _ _ _)
    (fun c f f' => by rw [smul_eq_C_mul, LFocks_C_mul_left, smul_eq_mul])
    (fun f a b => by rw [map_add, fischerInner_add_right])
    (fun c f f' => by
      rw [smul_eq_C_mul, map_mul, map_C, LFocks_C_mul_right, smul_eq_mul]
      simp)

theorem bil_apply {σ : Type} (f f' : MvPolynomial σ ℂ) : bil σ f f' = fockF f (map (starRingEnd ℂ) f') := rfl

theorem bil_rowAct {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (f f' : MvPolynomial (Fin r × Fin n) ℂ) :
    bil _ (rowAct ℂ A f) f' = bil _ f (rowAct ℂ Aᵀ f') := by
  rw [bil_apply, bil_apply, fockRowAdj, map_rowAct]
  rfl

theorem bil_conj {σ : Type} (f : MvPolynomial σ ℂ) : bil σ f (map (starRingEnd ℂ) f) = fockF f f := by
  rw [bil_apply, map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext; simp
  rw [this, map_id]

def toDual (n : ℕ) (lam : DomWeight n) : nablaSq ℂ n lam →ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ n lam) :=
  (bil _).compl₁₂ (nablaSq ℂ n lam).subtype (nablaSq ℂ n lam).subtype

theorem toDual_injective (n : ℕ) (lam : DomWeight n) : Function.Injective (toDual n lam) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra h0
  have h1 : f.1 ≠ 0 := fun h => h0 (Subtype.ext h)
  have h2 := LinearMap.congr_fun hf ⟨map (starRingEnd ℂ) f.1, dualWeylMap ℂ ℂ _ n n _ _ f.2⟩
  have h3 : fockF f.1 f.1 = 0 := (bil_conj f.1).symm.trans h2
  have h := fockPos _ f.1 h1
  rw [h3] at h
  simp at h

theorem detPow_conjU (n : ℕ) (g : U n) (c : ℤ) :
    detPow ℂ n (unitaryIncl n (conjU n g)) c = detPow ℂ n (unitaryIncl n g⁻¹) c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, unitaryIncl_coe,
    unitaryIncl_coe, conjU_coe, Matrix.det_transpose]
  rfl

theorem iso_conj_dual : ∀ (n : ℕ) (lam : DomWeight n),
    Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  intro n lam
  refine ⟨(toDual n lam).linearEquivOfInjective (toDual_injective n lam) Subspace.dual_finrank_eq.symm,
    fun g x => ?_⟩
  ext y
  change bil _ (sqAct ℂ n lam (unitaryIncl n (conjU n g)) x.1) y.1 =
    bil _ x.1 (sqAct ℂ n lam (unitaryIncl n g⁻¹) y.1)
  unfold sqAct
  rw [map_smul, map_smul, LinearMap.smul_apply, detPow_conjU, bil_rowAct, Matrix.transpose_transpose]
  rfl

end GlobalTheory.ConjDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureParahoricDatumSupport
section
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.SupportVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_lt (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem isUnit_iff_val (x : 𝒪[k]) : IsUnit x ↔ valuation k (x : k) = 1 :=
  (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one

theorem isUnit_red_iff {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n 𝒪[k]) :
    IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.red A) ↔ valuation k ((A.det : 𝒪[k]) : k) = 1 := by
  rw [← isUnit_iff_val, ← Matrix.isUnit_iff_isUnit_det]
  exact ⟨GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.isUnit_of_red A, fun h => h.map (IsLocalRing.residue 𝒪[k]).mapMatrix⟩

theorem det_coe {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n 𝒪[k]) :
    ((A.det : 𝒪[k]) : k) = (A.map (algebraMap 𝒪[k] k)).det :=
  by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl

def suppBar (A D E : Type) [Fintype A] [DecidableEq A] :
    Set (Matrix (A ⊕ E) (A ⊕ D) 𝓀[k]) :=
  {B | IsUnit B.toBlocks₁₁ ∧ B.toBlocks₂₁ = 0}

theorem inSupp_eq_pre {A D E : Type} [Fintype A] [DecidableEq A] :
    {x : Matrix (A ⊕ E) (A ⊕ D) k | InSupp x} = GlobalTheory.IndexVolume.pre (suppBar (k := k) A D E) := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Matrix.of fun i j => ⟨x i j, h1 i j⟩, rfl, ?_, ?_⟩
    · change IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.red (Matrix.of fun i j => (⟨x i j, h1 i j⟩ : 𝒪[k])).toBlocks₁₁)
      rw [isUnit_red_iff, det_coe]
      exact h2
    · ext i j
      exact (residue_eq_zero_iff_lt _).2 (h3 i j)
  · rintro ⟨A, rfl, hu, hz⟩
    refine ⟨fun i j => (A i j).2, ?_, fun i j => ?_⟩
    · have := (isUnit_red_iff A.toBlocks₁₁).1 hu
      rw [det_coe] at this
      exact this
    · exact (residue_eq_zero_iff_lt (A (.inr i) (.inl j))).1 (congrFun (congrFun hz i) j)

def unitBar (A : Type) [Fintype A] [DecidableEq A] : Set (Matrix A A 𝓀[k]) := {U | IsUnit U}

theorem KO_eq_pre (A : Type) [Fintype A] [DecidableEq A] :
    Units.val '' (KO k A : Set (GL A k)) = GlobalTheory.IndexVolume.pre (unitBar (k := k) A) := by
  ext x
  constructor
  · rintro ⟨g, ⟨h, rfl⟩, rfl⟩
    exact ⟨h.val, rfl, h.isUnit.map (IsLocalRing.residue 𝒪[k]).mapMatrix⟩
  · rintro ⟨M, rfl, hM⟩
    obtain ⟨u, hu⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.isUnit_of_red M hM
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u, ⟨u, rfl⟩, ?_⟩
    rw [← hu]
    rfl

theorem card_matrix (m n : Type) [Fintype m] [Fintype n] :
    Nat.card (Matrix m n 𝓀[k]) = Nat.card 𝓀[k] ^ (Fintype.card m * Fintype.card n) := by
  change Nat.card (m → n → 𝓀[k]) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul, Nat.card_eq_fintype_card (α := m), Nat.card_eq_fintype_card (α := n), mul_comm]

def suppEquiv (A D E : Type) [Fintype A] [DecidableEq A] :
    suppBar (k := k) A D E ≃ unitBar (k := k) A × Matrix A D 𝓀[k] × Matrix E D 𝓀[k] where
  toFun B := (⟨B.1.toBlocks₁₁, B.2.1⟩, B.1.toBlocks₁₂, B.1.toBlocks₂₂)
  invFun U := ⟨fromBlocks U.1.1 U.2.1 0 U.2.2, ⟨by rw [toBlocks_fromBlocks₁₁]; exact U.1.2, toBlocks_fromBlocks₂₁ _ _ _ _⟩⟩
  left_inv B := by
    obtain ⟨B, h1, h2⟩ := B
    apply Subtype.ext
    simp only
    rw [← h2, fromBlocks_toBlocks]
  right_inv U := by
    obtain ⟨⟨U, hU⟩, X, Y⟩ := U
    simp

theorem card_suppBar (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [Fintype E] :
    Nat.card (suppBar (k := k) A D E) = Nat.card (unitBar (k := k) A) *
      (Nat.card 𝓀[k] ^ (Fintype.card A * Fintype.card D) * Nat.card 𝓀[k] ^ (Fintype.card E * Fintype.card D)) := by
  rw [Nat.card_congr (suppEquiv A D E), Nat.card_prod, Nat.card_prod, card_matrix, card_matrix]

theorem measure_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (r : ℕ) (D E : Type) [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E],
    MeasurableSet {x : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k | InSupp x} ∧
    (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real {x | InSupp x} = volAdd ν r * ((resCard k : ℝ) ^ (r * Fintype.card E))⁻¹ := by
  intro k _ _ _ _ _ _ ν hν r D E _ _ _ _
  haveI := hν.1
  rw [inSupp_eq_pre]
  refine ⟨GlobalTheory.IndexVolume.measurableSet_pre _, ?_⟩
  have h1 : (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real (GlobalTheory.IndexVolume.pre (suppBar (k := k) (Fin r) D E)) =
      _ := GlobalTheory.IndexVolume.measureReal_pre ν hν.2 _
  have h2 : (volM ν (Fin r) (Fin r)).real (GlobalTheory.IndexVolume.pre (unitBar (k := k) (Fin r))) =
      _ := GlobalTheory.IndexVolume.measureReal_pre ν hν.2 _
  unfold volAdd
  rw [KO_eq_pre, h1, h2, card_suppBar]
  have hq : (0 : ℝ) < Nat.card 𝓀[k] := by exact_mod_cast Nat.card_pos
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.resCard, resCard, Fintype.card_sum, Fintype.card_fin]
  push_cast
  set q : ℝ := (Nat.card 𝓀[k] : ℝ)
  set d := Fintype.card D
  set e := Fintype.card E
  have hexp : q ^ ((r + e) * (r + d)) = q ^ (r * r) * q ^ (r * e) * (q ^ (r * d) * q ^ (e * d)) := by
    rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
  rw [hexp]
  have : q ≠ 0 := hq.ne'
  field_simp

end GlobalTheory.SupportVolume
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebraStatement
section
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra : ∀ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ), Continuous u → u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) → ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | exact GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU | (intros; apply GlobalTheory.OneParamUnitary.oneParam_eq_exp_lieU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaJetMapWeightedTableScaleStatement
section
open Formalism.L2.Ker MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetMap_weighted_table_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (u : ℂ) (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ) (P : Formalism.L2.DIV.Pol ℂ ι a), jetMap (fun m => u * ((m.prod fun k e => c k.1 ^ e) * J m)) nn P = u • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin b => c τ) (jetMap J nn P) := by
  first | exact @GlobalTheory.JetScale.jetMap_weight_scale | exact GlobalTheory.JetScale.jetMap_weight_scale | (intros; apply GlobalTheory.JetScale.jetMap_weight_scale <;> assumption)
end

