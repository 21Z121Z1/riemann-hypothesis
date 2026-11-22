import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeJacquetFunctorPiTensorEquiv
section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory.JacPiTensor (qlift mk_qlift descend descend_mk)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RelJacTensor

section Spec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

theorem piTensor_mulSingle (a : α) (g : GL (m a) k) (x : ∀ j, X j) :
    piTensor ρ (Pi.mulSingle a g) (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a g (x a))) := by
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h
    simp
  · simp [h]

def qf : MultilinearMap ℂ X (Jacquet (piTensor ρ) (relUnip k e')) :=
  (twKer (piTensor ρ) (relUnip k e') 1).mkQ.compMultilinearMap (PiTensorProduct.tprod ℂ)

theorem qf_update (v : ∀ a, X a) (i : α) (w : X i)
    (hw : w ∈ twKer (ρ i) (unipRad k (e' i)) 1) : qf e' ρ (Function.update v i w) = 0 := by
  unfold twKer at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, y, rfl⟩ := hz
    have hu : (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k)) ∈ relUnip k e' := by
      simp only [relUnip, Subgroup.mem_pi]
      intro j _
      by_cases h : j = i
      · subst h
        simpa using n.2
      · rw [Pi.mulSingle_eq_of_ne h]
        exact one_mem _
    have h1 : PiTensorProduct.tprod ℂ (Function.update v i (ρ i (n : GL (m i) k) y)) =
        piTensor ρ (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k))
          (PiTensorProduct.tprod ℂ (Function.update v i y)) := by
      rw [piTensor_mulSingle]
      simp
    rw [qf, LinearMap.compMultilinearMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      MonoidHom.one_apply, Units.val_one, one_smul, MultilinearMap.map_update_sub, h1]
    exact Submodule.subset_span ⟨⟨_, hu⟩, PiTensorProduct.tprod ℂ (Function.update v i y), by simp⟩
  | zero => simp [qf]
  | add z z' _ _ hz hz' => rw [MultilinearMap.map_update_add, hz, hz', add_zero]
  | smul r z _ hz => rw [MultilinearMap.map_update_smul, hz, smul_zero]

end Spec

section Spec2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

def qmap : (⨂[ℂ] a, X a) →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  PiTensorProduct.map fun a => (twKer (ρ a) (unipRad k (e' a)) 1).mkQ

theorem qmap_tprod (x : ∀ a, X a) :
    qmap e' ρ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp only [qmap, PiTensorProduct.map_tprod, Submodule.mkQ_apply]

theorem qmap_comp (u : ∀ a, GL (m a) k) (hu : u ∈ relUnip k e') :
    qmap e' ρ ∘ₗ piTensor ρ u = qmap e' ρ := by
  have hu' : ∀ a, u a ∈ unipRad k (e' a) := by
    intro a
    have h := hu
    simp only [relUnip, Subgroup.mem_pi] at h
    exact h a (Set.mem_univ a)
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, qmap_tprod]
  congr 1
  funext a
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨⟨u a, hu' a⟩, x a, by simp⟩

theorem twKer_le_ker : twKer (piTensor ρ) (relUnip k e') 1 ≤ LinearMap.ker (qmap e' ρ) := by
  rw [twKer, Submodule.span_le]
  rintro _ ⟨n, y, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub,
    sub_eq_zero]
  exact LinearMap.congr_fun (qmap_comp e' ρ (n : ∀ a, GL (m a) k) n.2) y

def fwd : Jacquet (piTensor ρ) (relUnip k e') →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  (twKer (piTensor ρ) (relUnip k e') 1).liftQ (qmap e' ρ) (twKer_le_ker e' ρ)

def bwd : (⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a))) →ₗ[ℂ] Jacquet (piTensor ρ) (relUnip k e') :=
  PiTensorProduct.lift (descend (qf e' ρ) (qf_update e' ρ))

theorem bwd_tprod (q : ∀ a, Jacquet (ρ a) (unipRad k (e' a))) :
    bwd e' ρ (PiTensorProduct.tprod ℂ q) = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ
      fun i => qlift (fun a => twKer (ρ a) (unipRad k (e' a)) 1) i (q i)) := by
  rw [bwd, PiTensorProduct.lift.tprod]
  rfl

theorem bwd_tprod_mk (x : ∀ a, X a) :
    bwd e' ρ (PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a)))) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x) := by
  rw [bwd, PiTensorProduct.lift.tprod, descend_mk]
  rfl

theorem fwd_mk_tprod' (x : ∀ a, X a) :
    fwd e' ρ (Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  rw [fwd, Submodule.liftQ_apply, qmap_tprod]

def jacEquiv : Jacquet (piTensor ρ) (relUnip k e') ≃ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  LinearEquiv.ofLinear (fwd e' ρ) (bwd e' ρ)
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, bwd_tprod, fwd_mk_tprod']
      simp only [mk_qlift, LinearMap.compMultilinearMap_apply, LinearMap.id_apply])
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        fwd_mk_tprod', bwd_tprod_mk, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Submodule.mkQ_apply])

theorem relJac_piTensor :
    Nonempty ((relJac e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  refine ⟨Representation.Equiv.mk (jacEquiv e' ρ) fun g => ?_⟩
  refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    LinearEquiv.coe_coe, jacEquiv, LinearEquiv.ofLinear_apply, relJac_mk, piTensor_tprod, relEmb_apply,
    map_smul, fwd_mk_tprod', jac_mk, MultilinearMap.map_smul_univ, relDeltaHalf_apply]
  congr 1
  rw [← Finset.prod_inv_distrib, Units.coe_prod]

end Spec2

theorem relJac_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β]
    (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)),
    Nonempty ((relJac f (piTensor ρ)).Equiv (piTensor fun i => jac (f i) (ρ i))) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f X _ _ ρ
  classical
  exact relJac_piTensor f ρ

end GlobalTheory.RelJacTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemilinearEquivPreservesProperties
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ConjRep

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}

theorem map_fixed (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (U : Subgroup G) :
    (fixed ρ U).map (e : V →ₛₗ[starRingEnd ℂ] W) = fixed ρ' U := by
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hxe' : e x = e v := hxe
    rw [← hxe', GlobalTheory.LGrp.mem_fixed]
    intro k hk
    rw [← he, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
  · intro h
    refine ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.injective ?_, rfl⟩
    rw [he, GlobalTheory.LGrp.mem_fixed.1 h k hk]

def comapSub (φ : V →ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, φ (ρ g x) = ρ' g (φ x)) (S : Subrepresentation ρ') :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap φ
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_comap] at hv ⊢
    rw [he]
    exact S.apply_mem_toSubmodule g hv

theorem symm_equivariant (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (g : G) (y : W) :
    e.symm (ρ' g y) = ρ g (e.symm y) := by
  apply e.injective
  rw [he]
  simp

def subOrderIso (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x)) :
    Subrepresentation ρ' ≃o Subrepresentation ρ where
  toFun := comapSub (e : V →ₛₗ[starRingEnd ℂ] W) he
  invFun := comapSub (e.symm : W →ₛₗ[starRingEnd ℂ] V) (symm_equivariant e he)
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    simp [comapSub]
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    simp [comapSub]
  map_rel_iff' := by
    intro S T
    constructor
    · intro h w hw
      obtain ⟨v, rfl⟩ := e.surjective w
      exact @h v hw
    · intro h v hv
      exact @h (e v) hv

theorem isUnitarisable (e : V ≃ₛₗ[starRingEnd ℂ] W) (he : ∀ g x, e (ρ g x) = ρ' g (e x))
    (h : GlobalTheory.LGrp.IsUnitarisable ρ) : GlobalTheory.LGrp.IsUnitarisable ρ' := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => B (e.symm y) (e.symm x)) ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro a b c; simp
  · intro a b c; simp [LinearEquiv.map_smulₛₗ]
  · intro a b c; simp
  · intro a b c; simp [LinearEquiv.map_smulₛₗ]
  · intro v w
    exact h1 _ _
  · intro v hv
    exact h2 _ (by simpa using hv)
  · intro g v w
    simp only [LinearMap.mk₂'ₛₗ_apply, symm_equivariant e he, h3]

theorem conj_transfer : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (φ : V →ₛₗ[starRingEnd ℂ] W), Function.Bijective φ → (∀ g x, φ (ρ g x) = ρ' g (φ x)) → (ρ.IsIrreducible → ρ'.IsIrreducible) ∧ (IsAdmissible ρ → IsAdmissible ρ') ∧ (GlobalTheory.LGrp.IsUnitarisable ρ → GlobalTheory.LGrp.IsUnitarisable ρ') ∧ (GlobalTheory.LGrp.IsSpherical ρ K → GlobalTheory.LGrp.IsSpherical ρ' K) := by
  intro G _ _ K V _ _ W _ _ ρ ρ' φ hφ hρ
  let e : V ≃ₛₗ[starRingEnd ℂ] W := LinearEquiv.ofBijective φ hφ
  have he : ∀ g x, e (ρ g x) = ρ' g (e x) := hρ
  refine ⟨fun h => ?_, fun h => ⟨fun w => ?_, fun U hU hc => ?_⟩, isUnitarisable e he, fun h h0 => h ?_⟩
  · haveI : IsSimpleOrder (Subrepresentation ρ) := h
    exact (subOrderIso e he).isSimpleOrder
  · obtain ⟨v, rfl⟩ := e.surjective w
    have := h.1 v
    convert this using 3 with g
    rw [← he]
    exact e.injective.eq_iff
  · haveI := h.2 U hU hc
    rw [← map_fixed e he U]
    have hfg : (fixed ρ U).FG := Module.Finite.iff_fg.1 inferInstance
    exact Module.Finite.iff_fg.2 (hfg.map _)
  · rw [← map_fixed e he K] at h0
    rw [eq_bot_iff]
    intro v hv
    have : e v ∈ (⊥ : Submodule ℂ W) := h0 ▸ Submodule.mem_map_of_mem hv
    simpa using this

end GlobalTheory.ConjRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClasses
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactorUnique

open GlobalTheory.SmGL

variable {β : Type} [Fintype β] [DecidableEq β] {X : β → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)]

def contrML (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) : MultilinearMap ℂ X (X j) := GlobalTheory.MultilinearContraction.contractMultilinear l j

def contr (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) : (PiTensorProduct ℂ X) →ₗ[ℂ] X j := GlobalTheory.MultilinearContraction.contract l j

theorem contr_tprod (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β) (x : ∀ a, X a) :
    contr l j (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase j, l i (x i)) • x j :=
  GlobalTheory.MultilinearContraction.contract_tprod l j x

theorem exists_contr_ne_zero (j : β) {y : PiTensorProduct ℂ X} (hy : y ≠ 0) :
    ∃ l : ∀ a, X a →ₗ[ℂ] ℂ, contr l j y ≠ 0 := by
  let b := fun a => Module.Free.chooseBasis ℂ (X a)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr y p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  refine ⟨fun a => (b a).coord (p a), fun h => hp ?_⟩
  have e : (b j).coord (p j) ∘ₗ contr (fun a => (b a).coord (p a)) j = B.coord p := by
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contr_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ j)
  have := LinearMap.congr_fun e y
  rw [LinearMap.comp_apply, h, map_zero] at this
  exact this.symm

variable {Γ : β → Type} [∀ a, Group (Γ a)]

theorem contr_mulSingle (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (l : ∀ a, X a →ₗ[ℂ] ℂ) (j : β)
    (g : Γ j) (y : PiTensorProduct ℂ X) :
    contr l j (piTensor ρ (Pi.mulSingle j g) y) = ρ j g (contr l j y) := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contr_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun a ha => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase ha), map_one, Module.End.one_apply]

omit [Fintype β] in

theorem tprod_update_mulSingle (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (x : ∀ a, X a) (j : β)
    (g : Γ j) (v : X j) :
    PiTensorProduct.tprod ℂ (Function.update x j (ρ j g v)) =
      piTensor ρ (Pi.mulSingle j g) (PiTensorProduct.tprod ℂ (Function.update x j v)) := by
  rw [piTensor_tprod]
  congr 1
  funext a
  by_cases h : a = j
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem cl_eq_of_piTensor_equiv : ∀ (β : Type) [Fintype β] (Γ : β → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)] (s s' : ∀ j, GlobalTheory.SmGL.IrrRep (Γ j)), Nonempty ((GlobalTheory.SmGL.piTensor fun j => (s j).ρ).Equiv (GlobalTheory.SmGL.piTensor fun j => (s' j).ρ)) → ∀ j, (s j).cl = (s' j).cl := by
  intro β _ Γ _ _ s s' ⟨φ⟩ j
  classical
  haveI := fun a => nontrivial_of_irreducible (s a).irr
  let b := fun a => Module.Free.chooseBasis ℂ (s a).V
  let p : ∀ a, Module.Free.ChooseBasisIndex ℂ (s a).V := fun a => (b a).index_nonempty.some
  let x : ∀ a, (s a).V := fun a => b a (p a)
  have hx : PiTensorProduct.tprod ℂ x ≠ 0 := by
    have := (Basis.piTensorProduct b).ne_zero p
    rwa [Basis.piTensorProduct_apply] at this
  have hy : φ (PiTensorProduct.tprod ℂ x) ≠ 0 := fun h => hx ((map_eq_zero_iff φ φ.injective).1 h)
  obtain ⟨l, hl⟩ := exists_contr_ne_zero j hy
  let ψ : (s j).ρ.IntertwiningMap (s' j).ρ :=
    { toLinearMap := contr l j ∘ₗ φ.toLinearMap ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x j
      isIntertwining' := fun g => by
        ext v
        simp only [LinearMap.comp_apply, MultilinearMap.toLinearMap_apply]
        rw [tprod_update_mulSingle (fun a => (s a).ρ), ← contr_mulSingle (fun a => (s' a).ρ)]
        congr 1
        exact LinearMap.congr_fun (φ.isIntertwining' (Pi.mulSingle j g)) _ }
  have hψ : ψ ≠ 0 := fun h => hl (by
    have : ψ (x j) = 0 := by rw [h]; rfl
    rw [← this]
    show _ = contr l j (φ (PiTensorProduct.tprod ℂ (Function.update x j (x j))))
    rw [Function.update_eq_self])
  haveI := (s j).irr
  haveI := (s' j).irr
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero ψ).resolve_right hψ
  exact IrrRep.cl_eq_iff.2 ⟨ψ.ofBijective hb⟩

end GlobalTheory.TensorFactorUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridRowZeroVerticesAgreeWeilData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem lattice_heq_of_eq_hermitianSpaceWithLattice_mk {D : D7} {x : LSp D} {s : HSp D} {l : Submodule (𝓞 D.host.E) (Fin s.rank → D.host.E)}
    (e : x = ⟨s, l⟩) : HEq l x.lat := by subst e; rfl

theorem nodeAgree_grid0_of_weil_over : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ j, j ≤ D.R.m → NodeAgree (GlobalTheory.Grid.row0 R j) W (.grid 0 j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW j hj
  rcases Nat.lt_or_ge j D.R.m with h | h
  · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]
    have e : G'.node (.grid 0 j) = ⟨Yc D j, R.ΛY j⟩ := colY_lt R.toLevCh h
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, (hW.cartY j h).symm, (hW.onbY j h).symm⟩
  · obtain rfl : j = D.R.m := le_antisymm hj h
    rw [← nodeX_eq_chainVertexAtRowZero_top R]
    have e : G'.node (.grid 0 D.R.m) = ⟨D.sp.X', R.ΛX⟩ := colY_m R.toLevCh
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, hW.cartX.symm, hW.onbX.symm⟩

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisa
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LFun.ConjParam

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem conj_mem_hecke {h : G → ℂ} (hh : h ∈ Hecke ℂ K) : (fun g => starRingEnd ℂ (h g)) ∈ Hecke ℂ K := by
  obtain ⟨h1, S, hS⟩ := hh
  exact ⟨fun a b g => congrArg _ (h1 a b g), S, fun g hg => hS g fun h0 => hg (by simp [h0])⟩

theorem eigen_conj (hK : IsCommensurated K) (hinv : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, g⁻¹ = k₁ * g * k₂)
    {ρ : Representation ℂ G V} (hρ : GlobalTheory.LGrp.IsUnitarisable ρ) {x : V} (h0 : x ≠ 0) (hx : x ∈ fixed ρ K)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ K) {a b : ℂ} (ha : heckeVec ρ K h x = a • x)
    (hb : heckeVec ρ K (fun g => starRingEnd ℂ (h g)) x = b • x) : starRingEnd ℂ b = a := by
  obtain ⟨B, hB, hpos, hinvB⟩ := hρ
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hreal : ∀ g, starRingEnd ℂ (B (ρ g x) x) = B (ρ g x) x := fun g => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hinv g
    have e1 : B x (ρ g x) = B (ρ g⁻¹ x) x := by
      rw [← hinvB g (ρ g⁻¹ x) x, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e2 : B (ρ k₁ (ρ g x)) x = B (ρ g x) x := by
      rw [← hinvB k₁ (ρ g x) x, hfix k₁ hk₁]
    rw [← hB, e1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix k₂ hk₂, e2]
  have key : ∀ f ∈ Hecke ℂ K, B (heckeVec ρ K f x) x = ∑ᶠ c : G ⧸ K, f c.out * B (ρ c.out x) x := fun f hf => by
    refine ((B.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_)
    simp
  have hxx : starRingEnd ℂ (B x x) = B x x := (hB x x).symm
  have hne : B x x ≠ 0 := fun e => by simpa [e] using hpos x h0
  have e1 := key h hh
  have e2 := congrArg (starRingEnd ℂ) (key _ (conj_mem_hecke hh))
  rw [ha] at e1
  rw [hb, show ⇑(starRingEnd ℂ) = (starAddEquiv : ℂ ≃+ ℂ) from rfl, AddEquiv.map_finsum] at e2
  apply mul_right_cancel₀ hne
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at e1 e2
  rw [e1]
  refine Eq.trans ?_ (e2.trans (finsum_congr fun c => ?_))
  · change _ = starRingEnd ℂ _
    rw [map_mul, hxx]
  · change starRingEnd ℂ _ = _
    rw [map_mul, hreal]
    exact congrArg (· * _) (Complex.conj_conj _)

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem conj_satU {m : ℕ} (ϖ : L) (q : ℕ) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    starRingEnd ℂ (SatU ϖ q (fun g => starRingEnd ℂ (h g)) α) = SatU ϖ q h fun i => starRingEnd ℂ (α i) := by
  have hs : ∀ {ι : Type} (f : ι → ℂ), starRingEnd ℂ (∑ᶠ i, f i) = ∑ᶠ i, starRingEnd ℂ (f i) := fun f =>
    AddEquiv.map_finsum (starAddEquiv : ℂ ≃+ ℂ) f
  unfold SatU
  rw [hs]
  refine finsum_congr fun a => ?_
  rw [map_mul, hs, map_prod]
  congr 1
  · simp
  · refine finsum_congr fun c => ?_
    split_ifs <;> simp

theorem inv_mem {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ n) :
    ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g⁻¹ = k₁ * g * k₂ := by
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ (g := (g : GL (Fin n) L)) (by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

theorem satU_star_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecU ϖ q ρ x α → ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => ((star (α i) : ℂˣ) : ℂ)) = SatU ϖ q h (fun i => (α i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hρ hx h hh
  exact (conj_satU ϖ q h fun i => (α i : ℂ)).symm.trans
    (eigen_conj (P.isCommensurated_integral_unitary_of_unramified hU n) (inv_mem hU) hρ hx.1 hx.2.1 hh (hx.2.2 h hh) (hx.2.2 _ (conj_mem_hecke hh)))

end GlobalTheory.LFun.ConjParam

end
end

