import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompacts
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime]

theorem isCompact_box (K : ∀ v : AwayP p, Set (Qv v)) (hK : ∀ v, IsCompact (K v))
    (h : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ) :
    IsCompact {a : AfP p | ∀ v, AfP.eval v a ∈ K v} := by
  let S : Set (AwayP p) := {v | K v ⊆ v.1.adicCompletionIntegers ℚ}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 h
  let P := RestrictedProduct (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (Filter.principal S)
  have h1 : IsCompact {x : P | ∀ v, x v ∈ K v} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hK
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ v -
      exact hy v
    · intro hx
      exact ⟨⟨x, fun v hv => hv (hx v trivial)⟩, fun v => hx v trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : AfP p | ∀ v, AfP.eval v a ∈ K v} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ v, x v ∈ K v} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨(LevelExists.rp a).1, fun v hv => hv (ha v)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

def basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

def tv (v : AwayP p) : AfP p ⊗[ℚ] G.C →+* Qv v ⊗[ℚ] G.C :=
  (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom

theorem repr_tv (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (tv G v y) i = AfP.eval v ((basA G).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp [tv, basV, basA, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem continuous_eval (v : AwayP p) : Continuous (AfP.eval (p := p) v) :=
  RestrictedProduct.continuous_eval v

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem tv_eq (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) :
    tv G v y = (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) := by
  apply (basV G v).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp only [Module.Basis.equivFun_apply]
  exact repr_tv G v y i

theorem continuous_tv (v : AwayP p) :
    @Continuous _ _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) (tv G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : ContinuousAdd (Qv v ⊗[ℚ] G.C) := IsModuleTopology.toContinuousAdd (Qv v) _
  have h1 : Continuous (basA G).equivFun := IsModuleTopology.continuous_of_linearMap (basA G).equivFun.toLinearMap
  have h2 : Continuous (basV G v).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.symm.toLinearMap
  have : tv G v = fun y => (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) :=
    funext (tv_eq G v)
  rw [this]
  exact h2.comp (continuous_pi fun i => (continuous_eval v).comp ((continuous_apply i).comp h1))

theorem continuous_piV (v : AwayP p) : Continuous (piV G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  have ht := continuous_tv G v
  have hval : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hinv : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hval2 : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hinv2 : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · rw [Units.continuous_iff]
    exact ⟨ht.comp hval, ht.comp hinv⟩
  · rw [Units.continuous_iff]
    exact ⟨(continuous_eval v).comp hval2, (continuous_eval v).comp hinv2⟩

end GlobalTheory.OrbFinAf.CompactOrbitVectors

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

open CompactOrbitVectors in

theorem isCompact_prod_local : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)),
    (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) →
    IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  intro p _ G D hDc hDi
  haveI : T2Space (AfP p) := inferInstanceAs
    (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _
  haveI : T2Space (AfP p ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C

  let c1 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c2 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c3 : ∀ v : AwayP p, Gv G v → Qv v := fun v h => (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v)
  let c4 : ∀ v : AwayP p, Gv G v → Qv v := fun v h =>
    ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v)
  have hc : ∀ v, (∀ i, Continuous (c1 v i)) ∧ (∀ i, Continuous (c2 v i)) ∧ Continuous (c3 v) ∧
      Continuous (c4 v) := by
    intro v
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    have hr : Continuous (basV G v).equivFun :=
      IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)))
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)))
    · exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    · exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  let K : ∀ v : AwayP p, Set (Qv v) := fun v =>
    ((⋃ i, c1 v i '' D v) ∪ (⋃ i, c2 v i '' D v)) ∪ (c3 v '' D v ∪ c4 v '' D v)
  have hKc : ∀ v, IsCompact (K v) := fun v =>
    ((isCompact_iUnion fun i => (hDc v).image ((hc v).1 i)).union
      (isCompact_iUnion fun i => (hDc v).image ((hc v).2.1 i))).union
      (((hDc v).image (hc v).2.2.1).union ((hDc v).image (hc v).2.2.2))
  have hKi : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ := by
    filter_upwards [hDi] with v hv
    rintro y ((hy | hy) | (hy | hy))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).1 i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).2.1 i
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.1
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.2
  let E : Set (AfP p) := {a | ∀ v, AfP.eval v a ∈ K v}
  have hE : IsCompact E := isCompact_box K hKc hKi
  let Bm : Set (AfP p ⊗[ℚ] G.C) := (basA G).equivFun.symm '' Set.univ.pi fun _ => E
  have hBm : IsCompact Bm := (isCompact_univ_pi fun _ => hE).image
    (IsModuleTopology.continuous_of_linearMap (basA G).equivFun.symm.toLinearMap)
  let B : Set (((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ)) :=
    (Bm ×ˢ (MulOpposite.op '' Bm)) ×ˢ (E ×ˢ (MulOpposite.op '' E))
  have hB : IsCompact B := (hBm.prod (hBm.image MulOpposite.continuous_op)).prod
    (hE.prod (hE.image MulOpposite.continuous_op))

  have hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop) := by
    let σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (AfP p) y).unop
        map_add' := fun x y ↦ by simp only [map_add, MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add, MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let emb : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hemb : Topology.IsClosedEmbedding emb :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal

  have hS : IsClosed {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
    have : {g : G.GAf | ∀ v, piV G v g ∈ D v} = ⋂ v, piV G v ⁻¹' D v := by
      ext g; simp
    rw [this]
    refine isClosed_iInter fun v => ?_
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
    haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
    haveI : T2Space (Gv G v) := inferInstance
    exact (hDc v).isClosed.preimage (continuous_piV G v)

  have hsub : emb '' {g : G.GAf | ∀ v, piV G v g ∈ D v} ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    have hco : ∀ y : AfP p ⊗[ℚ] G.C,
        (∀ v i, (basV G v).repr (tv G v y) i ∈ K v) → y ∈ Bm := by
      intro y hy
      refine ⟨(basA G).equivFun y, fun i _ v => ?_, by simp⟩
      rw [Module.Basis.equivFun_apply, ← repr_tv]
      exact hy v i
    refine ⟨⟨hco _ fun v i => ?_, ⟨_, hco _ fun v i => ?_, rfl⟩⟩, ⟨fun v => ?_, ⟨_, fun v => ?_, rfl⟩⟩⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inr (Or.inl ⟨piV G v x, hx v, rfl⟩)
    · exact Or.inr (Or.inr ⟨piV G v x, hx v, rfl⟩)
  exact hemb.isInducing.isCompact_iff.2 (hB.of_isClosed_subset (hemb.isClosedMap _ hS) hsub)

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section OnePlace

variable {P Q R S : ℕ}

def IsLift (x t : ℚ) (M : GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V) : Prop :=
  Function.Surjective pr ∧ (∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f) ∧
    ∀ Y f, M.act Y (pr f) = pr (fockAct2 P Q R S Y f) + ((t : ℂ) * Y.trace) • pr f

def Num (P Q P' Q' R S : ℕ) (κ : ℤ) : Prop :=
  R = P + Q' ∧ S = Q + P' ∧ S < P ∧ S < Q' ∧ Even (R + S) ∧ Even κ ∧ ((R + S : ℕ) : ℤ) < κ

def lam (P Q R S : ℕ) (κ : ℤ) : Ix R S → ℚ
  | .inl i => if (i : ℕ) < P then (κ : ℚ) / 2 - cPair R S + cPair P Q else cPair P Q
  | .inr j => if (j : ℕ) < Q then (κ : ℚ) / 2 + cPair R S - cPair P Q else -cPair P Q

def casK (μ : Ix R S → ℚ) : ℚ :=
  ∑ a, μ a ^ 2 + (∑ i : Fin R, μ (.inl i) * ((R : ℚ) - 1 - 2 * (i : ℕ))) + ∑ j : Fin S, μ (.inr j) * ((S : ℚ) - 1 - 2 * (j : ℕ))

def addRoot (μ : Ix R S → ℚ) (a b : Ix R S) : Ix R S → ℚ :=
  fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)

def Steep (M : GKMod R S) (Λ : Ix R S → ℚ) : Prop :=
  ∀ a b, ¬ sameBlock a b → ∀ w, IsHW M.act (addRoot Λ a b) w → casK Λ + ((R + S : ℕ) : ℚ) < casK (addRoot Λ a b)

def GenBy (M : GKMod R S) (Λ : Ix R S → ℚ) : Prop := ∃ v, IsHW M.act Λ v ∧ genSub M.act {v} = ⊤

def IsQuot (M N : GKMod R S) (π : M.V →ₗ[ℂ] N.V) : Prop :=
  Function.Surjective π ∧ ∀ Y v, π (M.act Y v) = N.act Y (π v)

def ScalarEnd (M : GKMod R S) : Prop :=
  ∀ T : M.V →ₗ[ℂ] M.V, (∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def HasForm (P Q R S : ℕ) (x : ℚ) : Prop :=
  ∃ l : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ X f, l (fockAct1 P Q R S X f) = (x : ℂ) * X.trace * l f

def IsHarmVec (x : ℚ) (μ : Ix R S → ℚ) (f : Formalism.BasicNotions.TH.Pol P Q R S) : Prop :=
  f ∈ harm2 P Q R S ∧ (∀ X, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f) ∧ IsHW (fockAct2 P Q R S) μ f

def heisOp (c : Matrix (Ix P Q) (Ix R S) ℂ) : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • ∑ l : Ln P Q R S,
    (c l.1 l.2 • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star (c l.1 l.2)) • lowB l)

def IsFrame {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (A : Matrix α (Ix P Q) ℂ) : Prop :=
  Aᵀ * M * A.map star = Jm P Q ∧ ∃ A' : Matrix (Ix P Q) α ℂ, A * A' = 1

end OnePlace

def MultOne : Prop :=
  ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v → genSub M.act {v} = ⊤ → Steep M Λ →
    ∀ w ∈ hwSub M.act Λ, ∃ c : ℂ, w = c • v

def FormEx : Prop :=
  ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ R → Q ≤ S → 0 < k → 0 < k' → x - cPair R S = k → x + cPair R S = k' →
    HasForm P Q R S x

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def atPl (w : ι) (L : Module.End ℂ (V w)) : Module.End ℂ (⨂[ℂ] i, V i) :=
  PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L)

def sumPl (L : ∀ w, Module.End ℂ (V w)) : Module.End ℂ (⨂[ℂ] i, V i) := ∑ w, atPl w (L w)

end Tensor

def LocFin {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) : Prop :=
  ∀ v, ∃ N : Submodule ℂ V, FiniteDimensional ℂ N ∧ v ∈ N ∧ ∀ y ∈ N, L y ∈ N

def IsExp {V : Type} [AddCommGroup V] [Module ℂ V] (L U : Module.End ℂ V) : Prop :=
  ∀ (v : V) (l : V →ₗ[ℂ] ℂ), HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) (l (U v))

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}

variable (F) in

abbrev Tens (P Q R S : ℕ) : Type := ⨂[ℂ] _ : InfinitePlace F, Formalism.BasicNotions.TH.Pol P Q R S

def SD (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ) : Prop :=
  ∀ g ∈ SB (κ → Af F), ∀ l ∈ (adeleClass F).adm κ, HasDerivAt (fun t => l (T t (pureA F f g))) (l (pureA F f₁ g)) 0

def SA (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ) : Prop :=
  ∀ g ∈ SB (κ → Af F), T (pureA F f g) = pureA F f₁ g

def Framed (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ) : Prop :=
  a * b = Complex.I ∧ (∀ w, IsFrame (a • JA.map (piInf (τ w))) (A w)) ∧ ∀ w, IsFrame (b • JB.map (piInf (τ w))) (C w)

def IsFockMap (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) : Prop :=
  Function.Injective Φ ∧ ∀ u : Matrix α β (AE F E), At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      ∀ T, SD (fun t => d.rho ψ (realAd F t • u)) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))

variable (σ) in

def RLines (J : Matrix β β (AE F E)) : Set (Multiplicative ℝ →* UG (cA σ) J) :=
  {γ | Continuous γ ∧ ∀ t, At (evI F) (((γ t).1 : Matrix β β (AE F E)) - 1)}

def IsGen (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (γ : Multiplicative ℝ →* UG (cA σ) J) (Y : InfinitePlace F → Mat R S) : Prop :=
  ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
    C w * NormedSpace.exp (t • Y w)

def ActsBy (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {r s : ℕ}
    (C : InfinitePlace F → Matrix β (Ix r s) ℂ) (om : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ))
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (act : Mat r s →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (c : InfinitePlace F → ℂ) : Prop :=
  ∀ γ ∈ RLines σ J, ∀ Y, IsGen τ C γ Y → ∀ T, SD (fun t => om (γ (Multiplicative.ofAdd t))) (Φ T)
    (Φ (sumPl (fun w => act (Y w) + (c w * (Y w).trace) • 1) T))

end Adelic

def ActsLaws : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f f₁ f₂ : SInf F κ),
    (∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, (∀ t, T t 0 = 0) → SD T f f₁ → ActsD (evI F) T f f₁) ∧
    (∀ T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, T 0 = 0 → SA T f f₁ → Acts (evI F) T f f₁) ∧
    (∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, ActsD (evI F) T f f₁ → ActsD (evI F) T f f₂ → f₁ = f₂) ∧
    (∀ T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, Acts (evI F) T f f₁ → Acts (evI F) T f f₂ → f₁ = f₂) ∧
    ∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, SD T f f₁ → SD T f f₂ → f₁ = f₂

def DerEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ →
    ∃ D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ), ∀ u, At (evI F) u → ∀ f,
      SD (fun t => d.rho ψ (realAd F t • u)) f (D u f) ∧ ∀ x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x

def FockEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C →
    ∃ Φ, IsFockMap ψ τ d A C Φ

def VacLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1)

def GenEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ γ ∈ RLines σ J, ∃ Y, (∀ w, Y w ∈ upq R S) ∧ IsGen τ C γ Y

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : InfinitePlace F → Mat R S, (∀ w, Y w ∈ upq R S) → ∃ γ ∈ RLines σ J, IsGen τ C γ Y

def LieScalar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsBy τ C om Φ (fockAct2 P Q R S) c

def LieSecond : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsUWeilB (cA σ) (adeleClass F) ψ (-1) JA JB d χ om → HasExp τ χ m →
    ActsBy τ C om Φ (fockAct2 P Q R S) fun w => (m w : ℂ) / 2

def LieFirst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)) (χ : Chr F E)
    (m : InfinitePlace F → ℤ), IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUWeilB (cA σ) (adeleClass F) ψ (-1) JB JA d' χ om → HasExp τ χ m →
    ActsBy τ A om Φ (fockAct1 P Q R S) fun w => (m w : ℂ) / 2

def KLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (θ : InfinitePlace F → Matrix β β ℂ), IsCMExt F E σ →
    (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) → (∀ w, θ w * C w = C w * Jm R S) → ∀ k : UG (cA σ) J,
    At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) → (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) →
    ∃ γ ∈ RLines σ J, ∃ Y, IsGen τ C γ Y ∧ (∀ w, IsKC (Y w)) ∧ γ (Multiplicative.ofAdd 1) = k

def FrameEx : Prop :=
  ∀ (n r s : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), HasSig M r s → IsCartan M θ →
    ∃ A : Matrix (Fin n) (Ix r s) ℂ, IsFrame M A ∧ θ * A = A * Jm r s

def PolRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d P Q R S : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → IsStd ψ →
    Framed τ (incM F X.J) (incM F W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm P Q) →
    (∀ w, W.θ w * C w = C w * Jm R S) → IsFockMap ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ

def Parity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ w, Even (B.mα w - B.mβ w)

theorem lines_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (X : Spc F E n) : Lines σ X = RLines σ (incM F X.J) := rfl

example : IsFrame (P := 1) (Q := 1) (Jm 1 1) 1 := ⟨by simp [Matrix.map_one], 1, by simp⟩

end GlobalTheory.RealLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulIntStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ), (∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) → IsIntegral ℤ ((M : ℤ) • x) := by
  first | (exact @GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (exact GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (intros; apply GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTopStatement
section
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x → LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  first | exact @GlobalTheory.LogDR.logWedge_basis | exact GlobalTheory.LogDR.logWedge_basis | (intros; apply GlobalTheory.LogDR.logWedge_basis <;> assumption)
end

