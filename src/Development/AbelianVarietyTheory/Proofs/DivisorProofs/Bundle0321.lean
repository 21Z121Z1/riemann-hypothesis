import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacquetBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem hasFiniteLength_twist_iff (ρ : Representation F G V) (χ : G →* Fˣ) :
    HasFiniteLength (twist ρ χ) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.apply_mem_toSubmodule g hv
        rw [twist_apply] at h1
        have h2 := S.toSubmodule.smul_mem ((χ g : F)⁻¹) h1
        rwa [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        rw [twist_apply]
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩

theorem hasFiniteLength_of_surjective {ρ : Representation F G V} {σ : Representation F G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (h : HasFiniteLength ρ) :
    HasFiniteLength σ :=
  IsFiniteLength.of_surjective h
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

end General

section Blocks

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem mem_unipRad_iff_blk {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ g ∈ parab R e ∧
      ∀ i j, blk e i = blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  refine and_congr_right fun _ => ⟨fun h i j hij => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    subst hij
    rw [h a x y]
    simp [Matrix.one_apply, e.injective.eq_iff]
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply, e.injective.eq_iff]

omit [LinearOrder α] in

theorem leviEmb_apply_of_blk_ne (e : (Σ a, m a) ≃ n) (g : Levi R m) {i j : n}
    (h : blk e i ≠ blk e j) : (leviEmb R e g : Matrix n n R) i j = 0 := by
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  exact leviEmb_apply_ne R e g (by simpa using h) x y

theorem leviEmb_leviProj_of_blk (e : (Σ a, m a) ≃ n) (p : parab R e)
    (h : ∀ i j, blk e i ≠ blk e j → ((p : GL n R) : Matrix n n R) i j = 0) :
    leviEmb R e (leviProj R e p) = p := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviProj_apply]
  · rw [leviEmb_apply_ne R e _ hab, h _ _ (by simpa using hab)]

theorem leviProj_eq_of_coe_eq (e : (Σ a, m a) ≃ n) (p : parab R e) (g : Levi R m)
    (h : (p : GL n R) = leviEmb R e g) : leviProj R e p = g := by
  rcases p with ⟨p, hp⟩
  simp only at h
  subst h
  exact leviProj_leviEmb R e g

end Blocks

section Transport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_of_transport (e : (Σ a, m a) ≃ n) (e' : (Σ b, m' b) ≃ n')
    (Φ : GL n' k →* GL n k) (Ψ : Levi k m' →* Levi k m) (hΨ : Function.Surjective Ψ)
    (hU : ∀ u ∈ unipRad k e', Φ u ∈ unipRad k e)
    (hL : ∀ g, Φ (leviEmb k e' g) = leviEmb k e (Ψ g)) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e' (π.comp Φ))) : HasFiniteLength (jacU e π) := by
  have hle : twKer (π.comp Φ) (unipRad k e') 1 ≤ twKer π (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨Φ u, hU u u.2⟩, v, by simp⟩
  let f : (jacU e' (π.comp Φ)).IntertwiningMap ((jacU e π).comp Ψ) :=
    ⟨(twKer (π.comp Φ) (unipRad k e') 1).mapQ (twKer π (unipRad k e) 1) LinearMap.id hle,
      fun g => by
        ext v
        show Submodule.Quotient.mk (π (Φ (leviEmb k e' g)) v) =
          (Submodule.Quotient.mk (π (leviEmb k e (Ψ g)) v) : Jacquet π (unipRad k e))
        rw [hL]⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  rw [← hasFiniteLength_comp_iff _ Ψ hΨ]
  exact hasFiniteLength_of_surjective f hf h

end Transport

section Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_reindex (e : (Σ b, m' b) ≃ n') (ψ : n' ≃ n)
    (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e (π.comp
      (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom))) :
    HasFiniteLength (jacU (e.trans ψ) π) := by
  set Φ : GL n' k →* GL n k := (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦ : ∀ (g : GL n' k) (i j : n), (Φ g : Matrix n n k) i j = (g : Matrix n' n' k) (ψ.symm i) (ψ.symm j) :=
    fun _ _ _ => rfl
  refine hasFiniteLength_jacU_of_transport (e.trans ψ) e Φ (MonoidHom.id _) Function.surjective_id
    (fun u hu => ?_) (fun g => ?_) π h
  · rw [mem_unipRad] at hu ⊢
    refine ⟨mem_parab_iff.2 fun a b x y hab => ?_, fun a x y => ?_⟩
    · rw [hΦ]
      simpa using mem_parab_iff.1 hu.1 a b x y hab
    · rw [hΦ]
      simpa using hu.2 a x y
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [hΦ]
    obtain ⟨⟨a, x⟩, rfl⟩ := (e.trans ψ).surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := (e.trans ψ).surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, MonoidHom.id_apply]
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, show ψ (e ⟨a, x⟩) = (e.trans ψ) ⟨a, x⟩ from rfl,
        show ψ (e ⟨a, y⟩) = (e.trans ψ) ⟨a, y⟩ from rfl, leviEmb_apply_same]
    · rw [leviEmb_apply_ne k e _ hab, show ψ (e ⟨a, x⟩) = (e.trans ψ) ⟨a, x⟩ from rfl,
        show ψ (e ⟨b, y⟩) = (e.trans ψ) ⟨b, y⟩ from rfl, leviEmb_apply_ne k _ _ hab]

theorem hasFiniteLength_jacU_relabel (e : (Σ a, m a) ≃ n) (s : (Σ b, m' b) ≃ (Σ a, m a))
    (f : β → α) (hf : StrictMono f) (hs : ∀ x, (s x).1 = f x.1) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU (s.trans e) π)) : HasFiniteLength (jacU e π) := by
  set e₁ := s.trans e
  have hblk : ∀ i, blk e i = f (blk e₁ i) := fun i => by
    have := hs (s.symm (e.symm i))
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hlt : ∀ i j, blk e i < blk e j ↔ blk e₁ i < blk e₁ j := fun i j => by
    rw [hblk, hblk, hf.lt_iff_lt]
  have heq : ∀ i j, blk e i = blk e j ↔ blk e₁ i = blk e₁ j := fun i j => by
    rw [hblk, hblk, hf.injective.eq_iff]
  have hpar : ∀ g : GL n k, g ∈ parab k e ↔ g ∈ parab k e₁ := fun g => by
    rw [mem_parab, mem_parab]
    exact forall_congr' fun i => forall_congr' fun j => by rw [hlt]
  let Ψ : Levi k m' →* Levi k m := (leviProj k e).comp ((leviEmb k e₁).codRestrict (parab k e)
    fun g => (hpar _).2 (leviEmb_mem_parab k e₁ g))
  have hL : ∀ g, leviEmb k e₁ g = leviEmb k e (Ψ g) := fun g => by
    refine (leviEmb_leviProj_of_blk (R := k) e ⟨leviEmb k e₁ g, (hpar _).2 (leviEmb_mem_parab k e₁ g)⟩
      fun i j hij => ?_).symm
    exact leviEmb_apply_of_blk_ne e₁ g fun h' => hij ((heq i j).2 h')
  have hΨ : Function.Surjective Ψ := by
    intro g
    refine ⟨leviProj k e₁ ⟨leviEmb k e g, (hpar _).1 (leviEmb_mem_parab k e g)⟩, ?_⟩
    refine leviProj_eq_of_coe_eq (R := k) e _ g ?_
    exact leviEmb_leviProj_of_blk (R := k) e₁ _ fun i j hij =>
      leviEmb_apply_of_blk_ne e g fun h' => hij ((heq i j).1 h')
  refine hasFiniteLength_jacU_of_transport e e₁ (MonoidHom.id _) Ψ hΨ (fun u hu => ?_)
    (fun g => hL g) π h
  rw [mem_unipRad_iff_blk] at hu ⊢
  exact ⟨(hpar _).2 hu.1, fun i j hij => hu.2 i j ((heq i j).1 hij)⟩

end Stages

theorem jacquetFiniteLength_of_standard :
    GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k]
      [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  intro hP k _ _ _ _ α n m _ _ _ _ _ _ e V _ _ π hπ hl
  classical
  let α' := {a : α // Nonempty (m a)}
  let o : Fin (Fintype.card α') ≃o α' := monoEquivOfFin α' rfl
  let d : Fin (Fintype.card α') → ℕ := fun i => Fintype.card (m (o i).1)
  have hd : ∀ i, 0 < d i := fun i => Fintype.card_pos_iff.2 (o i).2
  let T : (Σ a' : α', m a'.1) ≃ (Σ a, m a) :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, ⟨x.2⟩⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let s : (Σ i, Fin (d i)) ≃ (Σ a, m a) :=
    ((Equiv.sigmaCongrRight fun i => (Fintype.equivFin (m (o i).1)).symm).trans
      (Equiv.sigmaCongrLeft (β := fun a' : α' => m a'.1) o.toEquiv)).trans T
  have hs : ∀ x, (s x).1 = (fun i => (o i).1) x.1 := by
    rintro ⟨i, j⟩
    rfl
  have hf : StrictMono (fun i => (o i).1) := fun i j h => o.strictMono h
  let e₁ := s.trans e
  let ψ : Fin (∑ i, d i) ≃ n := finSigmaFinEquiv.symm.trans e₁
  let Φ : GL (Fin (∑ i, d i)) k →* GL n k :=
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦs : Function.Surjective Φ := (Units.mapEquiv _).surjective
  have hΦc : Continuous Φ := by
    refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
    · exact Units.continuous_val.matrix_elem (ψ.symm i) (ψ.symm j)
    · exact Units.continuous_coe_inv.matrix_elem (ψ.symm i) (ψ.symm j)
  have h1 := (hP k _ d hd).1 V (π.comp Φ) (isSmooth_comp hπ Φ hΦc)
    ((hasFiniteLength_comp_iff π Φ hΦs).2 hl)
  have h2 : HasFiniteLength (jacU (finSigmaFinEquiv.trans ψ) π) :=
    hasFiniteLength_jacU_reindex _ ψ π
      ((hasFiniteLength_twist_iff (jacU finSigmaFinEquiv (π.comp Φ)) _).1 h1)
  have he : finSigmaFinEquiv.trans ψ = e₁ := by
    ext x
    simp [ψ]
  rw [he] at h2
  exact (hasFiniteLength_twist_iff (jacU e π) (deltaHalf k m)⁻¹).2
    (hasFiniteLength_jacU_relabel e s _ hf hs π h2)

end GlobalTheory.JacquetBlocks

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTransposeInvTranspose
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion Matrix
open scoped TensorProduct

namespace GlobalTheory.InvTransposeEnds

section General

variable {G H V W Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem isIrreducible_comp {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (φ : H →* G)
    (hφ : Function.Surjective φ) : Representation.IsIrreducible (ρ.comp φ) := by
  haveI hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule, fun g v hv => by
      obtain ⟨x, rfl⟩ := hφ g
      exact S.apply_mem_toSubmodule x hv⟩
    rcases h.eq_bot_or_eq_top S' with e | e
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))

end General

section Matrices

variable {k : Type} [Field k]

theorem invTranspose_invTranspose (n : ℕ) (g : GL (Fin n) k) :
    invTranspose n k (invTranspose n k g) = g := by
  apply Units.ext
  show ((invTranspose n k g)⁻¹ : GL (Fin n) k).valᵀ = g.val
  rw [← map_inv]
  show ((g⁻¹)⁻¹ : GL (Fin n) k).valᵀᵀ = g.val
  rw [inv_inv, transpose_transpose]

def swapT (k : Type) [Field k] (a c : ℕ) : GL (Fin a) k × GL (Fin c) k ≃* GL (Fin c) k × GL (Fin a) k where
  toFun g := (invTranspose c k g.2, invTranspose a k g.1)
  invFun g := (invTranspose a k g.2, invTranspose c k g.1)
  left_inv g := Prod.ext (invTranspose_invTranspose _ _) (invTranspose_invTranspose _ _)
  right_inv g := Prod.ext (invTranspose_invTranspose _ _) (invTranspose_invTranspose _ _)
  map_mul' g g' := Prod.ext (map_mul (invTranspose c k) g.2 g'.2) (map_mul (invTranspose a k) g.1 g'.1)

section Blocks

variable {b N : ℕ} (h : b + 1 = N) (h' : 1 + b = N)

variable {h h'} {w : GL (Fin N) k}
  (hw : Placing.Moves (stdSum h) ((Equiv.sumComm _ _).trans (stdSum h')) w)
include hw

end Blocks

end Matrices

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

end Local

end GlobalTheory.InvTransposeEnds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.FunObj
open Matrix

section Ratio
variable {G : Type*} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / A.relIndex B

theorem idxRatio_eq_of_le {A B D : Subgroup G} (hD : D ≤ A ⊓ B) (h0 : D.relIndex (A ⊓ B) ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / D.relIndex B := by
  have h1 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hD inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hD inf_le_right
  have e1 : (A ⊓ B).relIndex A = B.relIndex A := by rw [inf_comm]; exact Subgroup.inf_relIndex_right B A
  have e2 : (A ⊓ B).relIndex B = A.relIndex B := Subgroup.inf_relIndex_right A B
  rw [idxRatio, ← h1, ← h2, e1, e2]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast h0)]

theorem idxRatio_map {f : G →* G} (hf : Function.Injective f) (A B : Subgroup G) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  rw [idxRatio, idxRatio, Subgroup.relIndex_map_map_of_injective _ _ hf,
    Subgroup.relIndex_map_map_of_injective _ _ hf]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_inf_ne_zero {N O C H : Subgroup G} (hO : IsOpen (O : Set G)) (hC : IsCompact (C : Set G))
    (hHN : H ≤ N) (hHC : H ≤ C) : (N ⊓ O).relIndex H ≠ 0 := by
  intro h
  have h1 : O ⊓ H ≤ N ⊓ O := fun x hx => Subgroup.mem_inf.2 ⟨hHN (Subgroup.mem_inf.1 hx).2, (Subgroup.mem_inf.1 hx).1⟩
  have h2 := Subgroup.relIndex_eq_zero_of_le_left h1 h
  rw [Subgroup.inf_relIndex_right] at h2
  exact relIndex_ne_zero_of_isOpen hO hC hHC h2

theorem idxRatio_cocycle (N : Subgroup G) {U V W : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVc : IsCompact (V : Set G))
    (hWo : IsOpen (W : Set G)) (hWc : IsCompact (W : Set G)) :
    idxRatio (N ⊓ U) (N ⊓ V) * idxRatio (N ⊓ V) (N ⊓ W) = idxRatio (N ⊓ U) (N ⊓ W) := by
  have hO : IsOpen ((U ⊓ V ⊓ W : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf, Subgroup.coe_inf]; exact (hUo.inter hVo).inter hWo
  have l1 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ V) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l2 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ V) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l3 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have nV : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) ≠ 0 := relIndex_inf_ne_zero hO hVc inf_le_left inf_le_right
  have nW : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) ≠ 0 := relIndex_inf_ne_zero hO hWc inf_le_left inf_le_right
  rw [idxRatio_eq_of_le l1 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l2 (relIndex_inf_ne_zero hO hVc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l3 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right))]
  have nV' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) : ℚ) ≠ 0 := by exact_mod_cast nV
  have nW' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) : ℚ) ≠ 0 := by exact_mod_cast nW
  field_simp

end Ratio

section Diag
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem diagGL_mul' (d e : n → kˣ) : diagGL (d * e) = diagGL d * diagGL e :=
  Units.ext (by simp [diagonal_mul_diagonal])

theorem diagGL_inv' (d : n → kˣ) : diagGL d⁻¹ = (diagGL d)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagGL_mul']; exact Units.ext (by simp))

theorem conj_diagGL_InN {p : ℕ} (d : n ⊕ Fin c → kˣ) {x : GL (n ⊕ Fin c) k} (hx : InN p x) :
    InN p (MulAut.conj (diagGL d) x) := by
  intro r s hrs
  have h := hx r s hrs
  have hinv : ((diagGL d)⁻¹ : GL (n ⊕ Fin c) k).val = diagonal fun i => (((d i)⁻¹ : kˣ) : k) := rfl
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, hinv, diagGL_val, mul_diagonal, diagonal_mul, h]
  by_cases hrs' : r = s
  · subst hrs'; simp
  · simp [hrs']

theorem map_conj_diagGL_N_le (p : ℕ) (d : n ⊕ Fin c → kˣ) :
    (N k n c p).map (MulAut.conj (diagGL d)).toMonoidHom ≤ N k n c p := by
  rw [N, MonoidHom.map_closure]
  exact (Subgroup.closure_le _).2 (by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (conj_diagGL_InN d hx))

theorem map_conj_diagGL_symN (d : n ⊕ Fin c → kˣ) :
    (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom = symN k n c := by
  have hle : ∀ d : n ⊕ Fin c → kˣ, (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom ≤ symN k n c := by
    intro d
    rw [symN, Subgroup.map_sup]
    exact sup_le_sup (map_conj_diagGL_N_le _ d) (map_conj_diagGL_N_le _ d)
  refine le_antisymm (hle d) ?_
  have h := Subgroup.map_mono (f := (MulAut.conj (diagGL d)).toMonoidHom) (hle d⁻¹)
  have e : (MulAut.conj (diagGL d)).toMonoidHom.comp (MulAut.conj (diagGL d⁻¹)).toMonoidHom = MonoidHom.id _ := by
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply, diagGL_inv']
    group
  rwa [Subgroup.map_map, e, Subgroup.map_id] at h

end Diag

end GlobalTheory.FunObj

namespace GlobalTheory.FunObj
open Matrix

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem relIndex_congr_inf {G : Type*} [Group G] {A B L : Subgroup G} (h : A ⊓ L = B ⊓ L) :
    A.relIndex L = B.relIndex L := by
  rw [← Subgroup.inf_relIndex_right A L, h, Subgroup.inf_relIndex_right]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem invVol_eq_idxRatio (C : Subgroup (GL (n ⊕ Fin c) k)) :
    invVol C = idxRatio (symN k n c ⊓ KO k _) (symN k n c ⊓ C) := by
  rw [invVol, idxRatio, relIndex_congr_inf (A := C) (B := symN k n c ⊓ C),
    relIndex_congr_inf (A := KO k _) (B := symN k n c ⊓ KO k _)]
  · ext x; simp only [Subgroup.mem_inf]; tauto
  · ext x; simp only [Subgroup.mem_inf]; tauto

theorem isOpen_map_conj_KO (x : GL (n ⊕ Fin c) k) :
    IsOpen (((KO k (n ⊕ Fin c)).map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (GL (n ⊕ Fin c) k)) := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact isOpen_KO.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_map_conj_KO (x : GL (n ⊕ Fin c) k) :
    IsCompact (((KO k (n ⊕ Fin c)).map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (GL (n ⊕ Fin c) k)) :=
  isCompact_KO.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem invVol_conj_diagGL_mul (d e : n ⊕ Fin c → kˣ) :
    invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) =
      invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) *
        invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  have hmapN : ∀ (d : n ⊕ Fin c → kˣ) (K' : Subgroup (GL (n ⊕ Fin c) k)),
      (symN k n c ⊓ K').map (MulAut.conj (diagGL d)).toMonoidHom =
        symN k n c ⊓ K'.map (MulAut.conj (diagGL d)).toMonoidHom := by
    intro d K'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (diagGL d)).injective, map_conj_diagGL_symN]
  have hcomp : (KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom =
      ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom).map
        (MulAut.conj (diagGL d)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, diagGL_mul']
    group
  rw [invVol_eq_idxRatio, invVol_eq_idxRatio, invVol_eq_idxRatio, hcomp,
    ← idxRatio_cocycle (symN k n c) isOpen_KO isCompact_KO (isOpen_map_conj_KO (diagGL d))
      (isCompact_map_conj_KO (diagGL d)) (hcomp ▸ isOpen_map_conj_KO (diagGL (d * e)))
      (hcomp ▸ isCompact_map_conj_KO (diagGL (d * e)))]
  congr 1
  rw [← hmapN d (KO k _), ← hmapN d ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom),
    idxRatio_map (MulAut.conj (diagGL d)).injective]

end Main

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainMonicRootsOfIsIndEtaleLocalStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O], IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  first | (exact @GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (exact GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (intros; apply GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderPicOfIsReducedFiniteIntStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_pic_of_isReduced_finite_int : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B), IsOfFinOrder M := by
  first | exact @GlobalTheory.PicReducedTors.pic_isOfFinOrder | exact GlobalTheory.PicReducedTors.pic_isOfFinOrder | (intros; apply GlobalTheory.PicReducedTors.pic_isOfFinOrder <;> assumption)
end

