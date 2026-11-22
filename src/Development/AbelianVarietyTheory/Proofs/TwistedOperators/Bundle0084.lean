import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryQuotient
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.GKQuot

variable {p q : ℕ}

def quotAct (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z)) :
    Mat p q →ₗ[ℂ] Module.End ℂ (M.V ⧸ N) where
  toFun Z := N.mapQ N (M.act Z) (hN Z)
  map_add' Z W := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_smul' c Z := by
    apply Submodule.linearMap_qext
    ext x
    simp

theorem quotAct_mk (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z))
    (Z : Mat p q) (x : M.V) : quotAct M N hN Z (N.mkQ x) = N.mkQ (M.act Z x) := rfl

def quotMod (M : GKMod p q) (N : Submodule ℂ M.V) (hN : ∀ Z, N ≤ N.comap (M.act Z)) :
    GKMod p q where
  V := M.V ⧸ N
  act := quotAct M N hN
  lie X Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    rw [quotAct_mk, M.lie X Y]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, quotAct_mk, map_sub]
  kfin v := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    obtain ⟨W, hW, hx, hK⟩ := M.kfin x
    refine ⟨W.map N.mkQ, inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    rw [quotAct_mk]
    exact Submodule.mem_map_of_mem (hK X hX w hw)
  wts v := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (quotAct M N hN) μ).comap N.mkQ := by
      refine iSup_le fun μ y hy => ?_
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      intro a
      rw [quotAct_mk, ← map_smul, ← map_sub, hy a, map_zero]
    exact h (M.wts x)

theorem exists_unitary_quotient (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H)
    (hE : ∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) :
    ∃ (A : UGKMod p q) (f : M.V →ₗ[ℂ] A.M.V) (Eb : A.M.V →ₗ[ℂ] H), Function.Surjective f ∧
      Function.Injective Eb ∧ (∀ x, Eb (f x) = E x) ∧ ∀ Z x, f (M.act Z x) = A.M.act Z (f x) := by

  let N : Submodule ℂ M.V := LinearMap.ker E
  have hN : ∀ Z, N ≤ N.comap (M.act Z) := by
    intro Z x hx
    have hx' : E x = 0 := hx
    show E (M.act Z x) = 0
    have h := hE Z x (M.act Z x)
    rw [hx', inner_zero_left] at h
    exact inner_self_eq_zero.mp h

  let Eb : M.V ⧸ N →ₗ[ℂ] H := N.liftQ E le_rfl
  have hEb : ∀ x, Eb (N.mkQ x) = E x := fun x => N.liftQ_apply E x
  have hinj : Function.Injective Eb := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    obtain ⟨x, rfl⟩ := N.mkQ_surjective v
    rw [LinearMap.mem_ker, hEb] at hv
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr hv
  have hact : ∀ Z x, quotAct M N hN Z (N.mkQ x) = N.mkQ (M.act Z x) := quotAct_mk M N hN

  let ip : M.V ⧸ N →ₗ⋆[ℂ] M.V ⧸ N →ₗ[ℂ] ℂ := ((innerₛₗ ℂ).comp Eb).compl₂ Eb
  let A : UGKMod p q :=
    { M := quotMod M N hN
      ip := ip
      herm := by
        intro v w
        show star (inner ℂ (Eb v) (Eb w)) = inner ℂ (Eb w) (Eb v)
        exact inner_conj_symm (Eb w) (Eb v)
      pos := by
        intro v hv
        have hne : Eb v ≠ 0 := fun h0 => hv (hinj (h0.trans (map_zero Eb).symm))
        have h : 0 < RCLike.re (inner ℂ (Eb v) (Eb v)) := by
          rw [inner_self_eq_norm_sq]
          exact pow_pos (norm_pos_iff.mpr hne) 2
        show 0 < (inner ℂ (Eb v) (Eb v)).re
        exact h
      adj := by
        intro Z v w
        obtain ⟨x, rfl⟩ := N.mkQ_surjective v
        obtain ⟨y, rfl⟩ := N.mkQ_surjective w
        show inner ℂ (Eb (quotAct M N hN Z (N.mkQ x))) (Eb (N.mkQ y)) =
          inner ℂ (Eb (N.mkQ x)) (Eb (quotAct M N hN (adjZ Z) (N.mkQ y)))
        rw [hact, hact, hEb, hEb, hEb, hEb]
        exact hE Z x y }
  exact ⟨A, N.mkQ, Eb, N.mkQ_surjective, hinj, hEb, fun Z x => (hact Z x).symm⟩

end GlobalTheory.GKQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSimpleModuleOfFinrankEnd
section
open GlobalTheory.GLq Polynomial
open scoped Classical

namespace GlobalTheory.AbsIrrDescent

theorem isSimpleModule_of_finrank_end {k R M : Type} [Field k] [Ring R] [Algebra k R] [AddCommGroup M] [Module R M]
    [Module k M] [IsScalarTower k R M] [SMulCommClass R k M] [IsSemisimpleModule R M]
    (h : Module.finrank k (Module.End R M) = 1) : IsSimpleModule R M := by
  have hE : Nontrivial (Module.End R M) := Module.nontrivial_of_finrank_eq_succ h
  have hM : Nontrivial M := by
    by_contra hM
    rw [not_nontrivial_iff_subsingleton] at hM
    exact not_subsingleton (Module.End R M) inferInstance
  have : Nontrivial (Submodule R M) := (Submodule.nontrivial_iff R).2 hM
  refine { eq_bot_or_eq_top := fun U => ?_ }
  obtain ⟨U', hU⟩ := exists_isCompl U
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : Module.End R M) one_ne_zero).1 h
    (U.subtype ∘ₗ U.projectionOnto U' hU)
  by_cases h0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := LinearMap.congr_fun hc x
    rw [h0, zero_smul] at this
    have h2 : (U.subtype ∘ₗ U.projectionOnto U' hU) x = x := by
      simpa using congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨x, hx⟩)
    rw [← h2, ← this]; rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have := LinearMap.congr_fun hc (c⁻¹ • x)
    have h2 : (c • (1 : Module.End R M)) (c⁻¹ • x) = x := by
      simp [smul_smul, h0]
    rw [← h2, this]
    exact Subtype.property _

theorem isIrreducible_of_norm_one {k G V : Type} [Field k] [CharZero k] [Group G] [Fintype G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (hn : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : k)) : ρ.IsIrreducible := by
  have hc : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have : NeZero (Nat.card G : k) := ⟨hc⟩
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [hn, inv_mul_cancel₀ hc, eq_comm, Nat.cast_eq_one] at h
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine isSimpleModule_of_finrank_end (k := k) ?_
  rw [← h]
  exact (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toLinearEquiv.finrank_eq.symm

theorem isAbsIrrChar_of_isIrr : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (χ : G → K), IsIrr (fun t => σ (χ t)) → Formalism.L2.DIV.IsAbsIrrChar χ := by
  intro K _ σ G _ _ χ h
  obtain ⟨V, hV, hχ⟩ := h
  haveI : CharZero K := σ.charZero
  letI : Algebra K ℂ := σ.toAlgebra
  let τ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) ℂ := τ.toRingHom.toAlgebra
  have hτ : ∀ x : K, algebraMap (AlgebraicClosure K) ℂ (algebraMap K (AlgebraicClosure K) x) = σ x :=
    fun x => τ.commutes x
  have hinj : Function.Injective (algebraMap (AlgebraicClosure K) ℂ) := RingHom.injective _
  have hm : Nat.card G ≠ 0 := Nat.card_pos.ne'
  haveI : NeZero (Nat.card G) := ⟨hm⟩
  haveI : NeZero (Nat.card G : AlgebraicClosure K) := ⟨Nat.cast_ne_zero.2 hm⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) (Nat.card G)
  have hch : GlobalTheory.BI.IsChar ℂ ℂ (fun t => σ (χ t)) := by
    have h := (GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G V V.ρ).1
    have e : (fun t => σ (χ t)) = fun g => algebraMap ℂ ℂ (Representation.character V.ρ g) := by
      funext g
      exact (hχ g).symm
    rw [e]
    exact h
  obtain ⟨n, ρ, hρ⟩ := GlobalTheory.BI.isChar_of_isPrimitiveRoot (AlgebraicClosure K) ℂ (Nat.card G) ζ hm hζ G
    (fun g => pow_card_eq_one') _ hch
  have hρ' : ∀ t, ρ.character t = algebraMap K (AlgebraicClosure K) (χ t) := fun t =>
    hinj (by rw [hτ]; exact (hρ t).symm)
  refine ⟨n, ρ, isIrreducible_of_norm_one ρ (hinj ?_), hρ'⟩
  have hn := (FDRep.simple_iff_char_is_norm_one V).1 hV
  rw [map_natCast, ← hn, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, hρ', hρ', hτ, hτ, hχ, hχ]

end GlobalTheory.AbsIrrDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormProportionalOfIrreducible
section
noncomputable section
namespace GlobalTheory.FockTensor
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem exists_repr_on_finiteDimensional {V H : Type} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : V →ₗ[ℂ] H) (hE : Function.Injective E)
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (f : V →ₗ[ℂ] ℂ) :
    ∃ a ∈ W, ∀ x ∈ W, inner ℂ (E a) (E x) = f x := by
  classical
  let e : W ≃ₗ[ℂ] W.map E := Submodule.equivMapOfInjective E hE W
  haveI : FiniteDimensional ℂ (W.map E) := LinearEquiv.finiteDimensional e
  haveI : CompleteSpace (W.map E) := FiniteDimensional.complete ℂ (W.map E)
  let g : W.map E →ₗ[ℂ] ℂ := (f.comp W.subtype).comp e.symm.toLinearMap
  let v : W.map E := (InnerProductSpace.toDual ℂ (W.map E)).symm (LinearMap.toContinuousLinearMap g)
  refine ⟨(e.symm v : V), (e.symm v).2, fun x hx => ?_⟩
  have h1 : E (e.symm v : V) = (v : H) := congrArg Subtype.val (e.apply_symm_apply v)
  calc inner ℂ (E (e.symm v : V)) (E x) = inner ℂ v (e ⟨x, hx⟩) := by
          rw [h1, Submodule.coe_inner]; rfl
    _ = g (e ⟨x, hx⟩) := InnerProductSpace.toDual_symm_apply
    _ = f x := by simp [g]

theorem mem_hwSub_iff_eigen {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧
      ∀ a b, posC a b → act (Eab a b) v = (0 : ℂ) • v := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, zero_smul]

theorem norm_proportional_of_irreducible (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ)
    (H₁ H₂ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (E₁ : M.V →ₗ[ℂ] H₁) (E₂ : M.V →ₗ[ℂ] H₂) (hirr : IrrGK M)
    (hΛ : Module.finrank ℂ ↥(hwSub M.act Λ) = 1) (hE : Function.Injective E₁)
    (h₁ : ∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₁ y) = inner ℂ (E₁ x) (E₁ (M.act (adjZ Z) y)))
    (h₂ : ∀ Z x y, inner ℂ (E₂ (M.act Z x)) (E₂ y) = inner ℂ (E₂ x) (E₂ (M.act (adjZ Z) y))) :
    ∃ c : ℝ, ∀ y, ‖E₂ y‖ = c * ‖E₁ y‖ := by
  classical
  obtain ⟨v₀s, hv₀s, hspan⟩ := finrank_eq_one_iff'.mp hΛ
  set v₀ : M.V := (v₀s : M.V) with hv₀def
  have hv₀ : v₀ ≠ 0 := fun h => hv₀s (Subtype.ext h)
  have hE₁v₀ : E₁ v₀ ≠ 0 := fun h => hv₀ (hE (by rw [h, map_zero]))

  set r : ℝ := ‖E₂ v₀‖ ^ 2 / ‖E₁ v₀‖ ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hn1 : ‖E₁ v₀‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hE₁v₀)
  have hrr : r * ‖E₁ v₀‖ ^ 2 = ‖E₂ v₀‖ ^ 2 := div_mul_cancel₀ _ hn1

  let ψ : M.V → M.V →ₗ[ℂ] ℂ := fun x =>
    (innerₛₗ ℂ (E₂ x)).comp E₂ - (r : ℂ) • (innerₛₗ ℂ (E₁ x)).comp E₁
  have hψ : ∀ x y, ψ x y = inner ℂ (E₂ x) (E₂ y) - (r : ℂ) * inner ℂ (E₁ x) (E₁ y) := by
    intro x y
    first
      | rfl
      | simp [ψ]
  have hψinv : ∀ Z x y, ψ (M.act Z x) y = ψ x (M.act (adjZ Z) y) := by
    intro Z x y
    rw [hψ, hψ, h₁, h₂]
  have hψsmul : ∀ (c : ℂ) x y, ψ (c • x) y = (starRingEnd ℂ) c * ψ x y := by
    intro c x y
    rw [hψ, hψ, map_smul, map_smul, inner_smul_left, inner_smul_left]
    ring
  have hψconj : ∀ x y, ψ x y = (starRingEnd ℂ) (ψ y x) := by
    intro x y
    rw [hψ, hψ, map_sub, map_mul, inner_conj_symm, inner_conj_symm, Complex.conj_ofReal]
  have hψ00 : ψ v₀ v₀ = 0 := by
    rw [hψ, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    have h := congrArg (fun t : ℝ => (t : ℂ)) hrr
    push_cast at h
    linear_combination -h

  have hkey : ∀ y, ψ v₀ y = 0 := by
    intro y
    obtain ⟨W₁, hW₁f, hyW₁, hW₁K⟩ := M.kfin y
    obtain ⟨W₀, hW₀f, hv₀W₀, hW₀K⟩ := M.kfin v₀
    haveI := hW₁f
    haveI := hW₀f
    haveI : FiniteDimensional ℂ ↥(W₁ ⊔ W₀) := Submodule.finiteDimensional_sup W₁ W₀
    have hWK : ∀ X, IsKC X → ∀ w ∈ W₁ ⊔ W₀, M.act X w ∈ W₁ ⊔ W₀ := by
      intro X hX w hw
      obtain ⟨w₁, hw₁, w₀, hw₀, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add]
      exact Submodule.add_mem_sup (hW₁K X hX w₁ hw₁) (hW₀K X hX w₀ hw₀)
    obtain ⟨a, haW, ha⟩ := exists_repr_on_finiteDimensional E₁ hE (W₁ ⊔ W₀) (ψ v₀)

    have heig : ∀ Z, IsKC Z → ∀ μ : ℝ, M.act Z v₀ = (μ : ℂ) • v₀ → M.act Z a = (μ : ℂ) • a := by
      intro Z hZ μ hZv
      have hmem : M.act Z a - (μ : ℂ) • a ∈ W₁ ⊔ W₀ :=
        Submodule.sub_mem _ (hWK Z hZ a haW) (Submodule.smul_mem _ _ haW)
      have h3 : ∀ x ∈ W₁ ⊔ W₀, inner ℂ (E₁ (M.act Z a - (μ : ℂ) • a)) (E₁ x) = 0 := by
        intro x hx
        have hx' : M.act (adjZ Z) x ∈ W₁ ⊔ W₀ := hWK _ (isKC_adjZ hZ) _ hx
        rw [map_sub E₁, map_smul E₁, inner_sub_left, inner_smul_left, h₁, ha _ hx', ha _ hx,
          ← hψinv, hZv, hψsmul, sub_self]
      have h4 := h3 _ hmem
      rw [inner_self_eq_zero] at h4
      exact sub_eq_zero.mp (hE (by rw [h4, map_zero]))
    have hahw : a ∈ hwSub M.act Λ := by
      rw [mem_hwSub_iff_eigen]
      have hv₀hw := (mem_hwSub_iff_eigen M.act Λ v₀).mp v₀s.2
      refine ⟨fun c => ?_, fun c d hcd => ?_⟩
      · have h := heig (Eab c c) (isKC_Eab (sameBlock_self c)) ((Λ c : ℚ) : ℝ)
          (by rw [hv₀hw.1 c]; push_cast; rfl)
        rw [h]
        push_cast
        rfl
      · have h := heig (Eab c d) (isKC_Eab (sameBlock_of_posC hcd)) 0
          (by rw [hv₀hw.2 c d hcd]; simp)
        rw [h]
        simp
    obtain ⟨t, ht⟩ := hspan ⟨a, hahw⟩
    have hat : a = t • v₀ := by
      have := congrArg Subtype.val ht
      simpa using this.symm
    have hEa : E₁ a = 0 := by
      have h1 := ha a haW
      have h2 : ψ v₀ a = 0 := by rw [hat, map_smul, hψ00, smul_zero]
      rw [h2, inner_self_eq_zero] at h1
      exact h1
    rw [← ha y (Submodule.mem_sup_left hyW₁), hEa, inner_zero_left]

  have hall : ∀ x y, ψ x y = 0 := by
    let N : Submodule ℂ M.V := ⨅ x, LinearMap.ker (ψ x)
    have hmemN : ∀ y, y ∈ N ↔ ∀ x, ψ x y = 0 := by
      intro y
      simp only [N, Submodule.mem_iInf, LinearMap.mem_ker]
    have hstab : ∀ Z, ∀ y ∈ N, M.act Z y ∈ N := by
      intro Z y hy
      rw [hmemN] at hy ⊢
      intro x
      rw [← adjZ_adjZ Z, ← hψinv]
      exact hy _
    have hv₀N : v₀ ∈ N := by
      rw [hmemN]
      intro x
      rw [hψconj, hkey, map_zero]
    have hirr' : Nontrivial M.V ∧ ∀ N : Submodule ℂ M.V, (∀ Z, ∀ y ∈ N, M.act Z y ∈ N) →
        N = ⊥ ∨ N = ⊤ := hirr
    rcases hirr'.2 N hstab with hN | hN
    · exact absurd (by rw [hN] at hv₀N; exact (Submodule.mem_bot ℂ).mp hv₀N) hv₀
    · intro x y
      have hy : y ∈ N := by rw [hN]; exact Submodule.mem_top
      exact (hmemN y).mp hy x
  refine ⟨Real.sqrt r, fun y => ?_⟩
  have hsq : ‖E₂ y‖ ^ 2 = r * ‖E₁ y‖ ^ 2 := by
    have h := hall y y
    rw [hψ, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ((‖E₂ y‖ ^ 2 : ℝ) : ℂ) = ((r * ‖E₁ y‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast h'
  rw [← Real.sqrt_sq (norm_nonneg (E₂ y)), hsq, Real.sqrt_mul hr0, Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.FockTensor
end
end

