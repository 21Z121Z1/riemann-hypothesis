import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionEqZeroOfPrimary
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem primitive_eq_zero_of_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ (f : F[X]) (m : ℕ), Irreducible f → (∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → aeval g f = 0 → φ g = 0) → ∀ g : Module.End F V, LinearMap.charpoly g = f ^ m → φ g = 0 := by
  intro F _ _ V _ _ _ φ hcl hpr f m hf h0
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  have key : ∀ n : ℕ, ∀ g : Module.End F V,
      Module.finrank F V - Module.finrank F (LinearMap.ker (aeval g f)) = n →
      LinearMap.charpoly g = f ^ m → φ g = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro g hn hg
    by_cases htop : LinearMap.ker (aeval g f) = ⊤
    · exact h0 g hg (LinearMap.ker_eq_top.mp htop)
    have hCH : ∀ g' : Module.End F V, LinearMap.charpoly g' = f ^ m → aeval g' (f ^ m) = 0 := by
      intro g' hg'
      rw [← hg']
      exact LinearMap.aeval_self_charpoly g'
    have hbot : LinearMap.ker (aeval g f) ≠ ⊥ := by
      intro hb
      have hinj : Function.Injective (aeval g f : Module.End F V) := LinearMap.ker_eq_bot.mp hb
      have hinj' : Function.Injective ((aeval g f) ^ m : Module.End F V) := by
        rw [Module.End.coe_pow]
        exact hinj.iterate m
      rw [← map_pow, hCH g hg] at hinj'
      apply htop
      rw [hb, eq_comm, eq_bot_iff]
      intro x _
      exact (Submodule.mem_bot F).mpr (hinj' (by simp))
    have hinv : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hc : aeval g f * g = g * aeval g f := by
        have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
        simpa using this
      have := congrArg (fun k : Module.End F V => k x) hc
      simpa [hx] using this
    have hsum := hpr _ hbot htop g hinv
    have hfin : (nilRad (LinearMap.ker (aeval g f))).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hterm : ∀ h ∈ hfin.toFinset, φ (g + h) =
        if LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) then φ g else 0 := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      have hcp : LinearMap.charpoly (g + h) = f ^ m := by
        rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V _ g hinv).2 h hh, hg]
      obtain ⟨hle, heq⟩ := GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle F V g h f hh
      split_ifs with hc
      · obtain ⟨e, he⟩ := GlobalTheory.T.conj_of_primary_finrank_ker_pow_eq F V g (g + h) f m hf (hCH g hg) (hCH _ hcp) (heq hc)
        rw [← he, hcl e g]
      · have hlt : LinearMap.ker (aeval g f) < LinearMap.ker (aeval (g + h) f) :=
          lt_of_le_of_ne hle (Ne.symm hc)
        have h1 := Submodule.finrank_lt_finrank_of_lt hlt
        have h2 := Submodule.finrank_le (LinearMap.ker (aeval (g + h) f))
        exact ih _ (by omega) (g + h) rfl hcp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    refine (mul_eq_zero.mp hsum).resolve_left ?_
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    refine ⟨0, ?_⟩
    simp [nilRad]
  intro g hg
  exact key _ g rfl hg

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_mem_virt_complex {G : Type} [Group G] {χ : G → ℂ}
    (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) : χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G :=
  AddSubgroup.subset_closure h

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_mul_complex {G : Type} [Group G] {a b : G → ℂ}
    (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) (hb : _root_.GlobalTheory.BI.IsChar ℂ ℂ b) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (a * b) := by
  obtain ⟨n, ρ, hρ⟩ := ha
  obtain ⟨m, σ, hσ⟩ := hb
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (Representation.tprod ρ σ)).1
  convert key using 1
  funext g
  simp [Representation.char_tensor, hρ, hσ]

open Polynomial in
private lemma trace_mulLeft_complex_lemma (z : ℂ) :
    LinearMap.trace ℂ ℂ (Algebra.lmul ℂ ℂ z) = z := by
  have hz : (Algebra.lmul ℂ ℂ z : ℂ →ₗ[ℂ] ℂ) = z • LinearMap.id := by
    ext x
    simp
  rw [hz, map_smul, LinearMap.trace_id]
  simp

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_monoidHom_complex {G : Type} [Group G] (lam : G →* ℂˣ) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (fun g => (lam g : ℂ)) := by
  let ρ : Representation ℂ G ℂ :=
    (Algebra.lmul ℂ ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp lam)
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G ℂ ρ).1
  convert key using 1
  funext g
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Representation.character]
  exact (trace_mulLeft_complex_lemma _).symm

open Polynomial in
theorem _root_.GlobalTheory.BI.subgroupFunctionExtendByZero_add {G : Type} [Group G] (H : Subgroup G) (a b : H → ℂ)
    (g : G) :
    _root_.GlobalTheory.BI.ext0 H (a + b) g =
      _root_.GlobalTheory.BI.ext0 H a g + _root_.GlobalTheory.BI.ext0 H b g := by
  unfold _root_.GlobalTheory.BI.ext0
  split_ifs <;> simp

noncomputable def indAddHomComplex {G : Type} [Group G] [Finite G] (H : Subgroup G) : (H → ℂ) →+ (G → ℂ) :=
  AddMonoidHom.mk' (ind H) (fun a b => by
    funext g
    haveI := Fintype.ofFinite G
    simp only [ind, Pi.add_apply, subgroupFunctionExtendByZero_add, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, mul_add])

open Polynomial in

theorem _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear : ∀ (G : Type) [Group G] [Finite G],
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G,
      a * b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ (H : Type) [Group H] (f : H →* G),
      (fun h => a (f h)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ g x : G, a (x⁻¹ * g * x) = a g) ∧
    (∀ (H : Subgroup G) (ψ : H → ℂ), ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H →
      _root_.GlobalTheory.BI.ind H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    ∀ lam : G →* ℂˣ, (fun g => (lam g : ℂ)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := by
  intro G _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      induction hb using AddSubgroup.closure_induction with
      | mem b hb' => exact AddSubgroup.subset_closure (_root_.GlobalTheory.BI.isChar_mul_complex ha' hb')
      | zero => simpa using zero_mem _
      | add b c _ _ hb hc => simpa [mul_add] using add_mem hb hc
      | neg b _ hb => simpa [mul_neg] using neg_mem hb
    | zero => simpa using zero_mem _
    | add a c _ _ ha hc => simpa [add_mul] using add_mem ha hc
    | neg a _ ha => simpa [neg_mul] using neg_mem ha
  · intro a ha H _ f
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      exact AddSubgroup.subset_closure
        ((_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').1 H f)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | neg a _ ha => exact neg_mem ha
  · intro a ha g x
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' => exact (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').2.1 g x
    | zero => rfl
    | add a c _ _ ha hc => simp [ha, hc]
    | neg a _ ha => simp [ha]
  · intro H ψ hψ
    change _root_.GlobalTheory.BI.indAddHomComplex H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G
    induction hψ using AddSubgroup.closure_induction with
    | mem ψ hψ' =>
      exact AddSubgroup.subset_closure
        (_root_.GlobalTheory.BI.isChar_ind ℂ ℂ G H ψ hψ')
    | zero => simpa using zero_mem _
    | add ψ φ _ _ hψ hφ => simpa [map_add] using add_mem hψ hφ
    | neg ψ _ hψ => simpa [map_neg] using neg_mem hψ
  · intro lam
    exact _root_.GlobalTheory.BI.isChar_mem_virt_complex (_root_.GlobalTheory.BI.isChar_monoidHom_complex lam)

end GlobalTheory.BI
end

