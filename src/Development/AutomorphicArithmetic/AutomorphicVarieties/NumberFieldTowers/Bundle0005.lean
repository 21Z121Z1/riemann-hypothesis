import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.GenDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem span_of_length_le {A : Type} [CommRing A] (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module A V], Module.length A V ≤ n →
      ∃ s : Fin n → V, Submodule.span A (Set.range s) = ⊤ := by
  induction n with
  | zero =>
    intro V _ _ h
    have h0 : Module.length A V = 0 := by simpa using h
    have : Subsingleton V := Module.length_eq_zero_iff.1 h0
    exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro V _ _ h
    rcases subsingleton_or_nontrivial V with hV | hV
    · exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    set P : Submodule A V := Submodule.span A {v} with hP
    have hadd : Module.length A V = Module.length A P + Module.length A (V ⧸ P) :=
      Module.length_eq_add_of_exact P.subtype P.mkQ P.injective_subtype P.mkQ_surjective
        (LinearMap.exact_subtype_mkQ P)
    have hP1 : 1 ≤ Module.length A P := by
      rw [Order.one_le_iff_ne_zero, Ne, Module.length_eq_zero_iff]
      intro hs
      exact hv (congrArg Subtype.val (Subsingleton.elim
        (⟨v, Submodule.mem_span_singleton_self v⟩ : P) 0))
    have hq : Module.length A (V ⧸ P) ≤ n := by
      have h2 : Module.length A (V ⧸ P) + 1 ≤ (n : ℕ∞) + 1 := by
        calc Module.length A (V ⧸ P) + 1 ≤ Module.length A (V ⧸ P) + Module.length A P := by gcongr
          _ = Module.length A V := by rw [hadd, add_comm]
          _ ≤ (n : ℕ∞) + 1 := by simpa using h
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h2
    obtain ⟨t, ht⟩ := ih (V ⧸ P) hq
    choose s hs using fun i => P.mkQ_surjective (t i)
    refine ⟨Fin.cons v s, ?_⟩
    rw [Fin.range_cons, Submodule.span_insert, ← hP, ← Submodule.map_mkQ_eq_top, Submodule.map_span,
      ← Set.range_comp, ← ht]
    congr 2
    exact funext hs

theorem UpperTheory.V.Tower.genDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (R : ℕ), (∀ m : M, ∃ r : ℕ, (l : ℤ_[l]) ^ r • m = 0) →
        (GenLE ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) R ↔ Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] M (l : ℤ_[l])) ≤ R) := by
  intro l _ M _ _ R hM
  have hc := UpperTheory.V.Tower.cokerDual l M ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] M))
    ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l))) (fun x φ => by simp)
  have hk : LinearMap.ker ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] M))
      = Submodule.torsionBy ℤ_[l] M (l : ℤ_[l]) := by
    ext m; simp
  rw [hk] at hc
  rw [← hc]
  constructor
  · intro h
    exact UpperTheory.V.PropA.cokL l _ R h
  · intro h
    set I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l])} with hI
    haveI : IsPrecomplete I ℤ_[l] := by
      rw [hI, ← PadicInt.maximalIdeal_eq_span_p]
      infer_instance
    haveI : IsHausdorff I (M →ₗ[ℤ_[l]] QZ l) := by
      refine ⟨fun x hx => LinearMap.ext fun m => ?_⟩
      obtain ⟨r, hr⟩ := hM m
      have h1 := hx r
      rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
        Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨y, -, rfl⟩ := h1
      rw [LinearMap.smul_apply, ← map_smul, hr, map_zero, LinearMap.zero_apply]
    set N : Submodule ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) :=
      LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l))) with hN
    have hNI : N = I • (⊤ : Submodule ℤ_[l] (M →ₗ[ℤ_[l]] QZ l)) := by
      ext x
      rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, hN]
      simp
    obtain ⟨t, ht⟩ := span_of_length_le R ((M →ₗ[ℤ_[l]] QZ l) ⧸ N) h
    choose s hs using fun i => N.mkQ_surjective (t i)
    have h2 : Submodule.span ℤ_[l] (Set.range s) = ⊤ := by
      refine (UpperTheory.V.abelian₂.nakayama ℤ_[l] I _).1 R s ?_
      rw [← hNI, sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp, ← ht]
      congr 2
      exact funext hs
    refine ⟨Fintype.linearCombination ℤ_[l] s, ?_⟩
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerUniq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem lu_key (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ)
    [Fact l.Prime] (hmu : HasMuQ l L) (n : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁] [Algebra L₁ Ω]
    [IsScalarTower L L₁ Ω] [IsCyclotomicExtension {l ^ n} L L₁] :
    galOf L L₁ Ω = layU l L Ω (n - cZero l L) ∧ Module.finrank L L₁ = l ^ (n - cZero l L) := by
  haveI : IsAlgClosure L₁ Ω := ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.tower_top (K := L) L₁⟩
  have h1 : galOf L L₁ Ω = Un L Ω l n := by
    rw [galOfCyc L Ω l n L L₁, galOf_self]
  have h2 : Un L Ω l n = layU l L Ω (n - cZero l L) := by
    rcases le_total n (cZero l L) with h | h
    · rw [((muQ L Ω l).2.1 n).2 h, layU, ((muQ L Ω l).2.1 _).2 (by omega)]
    · rw [layU, Nat.add_sub_cancel' h]
  refine ⟨h1.trans h2, ?_⟩
  rw [← (galEmbTop L L₁ Ω).2.2, h1, h2, (layerGen L Ω l hmu).1]

theorem UpperTheory.V.Tower.layerUniq :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (∀ m, IsLayer l m L (layF l L Ω m)) ∧
        (∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁] [Algebra L₁ Ω] [IsScalarTower L L₁ Ω], IsLayer l m L L₁ → galOf L L₁ Ω = layU l L Ω m) ∧
        ∀ (n : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁], IsCyclotomicExtension {l ^ n} L L₁ → IsLayer l (n - cZero l L) L L₁ := by
  intro L Ω _ _ _ _ _ l hl hmu
  refine ⟨fun m => ?_, fun m L₁ _ _ _ _ _ h => ?_, fun n L₁ _ _ _ h => ?_⟩
  · haveI h := (fnCyc L Ω l (cZero l L + m)).1
    refine ⟨⟨_, h⟩, ?_⟩
    have := (lu_key L Ω l hmu (cZero l L + m) (layF l L Ω m)).2
    rwa [Nat.add_sub_cancel_left] at this
  · obtain ⟨⟨k, hk⟩, hf⟩ := h
    obtain ⟨h1, h2⟩ := lu_key L Ω l hmu k L₁
    rw [h1, Nat.pow_right_injective hl.out.two_le (h2.symm.trans hf)]
  · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
    haveI : FiniteDimensional L L₁ := Module.Finite.of_restrictScalars_finite ℚ L L₁
    let f : L₁ →ₐ[L] Ω := IsAlgClosed.lift
    letI : Algebra L₁ Ω := f.toRingHom.toAlgebra
    haveI : IsScalarTower L L₁ Ω := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    exact ⟨⟨n, h⟩, (lu_key L Ω l hmu n L₁).2⟩
end

