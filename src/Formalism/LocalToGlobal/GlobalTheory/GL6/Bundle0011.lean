import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0003
import Formalism.LocalToGlobal.GlobalTheory.GL6.LocalBasisChangeDecompCompatible
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0008

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfLevelZeroIdentities
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

section UnramifiedDiagonal

variable (D : D7) (u : D.what₂.Word)

def DiamondCommutesLevelZero : Prop :=
  ∀ v v' (a : ((D.mem u).A.Fv v')ˣ), ∀ φ ∈ (D.fm u).Fi 0,
    dia D u 0 v' a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v' a φ) ∧
    dia D u 0 v' a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v' a φ)

def TraceDiamondInvariantLevelZero : Prop :=
  ∀ v (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi 0, trp D u 0 v (dia D u 0 v a φ) = trp D u 0 v φ

def DUFormulaLevelZero : Prop :=
  ∀ v, ∀ φ ∈ (D.fm u).Fi 0, Dop D u 0 v (Uop D u 0 v φ) =
    ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ - ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 2) • Nm D u 0 v φ
      + ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 2) • trp D u 0 v φ

variable {D u}

theorem norm_commutes_hecke_level_zero (hc : DiamondCommutesLevelZero D u) (v v' : (D.mem u).A.vT) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    Nm D u 0 v' (Uop D u 0 v φ) = Uop D u 0 v (Nm D u 0 v' φ) ∧
    Nm D u 0 v' (Dop D u 0 v φ) = Dop D u 0 v (Nm D u 0 v' φ) := by
  simp only [norm_eq_sum_diamond, map_sum]
  exact ⟨Finset.sum_congr rfl fun a _ => (hc v v' a φ hφ).1, Finset.sum_congr rfl fun a _ => (hc v v' a φ hφ).2⟩

theorem trace_zero_of_norm_zero_level_zero (ht : TraceDiamondInvariantLevelZero D u) (v : (D.mem u).A.vT) (φ : Fn D u 0)
    (hφ : φ ∈ (D.fm u).Fi 0) (hN : Nm D u 0 v φ = 0) : trp D u 0 v φ = 0 := by
  have h1 : ∑ a : ((D.mem u).A.Fv v)ˣ, trp D u 0 v (dia D u 0 v a φ) = trp D u 0 v (Nm D u 0 v φ) := by
    rw [norm_eq_sum_diamond, map_sum]
  rw [hN, map_zero, Finset.sum_congr rfl (fun a _ => ht v a φ hφ), Finset.sum_const,
    Finset.card_univ] at h1
  have hc : (Fintype.card ((D.mem u).A.Fv v)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left hc

theorem hecke_ramified_zero_of_identities (Tf : FormsTied D u) (hT : (D.mem u).A.T ≠ 0) (hc : DiamondCommutesLevelZero D u)
    (ht : TraceDiamondInvariantLevelZero D u) (h6 : DUFormulaLevelZero D u) : HeckeRamifiedLevelZero D u := by
  intro v φ hφ
  have hU : ∀ ψ ∈ MramI D u 0, Uop D u 0 v ψ ∈ MramI D u 0 := by
    intro ψ hψ; rw [mem_ramified_forms_iff] at hψ ⊢
    refine ⟨U_op_preserves_forms_level_zero Tf v ψ hψ.1, fun v' => ?_⟩
    rw [(norm_commutes_hecke_level_zero hc v v' ψ hψ.1).1, hψ.2 v', map_zero]
  have hD : ∀ ψ ∈ MramI D u 0, Dop D u 0 v ψ ∈ MramI D u 0 := by
    intro ψ hψ; rw [mem_ramified_forms_iff] at hψ ⊢
    refine ⟨D_op_preserves_forms_level_zero Tf v ψ hψ.1, fun v' => ?_⟩
    rw [(norm_commutes_hecke_level_zero hc v v' ψ hψ.1).2, hψ.2 v', map_zero]
  have hDU : ∀ ψ ∈ MramI D u 0, Dop D u 0 v (Uop D u 0 v ψ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • ψ := by
    intro ψ hψ
    have hψ' := (mem_ramified_forms_iff D u ψ).1 hψ
    rw [h6 v ψ hψ'.1, hψ'.2 v, trace_zero_of_norm_zero_level_zero ht v ψ hψ'.1 (hψ'.2 v), smul_zero, sub_zero, add_zero]
  have := ramified_forms_finite_dimensional D u 0
  have hc0 : ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hT)
  exact ⟨hU φ hφ, hD φ hφ, U_D_of_D_U_on_finite_dim (MramI D u 0) (Uop D u 0 v) (Dop D u 0 v) _ hc0 hU hDU φ hφ⟩

theorem congruence_no_kernel_of_level_zero_identities
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u → admS D u →
      HeckeIntegralLevelZero D u ∧ DiamondCommutesLevelZero D u ∧ TraceDiamondInvariantLevelZero D u ∧ DUFormulaLevelZero D u ∧ SecondBranchInclusionLength D u) : CongruenceLatticeLengthBoundFamily :=
  congruence_no_kernel_family_minimal fun D u hT hS hA => by
    obtain ⟨h4, hc, ht, h6, hB⟩ := h D u hT hS hA
    obtain ⟨Tf, -⟩ := hT
    exact ⟨h4, hecke_ramified_zero_of_identities Tf (by have := hS.1; omega) hc ht h6, hB⟩

end UnramifiedDiagonal

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.IntegralTensorBasisLinIndep
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial

variable (D : D7)

theorem tensor_sum_expand {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (y : ∀ τ, κ τ → MvPolynomial (Fin N × Fin N) ℂ) (c : ∀ τ, κ τ → ℂ) :
    Formalism.L2.Forms.ten (fun τ => ∑ i, c τ i • y τ i) =
      ∑ g : (∀ τ, κ τ), (∏ τ, c τ (g τ)) • Formalism.L2.Forms.ten (fun τ => y τ (g τ)) := by
  simp only [Formalism.L2.Forms.ten, map_sum, smul_eq_C_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [map_mul, rename_C, Finset.prod_mul_distrib, map_prod]

theorem integral_span_eq_tensor_span (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (κ : D.what₂.Tau → Type)
    [∀ τ, Fintype (κ τ)] (b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ N (lam τ))) :
    ((Formalism.L2.Forms.IntSpan D w lam : AddSubgroup _) : Set (MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ)) =
      (Submodule.span (bwA_Ow D w) (Set.range fun g : (∀ τ, κ τ) => Formalism.L2.Forms.ten (fun τ =>
        MvPolynomial.map (Int.castRingHom ℂ) ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ))) : Set _) := by
  classical
  apply Set.Subset.antisymm
  · intro p hp
    induction hp using AddSubgroup.closure_induction with
    | mem p hp =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hp
      have hfe : ∀ τ, MvPolynomial.map (Int.castRingHom ℂ) (f τ) =
          ∑ i, (((b τ).repr ⟨f τ, hf τ⟩ i : ℤ) : ℂ) • MvPolynomial.map (Int.castRingHom ℂ)
            ((b τ i : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ) := by
        intro τ
        have h1 := congrArg (fun x : delSq ℤ N (lam τ) => MvPolynomial.map (Int.castRingHom ℂ)
          (x : MvPolynomial (Fin N × Fin N) ℤ)) ((b τ).sum_repr ⟨f τ, hf τ⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Int.cast_smul_eq_zsmul]
      have hx : Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) =
          ∑ g : (∀ τ, κ τ), (∏ τ, (((b τ).repr ⟨f τ, hf τ⟩ (g τ) : ℤ) : ℂ)) • Formalism.L2.Forms.ten (fun τ =>
            MvPolynomial.map (Int.castRingHom ℂ) ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) := by
        rw [show (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) = fun τ => ∑ i,
          (((b τ).repr ⟨f τ, hf τ⟩ i : ℤ) : ℂ) • MvPolynomial.map (Int.castRingHom ℂ)
            ((b τ i : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ) from funext hfe]
        exact tensor_sum_expand κ _ _
      rw [SetLike.mem_coe, hx, Finset.smul_sum]
      refine Submodule.sum_mem _ fun g _ => ?_
      rw [smul_smul]
      have hmem : D.what₂.embLL r * ∏ τ, (((b τ).repr ⟨f τ, hf τ⟩ (g τ) : ℤ) : ℂ) ∈ bwA_Ow D w :=
        (bwA_Ow D w).mul_mem ⟨r, hr, rfl⟩ ((bwA_Ow D w).prod_mem fun τ _ => intCast_mem _ _)
      exact Submodule.smul_mem _ (⟨_, hmem⟩ : bwA_Ow D w) (Submodule.subset_span ⟨g, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | neg x _ hx => exact Submodule.neg_mem _ hx
  · intro p hp
    replace hp : p ∈ Submodule.span (bwA_Ow D w) _ := hp
    rw [SetLike.mem_coe]
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨1, fun τ => ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ),
        (intW D.what₂.places w).one_mem, fun τ => (b τ (g τ)).2, ?_⟩
      rw [map_one, one_smul]
    | zero => exact (Formalism.L2.Forms.IntSpan D w lam).zero_mem
    | add x y _ _ hx hy => exact (Formalism.L2.Forms.IntSpan D w lam).add_mem hx hy
    | smul o x _ hx =>
      obtain ⟨o, ⟨r, hr, rfl⟩⟩ := o
      exact bwG_intSpan_smul D w lam r hr hx

theorem integral_tensor_basis_lin_indep (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (κ : D.what₂.Tau → Type)
    (b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ N (lam τ))) :
    LinearIndependent (bwA_Ow D w) (fun g : (∀ τ, κ τ) => Formalism.L2.Forms.ten (fun τ =>
      MvPolynomial.map (Int.castRingHom ℂ) ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ))) := by
  classical
  have hinj : Function.Injective fun c : bwA_Ow D w => c • (1 : ℂ) := by
    intro x y h; simpa using h
  exact (tensor_weyl_basis_lin_indep lam κ b).restrict_scalars hinj

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

