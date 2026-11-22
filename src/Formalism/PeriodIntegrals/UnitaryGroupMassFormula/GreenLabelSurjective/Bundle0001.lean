import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.ExistsNeZeroTensor
section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

namespace PI.GreenLabelSurjWork

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem levi_mul (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  show blk K b c ((p.1 * q.1 : GL ι K) : Matrix ι ι K) = blk K b c p.1 * blk K b c q.1
  rw [Units.val_mul]
  exact blk_mul b c p.2.1 q.2.1

theorem levi_one (c : Fin s) : levi K b c 1 = 1 := by
  apply Units.ext
  show blk K b c ((1 : GL ι K) : Matrix ι ι K) = 1
  rw [Units.val_one]
  exact Matrix.submatrix_one _ Subtype.val_injective

theorem infl_mul (p q : parab K b) :
    infl K b lam (p * q) = infl K b lam p ∘ₗ infl K b lam q := by
  unfold infl
  rw [← PiTensorProduct.map_comp]
  congr 1
  funext c
  rw [levi_mul, map_mul]
  rfl

theorem infl_one : infl K b lam 1 = LinearMap.id := by
  unfold infl
  simp only [levi_one, map_one]
  exact PiTensorProduct.map_id

theorem exists_ne_zero_tensor (hl : ∀ c, Nontrivial (lam c)) :
    ∃ v : PiTensorProduct ℂ (fun c => (lam c : Type)), v ≠ 0 := by
  classical
  choose w hw using fun c => exists_ne (0 : lam c)
  have hφ : ∀ c, ∃ φ : Module.Dual ℂ (lam c), φ (w c) ≠ 0 := fun c => by
    by_contra hc
    push_neg at hc
    exact hw c ((Module.forall_dual_apply_eq_zero_iff ℂ (w c)).mp hc)
  choose φ hφ using hφ
  refine ⟨PiTensorProduct.tprod ℂ w, fun h0 => ?_⟩
  have h1 := PiTensorProduct.dualDistrib_apply φ w
  rw [show (⨂ₜ[ℂ] i, w i) = PiTensorProduct.tprod ℂ w from rfl, h0, map_zero] at h1
  exact (Finset.prod_ne_zero_iff.mpr (fun c _ => hφ c)) h1.symm

theorem hcSpace_nontrivial (hl : ∀ c, Nontrivial (lam c)) : Nontrivial (hcSpace K b lam) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne_zero_tensor b lam hl
  let f : GL ι K → PiTensorProduct ℂ (fun c => (lam c : Type)) := fun x =>
    if hx : x ∈ parab K b then infl K b lam ⟨x, hx⟩ v else 0
  have hf : f ∈ hcSpace K b lam := by
    show ∀ (p : parab K b) (x : GL ι K), f (p.1 * x) = infl K b lam p (f x)
    intro p x
    by_cases hx : x ∈ parab K b
    · have hpx : p.1 * x ∈ parab K b := mul_mem p.2 hx
      simp only [f, dif_pos hx, dif_pos hpx]
      rw [show (⟨p.1 * x, hpx⟩ : parab K b) = p * ⟨x, hx⟩ from rfl, infl_mul]
      rfl
    · have hpx : p.1 * x ∉ parab K b := fun h => hx (by
        have := mul_mem (inv_mem p.2) h
        rwa [inv_mul_cancel_left] at this)
      simp only [f, dif_neg hx, dif_neg hpx, map_zero]
  refine ⟨⟨⟨f, hf⟩, 0, fun h => hv ?_⟩⟩
  have h1 := congrFun (congrArg Subtype.val h) 1
  simp only [f, dif_pos (one_mem (parab K b))] at h1
  rw [show (⟨1, one_mem (parab K b)⟩ : parab K b) = 1 from rfl, infl_one] at h1
  exact h1

end PI.GreenLabelSurjWork
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
section
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

namespace PI.GreenLabelSurjWork

variable {G : Type} [Group G] [Fintype G]

def repHomLin (A B : Rep ℂ G) : (A ⟶ B) ≃ₗ[ℂ] A.ρ.IntertwiningMap B.ρ :=
  { Rep.homEquiv with map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem simple_of_irr {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [σ.IsIrreducible] : Simple (FDRep.of σ) := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  rw [FDRep.simple_iff_end_is_rank_one]
  rw [← (FDRep.forget₂HomLinearEquiv _ _).finrank_eq, (repHomLin _ _).finrank_eq]
  exact Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := σ)

theorem nontrivial_of_simple (V : FDRep ℂ G) (h : Simple V) : Nontrivial V := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply CategoryTheory.id_nonzero V
  first
    | (ext x; exact Subsingleton.elim _ _)
    | (apply Action.Hom.ext; ext x; exact Subsingleton.elim _ _)
    | (ext; exact Subsingleton.elim _ _)

theorem exists_simple_constituent {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V) : ∃ τ : FDRep ℂ G, Simple τ ∧ IsConstituent τ ρ := by
  classical
  have hex : ∃ n, ∃ A : Subrepresentation ρ, A.toSubmodule ≠ ⊥ ∧
      Module.finrank ℂ A.toSubmodule = n :=
    ⟨_, ⊤, show (⊤ : Submodule ℂ V) ≠ ⊥ from top_ne_bot, rfl⟩
  obtain ⟨A, hA0, hAn⟩ := Nat.find_spec hex
  have hirr : (A.toRepresentation).IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hA0 ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
    · have h1 := congrArg Subrepresentation.toSubmodule h
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h2 : (⟨x, hx⟩ : A.toSubmodule) ∈ (⊥ : Subrepresentation A.toRepresentation).toSubmodule := by
        rw [h1]; exact Submodule.mem_top
      have h3 : (⟨x, hx⟩ : A.toSubmodule) = 0 := (Submodule.mem_bot ℂ).mp h2
      exact congrArg Subtype.val h3
    · by_cases hU : U.toSubmodule = ⊥
      · left
        exact Subrepresentation.toSubmodule_injective hU
      · right
        let U' : Subrepresentation ρ :=
          ⟨U.toSubmodule.map A.toSubmodule.subtype, by
            intro g v hv
            obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
            exact Submodule.mem_map.mpr ⟨A.toRepresentation g u, U.apply_mem_toSubmodule g hu, rfl⟩⟩
        have hfr : Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ U.toSubmodule :=
          Submodule.finrank_map_subtype_eq _ _
        have hU0 : U'.toSubmodule ≠ ⊥ := by
          intro h
          have : Module.finrank ℂ U'.toSubmodule = 0 := by rw [h]; exact finrank_bot ℂ V
          rw [hfr, Submodule.finrank_eq_zero] at this
          exact hU this
        have hmin := Nat.find_min' hex ⟨U', hU0, rfl⟩
        have hle : Module.finrank ℂ U.toSubmodule ≤ Module.finrank ℂ A.toSubmodule :=
          Submodule.finrank_le _
        apply Subrepresentation.toSubmodule_injective
        exact Submodule.eq_top_of_finrank_eq (by omega)
  refine ⟨FDRep.of A.toRepresentation, simple_of_irr _, A.toSubmodule.subtype, ?_, ?_⟩
  · intro g
    ext v
    rfl
  · intro h
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
    exact hv0 (congrArg (fun φ : A.toSubmodule →ₗ[ℂ] V => φ ⟨v, hv⟩) h)

end PI.GreenLabelSurjWork
end

