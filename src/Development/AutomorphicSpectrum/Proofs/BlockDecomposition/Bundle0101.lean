import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0093

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardParabolicSubgroup
section
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.FinGL

theorem prod_pow_sub (q : ℤ) (n : ℕ) :
    ∏ i ∈ Finset.range n, (q ^ n - q ^ i) =
      q ^ n.choose 2 * ∏ i ∈ Finset.Icc 1 n, (q ^ i - 1) := by
  have h1 : ∀ i ∈ Finset.range n, q ^ n - q ^ i = q ^ i * (q ^ (n - i) - 1) := by
    intro i hi
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hin, mul_one]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Nat.choose_two_right]
  congr 1
  refine Finset.prod_nbij' (fun i => n - i) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    show n - (n - i) = i
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    show n - (n - j) = j
    omega
  · intro i _
    rfl

theorem two_choose_add (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have h : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [h]
    nlinarith

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

theorem card_GL_int (ι : Type) [Fintype ι] [DecidableEq ι] :
    (Nat.card (GL ι K) : ℤ) = (Fintype.card K : ℤ) ^ (Fintype.card ι).choose 2 *
      ∏ i ∈ Finset.Icc 1 (Fintype.card ι), ((Fintype.card K : ℤ) ^ i - 1) := by
  rw [Nat.card_congr (glEquiv K (Fintype.equivFin ι)).toEquiv, Matrix.card_GL_field,
    ← prod_pow_sub, Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ Fintype.card ι - Fintype.card K ^ i),
    Nat.cast_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hq : 0 < Fintype.card K := Fintype.card_pos
  have hle : Fintype.card K ^ i ≤ Fintype.card K ^ Fintype.card ι :=
    Nat.pow_le_pow_right hq (Finset.mem_range.mp hi).le
  push_cast [Nat.cast_sub hle]
  rfl

section Parab

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)

def parabCoord (p : parab K b) :
    ({p : ι × ι // b p.1 < b p.2} → K) × (∀ c, GL {i // b i = c} K) :=
  (fun x => (p.1 : Matrix ι ι K) x.1.1 x.1.2, fun c => levi K b c p)

theorem parabCoord_injective : Function.Injective (parabCoord K b) := by
  intro x y h
  have h1 := congrFun (congrArg Prod.fst h)
  have h2 := fun c => congrArg (fun g : GL {i // b i = c} K => (g : Matrix {i // b i = c} {i // b i = c} K))
    (congrFun (congrArg Prod.snd h) c)
  apply Subtype.ext
  apply Units.ext
  ext i j
  rcases lt_trichotomy (b i) (b j) with hij | hij | hij
  · exact h1 ⟨(i, j), hij⟩
  · exact congrFun (congrFun (h2 (b j)) ⟨i, hij⟩) ⟨j, rfl⟩
  · rw [x.2.1 i j hij, y.2.1 i j hij]

theorem parabCoord_surjective : Function.Surjective (parabCoord K b) := by
  rintro ⟨u, g⟩
  let M : Matrix ι ι K := fun i j =>
    if h : b i < b j then u ⟨(i, j), h⟩
    else if h' : b i = b j then (g (b j)).1 ⟨i, h'⟩ ⟨j, rfl⟩ else 0
  have hM : IsBlockUT K b M := by
    intro i j h
    simp [M, not_lt_of_gt h, h.ne']
  have hT : M.BlockTriangular b := fun i j h => hM i j h
  have hblk : ∀ c, M.toSquareBlock b c = (g c).1 := by
    intro c
    ext ⟨i, hi⟩ ⟨j, hj⟩
    subst hj
    have h0 : ¬ b i < b j := by rw [hi]; exact lt_irrefl _
    show M i j = _
    simp only [M]
    rw [dif_neg h0, dif_pos hi]
  have hdet : M.det ≠ 0 := by
    rw [hT.det]
    refine Finset.prod_ne_zero_iff.mpr fun c _ => ?_
    rw [hblk]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (g c).isUnit).ne_zero
  haveI : Invertible M := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hdet)
  let G : GL ι K := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  have hG : (G : Matrix ι ι K) = M := rfl
  have hGi : IsBlockUT K b ((G⁻¹ : GL ι K) : Matrix ι ι K) := by
    rw [Matrix.coe_units_inv, hG]
    exact fun i j h => Matrix.blockTriangular_inv_of_blockTriangular hT h
  refine ⟨⟨G, hM, hGi⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · funext x
    show M x.1.1 x.1.2 = u x
    simp [M, x.2]
  · funext c
    apply Units.ext
    exact hblk c

theorem card_parab : Nat.card (parab K b) =
    Fintype.card K ^ Fintype.card {p : ι × ι // b p.1 < b p.2} *
      ∏ c, Nat.card (GL {i // b i = c} K) := by
  rw [Nat.card_eq_of_bijective _ ⟨parabCoord_injective K b, parabCoord_surjective K b⟩,
    Nat.card_prod, Nat.card_fun, Nat.card_pi, Nat.card_eq_fintype_card (α := K),
    Nat.card_eq_fintype_card (α := {p : ι × ι // b p.1 < b p.2})]

theorem card_eq_sum_blocks :
    Fintype.card ι = ∑ c, Fintype.card {i // b i = c} := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv b).symm

theorem card_same_block :
    Fintype.card {p : ι × ι // b p.1 = b p.2} =
      ∑ c, Fintype.card {i // b i = c} * Fintype.card {i // b i = c} := by
  simp only [← Fintype.card_prod]
  rw [← Fintype.card_sigma]
  refine Fintype.card_congr
    { toFun := fun p => ⟨b p.1.2, ⟨p.1.1, p.2⟩, ⟨p.1.2, rfl⟩⟩
      invFun := fun x => ⟨(x.2.1.1, x.2.2.1), x.2.1.2.trans x.2.2.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := ?_ }
  rintro ⟨c, ⟨i, hi⟩, ⟨j, hj⟩⟩
  subst hj
  rfl

theorem card_swap_block :
    Fintype.card {p : ι × ι // b p.2 < b p.1} = Fintype.card {p : ι × ι // b p.1 < b p.2} :=
  Fintype.card_congr
    { toFun := fun p => ⟨p.1.swap, p.2⟩
      invFun := fun p => ⟨p.1.swap, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_pairs :
    Fintype.card ι * Fintype.card ι = Fintype.card {p : ι × ι // b p.1 < b p.2} +
      Fintype.card {p : ι × ι // b p.2 < b p.1} + Fintype.card {p : ι × ι // b p.1 = b p.2} := by
  rw [← Fintype.card_prod]
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases lt_trichotomy (b p.1) (b p.2) with h | h | h
  · simp [h, h.ne, not_lt_of_gt h]
  · simp [h]
  · simp [h, h.ne', not_lt_of_gt h]

theorem choose_blocks :
    (Fintype.card ι).choose 2 = Fintype.card {p : ι × ι // b p.1 < b p.2} +
      ∑ c, (Fintype.card {i // b i = c}).choose 2 := by
  have h1 := card_pairs b
  rw [card_swap_block, card_same_block] at h1
  have h2 := two_choose_add (Fintype.card ι)
  have h3 : ∑ c, Fintype.card {i // b i = c} * Fintype.card {i // b i = c} =
      2 * ∑ c, (Fintype.card {i // b i = c}).choose 2 + Fintype.card ι := by
    rw [card_eq_sum_blocks b, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => (two_choose_add _).symm
  omega

end Parab

theorem cardParab : ReciprocityTheory.Ty.Fin.St.CardParab := by
  intro K _ _ _ ι _ _
  exact ⟨card_GL_int K ι, fun s b => ⟨card_parab K b, choose_blocks b⟩⟩

end GlobalTheory.CompanionTheory.FinGL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentAction
section
open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

theorem asAlgebraHom_centralIdem {Γ V W : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) :
    σ.asAlgebraHom (centralIdem ρ) =
      ∑ g, ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) • σ g := by
  unfold centralIdem
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => Representation.asAlgebraHom_single _ _ _

theorem centralIdemAct : ReciprocityTheory.Ty.Fin.St.CentralIdemAct := by
  intro Γ _ _ V _ _ _ W _ _ _ ρ σ hρ hσ
  obtain ⟨hVn, hρ'⟩ := hρ
  obtain ⟨hWn, hσ'⟩ := hσ
  haveI := hVn
  haveI := hWn
  haveI hirrρ : ρ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of ρ hρ'
  haveI hirrσ : σ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of σ hσ'
  have hc0 : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Nat.card Γ : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hV0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hW0 : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  obtain ⟨μ, hμ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.schur_scalar σ hσ'
    (fun g => (Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) (by
      intro g k
      have e : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
      have := Representation.char_conj ρ g⁻¹ k
      simp only [Representation.character] at this
      simp only [e, this])
  have hT : σ.asAlgebraHom (centralIdem ρ) = μ • (1 : Module.End ℂ W) := by
    rw [asAlgebraHom_centralIdem]; exact hμ
  have htr : μ * (Module.finrank ℂ W : ℂ) = (Module.finrank ℂ V : ℂ) *
      ((Nat.card Γ : ℂ)⁻¹ * ∑ g, σ.character g * ρ.character g⁻¹) := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum, Finset.mul_sum, Nat.card_eq_fintype_card]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Representation.character]
    field_simp
  rw [Representation.char_orthonormal σ ρ] at htr
  rw [hT]
  by_cases h : Nonempty (Representation.Equiv ρ σ)
  · rw [if_pos h] at htr ⊢
    obtain ⟨φ⟩ := h
    have hd : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    rw [hd] at htr
    have : μ = 1 := by
      apply mul_right_cancel₀ hW0
      simpa using htr
    rw [this, one_smul]
  · rw [if_neg h] at htr ⊢
    have : μ = 0 := by
      have h0 : μ * (Module.finrank ℂ W : ℂ) = 0 := by simpa using htr
      exact (mul_eq_zero.mp h0).resolve_right hW0
    rw [this, zero_smul]

end GlobalTheory.CompanionTheory.TyFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLattice
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

private theorem forall_locMem_iff_exists_mem_ideal {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (z : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.CompanionTheory.Equi.LocMem I v z) ↔ ∃ y ∈ I, (y : F) = z := by
  constructor
  · intro h
    let J : Ideal (𝓞 F) :=
      { carrier := {s | ∃ y ∈ I, (s : F) * z = y}
        add_mem' := by
          rintro a b ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, I.add_mem hy₁ hy₂, by push_cast; rw [add_mul, h₁, h₂]⟩
        zero_mem' := ⟨0, I.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨y, hy, h₁⟩
          exact ⟨c * y, I.mul_mem_left c hy, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h₁]⟩ }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : M ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      have hv := h ⟨M, hM.isPrime, hM0⟩
      unfold GlobalTheory.CompanionTheory.Equi.LocMem at hv
      obtain ⟨s, hs, y, hy, hsy⟩ := hv
      exact hs (hJM ⟨y, hy, hsy⟩)
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := h1
    exact ⟨y, hy, by simpa using hy1.symm⟩
  · rintro ⟨y, hy, rfl⟩ v
    unfold GlobalTheory.CompanionTheory.Equi.LocMem
    exact ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), y, hy, by simp⟩

theorem cosetOff_empty_eq_latCoset (F : Type) [Field F] [NumberField F] (ι : Type)
    (I : Ideal (𝓞 F)) (x0 : ι → F) :
    cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  ext x
  simp only [GlobalTheory.CompanionTheory.Equi.cosetOff, GlobalTheory.CompanionTheory.Equi.latCoset, Set.mem_setOf_eq]
  constructor
  · intro h i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mp fun v => h v (by simp) i
  · intro h v _ i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mpr (h i) v

end GlobalTheory.CompanionTheory.Equi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Equi.CosetTop

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    Valued.v (algebraMap F (Fv F v) z) = v.valuation F z := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    algebraMap F (Fv F v) z ∈ v.adicCompletionIntegers F ↔ v.valuation F z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]

theorem locMem_top_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    LocMem (⊤ : Ideal (𝓞 F)) v z ↔ v.valuation F z ≤ 1 := by
  constructor
  · rintro ⟨s, hs, y, -, h⟩
    have h1 : v.valuation F (s : F) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 : v.valuation F (s : F) * v.valuation F z = v.valuation F (y : F) := by
      rw [← map_mul, h]
    rw [h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one v y
  · intro hz
    have hmem : z ∈ HeightOneSpectrum.valuationSubringAtPrime F v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hz
    obtain ⟨a, s, hs, h⟩ := hmem
    refine ⟨s, hs, a, Submodule.mem_top, ?_⟩
    have hs0 : (s : F) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := RingOfIntegers.coe_injective (by simpa using h0)
      rw [this]
      exact v.asIdeal.zero_mem
    rw [h]
    change (s : F) * ((a : F) * (s : F)⁻¹) = a
    field_simp

theorem cosetOff_top : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  intro F _ _ ι S
  ext x
  simp only [cosetOff, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, locMem_top_iff, algebraMap_mem_iff]

end GlobalTheory.CompanionTheory.Equi.CosetTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsomorphismProperties
section
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

omit [Fintype K] [DecidableEq K] in

theorem glReindex_glReindex (e₁ : α ≃ β) (e₂ : β ≃ γ) (g : GL α K) :
    glReindex K e₂ (glReindex K e₁ g) = glReindex K (e₁.trans e₂) g := by
  ext i j
  simp [glReindex_val]

omit [Fintype K] [DecidableEq K] in

theorem glReindex_refl (g : GL α K) : glReindex K (Equiv.refl α) g = g := by
  ext i j
  simp [glReindex_val]

omit [Fintype K] [DecidableEq K] in

theorem glReindex_symm_apply (e : α ≃ β) (g : GL β K) :
    glReindex K e (glReindex K e.symm g) = g := by
  rw [glReindex_glReindex, Equiv.symm_trans_self, glReindex_refl]

omit [Fintype K] [DecidableEq K] in

theorem reRep_ρ_apply (e : α ≃ β) (τ : FDRep ℂ (GL α K)) (g : GL β K) :
    (reRep e τ).ρ g = τ.ρ ((glEquiv K e).symm g) := by
  rfl

theorem cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts := by
  intro K _ _ _ α β γ _ _ _ _ _ _ lam lam' mu nu e
  refine ⟨?_, ?_, ?_, ?_, fun g => glReindex_symm_apply e g⟩
  · rintro ⟨e, φ, h⟩
    refine ⟨e.symm, φ.symm, fun g x => φ.injective ?_⟩
    rw [φ.apply_symm_apply, h, φ.apply_symm_apply, glReindex_symm_apply]
  · rintro ⟨e₁, φ₁, h₁⟩ ⟨e₂, φ₂, h₂⟩
    refine ⟨e₁.trans e₂, φ₁.trans φ₂, fun g x => ?_⟩
    simp only [LinearEquiv.trans_apply, h₁, h₂, glReindex_glReindex]
  · rintro ⟨i⟩
    refine ⟨Equiv.refl α, FDRep.isoToLinearEquiv i, fun g x => ?_⟩
    rw [glReindex_refl]
    have := FDRep.Iso.conj_ρ i g
    rw [this]
    simp [LinearEquiv.conj_apply]
  · refine ⟨e, LinearEquiv.refl ℂ _, fun g x => ?_⟩
    change lam.ρ g x = lam.ρ ((glEquiv K e).symm (glEquiv K e g)) x
    rw [MulEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.TyFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyActMemLatVIff
section
open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatFix

section Gen

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]

theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (x y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis R b).repr x i *
        (Algebra.TensorProduct.basis R b).repr y j * algebraMap F R (b.repr (b i * b j) k) := by
  classical
  set B := Algebra.TensorProduct.basis R b with hB
  conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hB, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]
  simp

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem eventually_integral (c : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := by
  exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) c).2

theorem eventually_mul_closed {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ x y : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x * y) k ∈
        v.adicCompletionIntegers F := by
  classical
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ i j k : Fin d,
      algebraMap F (Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    exact fun i j k => eventually_integral _
  filter_upwards [h] with v hv x y hx hy k
  rw [repr_mul]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (hv i j k)

end Adelic

end GlobalTheory.CompanionTheory.SW.LatFix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLatticeStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_separating_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A → ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | exact GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | (intros; apply GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirstStatement
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_of_lseq_first : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  first | exact @GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level | exact GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level | (intros; apply GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FractionFieldTranscendenceBasisExtStatement
section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fraction_field_transcendence_basis_ext : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (m : ℕ) (κ : Fin m ↪ Fin d) (c : B) (b : Fin m → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D (κ k) (algebraMap B L (b l))).det) := by
  first | exact @GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem | exact GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem | (intros; apply GlobalTheory.CompanionTheory.TraceJac.trace_minor_mem <;> assumption)
end

