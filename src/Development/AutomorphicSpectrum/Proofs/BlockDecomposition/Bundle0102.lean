import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossing
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0095
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelShift

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanish
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspIff

def stdRadical (K : Type) [Field K] [Fintype K] [DecidableEq K] (d a : ℕ) : Subgroup (GL (Fin d) K) :=
  have hmul : ∀ u v : GL (Fin d) K,
      (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      (∀ i j : Fin d, (v : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      ∀ i j : Fin d, ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
    intro u v hu hv i j
    by_cases hij : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr hij
    left
    rw [Units.val_mul, Matrix.mul_apply]
    by_cases hi : (i : ℕ) < a
    · have hk : ∀ k, (v : Matrix (Fin d) (Fin d) K) k j = if k = j then 1 else 0 :=
        fun k => (hv k j).resolve_right (by omega)
      simp only [hk]
      simpa using (hu i j).resolve_right hij
    · have hk : ∀ k, (u : Matrix (Fin d) (Fin d) K) i k = if i = k then 1 else 0 :=
        fun k => (hu i k).resolve_right (by omega)
      simp only [hk]
      simpa using (hv i j).resolve_right hij
  have hone : ∀ i j : Fin d, ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := fun i j => Or.inl (by simp [Matrix.one_apply])
  { carrier := {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ))}
    one_mem' := hone
    mul_mem' := fun {u v} hu hv => hmul u v hu hv
    inv_mem' := by
      intro u hu
      have hpow : ∀ n : ℕ, ∀ i j : Fin d, ((u ^ n : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
          (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hu
      have hinv : u⁻¹ = u ^ (orderOf u - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
      show ∀ i j : Fin d, ((u⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = _ ∨ _
      rw [hinv]
      exact hpow _ }

theorem mem_stdRadical {K : Type} [Field K] [Fintype K] [DecidableEq K] {d a : ℕ} {u : GL (Fin d) K} :
    u ∈ stdRadical K d a ↔ ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := Iff.rfl

theorem pm_conj {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (g : GL ι K) : pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g := by
  have hp : ∀ i j, (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
    intro i j
    show (Equiv.toPEquiv σ⁻¹).toMatrix i j = _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    exact if_congr Equiv.Perm.inv_eq_iff_eq rfl rfl
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  have hg : ∀ x : GL ι K, ((glEquiv K σ x : GL ι K) : Matrix ι ι K) = (x : Matrix ι ι K).submatrix σ.symm σ.symm :=
    fun _ => rfl
  simp only [Units.val_mul, Matrix.mul_apply, hp, hg, Matrix.submatrix_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm i) (fun x _ hx => if_neg (fun h => hx (by simp [h]))) (by simp)]
  simp

theorem eq_zero_of_sum_char {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) [DecidablePred (· ∈ U)]
    (h : (∑ u : G, if u ∈ U then ρ.character u else 0) = 0) (v : V) (hv : ∀ u ∈ U, ρ u v = v) : v = 0 := by
  have hc : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have h1 := Representation.card_inv_mul_sum_char_eq_finrank (ρ.comp U.subtype : Representation ℂ U V)
  have hs : (∑ u : G, if u ∈ U then ρ.character u else 0) =
      ∑ g : U, Representation.character (ρ.comp U.subtype : Representation ℂ U V) g := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) (fun g => ρ.character g)
  rw [hs] at h
  rw [h, mul_zero] at h1
  have h2 : Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ)]
    exact h1.symm
  have hm : v ∈ Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) := by
    rw [Representation.mem_invariants]
    exact fun u => hv u.1 u.2
  rw [h2] at hm
  simpa using hm

theorem isCuspidal_of_sum_char : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  classical
  intro K _ _ _ d τ h s b hb hs v hv
  let c0 : Fin s := ⟨0, by omega⟩
  let c1 : Fin s := ⟨1, by omega⟩
  have hc : c0 ≠ c1 := by simp [c0, c1, Fin.ext_iff]
  obtain ⟨i0, hi0⟩ := hb c0
  obtain ⟨i1, hi1⟩ := hb c1
  set a := Fintype.card {i // b i = c0} with ha
  have ha0 : 0 < a := Fintype.card_pos_iff.2 ⟨⟨i0, hi0⟩⟩
  have had : a < d := by
    have := Fintype.card_subtype_lt (p := fun i => b i = c0) (x := i1) (by rw [hi1]; exact hc.symm)
    simpa using this
  have hcard : Fintype.card {i // b i = c0} = Fintype.card {i : Fin d // (i : ℕ) < a} := by
    rw [← ha]
    exact (Fintype.card_fin a).symm.trans (Fintype.card_congr
      { toFun := fun k => ⟨⟨k, by omega⟩, k.2⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  let e := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm (Fin d) := e.extendSubtype
  have hσ : ∀ i, (σ i : ℕ) < a ↔ b i = c0 := by
    intro i
    by_cases hi : b i = c0
    · exact ⟨fun _ => hi, fun _ => e.extendSubtype_mem i hi⟩
    · exact ⟨fun h' => absurd h' (e.extendSubtype_not_mem i hi), fun h' => absurd h' hi⟩
  have hfix : ∀ w : τ, (∀ u ∈ stdRadical K d a, τ.ρ u w = w) → w = 0 := by
    refine eq_zero_of_sum_char τ.ρ (stdRadical K d a) ?_
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (h a ha0 had)
    by_cases hu : u ∈ stdRadical K d a
    · rw [if_pos hu, if_pos (mem_stdRadical.1 hu)]; rfl
    · rw [if_neg hu, if_neg (fun h' => hu (mem_stdRadical.2 h'))]

  have hent : ∀ (x : GL (Fin d) K) (i j : Fin d),
      ((pm K σ * x * (pm K σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) (σ j) =
        (x : Matrix (Fin d) (Fin d) K) i j := by
    intro x i j
    rw [pm_conj]
    show (x : Matrix (Fin d) (Fin d) K) (σ.symm (σ i)) (σ.symm (σ j)) = _
    simp
  have key : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a → ∀ i j,
      (x : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ (b i = c0 ∧ b j ≠ c0) := by
    intro x hx i j
    have := hx (σ i) (σ j)
    rw [hent] at this
    rcases this with h1 | ⟨h1, h2⟩
    · left; simpa [σ.injective.eq_iff] using h1
    · right
      refine ⟨(hσ i).1 h1, fun h3 => ?_⟩
      have := (hσ j).2 h3
      omega
  have hut : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a →
      IsBlockUT K b (x : Matrix (Fin d) (Fin d) K) := by
    intro x hx i j hij
    rcases key x hx i j with h1 | ⟨h1, -⟩
    · have : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
      simpa [this] using h1
    · rw [h1] at hij
      exact absurd hij (by simp [c0, Fin.lt_def])
  have hun : ∀ x : GL (Fin d) K, pm K σ * x * (pm K σ)⁻¹ ∈ stdRadical K d a → x ∈ unip K b := by
    intro x hx
    refine ⟨⟨hut x hx, hut x⁻¹ ?_⟩, ?_⟩
    · have : pm K σ * x⁻¹ * (pm K σ)⁻¹ = (pm K σ * x * (pm K σ)⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
    · intro i j hij
      rcases key x hx i j with h1 | ⟨h1, h2⟩
      · exact h1
      · exact absurd (hij ▸ h1) h2
  have hw := hfix (τ.ρ (pm K σ) v) (by
    intro u hu
    have hx : (pm K σ)⁻¹ * u * pm K σ ∈ unip K b := by
      apply hun
      have : pm K σ * ((pm K σ)⁻¹ * u * pm K σ) * (pm K σ)⁻¹ = u := by group
      rw [this]
      exact hu
    have hh : u * pm K σ = pm K σ * ((pm K σ)⁻¹ * u * pm K σ) := by group
    rw [← Module.End.mul_apply, ← map_mul, hh, map_mul, Module.End.mul_apply, hv _ hx])
  have h3 := congrArg (τ.ρ (pm K σ)⁻¹) hw
  simpa [← Module.End.mul_apply, ← map_mul] using h3

end GlobalTheory.CompanionTheory.TyFin.CuspIff
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalVanishing
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspVan

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem levi_mul {s : ℕ} (b : ι → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  exact blk_mul b c p.2.1 q.2.1

theorem unip_mul {s : ℕ} (b : ι → Fin s) {x y : GL ι K} (hx : x ∈ unip K b) (hy : y ∈ unip K b) :
    x * y ∈ unip K b := by
  refine ⟨mul_mem hx.1 hy.1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hx.2 i i rfl, if_pos rfl, one_mul]
    exact hy.2 i j hij
  · intro k _ hk
    rcases lt_trichotomy (b k) (b i) with h | h | h
    · rw [hx.1.1 i k h, zero_mul]
    · rw [hx.2 i k h.symm, if_neg (Ne.symm hk), zero_mul]
    · rw [hy.1.1 k j (hij ▸ h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem one_mem_unip {s : ℕ} (b : ι → Fin s) : (1 : GL ι K) ∈ unip K b := by
  refine ⟨one_mem _, fun i j _ => ?_⟩
  simp [Matrix.one_apply]

open Classical in

theorem sum_unip_rho {t : ℕ} (bb : ι → Fin t) (hs : Function.Surjective bb) (ht : 2 ≤ t)
    (τ : FDRep ℂ (GL ι K)) (hτ : IsCuspidal K τ) :
    ∑ v ∈ Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb), τ.ρ v = 0 := by
  set Y := Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb) with hY
  apply LinearMap.ext
  intro w
  apply hτ t bb hs ht
  intro y hy
  have himg : Y.image (fun v => y * v) = Y := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact unip_mul bb hy hv
    · rw [Finset.card_image_of_injective _ (mul_right_injective y)]
  have h1 : ∑ v ∈ Y, τ.ρ (y * v) = ∑ v ∈ Y, τ.ρ v := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a _ b _ h => mul_right_injective y h)]
  rw [LinearMap.sum_apply, map_sum, ← LinearMap.sum_apply, ← h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  rfl

open Classical in

theorem sum_char {t : ℕ} (bb : ι → Fin t) (hs : Function.Surjective bb) (ht : 2 ≤ t)
    (τ : FDRep ℂ (GL ι K)) (hτ : IsCuspidal K τ) (g : GL ι K) :
    ∑ v ∈ Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb), τ.character (g * v) = 0 := by
  have h := congrArg (fun P => LinearMap.trace ℂ τ (τ.ρ g * P)) (sum_unip_rho bb hs ht τ hτ)
  simp only [mul_zero, map_zero, Finset.mul_sum, map_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [FDRep.character, map_mul]

def rankMap {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) :
    κ → Fin (Finset.univ.image β).card := fun i =>
  ((Finset.univ.image β).orderIsoOfFin rfl).symm ⟨β i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

theorem rankMap_lt {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) (i j : κ) :
    rankMap β i < rankMap β j ↔ β i < β j := by
  simp only [rankMap]
  rw [OrderIso.lt_iff_lt]
  exact Iff.rfl

theorem rankMap_eq {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) (i j : κ) :
    rankMap β i = rankMap β j ↔ β i = β j := by
  simp only [rankMap]
  rw [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]

theorem rankMap_surj {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) :
    Function.Surjective (rankMap β) := by
  intro x
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (((Finset.univ.image β).orderIsoOfFin rfl) x).2
  refine ⟨i, ?_⟩
  simp only [rankMap]
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext hi

def extHom {s : ℕ} (b : ι → Fin s) (c : Fin s) : GL {i // b i = c} K →* GL ι K :=
  (leviEmb K (fun i => b i = c)).comp (MonoidHom.inl _ _)

theorem extHom_apply {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K) (i j : ι) :
    (extHom b c v : Matrix ι ι K) i j =
      if h : b i = c ∧ b j = c then (v : Matrix {i // b i = c} {i // b i = c} K) ⟨i, h.1⟩ ⟨j, h.2⟩ else if i = j then 1 else 0 := by
  have h0 : (extHom b c v : Matrix ι ι K) =
      (Matrix.fromBlocks (v : Matrix {i // b i = c} {i // b i = c} K) 0 0 1).submatrix
        (Equiv.sumCompl (fun i => b i = c)).symm (Equiv.sumCompl (fun i => b i = c)).symm := rfl
  rw [h0, Matrix.submatrix_apply]
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos]
  · have : i ≠ j := fun h => hj (h ▸ hi)
    simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, this]
  · have : i ≠ j := fun h => hi (h ▸ hj)
    simp [hi, hj, Equiv.sumCompl_symm_apply_of_pos, Equiv.sumCompl_symm_apply_of_neg, this]
  · simp [hi, hj, Equiv.sumCompl_symm_apply_of_neg, Matrix.one_apply, Subtype.ext_iff]

theorem extHom_blockUT {s s' : ℕ} (b : ι → Fin s) (c : Fin s) (β : ι → Fin s')
    {w : GL {i // b i = c} K}
    (hw : IsBlockUT K (rankMap fun i : {i // b i = c} => β i.1)
      (w : Matrix {i // b i = c} {i // b i = c} K)) :
    IsBlockUT K β (extHom b c w : Matrix ι ι K) := by
  intro i j h
  rw [extHom_apply]
  split_ifs with h1 h2
  · exact hw _ _ ((rankMap_lt _ _ _).mpr h)
  · exact absurd (h2 ▸ h) (lt_irrefl _)
  · rfl

theorem extHom_mem_unip {s s' : ℕ} (b : ι → Fin s) (c : Fin s) (β : ι → Fin s')
    {v : GL {i // b i = c} K} (hv : v ∈ unip K (rankMap fun i : {i // b i = c} => β i.1)) :
    extHom b c v ∈ unip K β := by
  refine ⟨⟨extHom_blockUT b c β hv.1.1, ?_⟩, fun i j hij => ?_⟩
  · rw [← map_inv]
    exact extHom_blockUT b c β hv.1.2
  · rw [extHom_apply]
    by_cases h : b i = c ∧ b j = c
    · rw [dif_pos h, hv.2 _ _ ((rankMap_eq _ _ _).mpr hij)]
      simp [Subtype.ext_iff]
    · rw [dif_neg h]

theorem extHom_off {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K) (i j : ι)
    (hij : b i ≠ b j) : (extHom b c v : Matrix ι ι K) i j = 0 := by
  rw [extHom_apply, dif_neg (fun h => hij (h.1.trans h.2.symm)),
    if_neg (fun e => hij (congrArg b e))]

theorem blkGL_mul {s : ℕ} (b : ι → Fin s) (c : Fin s) {g e : GL ι K} (hg : g ∈ parab K b)
    (he : e ∈ parab K b) : blkGL b c (g * e) = blkGL b c g * blkGL b c e := by
  simp only [blkGL]
  rw [dif_pos hg, dif_pos he, dif_pos (mul_mem hg he)]
  exact levi_mul b c ⟨g, hg⟩ ⟨e, he⟩

theorem blkGL_extHom_self {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K)
    (hp : extHom b c v ∈ parab K b) : blkGL b c (extHom b c v) = v := by
  simp only [blkGL]
  rw [dif_pos hp]
  apply Units.ext
  refine Matrix.ext ?_
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  change (extHom b c v : Matrix ι ι K) i j = _
  rw [extHom_apply, dif_pos ⟨hi, hj⟩]

theorem blkGL_extHom_ne {s : ℕ} (b : ι → Fin s) {c c' : Fin s} (hc : c' ≠ c)
    (v : GL {i // b i = c} K) (hp : extHom b c v ∈ parab K b) :
    blkGL b c' (extHom b c v) = 1 := by
  simp only [blkGL]
  rw [dif_pos hp]
  apply Units.ext
  refine Matrix.ext ?_
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  change (extHom b c v : Matrix ι ι K) i j = (1 : Matrix {i // b i = c'} {i // b i = c'} K) ⟨i, hi⟩ ⟨j, hj⟩
  rw [extHom_apply, dif_neg (fun h => hc (hi.symm.trans h.1)), Matrix.one_apply]
  simp [Subtype.ext_iff]

theorem vanish {s s' : ℕ} (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hcusp : ∀ c, IsCuspidal K (lam c))
    (c : Fin s) (i₀ j₀ : ι) (hi : b i₀ = c) (hj : b j₀ = c) (hβ : β i₀ ≠ β j₀)
    (H : Subgroup (GL ι K)) [DecidablePred (· ∈ H)] (F : GL ι K → ℂ) (hH : H ≤ parab K b)
    (hF : ∀ u ∈ unip K β, (∀ i j, b i ≠ b j → (u : Matrix ι ι K) i j = 0) →
      u ∈ H ∧ ∀ h ∈ H, F (h * u) = F h) :
    ∑ h, (if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0 := by
  set βc : {i // b i = c} → Fin s' := fun i => β i.1 with hβc
  have ht : 2 ≤ (Finset.univ.image βc).card :=
    Finset.one_lt_card.mpr ⟨βc ⟨i₀, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      βc ⟨j₀, hj⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hβ⟩
  have key : ∀ Y : Finset (GL {i // b i = c} K), (∀ v ∈ Y, v ∈ unip K (rankMap βc)) → 1 ∈ Y →
      (∀ g, ∑ v ∈ Y, (lam c).character (g * v) = 0) →
      ∑ h, (if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0) = 0 := by
    intro Y hY h1 hY0
    set A : GL ι K → ℂ := fun h => ∏ c' ∈ Finset.univ.erase c, (lam c').character (blkGL b c' h)
      with hA
    set G : GL ι K → GL {i // b i = c} K → ℂ := fun h v =>
      if h ∈ H then F h * ((lam c).character (blkGL b c h * v) * A h) else 0 with hG
    set T : GL ι K → ℂ := fun h =>
      if h ∈ H then F h * hcFun b (fun c => (lam c).character) h else 0 with hT
    have step : ∀ v ∈ Y, ∑ h, T h = ∑ h, G h v := by
      intro v hv
      obtain ⟨heH, hFe⟩ := hF (extHom b c v) (extHom_mem_unip b c β (hY v hv)) (extHom_off b c v)
      have hep : extHom b c v ∈ parab K b := hH heH
      refine (Equiv.sum_comp (Equiv.mulRight (extHom b c v)) T).symm.trans ?_
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [Equiv.coe_mulRight, hT, hG]
      by_cases hh : h ∈ H
      · rw [if_pos (mul_mem hh heH), if_pos hh, hFe h hh, hcFun,
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
          blkGL_mul b c (hH hh) hep, blkGL_extHom_self b c v hep]
        congr 2
        refine Finset.prod_congr rfl fun c' hc' => ?_
        rw [blkGL_mul b c' (hH hh) hep, blkGL_extHom_ne b (Finset.ne_of_mem_erase hc') v hep, mul_one]
      · rw [if_neg hh, if_neg (fun h' => hh (by simpa using mul_mem h' (inv_mem heH)))]
    have hcard : (Y.card : ℂ) * ∑ h, T h = 0 := by
      calc (Y.card : ℂ) * ∑ h, T h = ∑ _v ∈ Y, ∑ h, T h := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ v ∈ Y, ∑ h, G h v := Finset.sum_congr rfl step
        _ = ∑ h, ∑ v ∈ Y, G h v := Finset.sum_comm
        _ = 0 := by
            refine Finset.sum_eq_zero fun h _ => ?_
            by_cases hh : h ∈ H
            · simp only [hG, if_pos hh]
              rw [← Finset.mul_sum, ← Finset.sum_mul, hY0, zero_mul, mul_zero]
            · simp only [hG, if_neg hh, Finset.sum_const_zero]
    have hne : (Y.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem h1)
    exact (mul_eq_zero.mp hcard).resolve_left hne
  classical
  exact key _ (fun v hv => (Finset.mem_filter.mp hv).2)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_mem_unip _⟩)
    (sum_char (rankMap βc) (rankMap_surj βc) ht (lam c) (hcusp c))

theorem cuspVanish : ReciprocityTheory.Ty.Fin.St.CuspVanish := by
  intro K _ _ _ ι _ _ s s' b β lam hcusp ⟨i₀, j₀, hb, hβ⟩ H F hH hF
  classical
  exact vanish b β lam hcusp (b i₀) i₀ j₀ rfl hb.symm hβ H F hH hF

end GlobalTheory.CompanionTheory.TyFin.CuspVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteProductDifferenceBound
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem abs_prod_sub_prod_le_sum_powerset (V : Type) (a : V → ℝ) (A U : Finset V) (hAU : A ⊆ U) :
    |∏ v ∈ U, a v - ∏ v ∈ A, a v| ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by
  have hexp : ∀ S : Finset V, ∏ v ∈ S, a v = ∑ D ∈ S.powerset, ∏ v ∈ D, (a v - 1) := by
    intro S
    rw [← Finset.prod_one_add]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hfilt : U.powerset.filter (fun D => D ⊆ A) = A.powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hAU, h⟩⟩
  rw [hexp U, hexp A, ← Finset.sum_filter_add_sum_filter_not U.powerset (fun D => D ⊆ A), hfilt,
    add_sub_cancel_left]
  calc |∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, (a v - 1)|
      ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, |∏ v ∈ D, (a v - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by simp_rw [Finset.abs_prod]

end GlobalTheory.CompanionTheory.Mass.MeanV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteProjectionPushforwardStatement
section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projection_pushforward : FiniteGermProjectionOpenAt.Statement → IrreducibleGermPrimitiveForm.Statement → PrimitiveFormSheetedOffDiscriminant.Statement → UnbranchedProperCountConstant.Statement → ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) → (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0) → ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover | exact GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gallery_of_tubes_and_crossing : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.IdTube → PositivityTheory.RgEis.TubeChain → PositivityTheory.RgEis.Cross → PositivityTheory.RgEis.Gallery := by
  first | exact @GlobalTheory.CompanionTheory.RgEisGal.gallery | exact GlobalTheory.CompanionTheory.RgEisGal.gallery | (intros; apply GlobalTheory.CompanionTheory.RgEisGal.gallery <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelOneStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_sum_hermitian_norm_level_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ 1, ψ 1 (Ideal.Quotient.mk (lev ϖ 1) a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) = (ε : ℂ) * q := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one | exact GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumHermitianNormLevelShiftStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_sum_hermitian_norm_level_shift : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ (j + 2), ψ (j + 2) (Ideal.Quotient.mk (lev ϖ (j + 2)) a * (barσ σ ϖ hR.fix_ϖ (j + 2) w * w))) = (q : ℂ) ^ 2 * ∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w)) := by
  first | exact @GlobalTheory.CompanionTheory.GaussRec.gauss_recursion | exact GlobalTheory.CompanionTheory.GaussRec.gauss_recursion | (intros; apply GlobalTheory.CompanionTheory.GaussRec.gauss_recursion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterOrthogonalityStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_character_orthogonality : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (n k : ℕ) (Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)), Y ∈ hermMod σ ϖ n k → (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧ (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod | exact GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.HermOrth.orth_hermMod <;> assumption)
end

