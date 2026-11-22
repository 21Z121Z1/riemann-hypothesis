import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesL2Space
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem blockDiagPart_mul {L : Type} [Field L] {n : ℕ} (β : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L)
    (hA : A.BlockTriangular β) (hB : B.BlockTriangular β) (hAB : A * B = 1) :
    (Matrix.of fun a b => if β a = β b then A a b else 0) *
      (Matrix.of fun a b => if β a = β b then B a b else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases h : β i = β j
  · rw [← hAB, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (β l) (β i) with h1 | h1 | h1
    · rw [hA h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hB (h ▸ h1 : β j < β l)]; simp
  · rw [Matrix.one_apply_ne (fun e => h (by rw [e]))]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : β i = β l
    · rw [if_neg (hl ▸ h : ¬ β l = β j), mul_zero]
    · rw [if_neg hl, zero_mul]

theorem leviPart : LeviPart := by
  intro L _ _ σ n β hβ g hg
  have hβ' : ∀ a b, β a = β b ↔ β a.rev = β b.rev := fun a b =>
    ⟨hβ a b, fun h => by simpa using hβ _ _ h⟩
  have h0 : (mat g⁻¹).BlockTriangular β := by
    letI : Invertible (mat g) := (g : GL (Fin n) L).invertible
    have e : mat g⁻¹ = (mat g)⁻¹ := by simp [mat]
    rw [e]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg
  have h1 := blockDiagPart_mul β _ _ h0 hg (mat_inv_mul g)
  set M : Matrix (Fin n) (Fin n) L := Matrix.of fun a b => if β a = β b then mat g a b else 0 with hM
  have h2 : antiJ L n * (cT σ M * antiJ L n) =
      Matrix.of fun a b => if β a = β b then mat g⁻¹ a b else 0 := by
    ext a b
    rw [antiJ_mul_apply, P.fSatake_cTJ, Matrix.of_apply, mat_inv_apply, hM, Matrix.of_apply]
    by_cases h : β a = β b
    · rw [if_pos h, if_pos ((hβ' _ _).1 h.symm)]
    · rw [if_neg h, if_neg (fun e => h ((hβ' _ _).2 e).symm), map_zero]
  have h3 : cT σ M * antiJ L n * M = antiJ L n := by
    rw [← h2] at h1
    calc cT σ M * antiJ L n * M
        = antiJ L n * (antiJ L n * (cT σ M * antiJ L n) * M) := by
          rw [← Matrix.mul_assoc (antiJ L n), ← Matrix.mul_assoc (antiJ L n),
            GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]
      _ = antiJ L n := by rw [h1, Matrix.mul_one]
  obtain ⟨m, hm⟩ := exists_mat M h3
  have hmL : m ∈ leviU σ β := fun i j h => by rw [hm, hM, Matrix.of_apply, if_neg h]
  refine ⟨m, hmL, fun a b h => by rw [hm, hM, Matrix.of_apply, if_pos h], fun i j h => ?_⟩
  rw [← mat_inv_mul m, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : β i = β l
  · rw [hm, hM, Matrix.of_apply]
    split_ifs with h4
    · rfl
    · rw [hg (lt_of_le_of_ne (hl ▸ h) (Ne.symm h4) : β j < β l)]
  · rw [(leviU σ β).inv_mem hmL i l hl, zero_mul, zero_mul]

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCellSumLeviReductionOfSteps
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem exists_diag_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L}
    (hσ : σ ϖ = ϖ) (h0 : ϖ ≠ 0) {r : ℕ} (b : Fin r → ℤ) (hb : ∀ i, b i.rev = -b i) :
    ∃ s : GU σ r, mat s = Matrix.diagonal (fun i => ϖ ^ b i) := by
  obtain ⟨s, hs, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  exact ⟨s, hs⟩

theorem leviStep_of_steps (hR : RankOne) (hE : EmbExists) (hM : EmbMem) (hT : EmbTorus) (hL : LeviRad)
    (hS : UnipSplit) (hC : Contract) (hJ : TorusConj) : LeviStep := by
  intro L _ _ ϖ σ q n r e β γ b B B' Q d t t' h hU hD hb hbd hB hB' hBB hd ht ht' hQ hidx hcar hh
  have hv := hU.2.1
  have hϖ : σ ϖ = ϖ := hU.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h0
    have := hU.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hinj : Function.Injective e := hD.1.injective
  obtain ⟨ι, hι⟩ := hE L σ n r e hinj hD.2.1
  obtain ⟨s₀, hs₀⟩ := exists_diag_zpow hϖ h0 b hb
  obtain ⟨s, hs⟩ := exists_diag_zpow hϖ h0 (fun i => B (e i)) (fun i => by rw [hD.2.1, hB])
  obtain ⟨s', hs'⟩ := exists_diag_zpow hϖ h0 (fun i => B' (e i)) (fun i => by rw [hD.2.1, hB'])
  obtain ⟨z, hz, hz', hzc⟩ := hT L σ n r e ι hinj hι (fun a => ϖ ^ B a) (fun a => ϖ ^ B' a) t t' s s' ht ht' hs hs'
    (fun a ha => by simp only [hBB a ha])
  have hMem := hM L σ n r e β γ ι hv hD hι
  have hCon := fun g hg => hC L ϖ σ q r γ b s₀ g hU hbd hs₀ hg
  have hnorm : s₀ ∈ Subgroup.normalizer ((rootU σ γ : Subgroup (GU σ r)) : Set (GU σ r)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => (hCon g hg).1, fun hg => ?_⟩
    have := (hCon _ hg).2.1
    simpa [mul_assoc] using this
  set c : MulAut (rootU σ γ) := (rootU σ γ).normalizerMonoidHom ⟨s₀, hnorm⟩ with hc
  have hc1 : ∀ a, ((c a : rootU σ γ) : GU σ r) = s₀ * a * s₀⁻¹ := fun a => rfl
  have hcz : ∀ (j : ℤ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹ := fun j a => by
    rw [hc, ← map_zpow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcn : ∀ (j : ℕ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹ := fun j a => by
    rw [hc, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcomap : (KU σ n).comap (ι.comp (rootU σ γ).subtype) = (KU σ r ⊓ rootU σ γ).subgroupOf (rootU σ γ) := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun ha => ⟨(hMem a).1.1 ha, a.2⟩, fun ha => (hMem a).1.2 ha.1⟩
  have hLR := hL L σ n β hv
  refine hR (GU σ n) (rootU σ γ) (KU σ n) (radU σ Fin.val) (radU σ β) (ι.comp (rootU σ γ).subtype) c Q d h t t'
    hh.1 (P.finite_supp (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) h hh) ?_ ?_ ?_ ?_ ?_ ?_ hQ ?_ ?_ ?_ ?_
  · intro u hu i j hij
    exact hu i j (hD.2.2.1 hij)
  · intro a
    exact (hMem a).2.2 a.2.1
  · intro u hu
    obtain ⟨a, ha, u', hu', e1⟩ := hS L σ n r e β γ ι hD hι u hu
    exact ⟨⟨a, ha⟩, u', hu', e1⟩
  · intro a u' hu'
    exact (hLR _ ((hMem a).2.1 a.2.2) u' hu').2
  · intro a u' hu'
    exact (hLR _ ((hMem a).2.1 a.2.2) u' hu').1
  · intro a ha
    exact (hMem _).1.2 ((hCon a a.2).2.2.1 ((hMem a).1.1 ha))
  · rw [hcomap, ← Subgroup.relIndex_map_map_of_injective _ _ (rootU σ γ).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← hidx s₀ hs₀, Subgroup.map_map]
    congr 1
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : KU σ r ⊓ rootU σ γ ≤ _), Subgroup.map_map]
    rfl
  · intro a
    obtain ⟨j, hj⟩ := (hCon a a.2).2.2.2
    refine ⟨j, (hMem _).1.2 ?_⟩
    rw [← hcn] at hj
    exact hj
  · intro a
    have e1 := hJ L ϖ σ r γ b (fun i => B' (e i)) d s₀ s' a h0 hd hs₀ hs' a.2.2
    show t' * ι a * t'⁻¹ = ι ((c ^ d) a : rootU σ γ)
    rw [hcz, ← e1, hz', map_mul, map_mul, map_inv, mul_assoc (ι s'), (hzc a).eq]
    group
  · intro a
    obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hcar s s' hs hs' a a.2
    have hk : ι k₂ ∈ leviU σ β := (hMem _).2.1 hk₂.2
    refine ⟨ι k₁, (hMem _).1.2 hk₁, ι k₂, (hMem _).1.2 hk₂.1, fun u hu => (hLR _ hk u hu).1, fun u hu => ?_, ?_⟩
    · simpa using (hLR _ (inv_mem hk) u hu).1
    · show (ι a)⁻¹ * t' = ι k₁ * (t * ι a) * ι k₂
      have e2 := congrArg ι e1
      simp only [map_mul, map_inv] at e2
      rw [hz, hz', ← mul_assoc, e2, mul_assoc (ι s), (hzc a).eq]
      simp only [mul_assoc]
      rw [(hzc k₂).eq]

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDiagonalFactorizationAlongEmbedding
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

open Classical in

theorem emb_mul_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    {e : Fin r → Fin n} {ι : GU σ r →* GU σ n} (he : Function.Injective e) (hι : IsEmb e ι)
    (D : Fin n → L) (s : GU σ r) (hs : mat s = Matrix.diagonal (D ∘ e)) :
    mat (ι s) * Matrix.diagonal (fun a => if a ∈ Set.range e then 1 else D a) = Matrix.diagonal D := by
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : b ∈ Set.range e
  · rw [if_pos hb, mul_one]
    by_cases ha : a ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      rw [(hι s).1, hs]
      simp [Matrix.diagonal_apply, he.eq_iff]
    · have hab : a ≠ b := fun h => ha (h ▸ hb)
      rw [(hι s).2 a b (Or.inl ha), Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab]
  · rw [if_neg hb, (hι s).2 a b (Or.inr hb)]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab, zero_mul]

theorem embTorus : EmbTorus := by
  classical
  intro L _ _ σ n r e ι he hι D D' t t' s s' ht ht' hs hs' hD
  have h1 := emb_mul_diagonal he hι D s hs
  have h2 := emb_mul_diagonal he hι D' s' hs'
  have hZ : (fun a => if a ∈ Set.range e then (1 : L) else D' a) =
      fun a => if a ∈ Set.range e then (1 : L) else D a := by
    funext a
    by_cases ha : a ∈ Set.range e
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha, hD a ha]
  have hz : mat ((ι s)⁻¹ * t) = Matrix.diagonal (fun a => if a ∈ Set.range e then (1 : L) else D a) := by
    rw [mat_mul, ht, ← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  refine ⟨(ι s)⁻¹ * t, by group, ?_, fun g => ?_⟩
  · apply mat_injective
    rw [mat_mul, hz, ← hZ, ht', ← h2]
  · apply mat_injective
    rw [mat_mul, mat_mul (ι g), hz]
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : a = b
    · subst hab
      exact mul_comm _ _
    · by_cases ha : a ∈ Set.range e
      · by_cases hb : b ∈ Set.range e
        · rw [if_pos ha, if_pos hb, one_mul, mul_one]
        · rw [(hι g).2 a b (Or.inr hb), Matrix.one_apply_ne hab, mul_zero, zero_mul]
      · rw [(hι g).2 a b (Or.inl ha), Matrix.one_apply_ne hab, mul_zero, zero_mul]

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDominantDiagonalConjugationContracts
section
open Formalism.UG GlobalTheory.SatakeWeyl

noncomputable section

namespace GlobalTheory.SatakeWeyl.ContractProof

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_inv_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) :
    mat s⁻¹ = Matrix.diagonal (fun i => ϖ ^ (-c i)) := by
  have h1 : mat s * Matrix.diagonal (fun i => ϖ ^ (-c i)) = 1 := by
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; simp
  calc mat s⁻¹ = mat s⁻¹ * (mat s * Matrix.diagonal (fun i => ϖ ^ (-c i))) := by rw [h1, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_conj {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (i l : Fin r) :
    mat (s * g * s⁻¹) i l = ϖ ^ (c i - c l) * mat g i l := by
  rw [mat_mul, mat_mul, mat_inv_diag h0 c s hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg,
    zpow_add₀ h0]
  ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_pow_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (j : ℕ) :
    mat (s ^ j) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * c i)) := by
  induction j with
  | zero => simp [mat_one]
  | succ j ih =>
    rw [pow_succ, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; congr 1; push_cast; ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem conj_mem_root {ϖ : L} (h0 : ϖ ≠ 0) (γ : Fin r → ℕ) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ) : s * g * s⁻¹ ∈ rootU σ γ := by
  refine ⟨fun i l h => ?_, fun i l h => ?_⟩
  · rw [mat_conj h0 c s g hs, hg.1 i l h]
    by_cases e : i = l
    · subst e; simp
    · rw [Matrix.one_apply_ne e, mul_zero]
  · rw [mat_conj h0 c s g hs, hg.2 i l h, mul_zero]

theorem conj_mem_K {ϖ : L} (h0 : ϖ ≠ 0) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (γ : Fin r → ℕ) (c : Fin r → ℤ)
    (s g : GU σ r) (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ)
    (H : ∀ i l, i < l → γ i = γ l → ϖ ^ (c i - c l) * mat g i l ∈ intL L) : s * g * s⁻¹ ∈ KU σ r := by
  rw [mem_KU_iff hσ]
  intro i l
  have hr := conj_mem_root h0 γ c s g hs hg
  by_cases h1 : i < l
  · by_cases h2 : γ i = γ l
    · rw [mat_conj h0 c s g hs]; exact H i l h1 h2
    · rw [hr.2 i l h2]; exact zero_mem _
  · rw [hr.1 i l (not_lt.1 h1), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem zpow_mul_int {ϖ : L} (hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → ϖ ^ m * x ∈ intL L := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by rw [hx, mul_zero]; exact zero_mem _⟩
  have hx' : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := by simpa using hx
  refine ⟨(WithZero.log (Valued.v x : WithZero (Multiplicative ℤ))).toNat, fun m hm => ?_⟩
  show Valued.v (ϖ ^ m * x) ≤ (1 : WithZero (Multiplicative ℤ))
  rw [map_mul, map_zpow₀, hv, ← WithZero.exp_log hx', ← WithZero.exp_zsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  have := Int.self_le_toNat (WithZero.log (Valued.v x : WithZero (Multiplicative ℤ)))
  simp only [smul_eq_mul]
  omega

theorem contract : GlobalTheory.SatakeWeyl.Contract := by
  intro L _ _ ϖ σ q r γ b s g hU hb hs hg
  obtain ⟨-, hσ, -, hv, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  refine ⟨conj_mem_root h0 γ b s g hs hg, ?_, fun hK => ?_, ?_⟩
  · have := conj_mem_root h0 γ _ s⁻¹ g (mat_inv_diag h0 b s hs) hg
    rwa [inv_inv] at this
  · refine conj_mem_K h0 hσ γ b s g hs hg fun i l h1 h2 => ?_
    refine mul_mem ?_ ((mem_KU_iff hσ g).1 hK i l)
    show Valued.v (ϖ ^ (b i - b l)) ≤ (1 : WithZero (Multiplicative ℤ))
    have := hb i l h1 h2
    rw [map_zpow₀, hv', ← WithZero.exp_zsmul, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    omega
  · choose N hN using fun p : Fin r × Fin r => zpow_mul_int hv' (mat g p.1 p.2)
    refine ⟨Finset.univ.sup N, conj_mem_K h0 hσ γ _ _ g (mat_pow_diag h0 b s hs _) hg fun i l h1 h2 => ?_⟩
    refine hN (i, l) _ ?_
    have h3 := hb i l h1 h2
    have h4 : (N (i, l) : ℤ) ≤ (Finset.univ.sup N : ℕ) := by
      exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ _)
    have h5 : (0 : ℤ) ≤ (Finset.univ.sup N : ℕ) := Int.natCast_nonneg _
    nlinarith

end GlobalTheory.SatakeWeyl.ContractProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets
section
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Four

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def unitaryFourUpperLeftBlock (g : GU σ 4) : Matrix (Fin 2) (Fin 2) L := !![mat g 0 0, mat g 0 1; mat g 1 0, mat g 1 1]

theorem unitaryFourUpperLeftBlock_mul_of_mem_levi {g : GU σ 4} (g' : GU σ 4) (hg : g ∈ leviU σ ![0, 0, 1, 1]) :
    unitaryFourUpperLeftBlock (g * g') = unitaryFourUpperLeftBlock g * unitaryFourUpperLeftBlock g' := by
  have h02 := hg 0 2 (by decide)
  have h03 := hg 0 3 (by decide)
  have h12 := hg 1 2 (by decide)
  have h13 := hg 1 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFourUpperLeftBlock, mat_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem unitaryFourUpperLeftBlock_one : unitaryFourUpperLeftBlock (1 : GU σ 4) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryFourUpperLeftBlock, mat_one]

theorem unitaryFourUpperLeftBlock_injective_on_levi {g g' : GU σ 4} (hg : g ∈ leviU σ ![0, 0, 1, 1]) (hg' : g' ∈ leviU σ ![0, 0, 1, 1])
    (h : unitaryFourUpperLeftBlock g = unitaryFourUpperLeftBlock g') : g = g' := by
  have h1 : unitaryFourUpperLeftBlock g⁻¹ * unitaryFourUpperLeftBlock g' = 1 := by
    rw [← h, ← unitaryFourUpperLeftBlock_mul_of_mem_levi _ (inv_mem hg), inv_mul_cancel, unitaryFourUpperLeftBlock_one]
  have h2 : unitaryFourUpperLeftBlock g' * unitaryFourUpperLeftBlock g'⁻¹ = 1 := by
    rw [← unitaryFourUpperLeftBlock_mul_of_mem_levi _ hg', mul_inv_cancel, unitaryFourUpperLeftBlock_one]
  have h3 : unitaryFourUpperLeftBlock g⁻¹ = unitaryFourUpperLeftBlock g'⁻¹ := left_inv_eq_right_inv h1 h2
  have low : ∀ i j : Fin 4, mat g⁻¹ j.rev i.rev = mat g'⁻¹ j.rev i.rev → mat g i j = mat g' i j := by
    intro i j e
    have e1 := mat_inv_apply g⁻¹ i j
    have e2 := mat_inv_apply g'⁻¹ i j
    rw [inv_inv] at e1 e2
    rw [e1, e2, e]
  have off : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ ![0, 0, 1, 1] j → mat g i j = mat g' i j :=
    fun i j e => by rw [hg i j e, hg' i j e]
  apply mat_injective
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact congrFun (congrFun h 1) 0
  · exact congrFun (congrFun h 1) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 1)
  · exact low _ _ (congrFun (congrFun h3 0) 1)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 0)
  · exact low _ _ (congrFun (congrFun h3 0) 0)

theorem exists_lift (h1 : ∀ x, σ (σ x) = x) (h2 : ∀ x, Valued.v (σ x) = Valued.v x) {p r u w : L}
    (hp : p ∈ intL L) (hr : r ∈ intL L) (hu : u ∈ intL L) (hw : w ∈ intL L) (hd : p * w - r * u = -1) :
    ∃ k ∈ KU σ 4 ⊓ leviU σ ![0, 0, 1, 1], unitaryFourUpperLeftBlock k = !![p, r; u, w] := by
  have hd' : σ p * σ w - σ r * σ u = -1 := by simpa using congrArg σ hd
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [h2]; exact hx
  obtain ⟨k, hk⟩ := exists_mat (σ := σ) !![p, r, 0, 0; u, w, 0, 0; 0, 0, -σ p, σ r; 0, 0, σ u, -σ w] (by
    ext i j
    rw [Matrix.mul_apply]
    simp only [P.fSatake_cTJ]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, antiJ, h1, Fin.rev] <;>
      first | linear_combination hd | linear_combination -hd | linear_combination hd' | linear_combination -hd' | ring)
  refine ⟨k, ⟨(mem_KU_iff h2 k).2 fun i j => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp [hp, hr, hu, hw, hs _ hp, hs _ hr, hs _ hu, hs _ hw]
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [unitaryFourUpperLeftBlock, hk]

theorem exists_conj {A D ξ : L} (hA : A ≠ 0) (hD : D ≠ 0) :
    ∃ p ∈ intL L, ∃ r ∈ intL L, ∃ u ∈ intL L, ∃ w ∈ intL L, p * w - r * u = -1 ∧
      !![D, -(A * ξ); 0, A] = !![p, r; u, w] * !![A, A * ξ; 0, D] * !![p, r; u, w] := by
  have mem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  by_cases h1 : ξ ∈ intL L
  · refine ⟨-ξ, neg_mem h1, 1, one_mem _, 1, one_mem _, 0, zero_mem _, by ring, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  by_cases h2 : A * ξ / D ∈ intL L
  · refine ⟨0, zero_mem _, 1, one_mem _, 1, one_mem _, -(A * ξ / D), neg_mem h2, by ring, ?_⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ, A * ξ = D * ζ := ⟨A * ξ / D, by field_simp⟩
    rw [hζ, mul_div_cancel_left₀ _ hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have hξ : ξ ≠ 0 := fun e => h1 (e ▸ zero_mem _)
  have inv : ∀ x : L, x ∉ intL L → x⁻¹ ∈ intL L := fun x hx => by
    rw [mem] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (not_le.1 hx).le
  refine ⟨1, one_mem _, 0, zero_mem _, -(ξ⁻¹ - (A * ξ / D)⁻¹), neg_mem (sub_mem (inv _ h1) (inv _ h2)),
    -1, neg_mem (one_mem _), by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem cartanFour : GlobalTheory.SatakeWeyl.CartanFour := by
  intro L _ _ ϖ σ q hU x y s s' hs hs' a ha
  obtain ⟨h1, h2, -, h4, -⟩ := hU
  have hϖ : ϖ ≠ 0 := fun e => by rw [e, map_zero] at h4; exact WithZero.zero_ne_coe h4
  have dl : ∀ (t : GU σ 4) (d : Fin 4 → L), mat t = Matrix.diagonal d → t ∈ leviU σ ![0, 0, 1, 1] :=
    fun t d e i j hij => by rw [e]; exact Matrix.diagonal_apply_ne _ fun e => hij (e ▸ rfl)
  have hsl := dl _ _ hs
  have hsl' := dl _ _ hs'
  have us : unitaryFourUpperLeftBlock s = !![ϖ ^ x, 0; 0, ϖ ^ y] := by simp [unitaryFourUpperLeftBlock, hs]
  have us' : unitaryFourUpperLeftBlock s' = !![ϖ ^ y, 0; 0, ϖ ^ x] := by simp [unitaryFourUpperLeftBlock, hs']
  have ua : unitaryFourUpperLeftBlock a = !![1, mat a 0 1; 0, 1] := by
    simp [unitaryFourUpperLeftBlock, ha.1 0 0 (by decide), ha.1 1 0 (by decide), ha.1 1 1 (by decide)]
  obtain ⟨p, hp, r, hr, u, hu, w, hw, hd, e⟩ :=
    exists_conj (ξ := mat a 0 1) (zpow_ne_zero x hϖ) (zpow_ne_zero y hϖ)
  obtain ⟨k, hk, uk⟩ := exists_lift h1 h2 hp hr hu hw hd
  refine ⟨k, hk.1, k, hk, ?_⟩
  rw [inv_mul_eq_iff_eq_mul]
  refine unitaryFourUpperLeftBlock_injective_on_levi hsl' (mul_mem ha.2 (mul_mem (mul_mem hk.2 (mul_mem hsl ha.2)) hk.2)) ?_
  have usa : unitaryFourUpperLeftBlock (s * a) = !![ϖ ^ x, ϖ ^ x * mat a 0 1; 0, ϖ ^ y] := by
    rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ hsl, us, ua]; simp
  rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ ha.2, unitaryFourUpperLeftBlock_mul_of_mem_levi _ (mul_mem hk.2 (mul_mem hsl ha.2)), unitaryFourUpperLeftBlock_mul_of_mem_levi _ hk.2, usa, uk, ← e, us', ua]
  simp [mul_comm]

end GlobalTheory.SatakeWeyl.Four

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesL2SpaceStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_preserves_L2_space : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → ∀ (μ' : Measure (Matrix α ν E)) [μ'.IsAddHaarMeasure] (g : UG c (stdJ ν E)) (φ : SB (Matrix α ν E)), ∫⁻ x, ‖(ω g φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' = ∫⁻ x, ‖(φ : Matrix α ν E → ℂ) x‖ₑ ^ 2 ∂μ' := by
  first | exact @GlobalTheory.KSp.weil_representation_preserves_L2 | exact GlobalTheory.KSp.weil_representation_preserves_L2 | (intros; apply GlobalTheory.KSp.weil_representation_preserves_L2 <;> assumption)
end

