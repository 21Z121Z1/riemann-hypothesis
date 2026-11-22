import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardStableEqCardHom
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory.StableGraph

variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁]
  [Algebra O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}

theorem mem_of_inl {M : Submodule O (A₁ × A₂)} (h : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    {a : A₁} (ha : (a, (0 : A₂)) ∈ M) : a ∈ M₁ := by
  rw [← h]; exact ha

theorem mem_of_snd {M : Submodule O (A₁ × A₂)} (h : M.map (LinearMap.snd O A₁ A₂) = M₂)
    {a : A₁} {x : A₂} (hx : (a, x) ∈ M) : x ∈ M₂ := by
  rw [← h]; exact Submodule.mem_map_of_mem (f := LinearMap.snd O A₁ A₂) hx

theorem exists_of_map {M : Submodule O (A₁ × A₂)} (h : M.map (LinearMap.snd O A₁ A₂) = M₂)
    (x : M₂) : ∃ a : A₁, (a, (x : A₂)) ∈ M := by
  have hx : (x : A₂) ∈ M.map (LinearMap.snd O A₁ A₂) := h ▸ x.2
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.1 hx
  have hp' : p = (p.1, (x : A₂)) := Prod.ext rfl hpx
  exact ⟨p.1, hp' ▸ hp⟩

noncomputable def classOf {M : Submodule O (A₁ × A₂)} (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂)
    (x : M₂) : A₁ ⧸ M₁ :=
  Submodule.Quotient.mk (exists_of_map h₂ x).choose

theorem classOf_eq {M : Submodule O (A₁ × A₂)} (h₁ : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂) {x : M₂} {a : A₁} (hp : (a, (x : A₂)) ∈ M) :
    classOf (M₁ := M₁) h₂ x = Submodule.Quotient.mk a := by
  unfold classOf
  rw [Submodule.Quotient.eq]
  apply mem_of_inl h₁
  have := M.sub_mem (exists_of_map h₂ x).choose_spec hp
  simpa using this

noncomputable def toHom (M : Submodule O (A₁ × A₂)) (h₁ : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun := classOf h₂
  map_add' x y := by
    obtain ⟨a, ha⟩ := exists_of_map h₂ x
    obtain ⟨b, hb⟩ := exists_of_map h₂ y
    rw [classOf_eq h₁ h₂ ha, classOf_eq h₁ h₂ hb, ← Submodule.Quotient.mk_add]
    exact classOf_eq h₁ h₂ (by simpa using M.add_mem ha hb)
  map_smul' c x := by
    obtain ⟨a, ha⟩ := exists_of_map h₂ x
    rw [classOf_eq h₁ h₂ ha, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    exact classOf_eq h₁ h₂ (by simpa using M.smul_mem c ha)

def graph (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : Submodule O (A₁ × A₂) where
  carrier := {p | ∃ h : p.2 ∈ M₂, Submodule.Quotient.mk p.1 = φ ⟨p.2, h⟩}
  add_mem' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨hx, ha⟩ ⟨hy, hb⟩
    refine ⟨M₂.add_mem hx hy, ?_⟩
    have e : (⟨x + y, M₂.add_mem hx hy⟩ : M₂) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    simp only [Prod.fst_add, Prod.snd_add] at *
    rw [e, map_add, Submodule.Quotient.mk_add, ha, hb]
  zero_mem' := ⟨M₂.zero_mem, by
    have e : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
    simp only [Prod.fst_zero, Prod.snd_zero]
    rw [e, map_zero, Submodule.Quotient.mk_zero]⟩
  smul_mem' := by
    rintro c ⟨a, x⟩ ⟨hx, ha⟩
    refine ⟨M₂.smul_mem c hx, ?_⟩
    have e : (⟨c • x, M₂.smul_mem c hx⟩ : M₂) = c • ⟨x, hx⟩ := rfl
    simp only [Prod.smul_fst, Prod.smul_snd] at *
    rw [e, map_smul, Submodule.Quotient.mk_smul, ha]

theorem mem_graph {φ : M₂ →ₗ[O] A₁ ⧸ M₁} {a : A₁} {x : A₂} :
    (a, x) ∈ graph φ ↔ ∃ h : x ∈ M₂, Submodule.Quotient.mk a = φ ⟨x, h⟩ := Iff.rfl

theorem graph_comap (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : (graph φ).comap (LinearMap.inl O A₁ A₂) = M₁ := by
    ext a
    simp only [Submodule.mem_comap, LinearMap.inl_apply]
    rw [mem_graph]
    constructor
    · rintro ⟨h, e⟩
      have e0 : (⟨0, h⟩ : M₂) = 0 := rfl
      rw [e0, map_zero, Submodule.Quotient.mk_eq_zero] at e
      exact e
    · intro ha
      refine ⟨M₂.zero_mem, ?_⟩
      have e0 : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
      rw [e0, map_zero, Submodule.Quotient.mk_eq_zero]
      exact ha

theorem graph_map (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : (graph φ).map (LinearMap.snd O A₁ A₂) = M₂ := by
    ext x
    constructor
    · rintro ⟨p, ⟨h, _⟩, rfl⟩
      exact h
    · intro hx
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective M₁ (φ ⟨x, hx⟩)
      exact ⟨(a, x), ⟨hx, ha⟩, rfl⟩

noncomputable def stableEquiv (g₁ : A₁) (g₂ : A₂) (hM₂ : ∀ y ∈ M₂, g₂ * y ∈ M₂) :
    {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧
        M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} ≃
      {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁,
        φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} where
  toFun M := ⟨toHom M.1 M.2.2.1 M.2.2.2, by
    obtain ⟨M, hst, h₁, h₂⟩ := M
    intro x y hy a ha
    obtain ⟨c, hc⟩ := exists_of_map h₂ x
    have hφx : toHom M h₁ h₂ x = Submodule.Quotient.mk c := classOf_eq h₁ h₂ hc
    rw [hφx, Submodule.Quotient.eq] at ha
    have h1 : (c - a, (0 : A₂)) ∈ M := by rw [← h₁] at ha; exact ha
    have h2 := hst _ hc
    have h3 := hst _ h1
    have h4 : (g₁ * a, (y : A₂)) ∈ M := by
      have := M.sub_mem h2 h3
      rw [hy]
      convert this using 1
      ext
      · simp only [Prod.fst_sub, Prod.fst_mul]; ring
      · simp
    exact classOf_eq h₁ h₂ h4⟩
  invFun φ := ⟨graph φ.1, by
    rintro ⟨a, x⟩ ⟨hx, ha⟩
    exact ⟨hM₂ x hx, (φ.2 ⟨x, hx⟩ ⟨g₂ * x, hM₂ x hx⟩ rfl a ha.symm).symm⟩,
    graph_comap φ.1, graph_map φ.1⟩
  left_inv M := by
    obtain ⟨M, hst, h₁, h₂⟩ := M
    apply Subtype.ext
    ext ⟨a, x⟩
    show (a, x) ∈ graph (toHom M h₁ h₂) ↔ (a, x) ∈ M
    rw [mem_graph]
    constructor
    · rintro ⟨hx, e⟩
      obtain ⟨c, hc⟩ := exists_of_map h₂ ⟨x, hx⟩
      have hφx : toHom M h₁ h₂ ⟨x, hx⟩ = Submodule.Quotient.mk c := classOf_eq h₁ h₂ hc
      rw [hφx, Submodule.Quotient.eq] at e
      have h1 : (a - c, (0 : A₂)) ∈ M := by rw [← h₁] at e; exact e
      have := M.add_mem h1 hc
      simpa using this
    · intro hm
      exact ⟨mem_of_snd h₂ hm, (classOf_eq h₁ h₂ hm).symm⟩
  right_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective M₁ (φ.1 x)
    have hm : (a, (x : A₂)) ∈ graph φ.1 := ⟨x.2, ha⟩
    exact (classOf_eq (graph_comap φ.1) (graph_map φ.1) hm).trans ha

end GlobalTheory.StableGraph

open GlobalTheory.StableGraph in

theorem GlobalTheory.StableGraph.card_stable_eq_card_hom : ∀ (O : Type) [CommRing O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] (g₁ : A₁) (g₂ : A₂) (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), (∀ y ∈ M₂, g₂ * y ∈ M₂) → Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} = Nat.card {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁, φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} := by
  intro O _ A₁ A₂ _ _ _ _ g₁ g₂ M₁ M₂ hM₂
  exact Nat.card_congr (stableEquiv g₁ g₂ hM₂)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosInnerEqShiftedOuter
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section WinInner

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def frobPerm : Equiv.Perm F := (frobeniusEquiv F p).toEquiv

theorem frobPerm_pow_apply (n : ℕ) (x : F) : (frobPerm (F := F) p ^ n) x = x ^ p ^ n := by
  rw [Equiv.Perm.coe_pow]
  have : (⇑(frobPerm (F := F) p)) = frobenius F p := by
    funext y; simp [frobPerm]
  rw [this, iterate_frobenius]

theorem pw_eq_zpow (k : ℤ) (x : F) : pw p k x = (frobPerm (F := F) p ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frobPerm_pow_apply]
    simp
  · push_neg at hk
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow]
    simp only [neg_neg, Int.toNat_natCast]
    rfl

theorem pw_pow (k : ℤ) (h : ℕ) (y : F) : pw p k (y ^ p ^ h) = pw p (k + h) y := by
  rw [pw_eq_zpow, pw_eq_zpow, ← frobPerm_pow_apply, ← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add]

theorem term_pow {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (r j : Fin h) (n : ℤ) :
    term p ϖ lam (fun i => x' i ^ p ^ h) r j n = ϖ * term p ϖ lam x' r j (n + 1) := by
  unfold term
  rw [pw_pow]
  have h1 : ((r : ℤ) + n * h + h) = (r : ℤ) + (n + 1) * h := by ring
  have h2 : ϖ ^ (-n) = ϖ * ϖ ^ (-(n + 1)) := by
    rw [show -n = -(n + 1) + 1 by ring, zpow_add_one₀ hϖ]; ring
  rw [h1, h2]; ring

theorem rowT_pow {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (K : ℕ) (hK : 1 ≤ K) (r : Fin h) :
    rowT p ϖ lam K (fun i => x' i ^ p ^ h) r = ϖ * rowS p ϖ lam (K - 1) (K + 1) x' r := by
  unfold rowT rowS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [term_pow p ϖ hϖ]
  rw [← Finset.mul_sum]
  congr 1
  have hI : Finset.Icc (-((K - 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ)
      = (Finset.Icc (-(K : ℤ)) (K : ℤ)).map (addRightEmbedding 1) := by
    rw [Finset.map_add_right_Icc]
    congr 1 <;> push_cast [hK] <;> ring
  rw [hI, Finset.sum_map]
  rfl

end WinInner

theorem win_inner : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F),
    ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F,
      Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} =
        Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  intro F _ p _ _ _ h K ϖ hϖ hK lam π
  let e : (Fin h → F) ≃ (Fin h → F) := Equiv.piCongrRight fun _ => frobPerm (F := F) p ^ h
  have he : ∀ x' : Fin h → F, e x' = fun i => x' i ^ p ^ h := by
    intro x'; funext i; simp [e, frobPerm_pow_apply]
  symm
  refine Nat.card_congr (e.subtypeEquiv fun x' => ?_)
  rw [he]
  have hq : p ^ h ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (h1 j) _
    · rw [rowT_pow p ϖ hϖ lam x' K hK, h2 r, mul_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · have := h1 j
      rw [norm_pow] at this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hq).1 this
    · have := h2 r
      rw [rowT_pow p ϖ hϖ lam x' K hK] at this
      exact (mul_eq_zero.1 this).resolve_left hϖ

end GlobalTheory.PMonE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsCharpolyCoeffEq
section
open GlobalTheory.JR Matrix

namespace GlobalTheory.JR.CompanionCharpoly

theorem companion_map {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {r : ℕ} (p : Fin r → k) :
    (companion p).map f = companion (fun i => f (p i)) := by
  ext i j
  simp only [Matrix.map_apply, companion, Matrix.of_apply]
  split_ifs <;> simp

theorem coeff_universal (r : ℕ) (i : Fin r) :
    (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).charpoly.coeff (i : ℕ) =
      MvPolynomial.X i := by
  set R := MvPolynomial (Fin r) ℤ
  set K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  apply hinj
  have h := GlobalTheory.JR.NormalFormL.charpoly_companion_coeff
    (fun j : Fin r => algebraMap R K (MvPolynomial.X j)) i
  rw [← companion_map, Matrix.charpoly_map, Polynomial.coeff_map] at h
  exact h

theorem charpoly_companion_coeff_ring :
    ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  intro k _ r p i
  let f : MvPolynomial (Fin r) ℤ →+* k := MvPolynomial.eval₂Hom (Int.castRingHom k) p
  have hp : companion p = (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).map f := by
    rw [companion_map]
    congr 1
    funext j
    simp [f]
  rw [hp, Matrix.charpoly_map, Polynomial.coeff_map, coeff_universal]
  simp [f]

end GlobalTheory.JR.CompanionCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceSubgroupsGLPadic
section
namespace GlobalTheory

theorem norm_mul_sub_one_le_of_norm_sub_one_le {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ t) (hY : ∀ i j, ‖(Y - 1) i j‖ ≤ t) :
    ∀ i j, ‖(X * Y - 1) i j‖ ≤ t := by
  intro i j
  have hXY : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]; abel
  have hp := GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (X - 1) (Y - 1) t t h0 h0 hX hY i j
  have htt : t * t ≤ t := by nlinarith
  rw [hXY, Matrix.add_apply, Matrix.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp.trans htt))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))

theorem congruenceSubgroups_GL_padic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n],
    ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔
      ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l _ n _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : ∀ k : ℕ, 0 ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) ∧ (l : ℝ) ^ (-((k : ℤ) + 2)) < 1 := by
    intro k
    refine ⟨zpow_nonneg (by linarith) _, zpow_lt_one_of_neg₀ hl (by omega)⟩
  refine ⟨fun k => {
    carrier := {X | ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))}
    one_mem' := by
      intro i j
      simpa using (ht k).1
    mul_mem' := by
      intro X Y hX hY
      simp only [Set.mem_setOf_eq, Units.val_mul] at *
      exact norm_mul_sub_one_le_of_norm_sub_one_le _ _ _ (ht k).1 (ht k).2.le hX hY
    inv_mem' := by
      intro X hX
      simp only [Set.mem_setOf_eq] at *
      exact GlobalTheory.T.ultrametric_matrix_inv_near_one ℚ_[l] n (X : Matrix n n ℚ_[l]) ((X⁻¹ : GL n ℚ_[l]) : Matrix n n ℚ_[l]) _
        (ht k).1 (ht k).2 (Units.inv_mul X) hX }, fun k X => Iff.rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousDistribHaarCharUnitsOfCompactOpen
section
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory

theorem continuous_distribHaarChar_units_of_compact_open (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] (S : Set R) (hSo : IsOpen S) (hSc : IsCompact S)
    (hSn : S.Nonempty) : Continuous (fun u : Rˣ => distribHaarChar R u) := by
  obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hSc hSo subset_rfl
  have h0 : μ S ≠ 0 := hSo.measure_ne_zero μ hSn
  have ht : μ S ≠ ⊤ := hSc.measure_lt_top.ne
  have hle : ∀ u : Rˣ, (u : R) ∈ V → distribHaarChar R u ≤ 1 := by
    intro u hu
    have h1 : μ (u • S) ≤ μ S := by
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hVS ⟨u, hu, x, hx, rfl⟩
    rw [← distribHaarChar_mul μ u S] at h1
    have h2 : ((distribHaarChar R u : NNReal) : ENNReal) * μ S ≤ 1 * μ S := by simpa using h1
    have h3 := (ENNReal.mul_le_mul_iff_left h0 ht).1 h2
    exact_mod_cast h3
  refine continuous_of_continuousAt_one (distribHaarChar R : Rˣ →* NNReal) ?_
  have e1 : ∀ᶠ u : Rˣ in 𝓝 1, (u : R) ∈ V :=
    Units.continuous_val.continuousAt.eventually (show V ∈ 𝓝 ((1 : Rˣ) : R) by simpa using hV)
  have e2 : ∀ᶠ u : Rˣ in 𝓝 1, ((u⁻¹ : Rˣ) : R) ∈ V :=
    Units.continuous_coe_inv.continuousAt.eventually
      (show V ∈ 𝓝 (((1 : Rˣ)⁻¹ : Rˣ) : R) by simpa using hV)
  have e3 : (fun _ : Rˣ => (1 : NNReal)) =ᶠ[𝓝 1] (distribHaarChar R : Rˣ →* NNReal) := by
    filter_upwards [e1, e2] with u h1 h2
    have a1 := hle u h1
    have a2 := hle u⁻¹ h2
    have a3 : distribHaarChar R u * distribHaarChar R u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    refine le_antisymm ?_ a1
    calc (1 : NNReal) = distribHaarChar R u * distribHaarChar R u⁻¹ := a3.symm
      _ ≤ distribHaarChar R u * 1 := by gcongr
      _ = _ := mul_one _
  exact continuousAt_const.congr e3

theorem exists_isHaarMeasure_units_div_module : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [IsOpenUnits R] [MeasurableSpace R] [BorelSpace R] [BorelSpace Rˣ] (μ : Measure R), μ.IsAddHaarMeasure → (∃ S : Set R, IsOpen S ∧ IsCompact S ∧ S.Nonempty) → ∃ μ' : Measure Rˣ, μ'.IsHaarMeasure ∧ ∀ (g δ : R → ℂ), (∀ u : Rˣ, δ u = ((distribHaarChar R u : ℝ) : ℂ)) → ∀ T : Set Rˣ, MeasurableSet T → ∫ u in T, g u ∂μ' = ∫ t in Units.val '' T, g t * (δ t)⁻¹ ∂μ := by
  intro R _ _ _ _ _ _ _ _ _ _ μ hμ ⟨S, hSo, hSc, hSn⟩
  have hc := continuous_distribHaarChar_units_of_compact_open R μ S hSo hSc hSn
  have hoe : IsOpenEmbedding (Units.val : Rˣ → R) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hme : MeasurableEmbedding (Units.val : Rˣ → R) := hoe.measurableEmbedding
  set ν : Measure Rˣ := μ.comap Units.val with hν
  set f : Rˣ → NNReal := fun u => distribHaarChar R u⁻¹ with hf
  have hfc : Continuous f := hc.comp continuous_inv
  have hνa : ∀ s : Set Rˣ, ν s = μ (Units.val '' s) := fun s => hme.comap_apply μ s
  haveI : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hs'⟩ := μ.finiteAt_nhds (x : R)
    refine ⟨Units.val ⁻¹' s, hoe.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    rw [hνa]
    exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hs'
  haveI : ν.IsOpenPosMeasure := by
    refine ⟨fun U hU hn => ?_⟩
    rw [hνa]
    exact (hoe.isOpenMap U hU).measure_ne_zero μ (hn.image _)
  haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := ν) hfc
  have hpos : (ν.withDensity fun x => (f x : ENNReal)).IsOpenPosMeasure := by
    refine (withDensity_absolutelyContinuous' (μ := ν)
      (hfc.measurable.coe_nnreal_ennreal.aemeasurable) ?_).isOpenPosMeasure
    exact Eventually.of_forall fun x => by
      simpa [hf] using (distribHaarChar_pos (A := R) (g := x)).ne'
  have hinv : (ν.withDensity fun x => (f x : ENNReal)).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hma : MeasurableEmbedding (fun x : Rˣ => a * x) :=
      (Homeomorph.mulLeft a).measurableEmbedding
    have hmap : Measure.map (fun x : Rˣ => a * x) ν = (f a : ENNReal) • ν := by
      ext s hs
      rw [hma.map_apply, Measure.smul_apply, hνa, hνa, smul_eq_mul, hf,
        distribHaarChar_mul μ a⁻¹]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, ⟨a * x, hx, rfl⟩, by simp [Units.smul_def]⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨a⁻¹ * x, by simpa using hx, by simp [Units.smul_def]⟩
    ext s hs
    rw [hma.map_apply, withDensity_apply _ (hma.measurable hs), withDensity_apply _ hs]
    have h1 : ∀ x : Rˣ, (f x : ENNReal) = (f a⁻¹ : ENNReal) * (f (a * x) : ENNReal) := by
      intro x
      rw [← ENNReal.coe_mul, hf]
      simp only
      rw [← map_mul]
      congr 2
      simp [mul_comm a x, mul_left_comm]
    have h2 : (f a⁻¹ : ENNReal) * (f a : ENNReal) = 1 := by
      rw [← ENNReal.coe_mul, hf]
      simp only
      rw [← map_mul]
      simp
    calc ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f x : ENNReal) ∂ν
        = ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f a⁻¹ : ENNReal) * (f (a * x) : ENNReal) ∂ν := by
          exact lintegral_congr h1
      _ = (f a⁻¹ : ENNReal) * ∫⁻ x in (fun x : Rˣ => a * x) ⁻¹' s, (f (a * x) : ENNReal) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (f a⁻¹ : ENNReal) * ∫⁻ x in s, (f x : ENNReal) ∂(Measure.map (fun x : Rˣ => a * x) ν) := by
          rw [hma.restrict_map, hma.lintegral_map]
      _ = _ := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, h2,
            one_mul]
  refine ⟨ν.withDensity fun x => (f x : ENNReal), ⟨⟩, fun g δ hδ T hT => ?_⟩
  rw [setIntegral_withDensity_eq_setIntegral_smul hfc.measurable _ hT]
  have h3 := hme.setIntegral_map (μ := ν) (fun t => g t * (δ t)⁻¹) (Units.val '' T)
  rw [hν, hme.map_comap, Measure.restrict_restrict (hme.measurableSet_image.2 hT),
    Set.inter_eq_left.2 (Set.image_subset_range _ _),
    Set.preimage_image_eq _ hme.injective] at h3
  rw [h3]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [hδ, hf, map_inv, NNReal.smul_def, NNReal.coe_inv, Complex.real_smul]
  push_cast
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnHermitianBlockMatrixOfInvariants
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.ImgSec

theorem continuousOn_mkX_of_isUnit_det (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E)
    (hc : ContinuousOn h Ω) (hd : ∀ a ∈ Ω, IsUnit (h a).det) :
    ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := by
  haveI := GlobalTheory.JR.ImgSec.continuousStar (E := E) F
  have hinv : ContinuousOn (fun a => (h a)⁻¹) Ω := by
    intro a ha
    exact (continuousAt_matrix_inv (h a)
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (hd a ha).ne_zero)).comp_continuousWithinAt (hc a ha)
  have hmap : Continuous (fun a : Inv r F => (hankelShift a).map (algebraMap F E)) :=
    continuous_matrix fun i j => (continuous_algebraMap F E).comp
      ((continuous_apply_apply i j).comp continuous_hankelShift)
  have h1 : ContinuousOn (fun a => star (h a)⁻¹ * (hankelShift a).map (algebraMap F E) * (h a)⁻¹) Ω :=
    (hinv.star.mul hmap.continuousOn).mul hinv
  have h2 : ContinuousOn (fun a => h a *ᵥ (e1 : Fin r → E)) Ω := by
    exact (continuous_id.matrix_mulVec continuous_const).comp_continuousOn hc
  have h3 : Continuous (fun a : Inv r F => a.2.2) := continuous_snd.comp continuous_snd
  have h1' : ContinuousOn (fun a => (GlobalTheory.JR.ImgSec.mkX a (h a)).1) Ω := by
    intro a ha
    exact Topology.IsInducing.subtypeVal.continuousWithinAt_iff.2 (h1 a ha)
  exact h1'.prodMk (h2.prodMk h3.continuousOn)

end GlobalTheory.JR.ImgSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvrStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_embedding_fractionField_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes → ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCongruenceNearSymmetricMatrixStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_congruence_near_symmetric_matrix : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (H₀ : Matrix (Fin r) (Fin r) F), H₀.IsSymm → H₀.det ≠ 0 → ∃ (Ω : Set (Matrix (Fin r) (Fin r) F)) (k : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F), IsOpen Ω ∧ H₀ ∈ Ω ∧ ContinuousOn k Ω ∧ k H₀ = 1 ∧ ∀ H ∈ Ω, H.IsSymm → (k H)ᵀ * H₀ * k H = H := by
  first | exact @GlobalTheory.symm_congr_local_continuous | exact GlobalTheory.symm_congr_local_continuous | (intros; apply GlobalTheory.symm_congr_local_continuous <;> assumption)
end

