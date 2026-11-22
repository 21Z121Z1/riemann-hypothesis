import Formalism.LagrangeIdealLifts.Statement

-- bundled from Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.CoeffSumXPowMulExpand
section
noncomputable section

namespace Formalism.LIFT

open Polynomial

def polyBase (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) : Base ℓ (Polynomial ℤ_[ℓ]) where
  φA := AlgHom.id ℤ_[ℓ] (Polynomial ℤ_[ℓ])
  γA := aeval (C (u : ℤ_[ℓ]) * X)
  X := X
  Q := 1
  u := u
  comm := fun _ => rfl
  φX := (mul_one _).symm
  γX := ⟨0, by
    change aeval (C (u : ℤ_[ℓ]) * X) (X : Polynomial ℤ_[ℓ]) =
      X * (algebraMap ℤ_[ℓ] (Polynomial ℤ_[ℓ]) (u : ℤ_[ℓ]) + X * 0)
    rw [aeval_X, mul_zero, add_zero, Polynomial.algebraMap_eq, mul_comm]⟩
  γQ := ⟨0, by simp⟩

lemma X_dvd_aeval_sub (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ_[ℓ]) (p : Polynomial ℤ_[ℓ]) :
    X ∣ aeval (C c * X) p - p := by
  rw [X_dvd_iff, coeff_sub, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero,
    ← comp_eq_aeval, eval_comp]
  simp

def polyWD (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) : WD (polyBase ℓ u) 0 (Polynomial ℤ_[ℓ]) where
  N := ⊤
  φ := LinearMap.id
  γ := (aeval (C (u : ℤ_[ℓ]) * X) : Polynomial ℤ_[ℓ] →ₐ[ℤ_[ℓ]] Polynomial ℤ_[ℓ]).toLinearMap
  φ_smul := fun _ _ => rfl
  γ_smul := fun a x => by
    simp only [AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
    rfl
  comm := fun _ => rfl
  X_inj := fun x hx => by
    change (X : Polynomial ℤ_[ℓ]) * x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left X_ne_zero
  Q_bij := by
    change Function.Bijective (fun x : Polynomial ℤ_[ℓ] => (1 : Polynomial ℤ_[ℓ]) • x)
    simp only [one_smul]
    exact Function.bijective_id
  φ_N := fun _ _ => Submodule.mem_top
  γ_N := fun x _ => by
    obtain ⟨c, hc⟩ := X_dvd_aeval_sub ℓ (u : ℤ_[ℓ]) x
    exact ⟨c, Submodule.mem_top, by
      simp only [AlgHom.toLinearMap_apply, smul_eq_mul]; exact hc⟩

theorem wDNonempty_proof : WDNonempty := by
  intro ℓ _ u
  refine ⟨polyBase ℓ u, polyWD ℓ u, rfl, ?_, ?_⟩
  · exact top_ne_bot
  · exact not_isUnit_X

section Decomp

variable {R : Type} [CommRing R]

def piece (ℓ : ℕ) (g : R[X]) (i : ℕ) : R[X] := contract ℓ (divX^[i] g)

end Decomp

end Formalism.LIFT
end
end

-- bundled from Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.CompsOfMemMap
section
noncomputable section

namespace Formalism.LIFT

open Finset

section XH

variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)

def Comps (ℓ : ℕ) (x : A) : Prop :=
  ∃ e : Fin ℓ → A, (∀ i, e i ∈ aa) ∧ x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)

theorem comps_zero : Comps φA ε aa ℓ 0 :=
  ⟨0, fun _ => aa.zero_mem, by simp⟩

theorem comps_add {x y : A} (hx : Comps φA ε aa ℓ x) (hy : Comps φA ε aa ℓ y) :
    Comps φA ε aa ℓ (x + y) := by
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨e', he', rfl⟩ := hy
  refine ⟨e + e', fun i => aa.add_mem (he i) (he' i), ?_⟩
  simp [map_add, mul_add, sum_add_distrib]

theorem comps_mul_phi (s : A) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (φA s * x) := by
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨fun i => s * e i, fun i => aa.mul_mem_left s (he i), ?_⟩
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring

theorem comps_mul_eps (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) {x : A} (hx : Comps φA ε aa ℓ x) :
    Comps φA ε aa ℓ (ε * x) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨Fin.cons (ε * e (Fin.last k)) (fun i => e i.castSucc), ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using aa.mul_mem_left ε (he (Fin.last k))
    · simpa using he j.castSucc
  · rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Fin.val_castSucc,
      Fin.val_last, map_mul, hε, pow_zero, one_mul, mul_add, mul_sum]
    rw [add_comm]
    congr 1
    · ring
    · refine sum_congr rfl fun i _ => ?_
      ring

theorem comps_mul_pow (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ) (n : ℕ) {x : A}
    (hx : Comps φA ε aa ℓ x) : Comps φA ε aa ℓ (ε ^ n * x) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact comps_mul_eps φA ε aa hℓ hε ih

theorem comps_sum {ι : Type} (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, Comps φA ε aa ℓ (f i)) :
    Comps φA ε aa ℓ (∑ i ∈ s, f i) :=
  Finset.sum_induction _ _ (fun _ _ => comps_add φA ε aa) (comps_zero φA ε aa) h

theorem comps_mul (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (r : A) {x : A} (hx : Comps φA ε aa ℓ x) : Comps φA ε aa ℓ (r * x) := by
  obtain ⟨e, he⟩ := (hU r).exists
  rw [he, sum_mul]
  refine comps_sum φA ε aa _ _ fun i _ => ?_
  rw [mul_assoc]
  exact comps_mul_pow φA ε aa hℓ hε _ (comps_mul_phi φA ε aa _ hx)

theorem comps_phi (hℓ : 0 < ℓ) {a : A} (ha : a ∈ aa) : Comps φA ε aa ℓ (φA a) := by
  refine ⟨fun i => if (i : ℕ) = 0 then a else 0, fun i => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact ha
    · exact aa.zero_mem
  · rw [Fintype.sum_eq_single ⟨0, hℓ⟩]
    · simp
    · intro i hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]

theorem comps_of_mem_map (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    {x : A} (hx : x ∈ Ideal.map φA aa) : Comps φA ε aa ℓ x := by
  let S : Ideal A :=
    { carrier := {x | Comps φA ε aa ℓ x}
      add_mem' := fun ha hb => comps_add φA ε aa ha hb
      zero_mem' := comps_zero φA ε aa
      smul_mem' := fun r _ hx => comps_mul φA ε aa hℓ hε hU r hx }
  have hle : Ideal.map φA aa ≤ S :=
    Ideal.map_le_iff_le_comap.2 fun a ha => comps_phi φA ε aa hℓ ha
  exact hle hx

theorem comp_mem (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    {x : A} (hx : x ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (he : x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) (i : Fin ℓ) : e i ∈ aa := by
  obtain ⟨e', he', hx'⟩ := comps_of_mem_map φA ε aa hℓ hε hU hx
  have : e = e' := (hU x).unique he hx'
  rw [this]
  exact he' i

theorem xh_comp (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (e : Fin ℓ → A)
    (h : X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) ∈ aa) (i : Fin ℓ) :
    X ^ H * e i ∈ aa := by
  have h1 := hQ _ h
  have h2 : Q ^ H * (X ^ H * ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) =
      ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (X ^ H * e i) := by
    simp only [map_mul, map_pow, hX, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  exact comp_mem φA ε aa hℓ hε hU h1 (fun i => X ^ H * e i) h2 i

theorem sum_split {M : Type} [AddCommMonoid M] (F : ℕ → M) (a N : ℕ) :
    ∑ i : Fin a, ∑ j ∈ range N, F (i + a * j) = ∑ k ∈ range (a * N), F k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_add, ← ih]
    simp only [sum_range_succ, sum_add_distrib]
    congr 1
    rw [Finset.sum_range (fun x => F (a * N + x))]
    refine sum_congr rfl fun i _ => ?_
    rw [add_comm]

theorem xh_coeffs (hℓ : 0 < ℓ) (hε : φA ε = ε ^ ℓ)
    (hU : ∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i))
    (X Q : A) (H : ℕ) (hX : φA X = X * Q)
    (hQ : ∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) (n : ℕ) :
    ∀ m : ℕ → ℤ, X ^ H * ∑ k ∈ range (ℓ ^ n), (m k : A) * ε ^ k ∈ aa →
      ∀ k < ℓ ^ n, X ^ H * (m k : A) ∈ aa := by
  induction n with
  | zero =>
    intro m h k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simpa using h
  | succ n ih =>
    intro m h k hk
    let e : Fin ℓ → A := fun i => ∑ j ∈ range (ℓ ^ n), (m (i + ℓ * j) : A) * ε ^ j
    have hdec : ∑ k ∈ range (ℓ ^ (n + 1)), (m k : A) * ε ^ k =
        ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i) := by
      rw [pow_succ', ← sum_split (fun k => (m k : A) * ε ^ k) ℓ (ℓ ^ n)]
      refine sum_congr rfl fun i _ => ?_
      simp only [e, map_sum, map_mul, map_intCast, map_pow, hε, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [pow_add, ← pow_mul]
      ring
    rw [hdec] at h
    have hb := xh_comp φA ε aa hℓ hε hU X Q H hX hQ e h ⟨k % ℓ, Nat.mod_lt _ hℓ⟩
    have hk' : k / ℓ < ℓ ^ n := by
      rw [Nat.div_lt_iff_lt_mul hℓ]
      rw [pow_succ] at hk
      exact hk
    have := ih (fun j => m (k % ℓ + ℓ * j)) hb (k / ℓ) hk'
    simpa [Nat.mod_add_div] using this

end XH

theorem xHKills_proof : XHKills := by
  intro ℓ _ A _ φA ε X Q H c aa _ hε hU hX hQ hc
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have h1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  obtain ⟨n, hn⟩ : ∃ n, c < ℓ ^ n := ⟨c, Nat.lt_pow_self h1⟩
  let p : Polynomial ℤ := (Polynomial.X - Polynomial.C 1) ^ c
  have hmon : p.Monic := (Polynomial.monic_X_sub_C (1 : ℤ)).pow c
  have hdeg : p.natDegree = c := by
    simp only [p]
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hsum : (ε - 1) ^ c = ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k := by
    have := Polynomial.aeval_eq_sum_range' (p := p) (by omega : p.natDegree < ℓ ^ n) ε
    simp only [zsmul_eq_mul] at this
    rw [← this]
    simp [p]
  have hmem : X ^ H * ∑ k ∈ range (ℓ ^ n), (p.coeff k : A) * ε ^ k ∈ aa := by
    rw [← hsum]
    exact aa.mul_mem_left _ hc
  have := xh_coeffs φA ε aa hℓ hε hU X Q H hX hQ n (fun k => p.coeff k) hmem c hn
  have hcoef : p.coeff c = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  simpa [hcoef] using this

end Formalism.LIFT
end
end

-- bundled from Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.Graded
section
namespace Formalism.LIFT

theorem gammaGradedStep_holds : GradedStep := by
  intro ℓ _ A _ _ B M D _ _ _ _ W i n hn
  obtain ⟨t, ht⟩ := B.γX
  obtain ⟨n', hn', hγ⟩ := W.γ_N n hn
  have hw : ∀ k : ℕ, ∃ r : A, (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t) ^ k
      = algebraMap ℤ_[ℓ] A ((B.u : ℤ_[ℓ]) ^ k) + B.X * r := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t)
        + algebraMap ℤ_[ℓ] A ((B.u : ℤ_[ℓ]) ^ k) * t, ?_⟩
      rw [pow_succ, hr, pow_succ, map_mul]; ring
  obtain ⟨r, hr⟩ := hw i
  have hγn : W.γ n = n + B.X • n' := by rw [← hγ]; abel
  refine ⟨r • n + (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t) ^ i • n', ?_, ?_⟩
  · exact W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')
  · rw [W.γ_smul, map_pow, ht, mul_pow, hγn, hr,
      ← algebraMap_smul A ((B.u : ℤ_[ℓ]) ^ i) (B.X ^ i • n)]
    module

theorem uGraded_of (h : GradedStep) : UGraded := by
  intro ℓ _ A _ _ B M D _ _ _ _ W K
  induction K with
  | zero =>
    intro n hn
    exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ K ih =>
    intro n hn
    obtain ⟨x, hx, n', hn', he⟩ := ih n hn
    obtain ⟨n'', hn'', hg⟩ := h ℓ A B M D W (K + 1) n' hn'
    refine ⟨((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • x + B.X ^ K • n', ?_, -n'', W.N.neg_mem hn'', ?_⟩
    · exact W.N.add_mem (Submodule.smul_of_tower_mem _ _ hx) (W.N.smul_mem _ hn')
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.X • (((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • x + B.X ^ K • n')
          = ((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • (B.X • x) + B.X ^ (K + 1) • n' := by
        rw [smul_add, smul_comm, ← mul_smul, ← pow_succ']
      rw [e1, LinearMap.map_add, LinearMap.map_smul]
      have e2 : W.γ (B.X ^ (K + 1) • n') = ((B.u : ℤ_[ℓ]) ^ (K + 1)) • (B.X ^ (K + 1) • n')
          + B.X ^ (K + 1 + 1) • n'' := by rw [← hg]; abel
      rw [e2]
      simp only [sub_smul, one_smul, smul_add, smul_sub, smul_neg]
      abel

namespace GradedDegree

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}

theorem X_pow_inj {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (k : ℕ) (x : D) (h : B.X ^ k • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply W.X_inj
    rw [← mul_smul, ← pow_succ']
    exact h

theorem aeval_mul_X {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (p : Polynomial ℤ_[ℓ]) : Polynomial.aeval g (p * Polynomial.X) = Polynomial.aeval g p * g := by
  rw [map_mul, Polynomial.aeval_X]

theorem aeval_mem {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (S : D → Prop) (hadd : ∀ x y, S x → S y → S (x + y))
    (hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x)) (hg : ∀ x, S x → S (g x))
    (p : Polynomial ℤ_[ℓ]) : ∀ x, S x → S (Polynomial.aeval g p x) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c x hx
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact hsmul c x hx
  · intro p q hp hq x hx
    rw [map_add, LinearMap.add_apply]
    exact hadd _ _ (hp x hx) (hq x hx)
  · intro k c h x hx
    rw [pow_succ, ← mul_assoc, aeval_mul_X, Module.End.mul_apply]
    exact h _ (hg x hx)

theorem hom_aeval {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WD B M D} {W' : WD B M D'} (f : Hom W W')
    (p : Polynomial ℤ_[ℓ]) : ∀ x, f.f (Polynomial.aeval W.γ p x) = Polynomial.aeval W'.γ p (f.f x) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c x
    rw [Polynomial.aeval_C, Polynomial.aeval_C, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, LinearMap.map_smul_of_tower]
  · intro p q hp hq x
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  · intro k c h x
    rw [pow_succ, ← mul_assoc, aeval_mul_X, aeval_mul_X, Module.End.mul_apply,
      Module.End.mul_apply, h, f.γ_comm]

theorem graded_prod (hG : GradedStep) {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (i j : ℕ) (hij : i ≤ j) :
    ∀ m ∈ W.N, ∃ m' ∈ W.N, Polynomial.aeval W.γ
      (∏ k ∈ Finset.Ico i j, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ k))) (B.X ^ i • m)
        = B.X ^ j • m' := by
  induction j, hij using Nat.le_induction with
  | base => intro m hm; exact ⟨m, hm, by simp⟩
  | succ j hij ih =>
    intro m hm
    obtain ⟨m', hm', he⟩ := ih m hm
    obtain ⟨m'', hm'', hg⟩ := hG ℓ A B M D W j m' hm'
    refine ⟨m'', hm'', ?_⟩
    rw [Finset.prod_Ico_succ_top hij, mul_comm, map_mul, Module.End.mul_apply, he, map_sub,
      Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, hg]

end GradedDegree

open GradedDegree in
theorem wBTail_of (hG : GradedStep) (hL : LagrangeIdealCyc) : WBTail := by
  intro ℓ _ A _ _ B M D₁ D₂ _ _ _ _ _ _ _ _ W₁ W₂ f s a hs hs2 hv hX n hn
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp (hL ℓ B.u s hs hs2 hv a)
  let S : D₂ → Prop := fun y => ∃ m ∈ W₁.N, y = f.f (B.X ^ a • m)
  have hadd : ∀ x y, S x → S y → S (x + y) := by
    rintro x y ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', W₁.N.add_mem hm hm', by rw [smul_add, map_add]⟩
  have hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x) := by
    rintro c x ⟨m, hm, rfl⟩
    exact ⟨c • m, Submodule.smul_of_tower_mem _ _ hm,
      by rw [smul_comm (B.X ^ a) c m]; exact (LinearMap.map_smul_of_tower f.f c _).symm⟩
  have hγS : ∀ x, S x → S (W₂.γ x) := by
    rintro x ⟨m, hm, rfl⟩
    obtain ⟨m', hm', hg⟩ := hG ℓ A B M D₁ W₁ a m hm
    refine ⟨((B.u : ℤ_[ℓ]) ^ a) • m + B.X • m',
      W₁.N.add_mem (Submodule.smul_of_tower_mem _ _ hm) (W₁.N.smul_mem _ hm'), ?_⟩
    have e : W₁.γ (B.X ^ a • m) = ((B.u : ℤ_[ℓ]) ^ a) • (B.X ^ a • m) + B.X ^ (a + 1) • m' := by
      rw [← hg]; abel
    rw [← f.γ_comm, e, smul_add, smul_comm (B.X ^ a) ((B.u : ℤ_[ℓ]) ^ a) m, ← mul_smul, ← pow_succ]
  obtain ⟨m, hm, hfm⟩ := hX n hn
  have hP₁ : S (Polynomial.aeval W₂.γ
      (∏ i ∈ Finset.range a, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ i))) (B.X ^ a • n)) := by
    obtain ⟨m₁, hm₁, h1⟩ := graded_prod hG W₁ 0 a (Nat.zero_le a) m hm
    rw [← Finset.range_eq_Ico, pow_zero, one_smul] at h1
    exact ⟨m₁, hm₁, by rw [← hfm, ← hom_aeval, h1]⟩
  have hP₂ : S (Polynomial.aeval W₂.γ
      (∏ i ∈ Finset.Ico a (2 * a), (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ i)))
        (B.X ^ a • n)) := by
    obtain ⟨n₂, hn₂, h2⟩ := graded_prod hG W₂ a (2 * a) (by omega) n hn
    obtain ⟨m₂, hm₂, hfm₂⟩ := hX n₂ hn₂
    exact ⟨m₂, hm₂, by rw [h2, LinearMap.map_smul, hfm₂, ← mul_smul, ← pow_add, two_mul]⟩
  have key : S (Polynomial.aeval W₂.γ (Polynomial.C ((ℓ : ℤ_[ℓ]) ^
      (2 * a * s + padicValNat ℓ (2 * a).factorial))) (B.X ^ a • n)) := by
    rw [← hαβ, map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    exact hadd _ _ (aeval_mem W₂.γ S hadd hsmul hγS α _ hP₁)
      (aeval_mem W₂.γ S hadd hsmul hγS β _ hP₂)
  rw [Polynomial.aeval_C, Module.algebraMap_end_apply] at key
  obtain ⟨m₃, hm₃, h3⟩ := key
  refine ⟨m₃, hm₃, ?_⟩
  have h0 := X_pow_inj W₂ a (f.f m₃ - ((ℓ : ℤ_[ℓ]) ^ (2 * a * s + padicValNat ℓ (2 * a).factorial)) • n)
    (by rw [smul_sub, ← LinearMap.map_smul, smul_comm (B.X ^ a), ← h3, sub_self])
  exact sub_eq_zero.mp h0

end Formalism.LIFT
end

