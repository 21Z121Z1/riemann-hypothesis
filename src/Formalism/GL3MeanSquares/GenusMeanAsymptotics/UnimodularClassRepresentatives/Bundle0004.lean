import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0002
import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFiberMulCardRange
import Lemmata.GeneralBFactSecondVariant.Imports

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsInvOneAdd
section
open Matrix

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Cayley.exists_det_one_add (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ s ∈ S, (1 + ϖ • M).det = 1 + ϖ * s := by
  obtain ⟨M₀, rfl⟩ := hM.exists_map
  let ϖ₀ : S := ⟨ϖ, hS.mem⟩
  refine ⟨((Matrix.trace M₀ + (Matrix.det (1 + (Polynomial.X : Polynomial S) •
      M₀.map Polynomial.C)).divX.divX.eval ϖ₀ * ϖ₀ : S) : K), SetLike.coe_mem _, ?_⟩
  have hmap : (1 : Matrix n n K) + ϖ • M₀.map S.subtype = S.subtype.mapMatrix (1 + ϖ₀ • M₀) := by
    ext i j
    by_cases h : i = j <;> simp [h, ϖ₀]
  rw [hmap, ← RingHom.map_det, Matrix.det_one_add_smul ϖ₀ M₀]
  simp only [map_add, map_mul, map_one, map_pow, Subring.coe_subtype]
  simp only [Subring.coe_add, Subring.coe_mul, ϖ₀]
  ring

theorem Cayley.exists_inv_one_add (hS : IsLocUnif S ϖ) {M : Matrix n n K} (hM : Ent S M) :
    ∃ Q : Matrix n n K, Ent S Q ∧ (1 + ϖ • M) * Q = 1 := by
  obtain ⟨s, hs, hdet⟩ := Cayley.exists_det_one_add hS hM
  obtain ⟨hne, hinv⟩ := hS.rad s hs
  have hA : Ent S (1 + ϖ • M) := Ent.add Ent.one (Ent.smul hS.mem hM)
  refine ⟨(1 + ϖ * s)⁻¹ • (1 + ϖ • M).adjugate, Ent.smul hinv hA.adjugate, ?_⟩
  rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem exists_cayley (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e l N : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hN : 2 * l + e + 1 ≤ N)
    {X Z W' : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ N • Z)
    {c : K} (hc : c ∈ S) (hcc : c + star c = 1) (hW' : Ent S W')
    (hWW : (c • (1 : Matrix n n K) + star c • X) * W' = ϖ ^ l • (1 : Matrix n n K)) :
    ∃ G D : Matrix n n K, Ent S D ∧ Gᴴ * H * G = H ∧ G = X + ϖ ^ (N - 2 * l - e) • D := by
  classical
  set j := N - 2 * l - e with hj
  have hj1 : 1 ≤ j := by omega
  have hNj : N = j + e + 2 * l := by omega
  have hϖ0 : ϖ ≠ 0 := hS.ne
  have hstar : ∀ k : ℕ, star (ϖ ^ k) = ϖ ^ k := fun k => by rw [star_pow, hS.fix]
  have hcs : star c ∈ S := hS.star_mem c hc
  obtain ⟨A, hA⟩ : ∃ A : Matrix n n K, A = c • (1 : Matrix n n K) + star c • X := ⟨_, rfl⟩
  rw [← hA] at hWW
  have hAent : Ent S A := by
    rw [hA]
    exact Ent.add (Ent.smul hc Ent.one) (Ent.smul hcs hX)
  have hWA : W' * A = ϖ ^ l • (1 : Matrix n n K) := by
    have hne : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
    have h1 : A * ((ϖ ^ l)⁻¹ • W') = 1 := by
      rw [Matrix.mul_smul, hWW, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have h2 : ((ϖ ^ l)⁻¹ • W') * A = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h2
    calc W' * A = ϖ ^ l • ((ϖ ^ l)⁻¹ • (W' * A)) := by
          rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
      _ = ϖ ^ l • (1 : Matrix n n K) := by rw [h2]
  have hAW : ∀ M : Matrix n n K, Aᴴ * (W'ᴴ * M) = ϖ ^ l • M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hWA, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hstar, Matrix.smul_mul, Matrix.one_mul]
  have hHE' : ∀ M : Matrix n n K, H * (E * M) = ϖ ^ e • M := by
    intro M
    rw [← Matrix.mul_assoc, hHE, Matrix.smul_mul, Matrix.one_mul]
  have hZh : Zᴴ = Z := by
    have h1 : (Xᴴ * H * X)ᴴ = Xᴴ * H * X := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
        Matrix.mul_assoc]
    rw [hXZ, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hH, hstar] at h1
    exact smul_right_injective _ (pow_ne_zero N hϖ0) (add_left_cancel h1)
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : Matrix n n K, D₁ = E * (W'ᴴ * (Z * W')) := ⟨_, rfl⟩
  have hD₁ent : Ent S D₁ := by
    rw [hD₁]
    exact Ent.mul hES (Ent.mul (Ent.conjTranspose hS.star_mem hW') (Ent.mul hZ hW'))
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix n n K, Δ = (c * ϖ ^ j) • (D₁ * A) := ⟨_, rfl⟩
  have key1 : Aᴴ * (H * Δ) = (c * ϖ ^ N) • Z := by
    rw [hΔ, hD₁]
    simp only [Matrix.mul_smul, Matrix.mul_assoc]
    rw [hHE']
    simp only [Matrix.mul_smul]
    rw [hAW, hWA]
    simp only [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    rw [hNj]
    ring
  have key2 : Δᴴ * (H * A) = (star c * ϖ ^ N) • Z := by
    have h : Δᴴ * (H * A) = (Aᴴ * (H * Δ))ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH,
        Matrix.mul_assoc]
    rw [h, key1, Matrix.conjTranspose_smul, hZh, star_mul', hstar]
  have hAh : Aᴴ = star c • (1 : Matrix n n K) + c • Xᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_star]
  have k1 : star c • (H * Δ) + c • (Xᴴ * (H * Δ)) = (c * ϖ ^ N) • Z := by
    rw [← key1, hAh, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  have k2 : c • (Δᴴ * H) + star c • (Δᴴ * (H * X)) = (star c * ϖ ^ N) • Z := by
    rw [← key2, hA, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one]
  have k0 : Xᴴ * (H * X) = H + ϖ ^ N • Z := by rw [← Matrix.mul_assoc, hXZ]
  have hTR : (X - c • Δ)ᴴ * H * (X - c • Δ) = (1 + star c • Δ)ᴴ * H * (1 + star c • Δ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    rw [k0]
    linear_combination (norm := module) -k1 - k2 - hcc • (ϖ ^ N • Z)
  have hMent : Ent S ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) :=
    Ent.smul (mul_mem (mul_mem hcs hc) (_root_.pow_mem hS.mem _)) (Ent.mul hD₁ent hAent)
  obtain ⟨Q, hQent, hRQ⟩ := Cayley.exists_inv_one_add hS hMent
  have hjj : ϖ * ϖ ^ (j - 1) = ϖ ^ j := by
    rw [← pow_succ']
    congr 1
    omega
  have hR : (1 : Matrix n n K) + ϖ • ((star c * c * ϖ ^ (j - 1)) • (D₁ * A)) =
      1 + star c • Δ := by
    rw [hΔ, smul_smul, smul_smul]
    congr 2
    rw [← hjj]
    ring
  rw [hR] at hRQ
  have hRQ' : Q + star c • (Δ * Q) = 1 := by
    have h := hRQ
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h
    exact h
  refine ⟨(X - c • Δ) * Q, -(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q)), ?_, ?_, ?_⟩
  · exact Ent.sub (Ent.smul (neg_mem (mul_mem hcs hc)) (Ent.mul hX (Ent.mul hD₁ent (Ent.mul hAent hQent))))
      (Ent.smul (mul_mem hc hc) (Ent.mul hD₁ent (Ent.mul hAent hQent)))
  · rw [Matrix.conjTranspose_mul]
    calc Qᴴ * (X - c • Δ)ᴴ * H * ((X - c • Δ) * Q)
        = Qᴴ * ((X - c • Δ)ᴴ * H * (X - c • Δ)) * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * ((1 + star c • Δ)ᴴ * H * (1 + star c • Δ)) * Q := by rw [hTR]
      _ = ((1 + star c • Δ) * Q)ᴴ * H * ((1 + star c • Δ) * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = H := by rw [hRQ]; simp
  · calc (X - c • Δ) * Q = X * (Q + star c • (Δ * Q)) - star c • (X * (Δ * Q)) - c • (Δ * Q) := by
          simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
          abel
      _ = X + ϖ ^ j • (-(star c * c) • (X * (D₁ * (A * Q))) - (c * c) • (D₁ * (A * Q))) := by
          rw [hRQ', Matrix.mul_one, hΔ]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
          module

end Formalism.HermitianLattices.Ext.L3.HU
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemRangeLinPart
section
namespace Formalism.HermitianLattices.Ext.L3.SecondPropositionFree

open NormLifting

variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}

theorem card_lift_pred [Finite A] (hπ : Function.Surjective π) (hστ : ∀ a, π (σ a) = τ (π a))
    (hσ : ∀ a, σ (σ a) = a) (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0) {θ e : A}
    (he : (θ - σ θ) * e = 1) {n : A} (hn : σ n = n) (q : ℕ)
    (hq : Nat.card A = q ^ 2 * Nat.card B) (M : ℕ) (hM : 1 ≤ M) (p : (Fin M → B) → Prop)
    (hsurj : ∀ y : Fin M → A, p (fun i => π (y i)) → ∀ w ∈ fixSub σ (RingHom.ker π),
      w ∈ (linPart σ (RingHom.ker π) y).range) :
    Nat.card {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =
      q ^ (2 * M - 1) * Nat.card {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n} := by
  classical
  have hIσ : ∀ a ∈ RingHom.ker π, σ a ∈ RingHom.ker π := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [hστ, ha, map_zero]
  haveI : Finite B := Finite.of_surjective π hπ

  have hker : Nat.card (RingHom.ker π) = q ^ 2 := by
    have h1 : Nat.card A = Nat.card (RingHom.ker π) * Nat.card B := by
      refine card_eq_mul_of_fibers π _ (fun b => ?_)
      obtain ⟨a0, ha0⟩ := hπ b
      exact Nat.card_congr
        { toFun := fun a => ⟨a.1 - a0, by rw [RingHom.mem_ker, map_sub, a.2, ha0, sub_self]⟩
          invFun := fun k => ⟨k.1 + a0, by rw [map_add, RingHom.mem_ker.mp k.2, ha0, zero_add]⟩
          left_inv := fun a => Subtype.ext (sub_add_cancel a.1 a0)
          right_inv := fun k => Subtype.ext (add_sub_cancel_right k.1 a0) }
    have hB : 0 < Nat.card B := Nat.card_pos
    rw [hq] at h1
    exact (Nat.eq_of_mul_eq_mul_right hB h1).symm
  have hq0 : 0 < q := by
    have hk : 0 < Nat.card (RingHom.ker π) := Nat.card_pos
    rw [hker] at hk
    exact Nat.pos_of_ne_zero (fun h => by simp [h] at hk)

  have hfix : Nat.card (fixSub σ (RingHom.ker π)) = q := by
    have h := card_fixSub_sq hσ hIσ he
    rw [hker] at h
    exact Nat.pow_left_injective two_ne_zero h

  have hrange : ∀ x0 : Fin M → A, p (fun i => π (x0 i)) →
      Nat.card (linPart σ (RingHom.ker π) x0).range = q := by
    intro x0 hp
    have hR : (linPart σ (RingHom.ker π) x0).range = fixSub σ (RingHom.ker π) := by
      ext w
      rw [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨δ, rfl⟩
        show linPart σ (RingHom.ker π) x0 δ ∈ RingHom.ker π ∧
          σ (linPart σ (RingHom.ker π) x0 δ) = linPart σ (RingHom.ker π) x0 δ
        refine ⟨?_, ?_⟩
        · rw [linPart_apply]
          refine Ideal.sum_mem _ fun i _ => Ideal.add_mem _ ?_ ?_
          · exact Ideal.mul_mem_left _ _ (δ i).2
          · exact Ideal.mul_mem_right _ _ (hIσ _ (δ i).2)
        · rw [linPart_apply, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_add, map_mul, hσ]
          ring
      · intro hw
        exact AddMonoidHom.mem_range.mp (hsurj x0 hp w hw)
    rw [hR, hfix]

  have hnorm : ∀ x : Fin M → A, ∑ i, σ (x i) * x i = n → ∑ i, τ (π (x i)) * π (x i) = π n := by
    intro x hx
    rw [← hx, map_sum]
    simp only [map_mul, hστ]
  refine card_eq_mul_of_fibers
    (fun x : {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =>
      (⟨fun i => π (x.1 i), x.2.1, hnorm x.1 x.2.2⟩ :
        {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n})) _ ?_
  intro y
  choose x0 hx0 using fun i => hπ (y.1 i)
  have hpx0 : p (fun i => π (x0 i)) := by
    have h : (fun i => π (x0 i)) = y.1 := funext hx0
    rw [h]
    exact y.2.1
  have hNx0 : π (∑ i, σ (x0 i) * x0 i) = π n := by
    rw [map_sum]
    simp only [map_mul, hστ, hx0]
    exact y.2.2
  have ht : n - ∑ i, σ (x0 i) * x0 i ∈ fixSub σ (RingHom.ker π) := by
    show n - ∑ i, σ (x0 i) * x0 i ∈ RingHom.ker π ∧
      σ (n - ∑ i, σ (x0 i) * x0 i) = n - ∑ i, σ (x0 i) * x0 i
    refine ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, map_sub, hNx0, sub_self]
    · rw [map_sub, hn, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, hσ]
      ring

  have key : Nat.card {δ : Fin M → RingHom.ker π //
      linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i} = q ^ (2 * M - 1) := by
    have hfib := card_fiber_mul_card_range (linPart σ (RingHom.ker π) x0) _ (hsurj x0 hpx0 _ ht)
    rw [hrange x0 hpx0, Nat.card_fun, hker, Nat.card_eq_fintype_card (α := Fin M), Fintype.card_fin,
      ← pow_mul] at hfib
    have hpow : q ^ (2 * M) = q ^ (2 * M - 1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at hfib
    exact Nat.eq_of_mul_eq_mul_right hq0 hfib

  have hfwd : ∀ x : Fin M → A, (∀ i, π (x i) = y.1 i) → ∀ i, x i - x0 i ∈ RingHom.ker π := by
    intro x hx i
    rw [RingHom.mem_ker, map_sub, hx, hx0, sub_self]
  have hexp : ∀ (x : Fin M → A) (hd : ∀ i, x i - x0 i ∈ RingHom.ker π),
      ∑ i, σ (x i) * x i = ∑ i, σ (x0 i) * x0 i +
        linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hd i⟩) := by
    intro x hd
    rw [linPart_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : σ (x i - x0 i) * (x i - x0 i) = 0 :=
      hsq _ _ (RingHom.mem_ker.mp (hIσ _ (hd i))) (RingHom.mem_ker.mp (hd i))
    dsimp only
    rw [map_sub] at h0 ⊢
    linear_combination h0
  have hLfwd : ∀ (x : Fin M → A) (hx : ∀ i, π (x i) = y.1 i), ∑ i, σ (x i) * x i = n →
      linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hfwd x hx i⟩) =
        n - ∑ i, σ (x0 i) * x0 i := by
    intro x hx hN
    have h := hexp x (hfwd x hx)
    rw [hN] at h
    rw [h]
    ring
  have hdmem : ∀ (δ : Fin M → RingHom.ker π) i, (x0 i + δ i) - x0 i ∈ RingHom.ker π := by
    intro δ i
    rw [add_sub_cancel_left]
    exact (δ i).2
  have hbinv : ∀ (δ : Fin M → RingHom.ker π) i, π (x0 i + δ i) = y.1 i := by
    intro δ i
    rw [map_add, RingHom.mem_ker.mp (δ i).2, add_zero, hx0]
  have hpinv : ∀ δ : Fin M → RingHom.ker π, p (fun i => π (x0 i + δ i)) := by
    intro δ
    have h : (fun i => π (x0 i + δ i)) = y.1 := funext (hbinv δ)
    rw [h]
    exact y.2.1
  have hNinv : ∀ δ : Fin M → RingHom.ker π,
      linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i →
        ∑ i, σ (x0 i + δ i) * (x0 i + δ i) = n := by
    intro δ hδ
    have h := hexp (fun i => x0 i + δ i) (hdmem δ)
    have hδ' : (fun i => (⟨(x0 i + δ i) - x0 i, hdmem δ i⟩ : RingHom.ker π)) = δ := by
      funext i
      exact Subtype.ext (add_sub_cancel_left (x0 i) (δ i : A))
    rw [hδ', hδ] at h
    rw [h]
    ring
  rw [← key]
  exact Nat.card_congr
    { toFun := fun x => ⟨fun i => ⟨x.1.1 i - x0 i,
          hfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) i⟩,
        hLfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) x.1.2.2⟩
      invFun := fun δ => ⟨⟨fun i => x0 i + δ.1 i, hpinv δ.1, hNinv δ.1 δ.2⟩,
        Subtype.ext (funext fun i => hbinv δ.1 i)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (funext fun i =>
        show x0 i + (x.1.1 i - x0 i) = x.1.1 i by ring))
      right_inv := fun δ => Subtype.ext (funext fun i => Subtype.ext
        (show x0 i + (δ.1 i : A) - x0 i = (δ.1 i : A) by ring)) }

theorem mem_range_linPart (I : Ideal A) {M : ℕ} (y : Fin M → A) (i₀ : Fin M)
    {b : A} (hb : σ (y i₀) * b + σ b * y i₀ = 1) {w : A} (hw : w ∈ fixSub σ I) :
    w ∈ (linPart σ I y).range := by
  have hw' : w ∈ I ∧ σ w = w := hw
  obtain ⟨hwI, hσw⟩ := hw'
  classical
  refine ⟨fun i => if i = i₀ then ⟨b * w, I.mul_mem_left b hwI⟩ else 0, ?_⟩
  rw [linPart_apply, Finset.sum_eq_single i₀]
  · rw [if_pos rfl]
    show σ (y i₀) * (b * w) + σ (b * w) * y i₀ = w
    rw [map_mul, hσw]
    linear_combination w * hb
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

end Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NotIsPrimeMapOfSplit
section
namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals

theorem card_eq_sq_fixed {k : Type*} [Field k] (τ : k →+* k) (hτ : ∀ x, τ (τ x) = x) (θ : k)
    (hθ : θ - τ θ ≠ 0) : Nat.card k = Nat.card {x : k // τ x = x} ^ 2 := by
  first | exact Bl.general_b_fact_second_variant.goal1 .. | (apply Bl.general_b_fact_second_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_variant.goal1 <;> assumption)

variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

theorem surj_of_invol (hσ : ∀ x, σ (σ x) = x) : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩

theorem comap_comap_invol (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) : (P.comap σ).comap σ = P := by
  ext x
  simp only [Ideal.mem_comap, hσ]

theorem comap_eq_map_invol (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) : P.comap σ = P.map σ := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective σ (surj_of_invol hσ)]
  constructor
  · exact fun hx => ⟨σ x, hx, hσ x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [hσ]

theorem comap_isMaximal_invol (hσ : ∀ x, σ (σ x) = x) {P : Ideal B} (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective σ (surj_of_invol hσ)

theorem card_quot_comap_invol (hσ : ∀ x, σ (σ x) = x) (P : Ideal B) :
    Nat.card (B ⧸ P.comap σ) = Nat.card (B ⧸ P) := by
  let e : B ≃+* B := RingEquiv.ofBijective σ
    ⟨Function.Involutive.injective hσ, surj_of_invol hσ⟩
  refine Nat.card_congr (Ideal.quotientEquiv (P.comap σ) P e ?_).toEquiv
  exact (Ideal.map_comap_of_surjective σ (surj_of_invol hσ) P).symm

theorem fix_ι (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (a : A) : σ (ι a) = ι a :=
  (hfix _).2 ⟨a, rfl⟩

theorem comap_ι_comap (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (P : Ideal B) :
    (P.comap σ).comap ι = P.comap ι := by
  ext a
  simp only [Ideal.mem_comap, fix_ι hfix]

theorem comap_eq_comap_iff (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P Q : Ideal B} (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap ι = Q.comap ι ↔ Q = P ∨ Q = P.comap σ := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP

    have hout : ∀ R : Ideal B, R.IsMaximal → Q ≠ R → ∃ y ∈ Q, y ∉ R := by
      intro R hR hQR
      by_contra hc
      push_neg at hc
      exact hQR (hQ.eq_of_le hR.ne_top hc)
    obtain ⟨y, hyQ, hyP⟩ := hout P hP hne.1
    obtain ⟨z, hzQ, hzP'⟩ := hout _ hP' hne.2

    have hx : ∃ x ∈ Q, x ∉ P ∧ x ∉ P.comap σ := by
      by_cases hy' : y ∈ P.comap σ
      · by_cases hz' : z ∈ P
        · refine ⟨y + z, Q.add_mem hyQ hzQ, fun h' => hyP ?_, fun h' => hzP' ?_⟩
          · simpa using P.sub_mem h' hz'
          · simpa using (P.comap σ).sub_mem h' hy'
        · exact ⟨z, hzQ, hz', hzP'⟩
      · exact ⟨y, hyQ, hyP, hy'⟩
    obtain ⟨x, hxQ, hxP, hxP'⟩ := hx
    have hfx : σ (x * σ x) = x * σ x := by rw [map_mul, hσ, mul_comm]
    obtain ⟨a, ha⟩ := (hfix _).1 hfx
    have haQ : a ∈ Q.comap ι := by
      rw [Ideal.mem_comap, ha]
      exact Q.mul_mem_right _ hxQ
    rw [← h, Ideal.mem_comap, ha] at haQ
    rcases hP.isPrime.mem_or_mem haQ with h1 | h1
    · exact hxP h1
    · exact hxP' h1
  · rintro (rfl | rfl)
    · rfl
    · exact (comap_ι_comap hfix P).symm

theorem exists_sub_mem_of_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) (b : B) : ∃ a : A, b - ι a ∈ P := by
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  rw [Ideal.mem_comap] at hv
  have hfx : σ (b * v + σ (b * v)) = b * v + σ (b * v) := by rw [map_add, hσ, add_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  refine ⟨a, ?_⟩
  have hv' : v = 1 - u := by rw [← huv]; ring
  have : b - ι a = b * u - σ b * σ v := by rw [ha, hv']; simp only [map_mul, map_sub, map_one]; ring
  rw [this]
  exact P.sub_mem (P.mul_mem_left _ hu) (P.mul_mem_left _ hv)

theorem card_quot_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) :
    Nat.card (A ⧸ P.comap ι) = Nat.card (B ⧸ P) := by
  let f : A ⧸ P.comap ι →+* B ⧸ P := Ideal.quotientMap P ι le_rfl
  have hinj : Function.Injective f := Ideal.quotientMap_injective
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_of_split hσ hfix hP hc b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    simpa using P.neg_mem ha
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem not_isPrime_map_of_split (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι)
    {P : Ideal B} (hP : P.IsMaximal) (hc : P.comap σ ≠ P) : ¬ ((P.comap ι).map ι).IsPrime := by
  intro hpr
  have hP' : (P.comap σ).IsMaximal := comap_isMaximal_invol hσ hP
  have hsup : P ⊔ P.comap σ = ⊤ := by
    exact Ideal.IsMaximal.coprime_of_ne hP hP' (Ne.symm hc)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : B) ∈ P ⊔ P.comap σ)
  have hu' : u ∉ P.comap σ := by
    intro h
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ (P.comap σ).add_mem h hv))
  have hle1 : (P.comap ι).map ι ≤ P := Ideal.map_comap_le
  have hle2 : (P.comap ι).map ι ≤ P.comap σ := by
    rw [← comap_ι_comap hfix P]
    exact Ideal.map_comap_le
  have hfx : σ (u * σ u) = u * σ u := by rw [map_mul, hσ, mul_comm]
  obtain ⟨a, ha⟩ := (hfix _).1 hfx
  have hmem : u * σ u ∈ (P.comap ι).map ι := by
    rw [← ha]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Ideal.mem_comap, ha]
    exact P.mul_mem_right _ hu
  rcases hpr.mem_or_mem hmem with h1 | h1
  · exact hu' (hle2 h1)
  · exact hu' (by rw [Ideal.mem_comap]; exact hle1 h1)

end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
end

