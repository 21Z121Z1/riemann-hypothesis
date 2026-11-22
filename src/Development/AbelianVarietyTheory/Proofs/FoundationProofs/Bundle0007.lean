import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FirstOrderRigid
section
open Polynomial

namespace GlobalTheory.TangentRigid

def Top {k : Type} [Field k] (p : k[X]) (d : ℕ) (c : k) : Prop :=
  p.natDegree ≤ d ∧ p.coeff d = c

section
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}

theorem Top.mul (hp : Top p d c) (hq : Top q e c') : Top (p * q) (d + e) (c * c') :=
  ⟨natDegree_mul_le.trans (add_le_add hp.1 hq.1), by
    rw [coeff_mul_add_eq_of_natDegree_le hp.1 hq.1, hp.2, hq.2]⟩

theorem Top.add (hp : Top p d c) (hq : Top q d c') : Top (p + q) d (c + c') :=
  ⟨(natDegree_add_le _ _).trans (max_le hp.1 hq.1), by rw [coeff_add, hp.2, hq.2]⟩

theorem Top.sub (hp : Top p d c) (hq : Top q d c') : Top (p - q) d (c - c') :=
  ⟨(natDegree_sub_le _ _).trans (max_le hp.1 hq.1), by rw [coeff_sub, hp.2, hq.2]⟩

theorem Top.cmul (a : k) (hp : Top p d c) : Top (C a * p) d (a * c) :=
  ⟨(natDegree_C_mul_le _ _).trans hp.1, by rw [coeff_C_mul, hp.2]⟩

theorem Top.raise (hp : Top p d c) (h : d < e) : Top p e 0 :=
  ⟨hp.1.trans h.le, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt h)⟩

theorem Top.cast {p' : k[X]} (hp : Top p d c) (h0 : p = p') (h : d = e) (h' : c = c') :
    Top p' e c' := by
  subst h0 h h'; exact hp

theorem top_X : Top (X : k[X]) 1 1 := ⟨natDegree_X_le, by simp⟩

theorem top_one : Top (1 : k[X]) 0 1 := ⟨by simp, by simp⟩

theorem top_of_monic (hp : p.Monic) (h : p.natDegree = d) : Top p d 1 :=
  ⟨h.le, by rw [← h]; exact hp⟩

theorem top_of_degree_lt (h : p.degree < (d : WithBot ℕ)) : Top p d 0 :=
  ⟨natDegree_le_of_degree_le h.le, coeff_eq_zero_of_degree_lt h⟩

theorem Top.xder (hp : Top p d c) : Top (X * derivative p) d (d * c) := by
  have key : ∀ j : ℕ, (X * derivative p).coeff j = j * p.coeff j := by
    intro j
    cases j with
    | zero => simp
    | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  refine ⟨natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_, by rw [key, hp.2]⟩
  rw [key, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt hj), mul_zero]

theorem Top.natDegree_eq (hp : Top p d 1) : p.natDegree = d :=
  le_antisymm hp.1 (le_natDegree_of_ne_zero (by rw [hp.2]; exact one_ne_zero))

end

theorem exists_param {k : Type} [Field k] (A B a dA dB : k) (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (ha : a ≠ 0) (hD : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hd : 12 * A ^ 2 * dA + 54 * B * dB = 0) :
    ∃ w : k, dA = 9 * B * a ^ 2 * w ∧ dB = -2 * A ^ 2 * a ^ 2 * w := by
  have h6 : (6 : k) ≠ 0 := by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  have hd' : 2 * A ^ 2 * dA + 9 * B * dB = 0 := by
    apply mul_left_cancel₀ h6
    linear_combination hd
  refine ⟨(3 * B * dA - 2 * A * dB) / ((4 * A ^ 3 + 27 * B ^ 2) * a ^ 2), ?_, ?_⟩
  · rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hD (pow_ne_zero 2 ha))]
    linear_combination (2 * A * a ^ 2) * hd'
  · rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hD (pow_ne_zero 2 ha))]
    linear_combination (3 * B * a ^ 2) * hd'

theorem first_order_rigid : ∀ (k : Type) [Field k] (m : ℕ) (A B a dA dB : k) (n h dn dh : k[X]), (2 : k) ≠ 0 → (3 : k) ≠ 0 → a ≠ 0 → a ^ 2 = -(2 * (m : k) + 1) → 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 → 12 * A ^ 2 * dA + 54 * B * dB = 0 → n.Monic → h.Monic → n.natDegree = 2 * m + 1 → h.natDegree = m → dn.degree < ((2 * m + 1 : ℕ) : WithBot ℕ) → dh.degree < (m : WithBot ℕ) → IsCoprime n h → (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2 = n ^ 3 + C (a ^ 4 * A) * n * h ^ 4 + C (a ^ 6 * B) * h ^ 6 → (C dA * X + C dB) * (derivative n * h - 2 * n * derivative h) ^ 2 + 2 * (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) * (derivative dn * h + derivative n * dh - 2 * dn * derivative h - 2 * n * derivative dh) = 3 * n ^ 2 * dn + C (a ^ 4 * dA) * n * h ^ 4 + C (a ^ 4 * A) * (dn * h ^ 4 + 4 * n * h ^ 3 * dh) + C (a ^ 6 * dB) * h ^ 6 + 6 * C (a ^ 6 * B) * h ^ 5 * dh → dA = 0 ∧ dB = 0 ∧ dn = 0 ∧ dh = 0 := by
  intro k _ m A B a dA dB n h dn dh h2 h3 ha ha2 hD hd hn hh hnd hhd hdn hdh hco E Ed
  obtain ⟨w, rfl, rfl⟩ := exists_param A B a dA dB h2 h3 ha hD hd
  obtain ⟨q, hq⟩ : ∃ q, q = derivative n * h - 2 * n * derivative h := ⟨_, rfl⟩
  obtain ⟨qd, hqd⟩ : ∃ qd, qd = derivative dn * h + derivative n * dh - 2 * dn * derivative h
      - 2 * n * derivative dh := ⟨_, rfl⟩
  rw [← hq] at E Ed
  rw [← hqd] at Ed
  have c2 : (C (2 : k) : k[X]) = 2 := rfl
  have c3 : (C (3 : k) : k[X]) = 3 := rfl
  have c4 : (C (4 : k) : k[X]) = 4 := rfl
  have c6 : (C (6 : k) : k[X]) = 6 := rfl
  have c9 : (C (9 : k) : k[X]) = 9 := rfl
  have c27 : (C (27 : k) : k[X]) = 27 := rfl
  have E' : (3 * X ^ 2 + C A) * q ^ 2 + 2 * (X ^ 3 + C A * X + C B) * q * derivative q
      = 3 * n ^ 2 * derivative n
        + C (a ^ 4 * A) * (derivative n * h ^ 4 + 4 * n * h ^ 3 * derivative h)
        + 6 * C (a ^ 6 * B) * h ^ 5 * derivative h := by
    have := congrArg derivative E
    simp only [derivative_mul, derivative_add, derivative_pow, derivative_X, derivative_C,
      Nat.cast_ofNat, c2, c3, c4, c6] at this
    norm_num only at this
    linear_combination this
  simp only [map_mul, map_pow, map_neg, c2, c9] at E E' Ed
  set F : k[X] := X ^ 3 + C A * X + C B with hF
  set r : k[X] := dn * h - 2 * n * dh with hr
  set V : k[X] := C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A) with hV
  set V' : k[X] := C w * (3 * n ^ 2 + 2 * (C a ^ 4 * C A) * h ^ 4) with hV'
  set G : k[X] := n ^ 3 + C a ^ 4 * C A * n * h ^ 4 + C a ^ 6 * C B * h ^ 6 with hG
  set G₁ : k[X] := 3 * n ^ 2 + C a ^ 4 * C A * h ^ 4 with hG₁
  set P : k[X] := h * r + V * h * q - V' with hP
  have key : G₁ * P = F * q * (9 * C a ^ 2 * C w * X * h ^ 2 * q + 2 * h ^ 2 * qd - 6 * h * dh * q
      + 2 * V * h ^ 2 * derivative q - 6 * V * h * derivative h * q - 9 * C w * n * q) := by
    simp only [hG₁, hP, hr, hV', hV, hF, hG] at E E' Ed ⊢
    linear_combination (-h ^ 2) * Ed
      - (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A) * h ^ 2) * E'
      + (6 * h * dh + 6 * (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A)) * h * derivative h
          + 9 * C w * n) * E
      + ((3 * n ^ 2 + C a ^ 4 * C A * h ^ 4) * (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A)) * h) * hq
  have hGh : IsCoprime G h := by
    have : G = n ^ 3 + h * (C a ^ 4 * C A * n * h ^ 3 + C a ^ 6 * C B * h ^ 5) := by
      rw [hG]; ring
    rw [this]
    exact IsCoprime.add_mul_left_left hco.pow_left _
  have hGG : IsCoprime G G₁ := by
    have hu : IsUnit (C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) : k[X]) :=
      isUnit_C.2 (mul_ne_zero (pow_ne_zero _ ha) hD).isUnit
    have h1 : IsCoprime G (C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) * h ^ 8) :=
      (isCoprime_mul_unit_left_right hu _ _).2 hGh.pow_right
    have h2' : C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) * h ^ 8 =
        (6 * (C a ^ 4 * C A) * n ^ 2 - 9 * (C a ^ 6 * C B) * n * h ^ 2
          + 4 * (C a ^ 4 * C A) ^ 2 * h ^ 4) * G₁
        + G * (27 * (C a ^ 6 * C B) * h ^ 2 - 18 * (C a ^ 4 * C A) * n) := by
      simp only [map_mul, map_pow, map_add, c4, c27, hG, hG₁]
      ring
    rw [h2'] at h1
    exact (IsCoprime.of_add_mul_left_right h1).of_mul_right_right
  have hdv : F * q ∣ G := ⟨q, by rw [← E]; ring⟩
  have hc1 : IsCoprime (F * q) G₁ := hGG.of_isCoprime_of_dvd_left hdv
  have hc2 : IsCoprime (F * q) h := hGh.of_isCoprime_of_dvd_left hdv
  have hFP : F * q ∣ P := hc1.dvd_of_dvd_mul_left ⟨_, key⟩
  set R : k[X] := P - 6 * C w * (F * q) * derivative h with hR
  have hFR : F * q ∣ R := dvd_sub hFP ⟨6 * C w * derivative h, by ring⟩
  have hhR : h ∣ R := by
    refine hco.symm.dvd_of_dvd_mul_left ⟨n * r + n * V * q + C w * (C a ^ 4 * C A) * n * h ^ 3
      + 3 * C w * (C a ^ 6 * C B) * h ^ 5 - 3 * C w * F * q * derivative n, ?_⟩
    simp only [hR, hP, hV', hG] at E ⊢
    linear_combination (3 * C w) * E - (3 * C w * F * q) * hq
  have hdR : F * q * h ∣ R := hc2.mul_dvd hFR hhR
  have tn := top_of_monic hn hnd
  have th := top_of_monic hh hhd
  have tX := top_X (k := k)
  have tF : Top F 3 1 := by
    refine ((((tX.mul tX).mul tX).add ((tX.cmul A).raise (by norm_num))).add
      (((top_one (k := k)).cmul B).raise (by norm_num))).cast ?_ rfl (by ring)
    rw [hF]; ring
  have tq : Top (X * q) (3 * m + 1) 1 := by
    refine ((tn.xder.mul th).sub ((tn.mul th.xder).cmul 2)).cast ?_ (by ring) (by push_cast; ring)
    rw [hq, c2]; ring
  have tr : Top r (3 * m + 1) 0 := by
    refine (((top_of_degree_lt hdn).mul th).sub
      ((tn.mul (top_of_degree_lt hdh)).cmul 2)).cast ?_ (by ring) (by ring)
    rw [hr, c2]; ring
  have tV : Top V 2 (3 * a ^ 2 * w) := by
    refine ((((tX.mul tX).cmul 3).add
      (((top_one (k := k)).cmul (2 * A)).raise (by norm_num))).cmul (a ^ 2 * w)).cast ?_ rfl
        (by ring)
    simp only [hV, map_mul, map_pow, c2, c3]; ring
  have tV' : Top V' (4 * m + 2) (3 * w) := by
    refine (((((tn.mul tn).cmul 3).cast rfl (show _ = 4 * m + 2 by ring) rfl).add
      ((((th.mul th).mul (th.mul th)).cmul (2 * (a ^ 4 * A))).raise (by omega))).cmul w).cast
        ?_ rfl (by ring)
    simp only [hV', map_mul, map_pow, c2, c3]; ring
  have tR : Top (X * X * R) (4 * m + 4) (3 * a ^ 2 * w - 3 * w - 6 * w * m) := by
    have t1 := (((tX.mul tX).mul th).mul tr).raise (show _ < 4 * m + 4 by omega)
    have t2 := (((tX.mul tV).mul th).mul tq).cast rfl (show _ = 4 * m + 4 by omega) rfl
    have t3 := ((tX.mul tX).mul tV').cast rfl (show _ = 4 * m + 4 by omega) rfl
    have t4 := (((tF.mul tq).mul th.xder).cmul (6 * w)).cast rfl
      (show _ = 4 * m + 4 by omega) rfl
    refine (((t1.add t2).sub t3).sub t4).cast ?_ rfl (by ring)
    simp only [hR, hP, map_mul, c6]; ring
  have tD : Top (X * (F * (X * q) * h)) (4 * m + 5) 1 :=
    (tX.mul ((tF.mul tq).mul th)).cast rfl (by omega) (by ring)
  have hXR : X * X * R = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt (p := X * (F * (X * q) * h)) ?_ ?_
    · obtain ⟨T, hT⟩ := hdR
      exact ⟨T, by rw [hT]; ring⟩
    · rw [tD.natDegree_eq]; have := tR.1; omega
  have hR0 : R = 0 := by simpa using hXR
  have hw : w = 0 := by
    have h0 := tR.2
    rw [hXR, coeff_zero] at h0
    have h1 : 2 * 3 * a ^ 2 * w = 0 := by linear_combination (3 * w) * ha2 - h0
    exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero (mul_ne_zero h2 h3) (pow_ne_zero _ ha))
  have hr0 : r = 0 := by
    have : h * r = 0 := by
      rw [← hR0]; simp [hR, hP, hV, hV', hw]
    exact (mul_eq_zero.1 this).resolve_left hh.ne_zero
  have hdh0 : dh = 0 := by
    have h1 : h ∣ n * dh := ⟨C (2 : k)⁻¹ * dn, by
      have : (C (2 : k)⁻¹ : k[X]) * 2 = 1 := by rw [← c2, ← map_mul, inv_mul_cancel₀ h2, map_one]
      linear_combination (-C (2 : k)⁻¹) * hr0 + (C (2 : k)⁻¹) * hr - (n * dh) * this⟩
    refine eq_zero_of_dvd_of_degree_lt (hco.symm.dvd_of_dvd_mul_left h1) ?_
    rwa [degree_eq_natDegree hh.ne_zero, hhd]
  refine ⟨by simp [hw], by simp [hw], ?_, hdh0⟩
  have : dn * h = 0 := by rw [← hr0, hr, hdh0]; ring
  exact (mul_eq_zero.1 this).resolve_right hh.ne_zero

end GlobalTheory.TangentRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FromBlocksMulInv
section
noncomputable section

open Matrix

namespace GlobalTheory.SingleBlock

variable {k : Type} [Field k] {r t : ℕ}

theorem fromBlocks_mul_inv (p : GL (Fin r) k) (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k) :
    fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) *
      fromBlocks ((p⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
        (-(((p⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * b *
          ((d⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k))) 0
        ((d⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = 1 := by
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
    ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, neg_add_cancel, neg_zero, fromBlocks_one]

def blockUnit (p : GL (Fin r) k) (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k) :
    GL (Fin r ⊕ Fin t) k :=
  ⟨_, _, fromBlocks_mul_inv p b d, mul_eq_one_comm.1 (fromBlocks_mul_inv p b d)⟩

def blockPar (t : ℕ) (Q : Subgroup (GL (Fin r) k)) : Subgroup (GL (Fin r ⊕ Fin t) k) where
  carrier := {h | ∃ p ∈ Q, ∃ (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k),
    (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
      fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k)}
  one_mem' := ⟨1, Q.one_mem, 0, 1, by simp⟩
  mul_mem' := by
    rintro x y ⟨p, hp, b, d, e⟩ ⟨p', hp', b', d', e'⟩
    refine ⟨p * p', Q.mul_mem hp hp', (p : Matrix (Fin r) (Fin r) k) * b' +
      b * (d' : Matrix (Fin t) (Fin t) k), d * d', ?_⟩
    rw [Units.val_mul, e, e', fromBlocks_multiply]
    simp
  inv_mem' := by
    rintro x ⟨p, hp, b, d, e⟩
    exact ⟨p⁻¹, Q.inv_mem hp, _, d⁻¹,
      Units.inv_eq_of_mul_eq_one_right (e ▸ fromBlocks_mul_inv p b d)⟩

private theorem mem_blockPar_iff' (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔ ∃ p ∈ Q, ∃ (b : Matrix (Fin r) (Fin t) k) (d : GL (Fin t) k),
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
        fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) :=
  Iff.rfl

theorem mem_blockPar_iff (Q : Subgroup (GL (Fin r) k)) (h : GL (Fin r ⊕ Fin t) k) :
    h ∈ blockPar t Q ↔
      (∃ p ∈ Q, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₁ =
        (p : Matrix (Fin r) (Fin r) k)) ∧
      (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₁ = 0 := by
  rw [mem_blockPar_iff']
  constructor
  · rintro ⟨p, hp, b, d, e⟩
    exact ⟨⟨p, hp, by rw [e, toBlocks_fromBlocks₁₁]⟩, by rw [e, toBlocks_fromBlocks₂₁]⟩
  · rintro ⟨⟨p, hp, h11⟩, h21⟩
    have hM : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k) =
        fromBlocks (p : Matrix (Fin r) (Fin r) k)
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₁₂ 0
          (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₂ := by
      rw [← h11, ← h21, fromBlocks_toBlocks]
    have hdet : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k).toBlocks₂₂.det ≠ 0 := by
      intro h0
      have hu := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h)).ne_zero
      rw [hM, det_fromBlocks_zero₂₁, h0, mul_zero] at hu
      exact hu rfl
    exact ⟨p, hp, _, Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet), hM⟩

theorem card_blockPar (Q : Subgroup (GL (Fin r) k)) :
    Nat.card (blockPar t Q) =
      Nat.card Q * (Nat.card k ^ (r * t) * Nat.card (GL (Fin t) k)) := by
  let φ : Q × (Matrix (Fin r) (Fin t) k × GL (Fin t) k) → blockPar t Q := fun x =>
    ⟨blockUnit x.1.1 x.2.1 x.2.2, (mem_blockPar_iff' Q _).mpr ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨p, hp⟩, b, d⟩ ⟨⟨p', hp'⟩, b', d'⟩ h
      have h1 : fromBlocks (p : Matrix (Fin r) (Fin r) k) b 0 (d : Matrix (Fin t) (Fin t) k) =
          fromBlocks (p' : Matrix (Fin r) (Fin r) k) b' 0 (d' : Matrix (Fin t) (Fin t) k) :=
        congrArg (fun z : blockPar t Q =>
          ((z : GL (Fin r ⊕ Fin t) k) : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) k)) h
      obtain ⟨e1, e2, -, e4⟩ := Matrix.fromBlocks_inj.mp h1
      have hp_eq : p = p' := Units.ext e1
      have hd_eq : d = d' := Units.ext e4
      subst hp_eq hd_eq e2
      rfl
    · rintro ⟨h, hh⟩
      obtain ⟨p, hp, b, d, e⟩ := (mem_blockPar_iff' Q h).mp hh
      exact ⟨(⟨p, hp⟩, b, d), Subtype.ext (Units.ext e.symm)⟩
  have hM : Nat.card (Matrix (Fin r) (Fin t) k) = Nat.card k ^ (r * t) := by
    show Nat.card (Fin r → Fin t → k) = _
    rw [Nat.card_fun, Nat.card_fun]
    simp only [Nat.card_eq_fintype_card (α := Fin t), Nat.card_eq_fintype_card (α := Fin r),
      Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm t r]
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_prod, hM]

theorem card_GL_real [Finite k] (n : ℕ) :
    (Nat.card (GL (Fin n) k) : ℝ) = (Nat.card k : ℝ) ^ (n * n) *
      ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
  classical
  have := Fintype.ofFinite k
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hq : (0 : ℝ) < Nat.card k := Nat.cast_pos.mpr (by omega)
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => ((Nat.card k ^ n - Nat.card k ^ i : ℕ) : ℝ)) n]
  have step : ∀ i ∈ Finset.range n, ((Nat.card k ^ n - Nat.card k ^ i : ℕ) : ℝ) =
      (Nat.card k : ℝ) ^ n * (1 - ((Nat.card k : ℝ) ^ (n - i))⁻¹) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by omega) hin.le)]
    push_cast
    have hsplit : (Nat.card k : ℝ) ^ n = (Nat.card k : ℝ) ^ i * (Nat.card k : ℝ) ^ (n - i) := by
      rw [← pow_add]
      congr 1
      omega
    have h2 : (Nat.card k : ℝ) ^ n * ((Nat.card k : ℝ) ^ (n - i))⁻¹ = (Nat.card k : ℝ) ^ i := by
      rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq.ne'), mul_one]
    rw [mul_sub, mul_one, h2]
  rw [Finset.prod_congr rfl step, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul]
  congr 1
  apply Finset.prod_nbij' (fun i => n - i) (fun i => n - i)
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range, Finset.mem_Ioc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_Ioc] at ha
    omega
  · intro a _
    rfl

theorem card_GL_sum : Nat.card (GL (Fin r ⊕ Fin t) k) = Nat.card (GL (Fin (r + t)) k) :=
  Nat.card_congr
    (Units.mapEquiv (Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toMulEquiv).toEquiv

private theorem mul_inv_eq_of_mul_eq_mul {I A a b c P P' : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hP : P ≠ 0) (h : I * (A * (b * (c * P))) = a * b * b * c * (P * P')) :
    I * (A * a⁻¹ * b⁻¹) = P' := by
  have key : I * A = a * b * P' := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hb hc) hP)
    linear_combination h
  calc I * (A * a⁻¹ * b⁻¹) = (I * A) * (a⁻¹ * b⁻¹) := by ring
    _ = P' * (a * a⁻¹) * (b * b⁻¹) := by rw [key]; ring
    _ = P' := by rw [mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, mul_one, mul_one]

theorem index_blockPar [Finite k] (Q : Subgroup (GL (Fin r) k)) :
    ((blockPar t Q).index : ℝ) * ((Nat.card Q : ℝ) * ((Nat.card k : ℝ) ^ (r ^ 2))⁻¹ *
      ((Nat.card k : ℝ) ^ (r * t))⁻¹) =
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hq : (0 : ℝ) < Nat.card k := Nat.cast_pos.mpr (by omega)
  have hq' : (1 : ℝ) < Nat.card k := by exact_mod_cast hq1
  have hpos : ∀ m : ℕ, 0 < ∏ i ∈ Finset.Ioc 0 m, (1 - ((Nat.card k : ℝ) ^ i)⁻¹) := by
    intro m
    apply Finset.prod_pos
    intro i hi
    have hi0 : i ≠ 0 := by
      simp only [Finset.mem_Ioc] at hi
      omega
    have : ((Nat.card k : ℝ) ^ i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq' hi0)
    linarith
  have hidx := (blockPar t Q).index_mul_card
  rw [card_blockPar, card_GL_sum] at hidx
  have hR : ((blockPar t Q).index : ℝ) * ((Nat.card Q : ℝ) * ((Nat.card k : ℝ) ^ (r * t) *
      (Nat.card (GL (Fin t) k) : ℝ))) = (Nat.card (GL (Fin (r + t)) k) : ℝ) := by
    exact_mod_cast hidx
  rw [card_GL_real, card_GL_real,
    ← Finset.prod_Ioc_consecutive _ (Nat.zero_le t) (Nat.le_add_left t r)] at hR
  have he : (Nat.card k : ℝ) ^ ((r + t) * (r + t)) = (Nat.card k : ℝ) ^ (r ^ 2) *
      (Nat.card k : ℝ) ^ (r * t) * (Nat.card k : ℝ) ^ (r * t) * (Nat.card k : ℝ) ^ (t * t) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [he] at hR
  exact mul_inv_eq_of_mul_eq_mul (pow_pos hq _).ne' (pow_pos hq _).ne' (pow_pos hq _).ne' (hpos t).ne' hR

end GlobalTheory.SingleBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqComap
section
namespace GlobalTheory.IdealComapPreimage

open IsDedekindDomain

theorem ideal_eq_comap {p : ℕ} (hp : Nat.Prime p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.comap (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ)
      (Ideal.span {(p : ℤ)}) := by
  set e := Rat.ringOfIntegersEquiv
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI : (Ideal.comap (e : NumberField.RingOfIntegers ℚ →+* ℤ) (Ideal.span {(p : ℤ)})).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.surjective
  symm
  refine Ideal.IsMaximal.eq_of_le this v.isPrime.ne_top ?_
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
  obtain ⟨k, hk⟩ := hx
  have : x = (p : NumberField.RingOfIntegers ℚ) * e.symm k := by
    apply e.injective
    simpa using hk
  rw [this]
  exact v.asIdeal.mul_mem_right _ hv

theorem main : ∀ {p : ℕ}, Nat.Prime p → ∀ {v v' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}, (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v' → v = v' := by
  intro p hp v v' hv hv'
  apply HeightOneSpectrum.ext
  rw [ideal_eq_comap hp v hv, ideal_eq_comap hp v' hv']

end GlobalTheory.IdealComapPreimage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Imports
section
namespace GlobalTheory.IdealPowerMembership

open MvPolynomial

theorem main : ∀ (K L : Type) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : FiniteDimensional K L], ∃ (f : MvPolynomial (Fin (Module.finrank K L)) K), MvPolynomial.IsHomogeneous f (Module.finrank K L) ∧ ∀ (x : L), (Algebra.norm K : L → K) x = (MvPolynomial.eval fun (i : Fin (Module.finrank K L)) ↦ ((Module.Basis.repr (Module.finBasis K L) : L → Fin (Module.finrank K L) →₀ K) x : Fin (Module.finrank K L) → K) i : MvPolynomial (Fin (Module.finrank K L)) K → K) f := by
  intro K L _ _ _ _
  classical
  let b := Module.finBasis K L
  let P : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) (MvPolynomial (Fin (Module.finrank K L)) K) :=
    fun j k => ∑ i, X i * C (Algebra.leftMulMatrix b (b i) j k)
  have hP : ∀ j k, (P j k).IsHomogeneous 1 := by
    intro j k
    apply IsHomogeneous.sum
    intro i _
    simpa using (isHomogeneous_X K i).mul (isHomogeneous_C (Fin (Module.finrank K L)) (Algebra.leftMulMatrix b (b i) j k))
  refine ⟨P.det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    apply IsHomogeneous.sum
    intro σ _
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin (Module.finrank K L))) (fun i => P (σ i) i) (fun _ => 1) (fun i _ => hP (σ i) i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact h
    · rw [hs, Units.neg_smul, one_smul]; exact h.neg
  · intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j k
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    have e1 : Algebra.leftMulMatrix b x = ∑ i, b.repr x i • Algebra.leftMulMatrix b (b i) := by
      conv_lhs => rw [hx]
      rw [map_sum]
      simp only [map_smul]
    rw [e1, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply]
    simp only [P, map_sum, eval_mul, eval_X, eval_C, Matrix.smul_apply, smul_eq_mul]
    rfl
end GlobalTheory.IdealPowerMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsAlt
section
namespace GlobalTheory.IntegralNormLeOne

open Polynomial

theorem norm_le_one_of_isIntegral {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  have hc : ∀ a : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact a.2
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have h0 : (0 : ℝ) < ‖x‖ := lt_trans one_pos h
  rw [hm.as_sum, eval₂_add, eval₂_pow, eval₂_X, eval₂_finset_sum] at hp
  have he : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree,
      eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) x (C (p.coeff i) * X ^ i) :=
    eq_neg_of_add_eq_zero_left hp
  rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
  · rw [hn] at he
    simp at he
  · have hle : ‖∑ i ∈ Finset.range p.natDegree,
        eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) x (C (p.coeff i) * X ^ i)‖
        ≤ ‖x‖ ^ (p.natDegree - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      have hi' : i ≤ p.natDegree - 1 := by
        have := Finset.mem_range.mp hi
        omega
      rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, norm_mul, norm_pow]
      calc _ ≤ 1 * ‖x‖ ^ i := by gcongr; exact hc _
        _ = ‖x‖ ^ i := one_mul _
        _ ≤ _ := pow_le_pow_right₀ h.le hi'
    have h1 : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
      rw [← norm_pow, he, norm_neg]; exact hle
    have h2 : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree :=
      pow_lt_pow_right₀ h (by omega)
    exact absurd h1 (not_le.mpr h2)

end GlobalTheory.IntegralNormLeOne
end

