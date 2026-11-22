import ReciprocityTheory.DualLattices.Bundle0020
import ReciprocityTheory.DualLattices.Bundle0021
import ReciprocityTheory.DualLattices.Bundle0003
import ReciprocityTheory.DualLattices.TotalFibreMapTotalFibreNsmulSnd

-- bundled from ReciprocityTheory.DualLattices.LengthDegreeOfWdetFrobenius
section
namespace ReciprocityTheory.PGsh.Up

theorem lengthDegree_of_wdet_frobenius (hU6 : CokernelLengthComparisonStatement) (hU7 : UnramifiedCokernelLengthStatement) : CokernelLowerBoundStatement :=
  cokernelLowerBound_of hU6 hU7 lenEx killedGen idemGen

theorem lengthDegree_of_wdet_parts (hW1 : WdetLenStatement) (hW2 : WdetDegStatement) (hU7 : UnramifiedCokernelLengthStatement) :
    CokernelLowerBoundStatement := by
  refine lengthDegree_of_wdet_frobenius ?_ hU7
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  obtain ⟨d, X, hd, hX, hXc⟩ :=
    hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  have hle := hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX
  have hcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h5 := hS.cp_val
    rw [h0, zero_pow (by have := (Fact.out : Nat.Prime p).two_le; omega)] at h5
    exact hS.p_ne h5.symm
  have hpos : 0 < v (algebraMap R C cp) ^ d := pow_pos (pos_iff_ne_zero.mpr hcp) d
  have h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw := by
    rw [← hXc]
    exact mul_le_mul_of_nonneg_right hle zero_le
  exact le_of_mul_le_mul_left h6 hpos

end ReciprocityTheory.PGsh.Up
end

-- bundled from ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section FrobDefs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def xL (D : Lifts H U X) (j : Ix g) (y : Nb p g) : C := algebraMap R C (D.ε j) * D.u j y

def monX (D : Lifts H U X) (α y : Nb p g) : C := ∏ j, xL D j y ^ (α j).val

def valM (D : Lifts H U X) : Matrix (Nb p g) (Nb p g) C := Matrix.of fun y α => monX D α y

def coefX (D : Lifts H U X) (f : Nb p g → C) : Nb p g → C := (valM D)⁻¹ *ᵥ f

def linX (D : Lifts H U X) (f : Nb p g → C) (k : Ix g) : C := coefX D f (Pi.single k 1)

def blockL (D : Lifts H U X) (τ : Fin U.m) : Submodule R (Ix g → R) where
  carrier := {c | ∀ k, D.κ k ≠ τ → c k = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; rfl
  smul_mem' := by intro r a ha k hk; simp [ha k hk]

end FrobDefs

def LiftMonomialDeterminantStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X), (valM D).det ≠ 0

def FrobeniusBlockStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    (∀ j l, D.κ l ≠ U.φ (D.κ j) → linX D (fun y => xL D j y ^ p) l = 0) ∧
    ∀ i (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}),
      v (Matrix.of fun j l : {j // D.κ j = i} => linX D (fun y => xL D j.1 y ^ p) (e l).1).det =
        X i ^ p / X (U.φ i)

def FrobeniusLengthBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    (valM D).det ≠ 0 →
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) →
    ∀ (τ : Fin U.m) (N : Submodule R (Ix g → R)) (z : NNReal), N ≤ blockL D τ →
      (∀ c ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier), ∀ k, algebraMap R C (c k) = linX D f k) →
      HasLen v R (blockL D τ ⧸ N.comap (blockL D τ).subtype) z →
      z ≤ v (algebraMap R C (p : R)) ^ U.r τ

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.OneAddPowOfSq
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma BX.ev_map (B : BX R₀) {R S : LAlg R₀} (f : (R : Type u) →ₐ[R₀] (S : Type u))
    (h : B.gg →ₗ[R₀] (R : Type u)) (v : B.gg ⊗[R₀] (R : Type u)) :
    f (B.ev h v) = B.ev (f.toLinearMap ∘ₗ h) (LinearMap.lTensor B.gg f.toLinearMap v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp [BX.ev]
  | tmul g r => simp [BX.ev]
  | add a b ha hb =>
    simp only [BX.ev, map_add] at ha hb ⊢
    rw [ha, hb]

private lemma one_add_pow_of_sq {S : Type*} [CommRing S] (a : S) (ha : a * a = 0) (k : ℕ) :
    (1 + a) ^ k = 1 + k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : S) * ha

theorem b4 (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw := by
  intro Dp ι τ E ht bt h1 h2 h3 i j
  apply sub_eq_zero.mp
  apply Tw.sep
  intro n
  obtain ⟨k, hk, hpair⟩ := h1 i j n
  obtain ⟨thi, wi, hmi, hNi, hwi⟩ := h3 i n
  obtain ⟨thj, wj, hmj, hNj, hwj⟩ := h3 j n
  have hsurjL : Function.Surjective (Tw.π n).1.toLinearMap := Tw.surj n
  obtain ⟨hsi, hsi_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht i) hsurjL
  obtain ⟨hsj, hsj_spec⟩ := Module.projective_lifting_property (Tw.π n).1.toLinearMap
    ((Tw.q n).1.toLinearMap ∘ₗ ht j) hsurjL
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  have hpq := hnat _ _ (Tw.q n) _ _ _ _ hpair
  rw [← hmi, ← hmj] at hpq
  have hB3' := hB3 (Tw.R' n) (Tw.R n) (Tw.π n) (Tw.ξ n) (Dp n) (p ^ (n + 1)) (Tw.surj n)
    (Tw.ker_eq n) (Tw.ξ_sq n) (Tw.ann n) (Tw.char n) thi thj
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wi)
    (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) wj)
    hsi hsj (Tw.zh n ^ k) _ hNi hNj
    (by rw [hmi, hsi_spec]; exact h2 i n) (by rw [hmj, hsj_spec]; exact h2 j n) hpq
    (Units.ext (by simp [Tw.ζ_spec]))
  have hev : ∀ (h : B.gg →ₗ[R₀] (Tw.R' n : Type u)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.evK (Tw.π n) h (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) =
        Tw.ξ n * B.ev h w := by
    intro h w
    induction w using TensorProduct.induction_on with
    | zero => simp [BX.evK, BX.ev]
    | tmul g r =>
      simp [BX.evK, BX.ev, ξmul]
      ring
    | add a b ha hb =>
      simp only [BX.evK, BX.ev, map_add] at ha hb ⊢
      rw [ha, hb, mul_add]
  rw [hev, hev] at hB3'
  have hpow : ((Tw.zh n ^ k : (Tw.R' n : Type u)ˣ) : (Tw.R' n : Type u)) ^ (p ^ (n + 1)) =
      1 + (k : (Tw.R' n : Type u)) * (Tw.cp n * Tw.ξ n) := by
    rw [Units.val_pow_eq_pow_val, pow_right_comm, Tw.zh_pow n]
    apply one_add_pow_of_sq
    calc Tw.cp n * Tw.ξ n * (Tw.cp n * Tw.ξ n) = Tw.cp n * Tw.cp n * (Tw.ξ n * Tw.ξ n) := by ring
      _ = 0 := by rw [Tw.ξ_sq n, mul_zero]
  have hξ : ((k : (Tw.R' n : Type u)) * Tw.cp n - (B.ev hsj wi - B.ev hsi wj)) * Tw.ξ n = 0 := by
    have hh := hB3'.symm.trans hpow
    linear_combination -hh
  have hmem := Tw.ann n _ hξ
  rw [← Tw.ker_eq n, RingHom.mem_ker] at hmem
  have e1 : (Tw.π n).1 (B.ev hsj wi) = (Tw.q n).1 (B.ev (ht j) (bt i)) := by
    rw [BX.ev_map B (Tw.π n).1 hsj wi, hsj_spec, hwi, ← BX.ev_map B (Tw.q n).1 (ht j) (bt i)]
  have e2 : (Tw.π n).1 (B.ev hsi wj) = (Tw.q n).1 (B.ev (ht i) (bt j)) := by
    rw [BX.ev_map B (Tw.π n).1 hsi wj, hsi_spec, hwj, ← BX.ev_map B (Tw.q n).1 (ht i) (bt j)]
  simp only [map_sub, map_mul, map_natCast, Tw.cp_spec, e1, e2] at hmem
  rw [map_sub, map_sub, map_mul, hk]
  linear_combination hmem

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.RestrictedHopfOrderApproximationStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def psiW {p : ℕ} [Fact p.Prime] {g r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p]) :
    (Fin r → ZMod p) →+ Nb p g :=
  (Matrix.mulVecLin (Bw.map PadicInt.toZMod)).toAddMonoidHom

def RestrictedHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (a : O), a * a = a →
    ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ a)) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ d : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL a)) ≃ₗ[R] (Fin d → R)) →
    ∃ AW : HopfOrder (C := C) R (Fin r → ZMod p),
      AW.carrier = H.AA.carrier.map (LinearMap.funLeft R C (psiW Bw)) ∧
      HasLen v R (OmAA AW.carrier) (v (algebraMap R C (p : R)) ^ d)

def RestrictedHopfOrderApproximationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ (lam : Fin r → R) (dj : R),
      dj • lam ∈ Submodule.span R (Set.range fun k : Fin g ⊕ Fin g =>
        fun i : Fin r => (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i) →
      v (algebraMap R C cp) ≤ v (algebraMap R C dj) →
      ∃ f ∈ H.AA.carrier.map (LinearMap.funLeft R C (psiW Bw)), ∀ x : Fin r → ℤ_[p],
        v (f (fun i => PadicInt.toZMod (x i)) -
          algebraMap R C (dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i))) < v (algebraMap R C dj)

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.StThmAFull
section
noncomputable section

open TensorProduct Matrix

namespace ReciprocityTheory.PGsh

variable {R₀ : Type} [CommRing R₀]

def thmAPhi (B : BX R₀) {O : LAlg R₀} {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg)
    (ht : Fin g ⊕ Fin g → B.gg →ₗ[R₀] (O : Type)) (bt : Fin g ⊕ Fin g → B.gg ⊗[R₀] (O : Type)) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) (O : Type) :=
  Matrix.of fun r i => Sum.elim (fun a => ht i (gb a))
    (fun a => B.ev (Algebra.linearMap R₀ (O : Type) ∘ₗ gb.coord a) (bt i)) r

def ThmAFullStatement (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : Prop :=
  ∀ [IsDomain (Tw.O : Type)] (Dp : ∀ n, DualPair (Tw.R n)) (g : ℕ)
    (gb : Module.Basis (Fin g) R₀ B.gg) (τ : Fin g ⊕ Fin g → ℕ → B.G Tw.O)
    (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) (Tw.O : Type))
    (ht : Fin g ⊕ Fin g → B.gg →ₗ[R₀] (Tw.O : Type))
    (bt : Fin g ⊕ Fin g → B.gg ⊗[R₀] (Tw.O : Type)),
    Tw.c ≠ 0 → Eᵀ = -E → (∀ i, E i i = 0) → IsUnit E.det →
    (∀ i j n, ∃ k : ℕ, (Tw.q n).1 (E i j) = k ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
        LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)) →
    let Φ := thmAPhi B gb ht bt
    let Ht : Matrix (Fin g) (Fin g ⊕ Fin g) (Tw.O : Type) := Φ.submatrix Sum.inl id
    let Bt : Matrix (Fin g) (Fin g ⊕ Fin g) (Tw.O : Type) := Φ.submatrix Sum.inr id
    let hb : Matrix (Fin g ⊕ Fin g) (Fin g) (Tw.O : Type) := (Eᵀ)⁻¹ * Htᵀ
    let ι := algebraMap (Tw.O : Type) (FractionRing (Tw.O : Type))
    Φᵀ * stdJ (Tw.O : Type) g * Φ = Tw.c • E ∧
    (∀ f : Fin g → (Tw.O : Type), ∃ t : Fin g ⊕ Fin g → (Tw.O : Type), Ht *ᵥ t = Tw.c • f) ∧
    Ht * hb = 0 ∧ Bt * hb = Tw.c • (1 : Matrix (Fin g) (Fin g) (Tw.O : Type)) ∧
    hbᵀ * E * hb = 0 ∧
    (∀ t : Fin g ⊕ Fin g → FractionRing (Tw.O : Type), Ht.map ι *ᵥ t = 0 →
      ∃ x : Fin g → FractionRing (Tw.O : Type), hb.map ι *ᵥ x = t) ∧
    (∀ x : Fin g → FractionRing (Tw.O : Type),
      (∃ w : Fin g ⊕ Fin g → (Tw.O : Type), hb.map ι *ᵥ x = ι ∘ w) →
      ∃ y : Fin g → (Tw.O : Type), Tw.c • x = ι ∘ y)

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.TangentPairingStatementOfHeightFunctional
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

theorem tangentPairingStatement_of_heightFunctional (hB2 : HighestWeightVectorUniformBounds B) : TangentPairingStatement B := by
  intro R' R π ξ Dp N hsurj hker hsq _ hN sh th Vs Vt hs ht zh z hsV htV hhs hht hpair hz
  have hπ : π.SqZero := π.sqZero_of_span ξ hsurj hker hsq
  obtain ⟨O, hOsw, hO⟩ := B.step1 π Dp ξ hsurj hker hsq hB2 N hN
  obtain ⟨hsN, htN, u0, l1, l2, h1, h2, hz'⟩ := hpair
  obtain ⟨l⟩ := B.nonempty R' sh th
  obtain ⟨μ, hμ⟩ := B.exists_smul (B.pmap π l) u0
  obtain ⟨μ', hμ'⟩ := π.exists_unit_lift hsurj μ
  obtain ⟨a1, ha1⟩ := π.exists_unit_lift hsurj l1
  obtain ⟨a2, ha2⟩ := π.exists_unit_lift hsurj l2
  obtain ⟨l', hl⟩ : ∃ l' : B.P R' sh th, B.pmap π l' = u0 :=
    ⟨B.smul μ' l, by rw [B.pmap_smul, hμ', hμ]⟩
  have htg0 : ∀ V, B.map π (B.tg π hπ V) = 0 := fun V => (B.tg_ker π hπ _).2 ⟨V, rfl⟩
  have hinv1 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a1⁻¹ * l1 = 1 := by
    rw [map_inv, ha1, inv_mul_cancel]
  have hinv2 : Units.map (π.1 : (R' : Type u) →* (R : Type u)) a2⁻¹ * l2 = 1 := by
    rw [map_inv, ha2, inv_mul_cancel]

  have hu : HEq (B.pmap π (B.smul a1⁻¹ (B.tr1 hsV (B.nsmul1 l' N))))
      (B.zero1 (B.map π th)) := by
    rw [B.pmap_smul]
    have e : HEq (B.pmap π (B.tr1 hsV (B.nsmul1 l' N))) (B.smul l1 (B.zero1 (B.map π th))) := by
      refine (B.pmap_hcongr π hsV.symm rfl (B.castFst_heq hsV _)).trans ?_
      refine (B.pmap_nsmul1 π _ N).trans ?_
      rw [hl, ← h1]
      exact (B.castFst_heq hsN _).symm
    refine (B.smul_hcongr (htg0 Vs) rfl _ e).trans ?_
    rw [← B.mul_smul, hinv1, B.one_smul]
  have hu'0 : HEq (B.pmap π (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))))
      (B.zero2 (B.map π sh)) := by
    rw [B.pmap_smul]
    have e : HEq (B.pmap π (B.tr2 htV (B.nsmul2 l' N))) (B.smul l2 (B.zero2 (B.map π sh))) := by
      refine (B.pmap_hcongr π rfl htV.symm (B.castSnd_heq htV _)).trans ?_
      refine (B.pmap_nsmul2 π _ N).trans ?_
      rw [hl, ← h2]
      exact (B.castSnd_heq htN _).symm
    refine (B.smul_hcongr rfl (htg0 Vt) _ e).trans ?_
    rw [← B.mul_smul, hinv2, B.one_smul]
  have hu' : HEq (B.pmap π (B.sw (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N)))))
      (B.zero1 (B.map π sh)) := by
    rw [← B.sw_nat]
    refine (B.sw_hcongr rfl (htg0 Vt) hu'0).trans ?_
    rw [B.sw_zero2]
  obtain ⟨ct, hct, hNt⟩ := hO Vs Vt th ht htV hht _ hu
  obtain ⟨cs, hcs, hNs⟩ := hO Vt Vs sh hs hsV hhs _ hu'

  have k1 : HEq (B.smul (a1⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul ct (O Vs Vt)) := by
    refine HEq.trans ?_ ((B.castSnd_heq htV _).symm.trans (heq_of_eq hNt))
    rw [B.nsmul2_smul]
    exact B.smul_hcongr hsV rfl _ (B.nsmul2_hcongr hsV rfl N (B.castFst_heq hsV _).symm)
  have k2 : HEq (B.smul (a2⁻¹ ^ N) (B.nsmul2 (B.nsmul1 l' N) N)) (B.smul cs (O Vs Vt)) := by
    have s1 : HEq (B.sw (B.nsmul1 (B.smul a2⁻¹ (B.tr2 htV (B.nsmul2 l' N))) N))
        (B.smul cs (O Vt Vs)) := by
      rw [B.sw_nsmul1]; exact (B.castSnd_heq hsV _).symm.trans (heq_of_eq hNs)
    have s2 := B.sw_hcongr rfl hsV s1
    rw [B.sw_sw, B.sw_smul, hOsw] at s2
    refine HEq.trans ?_ s2
    rw [B.nsmul1_smul, B.nsmul_comm]
    exact B.smul_hcongr rfl htV _ (B.nsmul1_hcongr rfl htV N (B.castSnd_heq htV _).symm)
  obtain ⟨X₀, hX₀⟩ := B.exists_cast hsV htV (B.nsmul2 (B.nsmul1 l' N) N)
  have e1 : B.smul (a1⁻¹ ^ N) X₀ = B.smul ct (O Vs Vt) :=
    eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k1)
  have e2 : B.smul (a2⁻¹ ^ N) X₀ = B.smul cs (O Vs Vt) :=
    eq_of_heq ((B.smul_hcongr hsV.symm htV.symm _ hX₀).trans k2)
  have hX1 : X₀ = B.smul (a1 ^ N * ct) (O Vs Vt) := by
    rw [B.mul_smul, ← e1, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]
  have hX2 : X₀ = B.smul (a2 ^ N * cs) (O Vs Vt) := by
    rw [B.mul_smul, ← e2, ← B.mul_smul, ← mul_pow, mul_inv_cancel, one_pow, B.one_smul]
  have key : a1 ^ N * ct = a2 ^ N * cs := B.smul_inj (hX1.symm.trans hX2)

  have hν : Units.map (π.1 : (R' : Type u) →* (R : Type u)) (zh * a2 * a1⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hz, ha1, ha2, hz', div_mul_cancel, mul_inv_cancel]
  have hνN := LHom.pow_eq_one hπ hN (zh * a2 * a1⁻¹)
    (by have := congrArg Units.val hν; simpa using this)
  have hz1 : zh ^ N * a2 ^ N = a1 ^ N := by
    rw [mul_pow, mul_pow, inv_pow] at hνN
    exact mul_inv_eq_one.1 hνN
  have hz2 : zh ^ N * ct = cs := by
    have h3 : a2 ^ N * (zh ^ N * ct) = a2 ^ N * cs := by
      rw [← key, ← hz1]; ac_rfl
    exact mul_left_cancel h3
  have hA : π.1 (B.evK π ht Vs) = 0 := (RingHom.mem_ker).1 (evalT_mem ht (RingHom.ker π.1) Vs)
  have hB : π.1 (B.evK π hs Vt) = 0 := (RingHom.mem_ker).1 (evalT_mem hs (RingHom.ker π.1) Vt)
  have hAA := LHom.mul_eq_zero hπ hA hA
  have hAB := LHom.mul_eq_zero hπ hA hB
  have h4 := congrArg Units.val hz2
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hct, hcs] at h4
  linear_combination (1 + B.evK π ht Vs) * h4 + (zh : (R' : Type u)) ^ N * hAA - hAB

end BX

end ReciprocityTheory.PGsh
end
end

