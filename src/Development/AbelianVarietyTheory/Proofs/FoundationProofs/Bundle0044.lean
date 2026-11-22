import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCube
section
noncomputable section

namespace GlobalTheory.DerExt

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
variable {ι : Type} [Fintype ι]

def D0 (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * d (tr (v k * x))

def phi (D : Ω → Ω) (x y : Ω) : Ω := D (x * y) - x * D y - y * D x

def psi (u v : ι → Ω) (D : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * phi D (v k) x

theorem phi_comm (D : Ω → Ω) (x y : Ω) : phi D x y = phi D y x := by
  unfold phi; rw [mul_comm x y]; ring

theorem phi_one (D : Ω → Ω) (y : Ω) : phi D 1 y = -(y * D 1) := by
  unfold phi; simp

theorem phi_ident (D : Ω → Ω) (w x y : Ω) :
    w * phi D x y - phi D (w * x) y + phi D w (x * y) - y * phi D w x = 0 := by
  unfold phi; rw [show w * x * y = w * (x * y) by ring]; ring

variable {B C : Subalgebra (O0 p) Ω} {u v : ι → Ω} {tr : Ω → Ω} {d : Ω → Ω}

theorem traceDerivationFirstApprox_add_isInt (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt p (D0 u v tr d (x + y) - D0 u v tr d x - D0 u v tr d y) := by
  obtain ⟨_, hCi, hu, hv, htr, hadd, -⟩ := h
  refine int_congr (int_sum Finset.univ _ fun k _ => int_mul (hCi _ (hu k))
    (hd.1 _ (htr _ (C.mul_mem (hv k) hx)) _ (htr _ (C.mul_mem (hv k) hy)))) ?_
  simp only [D0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, hadd _ (C.mul_mem (hv k) hx) _ (C.mul_mem (hv k) hy)]; ring

theorem traceDerivationFirstApprox_mul_left_isInt (h : DualData B C u v tr) (hd : IsDer B d) {b x : Ω} (hb : b ∈ B) (hx : x ∈ C) :
    IsInt p (D0 u v tr d (b * x) - b * D0 u v tr d x - p * x * d b) := by
  obtain ⟨_, hCi, hu, hv, htr, -, hlin, hdual, -⟩ := h
  refine int_congr (int_sum Finset.univ _ fun k _ => int_mul (hCi _ (hu k))
    (hd.2.1 b hb _ (htr _ (C.mul_mem (hv k) hx)))) ?_
  rw [← hdual x hx]
  simp only [D0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show v k * (b * x) = b * (v k * x) by ring, hlin b hb _ (C.mul_mem (hv k) hx)]; ring

theorem phi_add (h : DualData B C u v tr) (hd : IsDer B d) {x x' y : Ω} (hx : x ∈ C) (hx' : x' ∈ C)
    (hy : y ∈ C) :
    IsInt p (phi (D0 u v tr d) (x + x') y - phi (D0 u v tr d) x y - phi (D0 u v tr d) x' y) := by
  refine int_congr (int_sub (traceDerivationFirstApprox_add_isInt h hd (C.mul_mem hx hy) (C.mul_mem hx' hy))
    (int_mul (h.2.1 y hy) (traceDerivationFirstApprox_add_isInt h hd hx hx'))) ?_
  simp only [phi, add_mul]; ring

theorem phi_bmul (h : DualData B C u v tr) (hd : IsDer B d) {b x y : Ω} (hb : b ∈ B) (hx : x ∈ C)
    (hy : y ∈ C) :
    IsInt p (phi (D0 u v tr d) (b * x) y - b * phi (D0 u v tr d) x y) := by
  refine int_congr (int_sub (traceDerivationFirstApprox_mul_left_isInt h hd hb (C.mul_mem hx hy))
    (int_mul (h.2.1 y hy) (traceDerivationFirstApprox_mul_left_isInt h hd hb hx))) ?_
  simp only [phi]; rw [show b * x * y = b * (x * y) by ring]; ring

theorem lin_sum (h : DualData B C u v tr) (f : Ω → Ω)
    (hadd : ∀ x ∈ C, ∀ y ∈ C, IsInt p (f (x + y) - f x - f y))
    (hlin : ∀ b ∈ B, ∀ x ∈ C, IsInt p (f (b * x) - b * f x))
    {κ : Type} (s : Finset κ) (w b : κ → Ω) (hw : ∀ i, w i ∈ C) (hb : ∀ i, b i ∈ B) :
    IsInt p (f (∑ i ∈ s, w i * b i) - ∑ i ∈ s, b i * f (w i)) := by
  classical
  have hBC := h.1
  induction s using Finset.induction_on with
  | empty =>
    simpa using hlin 0 B.zero_mem 0 C.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : ∑ i ∈ s, w i * b i ∈ C := C.sum_mem fun i _ => C.mul_mem (hw i) (hBC (hb i))
    have h1 := hadd _ (C.mul_mem (hw a) (hBC (hb a))) _ hS
    have h2 := hlin (b a) (hb a) (w a) (hw a)
    rw [mul_comm (b a) (w a)] at h2
    exact int_congr (int_add h1 (int_add h2 ih)) (by ring)

theorem sum_swap_eq (h : DualData B C u v tr) (D : Ω → Ω) {x : Ω} (hx : x ∈ C) (y : Ω) :
    ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y = p * x * psi u v D y := by
  obtain ⟨_, -, hu, -, -, -, -, hdual, -⟩ := h
  calc ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y
      = ∑ k, ∑ l, u k * tr (v k * (x * u l)) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show u l * (v k * x) = v k * (x * u l) by ring]; ring
    _ = ∑ l, ∑ k, u k * tr (v k * (x * u l)) * phi D (v l) y := Finset.sum_comm
    _ = ∑ l, (∑ k, u k * tr (v k * (x * u l))) * phi D (v l) y := by
        simp only [Finset.sum_mul]
    _ = ∑ l, p * (x * u l) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hdual _ (C.mul_mem hx (hu l))]
    _ = p * x * psi u v D y := by
        simp only [psi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem S_congr (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt p (p * ∑ k, u k * phi (D0 u v tr d) (v k * x) y - p * x * psi u v (D0 u v tr d) y) := by
  have hBC := h.1
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have htr := h.2.2.2.2.1
  have hdual2 := h.2.2.2.2.2.2.2.2.1
  have hpB : (p : Ω) ∈ B := natCast_mem B p
  have key : ∀ k, IsInt p (u k * (p * phi (D0 u v tr d) (v k * x) y -
      ∑ l, tr (u l * (v k * x)) * phi (D0 u v tr d) (v l) y)) := by
    intro k
    have hz : v k * x ∈ C := C.mul_mem (hv k) hx
    have ha := phi_bmul h hd hpB hz hy
    have hb := lin_sum h (fun z => phi (D0 u v tr d) z y)
      (fun a ha b hb => phi_add h hd ha hb hy) (fun b hb a ha => phi_bmul h hd hb ha hy)
      Finset.univ v (fun l => tr (u l * (v k * x))) hv
      (fun l => htr _ (C.mul_mem (hu l) hz))
    rw [hdual2 _ hz] at hb
    exact int_mul (hCi _ (hu k)) (int_congr (int_sub hb ha) (by ring))
  refine int_congr (int_sum Finset.univ _ fun k _ => key k) ?_
  rw [← sum_swap_eq h (D0 u v tr d) hx y, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

def Dext (p : ℕ) (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω :=
  (p : Ω) ^ 2 * D0 u v tr d x + p * psi u v (D0 u v tr d) x

theorem Dext_mul (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt p (Dext p u v tr d (x * y) - x * Dext p u v tr d y - y * Dext p u v tr d x) := by
  have hsum := h.2.2.2.2.2.2.2.2.2
  have hid : (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
      psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x = 0 := by
    calc (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
          psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x
        = ∑ k, u k * (v k * phi (D0 u v tr d) x y - phi (D0 u v tr d) (v k * x) y +
            phi (D0 u v tr d) (v k) (x * y) - y * phi (D0 u v tr d) (v k) x) := by
          rw [← hsum]
          simp only [psi, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by simp [phi_ident]
  refine int_congr (S_congr h hd hx hy) ?_
  simp only [Dext, phi, psi] at hid ⊢
  linear_combination (p : Ω) * hid

theorem Dext_add (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt p (Dext p u v tr d (x + y) - Dext p u v tr d x - Dext p u v tr d y) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have h1 := traceDerivationFirstApprox_add_isInt h hd hx hy
  have h2 : IsInt p (∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
      phi (D0 u v tr d) y (v k))) :=
    int_sum Finset.univ _ fun k _ => int_mul (hCi _ (hu k)) (phi_add h hd hx hy (hv k))
  refine int_congr (int_add (int_mul (int_pow (int_nat p) 2) h1) (int_mul (int_nat p) h2)) ?_
  have e : psi u v (D0 u v tr d) (x + y) - psi u v (D0 u v tr d) x - psi u v (D0 u v tr d) y =
      ∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
        phi (D0 u v tr d) y (v k)) := by
    simp only [psi, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) (x + y), phi_comm _ (v k) x, phi_comm _ (v k) y]; ring
  simp only [Dext]
  linear_combination (p : Ω) * e

theorem Dext_B (h : DualData B C u v tr) (hd : IsDer B d) {b : Ω} (hb : b ∈ B) :
    IsInt p (Dext p u v tr d b - (p : Ω) ^ 3 * d b) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have hsum := h.2.2.2.2.2.2.2.2.2
  have h1 := traceDerivationFirstApprox_mul_left_isInt h hd hb C.one_mem
  rw [mul_one, mul_one] at h1
  have h2 : IsInt p (psi u v (D0 u v tr d) b + p * b * D0 u v tr d 1) := by
    refine int_congr (int_sum Finset.univ _ fun k _ => int_mul (hCi _ (hu k))
      (phi_bmul h hd hb C.one_mem (hv k))) ?_
    rw [← hsum]
    simp only [psi, phi_one, mul_one, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) b]; ring
  refine int_congr (int_add (int_mul (int_pow (int_nat p) 2) h1) (int_mul (int_nat p) h2)) ?_
  simp only [Dext]; ring

theorem Dext_isDer (h : DualData B C u v tr) (hd : IsDer B d) : IsDer C (Dext p u v tr d) :=
  ⟨fun x hx y hy => Dext_add h hd hx hy, fun x hx y hy => Dext_mul h hd hx hy,
   fun c => int_congr (int_add (Dext_B h hd (B.algebraMap_mem c))
     (int_mul (int_pow (int_nat p) 3) (hd.2.2 c))) (by ring)⟩

theorem exists_ext : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
    ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt p (D b - (p : Ω) ^ 3 * d b) := by
  intro p _ Ω _ _ B C ι _ u v tr h d hd
  exact ⟨Dext p u v tr d, Dext_isDer h hd, fun b hb => Dext_B h hd hb⟩

end GlobalTheory.DerExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefect
section
noncomputable section

namespace GlobalTheory.AlmostEt

variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

def trTwist (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x : S) : M :=
  ∑ i, a i • D (tr (b i * x))

def trTwistDefect (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x u : S) : M :=
  trTwist tr a b D (x * u) - x • trTwist tr a b D u

def trExtDer (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) (D : S → M) (y : S) : M :=
  e • ∑ j, b j • trTwistDefect tr a b D y (a j)

variable {B C : Subalgebra A S} {tr : S → S} {n : ℕ} {a b : Fin n → S} {e : S} {D : S → M}

theorem trTwist_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : trTwist tr a b D (x + y) = trTwist tr a b D x + trTwist tr a b D y := by
  unfold trTwist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := C.mul_mem (h.b_mem i) hx
  have h2 := C.mul_mem (h.b_mem i) hy
  rw [mul_add, h.tr_add _ h1 _ h2, hD.add _ (h.tr_mem _ h1) _ (h.tr_mem _ h2), smul_add]

theorem trTwist_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β x : S} (hβ : β ∈ B)
    (hx : x ∈ C) : trTwist tr a b D (β * x) = β • trTwist tr a b D x + (e * x) • D β := by
  unfold trTwist
  have key : ∀ i, a i • D (tr (b i * (β * x))) =
      β • (a i • D (tr (b i * x))) + (a i * tr (b i * x)) • D β := by
    intro i
    have h1 := C.mul_mem (h.b_mem i) hx
    have hm : b i * (β * x) = β * (b i * x) := by ring
    rw [hm, h.tr_mul _ hβ _ h1, hD.mul _ hβ _ (h.tr_mem _ h1), smul_add, mul_smul, smul_comm (a i) β]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul, h.left x hx]

theorem trTwist_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    trTwist tr a b D (0 : S) = 0 := by
  have := trTwist_add h hD C.zero_mem C.zero_mem
  rw [add_zero] at this
  simpa using this

theorem defect_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x u v : S} (hx : x ∈ C)
    (hu : u ∈ C) (hv : v ∈ C) :
    trTwistDefect tr a b D x (u + v) = trTwistDefect tr a b D x u + trTwistDefect tr a b D x v := by
  unfold trTwistDefect
  rw [mul_add, trTwist_add h hD (C.mul_mem hx hu) (C.mul_mem hx hv), trTwist_add h hD hu hv, smul_add]
  abel

theorem defect_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C) :
    trTwistDefect tr a b D x 0 = 0 := by
  unfold trTwistDefect
  rw [mul_zero, trTwist_zero h hD, smul_zero, sub_zero]

theorem defect_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x β u : S} (hx : x ∈ C)
    (hβ : β ∈ B) (hu : u ∈ C) :
    trTwistDefect tr a b D x (β * u) = β • trTwistDefect tr a b D x u := by
  unfold trTwistDefect
  have hm : x * (β * u) = β * (x * u) := by ring
  rw [hm, trTwist_smul h hD hβ (C.mul_mem hx hu), trTwist_smul h hD hβ hu, smul_add, smul_sub,
    smul_smul x (e * u), smul_comm x β]
  have : x * (e * u) = e * (x * u) := by ring
  rw [this]
  abel

theorem defect_sum (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C)
    (c : Fin n → S) (hc : ∀ i, c i ∈ B) :
    trTwistDefect tr a b D x (∑ i, c i * a i) = ∑ i, c i • trTwistDefect tr a b D x (a i) := by
  have : ∀ s : Finset (Fin n), trTwistDefect tr a b D x (∑ i ∈ s, c i * a i) =
      ∑ i ∈ s, c i • trTwistDefect tr a b D x (a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using defect_zero h hD hx
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        defect_add h hD hx (C.mul_mem (h.le (hc j)) (h.a_mem j))
          (C.sum_mem fun i _ => C.mul_mem (h.le (hc i)) (h.a_mem i)),
        defect_smul h hD hx (hc j) (h.a_mem j), ih]
  exact this Finset.univ

theorem defect_mul (x y u : S) :
    trTwistDefect tr a b D (x * y) u =
      trTwistDefect tr a b D x (y * u) + x • trTwistDefect tr a b D y u := by
  unfold trTwistDefect
  rw [smul_sub, mul_assoc, mul_smul]
  abel

theorem trExtDer_swap (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : y • trExtDer tr a b e D x =
      e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) := by

  have step1 : ∀ j, e • (b j • trTwistDefect tr a b D x (y * a j)) =
      ∑ i, (tr (b i * (y * a j)) * b j) • trTwistDefect tr a b D x (a i) := by
    intro j
    have hya := C.mul_mem hy (h.a_mem j)
    have hl : e * (y * a j) = ∑ i, tr (b i * (y * a j)) * a i := by
      rw [← h.left _ hya]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [smul_comm, ← defect_smul h hD hx h.e_mem hya, hl,
      defect_sum h hD hx _ fun i => h.tr_mem _ (C.mul_mem (h.b_mem i) hya), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm (b j)]
  rw [Finset.smul_sum]
  simp_rw [step1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hr : ∀ i, ∑ j, tr (b i * (y * a j)) * b j = y • (e • b i) := by
    intro i
    have := h.right _ (C.mul_mem (h.b_mem i) hy)
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm y e, mul_assoc, mul_comm y (b i), ← this]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; congr 2; ring
  simp_rw [hr]
  unfold trExtDer
  rw [Finset.smul_sum, Finset.smul_sum]
  simp_rw [smul_smul, smul_eq_mul, mul_assoc]

theorem trExtDer_isDerOn (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    IsDerOn C (trExtDer tr a b e D) where
  add x hx y hy := by
    unfold trExtDer
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold trTwistDefect
    rw [← smul_add, add_mul, trTwist_add h hD (C.mul_mem hx (h.a_mem j)) (C.mul_mem hy (h.a_mem j)),
      add_smul]
    congr 1
    abel
  mul x hx y hy := by
    have e1 : trExtDer tr a b e D (x * y) =
        e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) + x • trExtDer tr a b e D y := by
      unfold trExtDer
      simp_rw [defect_mul, smul_add, Finset.sum_add_distrib, smul_add]
      congr 1
      rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_comm (b j) x, smul_comm e x]
    rw [e1, ← trExtDer_swap h hD hx hy, add_comm]
  alg c := by
    unfold trExtDer
    have hc : algebraMap A S c ∈ B := B.algebraMap_mem c
    have : ∀ j, b j • trTwistDefect tr a b D (algebraMap A S c) (a j) =
        (b j * (e * a j)) • D (algebraMap A S c) := by
      intro j
      unfold trTwistDefect
      rw [trTwist_smul h hD hc (h.a_mem j), add_sub_cancel_left, smul_smul]
    simp [this, hD.alg c]

theorem trExtDer_apply_of_mem (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β : S} (hβ : β ∈ B) :
    trExtDer tr a b e D β = (e ^ 3) • D β := by
  unfold trExtDer
  have : ∀ j, b j • trTwistDefect tr a b D β (a j) = (b j * (e * a j)) • D β := by
    intro j
    unfold trTwistDefect
    rw [trTwist_smul h hD hβ (h.a_mem j), add_sub_cancel_left, smul_smul]
  simp_rw [this, ← Finset.sum_smul, smul_smul]
  have hs : ∑ j, b j * (e * a j) = e * e := by
    rw [← h.sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; congr 1; ring

theorem exists_derOn_ext : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D →
      ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD
  exact ⟨trExtDer tr a b e D, trExtDer_isDerOn h hD, fun β hβ => trExtDer_apply_of_mem h hD hβ⟩

end GlobalTheory.AlmostEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatible
section
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem isDerOn_iSup_glue (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B : ℕ → Subalgebra A S) (hB : Monotone B) (D : ℕ → S → M)
    (hDer : ∀ m, IsDerOn (B m) (D m)) (hcomp : ∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) :
    ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  classical
  have hD : ∀ m k, m ≤ k → ∀ x ∈ B m, D k x = D m x := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => intro x _; rfl
    | succ k hmk ih =>
      intro x hx
      rw [hcomp k x (hB hmk hx), ih x hx]
  let D' : S → M := fun x => if h : ∃ m, x ∈ B m then D (Nat.find h) x else 0
  have hD' : ∀ m, ∀ x ∈ B m, D' x = D m x := by
    intro m x hx
    have h : ∃ m, x ∈ B m := ⟨m, hx⟩
    simp only [D', dif_pos h]
    exact (hD _ m (Nat.find_min' h hx) x (Nat.find_spec h)).symm
  have hmem : ∀ x ∈ (⨆ m, B m), ∃ m, x ∈ B m := fun x hx =>
    by
    have := hx
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hB.directed_le, Set.mem_iUnion] at this
    exact this
  refine ⟨D', ⟨?_, ?_, ?_⟩, hD'⟩
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (add_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).add x hx' y hy']
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hmem x hx
    obtain ⟨n, hn⟩ := hmem y hy
    have hx' : x ∈ B (max m n) := hB (le_max_left m n) hm
    have hy' : y ∈ B (max m n) := hB (le_max_right m n) hn
    rw [hD' _ _ (mul_mem hx' hy'), hD' _ _ hx', hD' _ _ hy', (hDer _).mul x hx' y hy']
  · intro a
    rw [hD' 0 _ ((B 0).algebraMap_mem a), (hDer 0).alg a]

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspFormsStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_oddFrame_cuspForms : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (-1 : SL(2, ℤ)) ∉ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0) → ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧ ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  first | exact @GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | exact GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms | (intros; apply GlobalTheory.OddFrame.DualFrame.exists_dual_cuspForms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEisensteinSlashNeOutsideGammaStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eisenstein_slash_ne_outside_gamma : ∀ M : ℕ, 3 ≤ M → ∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f := by
  first | exact @GlobalTheory.EisSep.exists_isMF_slash_ne | exact GlobalTheory.EisSep.exists_isMF_slash_ne | (intros; apply GlobalTheory.EisSep.exists_isMF_slash_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCuspsStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps : ∀ (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ), IsMF Γ K H → (∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) → ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  first | exact @GlobalTheory.exists_eq_discriminant_mul | exact GlobalTheory.exists_eq_discriminant_mul | (intros; apply GlobalTheory.exists_eq_discriminant_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicIntStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  first | exact @GlobalTheory.exists_finite_pid_subalgebra_div_padicInt | exact GlobalTheory.exists_finite_pid_subalgebra_div_padicInt | (intros; apply GlobalTheory.exists_finite_pid_subalgebra_div_padicInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoinStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (w : On p n), 1 ≤ n ∧ IsEmb T n ι ∧ ι w = b ∧ ∀ w' : On p n, ι w' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  first | exact @GlobalTheory.K5.exists_level_of_mem_adjoin | exact GlobalTheory.K5.exists_level_of_mem_adjoin | (intros; apply GlobalTheory.K5.exists_level_of_mem_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneFormOneAddExpDecayStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelOne_form_one_add_expDecay : ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧ (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  first | exact @GlobalTheory.levelOne_form_one_add_expDecay | exact GlobalTheory.levelOne_form_one_add_expDecay | (intros; apply GlobalTheory.levelOne_form_one_add_expDecay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixingStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finiteIndex_fixing_finite_orbits : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L] (S : Finset L), (∀ s ∈ S, (MulAction.orbit G s).Finite) → ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧ ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | exact GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | (intros; apply GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalSubgroupNotMovesUniformBoundStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) → ∃ N : Subgroup G, N.Normal ∧ (∀ σ : G, σ ∈ N ↔ ¬ Moves v ⊤ σ) ∧ ∃ i : ℝ≥0, i < 1 ∧ ∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_not_moves_uniform | exact GlobalTheory.AlmostEt.exists_normal_not_moves_uniform | (intros; apply GlobalTheory.AlmostEt.exists_normal_not_moves_uniform <;> assumption)
end

