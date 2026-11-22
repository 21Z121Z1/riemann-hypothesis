import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Formalism.GL3MeanSquares.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ColMeas
section
noncomputable section

open PowerSeries

namespace GlobalTheory.Col

variable {R : Type} [CommRing R]

def pmeas (p r : ℕ) (g : PowerSeries R) (x : ℕ) : R :=
  ∑ m ∈ Finset.range (r + 1), Algebra.trace R (lev R p m) (ev R p m ((1 + X) ^ (p ^ r - x % p ^ r) * g))

def intU (p r : ℕ) [NeZero p] (η : (ZMod (p ^ r))ˣ → R) (g : PowerSeries R) : R :=
  ∑ b : (ZMod (p ^ r))ˣ, η b * pmeas p r g (b : ZMod (p ^ r)).val

def colMeas (p : ℕ) [hp : Fact p.Prime] (a : Rˣ) (g : PowerSeries R) : PowerSeries R :=
  g - PowerSeries.C (↑a⁻¹ : R) * phi (R := R) p hp.out.pos g

def chSum (p m : ℕ) [NeZero p] (ch : (ZMod (p ^ m))ˣ →* Rˣ) (g : PowerSeries R) : lev R p m :=
  ∑ b : (ZMod (p ^ m))ˣ, ev R p m (PowerSeries.C (ch b : R) * sb (b : ZMod (p ^ m)).val g)

def gauss (p m : ℕ) [NeZero p] (ch : (ZMod (p ^ m))ˣ →* Rˣ) : lev R p m :=
  ∑ b : (ZMod (p ^ m))ˣ, ev R p m (PowerSeries.C (ch b : R) * (1 + X) ^ (b : ZMod (p ^ m)).val)

end GlobalTheory.Col
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.Glue

open GlobalTheory.KZ

section Global

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def CgA (A : ValuationSubring Ω) (l n : ℕ) (x y : Ω) : Prop := ∃ z ∈ A, x - y = (l : Ω) ^ n * z

def theta (s : ℚ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := algebraMap ℚ Ω (s * r) * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

def Prim (A : ValuationSubring Ω) (φ : HahnSeries ℚ Ω) : Prop :=
  (∀ r, φ.coeff r ∈ A) ∧ ∃ r, φ.coeff r ≠ 0 ∧ (φ.coeff r)⁻¹ ∈ A

def IsDl (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω) : Prop :=
  (∀ r, φ.coeff r ∈ A) ∧ ∃ (a b : X.K) (κ : Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧
    ∀ r, CgA A l n ((φ * X.exp a * X.exp b).coeff r) ((theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b)).coeff r)

def Inv (X : Tower Ω ε) (H : Subgroup SL(2, ℤ)) (f : X.K) : Prop := ∀ γ ∈ H, X.sl (ofSL γ) f = f

def GamTop (N l n : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma (l ^ n) ⊓ CongruenceSubgroup.Gamma1 N

def IsThB (X : Tower Ω ε) (A : ValuationSubring Ω) (N l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) : Prop :=
  ∃ f : X.Kˣ, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K) ∧
    AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f ∧
    (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (f : X.K) * X.sl (ofSL δ) f = g ^ (l ^ n)) ∧
    IsDl X A l n 1 f φ

def nrmT (X : Tower Ω ε) (M : ℕ) (f : X.K) : X.K := ∏ b ∈ Finset.range M, X.sl (ofSL (ModularGroup.T ^ b)) f

def sgN (X : Tower Ω ε) (c N M : ℕ) (a : ℤ × ℤ) : X.K :=
  X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])

def coefQ (M : ℕ) (f : ℕ → Ω) (r : ℚ) : Ω := if 0 ≤ r ∧ (r * M).den = 1 then f (r * M).num.toNat else 0

def eeProd [CharZero Ω] (N l n : ℕ) (c d : ℕ) (w w' : ℤ × ℤ) (ζ : Ω) (γ : GL (Fin 2) (ZMod (l ^ n))) : ℕ → Ω :=
  GlobalTheory.KummerEisensteinGalois.cmul (GlobalTheory.KummerEisensteinGalois.smF c 1 (N * l ^ n) ζ (GlobalTheory.KummerEisensteinGalois.rowT N l n γ 0 w).1 (GlobalTheory.KummerEisensteinGalois.rowT N l n γ 0 w).2)
    (GlobalTheory.KummerEisensteinGalois.smF d 1 (N * l ^ n) ζ (GlobalTheory.KummerEisensteinGalois.rowT N l n γ 1 w').1 (GlobalTheory.KummerEisensteinGalois.rowT N l n γ 1 w').2)

def IsLamG (ε : Ω →+* ℂ) (l n m : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (t : ZMod (l ^ n)) : Prop :=
  (s ^ (l ^ (n - m))) (eOm ε (1 / (l : ℚ) ^ (2 * n))) = eOm ε (1 / (l : ℚ) ^ n) ^ t.val * eOm ε (1 / (l : ℚ) ^ (2 * n))

end Global

section Local

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

structure IsReb (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω) : Prop where
  inj : Function.Injective ψ
  par : ψ (qO p) = T.qq n
  sub : ∀ a b : Lau p, (∀ i : ℤ, b.coeff ((p : ℤ) ^ n * i) = a.coeff i) → (∀ r : ℤ, ¬ (p : ℤ) ^ n ∣ r → b.coeff r = 0) →
    ψ (algebraMap (Lau p) (O0 p) b) = algebraMap (O0 p) Ω (algebraMap (Lau p) (O0 p) a)
  rng : ψ.range = (Algebra.adjoin (O0 p) {T.qq n}).toSubring

def thL (a : Lau p) : Lau p where
  coeff r := (r : ℤ_[p]) * a.coeff r
  isPWO_support' := a.isPWO_support.mono (fun r hr h => hr (by simp [h]))

def zp (Ω : Type*) [Field Ω] [Algebra (O0 p) Ω] (z : ℤ_[p]) : Ω :=
  algebraMap (O0 p) Ω (algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z))

def Ev (ψ : O0 p →+* Ω) (c : ℤ → Ω) (x x' : Ω) : Prop :=
  ∃ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt p (e t) ∧ IsAlgZp p (e t)) ∧
    (∀ r, c r = ∑ t, e t * zp Ω ((a t).coeff r)) ∧ x = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) ∧
    x' = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))

end Local

end GlobalTheory.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def SSPotA (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ Algebra.adjoin ℂ (FreeAlgebra.ι ℂ '' {T : Letter | admitted N l T}),
    FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.SSBA (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) :
    Prop :=
  ∃ P ∈ Algebra.adjoin E (FreeAlgebra.ι E '' {T : Letter | admitted N l T}),
    FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

namespace SSAdm

variable {R : Type} [CommRing R] {A : Set Letter}

theorem lift_congr {B : Type} [Semiring B] [Algebra R B] {f g : Letter → B} (h : ∀ T ∈ A, f T = g T)
    {P : FreeAlgebra R Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P = FreeAlgebra.lift R g P := by
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [h T hT]
  | algebraMap r => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

variable {M : Type} [AddCommGroup M] [Module R M]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
variable {R : Type} [CommRing R] {A : Set _root_.GlobalTheory.KZ.Letter} in
variable {M : Type} [AddCommGroup M] [Module R M] in

theorem _root_.GlobalTheory.KZ.SSAdm.lift_sub_smul_mem {f : _root_.GlobalTheory.KZ.Letter → Module.End R M}
    {lam : _root_.GlobalTheory.KZ.Letter → R} {W : Submodule R M}
    (hW : ∀ T ∈ A, ∀ x ∈ W, f T x ∈ W) {x : M} (hx : ∀ T ∈ A, f T x - lam T • x ∈ W)
    {P : FreeAlgebra R _root_.GlobalTheory.KZ.Letter} (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) :
    FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
  have key : ∀ P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A),
      (∀ y ∈ W, FreeAlgebra.lift R f P y ∈ W) ∧
        FreeAlgebra.lift R f P x - FreeAlgebra.lift R lam P • x ∈ W := by
    intro P hP
    induction hP using Algebra.adjoin_induction with
    | mem P hP =>
      obtain ⟨T, hT, rfl⟩ := hP
      simp only [FreeAlgebra.lift_ι_apply]
      exact ⟨hW T hT, hx T hT⟩
    | algebraMap r =>
      simp only [AlgHom.commutes, Module.algebraMap_end_apply, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
      exact ⟨fun y hy => W.smul_mem r hy, W.zero_mem⟩
    | add P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_add, LinearMap.add_apply]
        exact W.add_mem (hP.1 y hy) (hQ.1 y hy)
      · convert W.add_mem hP.2 hQ.2 using 1
        simp only [map_add, LinearMap.add_apply, add_smul]
        abel
    | mul P Q _ _ hP hQ =>
      refine ⟨fun y hy => ?_, ?_⟩
      · rw [map_mul, Module.End.mul_apply]
        exact hP.1 _ (hQ.1 y hy)
      · convert W.add_mem (hP.1 _ hQ.2) (W.smul_mem (FreeAlgebra.lift R lam Q) hP.2) using 1
        simp only [map_mul, Module.End.mul_apply, map_sub, LinearMap.map_smul, smul_sub,
          smul_smul]
        rw [mul_comm (FreeAlgebra.lift R lam Q)]
        abel
  exact (key P hP).2

theorem eigen_of_two_step {f : Letter → Module.End R M} {lam : Letter → R} {Z : Submodule R M}
    (hZ : ∀ T ∈ A, ∀ z ∈ Z, f T z ∈ Z) {P : FreeAlgebra R Letter}
    (hP : P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' A)) (h1 : FreeAlgebra.lift R lam P = 1) {x : M}
    (hPx : ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) (FreeAlgebra.lift R f P x) ∈ Z)
    (hx : ∀ S ∈ A, ∀ T ∈ A,
      (f S - lam S • (1 : Module.End R M)) ((f T - lam T • (1 : Module.End R M)) x) ∈ Z) :
    ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) x ∈ Z := by
  let W : Submodule R M := ⨅ T ∈ A, Z.comap (f T - lam T • (1 : Module.End R M))
  have hmem : ∀ y, y ∈ W ↔ ∀ T ∈ A, (f T - lam T • (1 : Module.End R M)) y ∈ Z := by
    intro y; simp only [W, Submodule.mem_iInf, Submodule.mem_comap]
  have hZW : ∀ z ∈ Z, z ∈ W := fun z hz => (hmem z).2 fun T hT => by
    simpa using Z.sub_mem (hZ T hT z hz) (Z.smul_mem _ hz)
  have hW : ∀ T ∈ A, ∀ y ∈ W, f T y ∈ W := fun T hT y hy => by
    have h := W.add_mem (hZW _ ((hmem y).1 hy T hT)) (W.smul_mem (lam T) hy)
    simpa using h
  have hx' : ∀ T ∈ A, f T x - lam T • x ∈ W := fun T hT => (hmem _).2 fun S hS => by
    simpa using hx S hS T hT
  have h2 := lift_sub_smul_mem hW hx' hP
  rw [h1, one_smul] at h2
  have h3 := W.sub_mem ((hmem _).2 hPx) h2
  rw [sub_sub_cancel] at h3
  exact (hmem x).1 h3

end SSAdm

theorem SSPotA_congr {N l w : ℕ} {lam lam' : Letter → ℂ} (h : ∀ T, admitted N l T → lam T = lam' T) :
    SSPotA N l w lam ↔ SSPotA N l w lam' := by
  have key : ∀ {a b : Letter → ℂ}, (∀ T, admitted N l T → a T = b T) → SSPotA N l w a → SSPotA N l w b := by
    rintro a b hab ⟨P, hP, h1, h2⟩
    refine ⟨P, hP, ?_, fun F hF T hT => ?_⟩
    · rw [← SSAdm.lift_congr (A := {T | admitted N l T}) hab hP, h1]
    · rw [← hab T hT]; exact h2 F hF T hT
  exact ⟨key h, key fun T hT => (h T hT).symm⟩

theorem Tower.SSBA.eigen_of_two_step {X : Tower Ω ε} {N l w : ℕ} [Fact l.Prime] {E : Type} [Field E]
    [Algebra ℤ_[l] E] {lam : Letter → E} (h : X.SSBA N l w E lam) {x : E ⊗[ℤ_[l]] X.Fn l} (hx : x ∈ X.VB N l w E)
    (h2 : ∀ S, admitted N l S → ∀ T, admitted N l T →
      (X.opV N l E S - lam S • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l)))
        ((X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) x) = 0) :
    ∀ T, admitted N l T → X.opV N l E T x = lam T • x := by
  obtain ⟨P, hP, h1, hk⟩ := h
  intro T hT
  have := SSAdm.eigen_of_two_step (A := {T | admitted N l T}) (Z := ⊥) (f := X.opV N l E) (lam := lam)
    (fun T _ z hz => by rw [(Submodule.mem_bot E).1 hz, map_zero]; exact Submodule.zero_mem _) hP h1 (x := x)
    (fun T hT => (Submodule.mem_bot E).2 (hk x hx T hT))
    (fun S hS T hT => (Submodule.mem_bot E).2 (h2 S hS T hT)) T hT
  rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
  exact sub_eq_zero.1 this

example (N l : ℕ) : ¬ admitted N l (Letter.T 1) := fun h => Nat.not_prime_one h.1

example : admitted 5 3 (Letter.T 2) ∧ admitted 5 3 Letter.U ∧ admitted 5 3 (Letter.D 2) ∧
    ¬ admitted 5 3 (Letter.T 3) ∧ ¬ admitted 5 3 (Letter.T 5) ∧ ¬ admitted 5 3 (Letter.D 5) := by
  simp only [admitted]
  norm_num

example (N l w : ℕ) (lam : Letter → ℂ) (c : ℂ) :
    SSPotA N l w lam ↔
      SSPotA N l w (fun T => match T with | Letter.T 1 => c | T => lam T) := by
  refine SSPotA_congr fun T hT => ?_
  split
  · exact absurd hT.1 Nat.not_prime_one
  · rfl

example (N l : ℕ) (f : Letter → Module.End ℂ (ℂ × ℂ)) (lam : Letter → ℂ)
    (hU : f Letter.U = LinearMap.inl ℂ ℂ ℂ ∘ₗ LinearMap.snd ℂ ℂ ℂ)
    (hf : ∀ T, admitted N l T → T ≠ Letter.U → f T = 0) (hl : ∀ T, admitted N l T → lam T = 0) :
    ¬ ∃ P ∈ Algebra.adjoin ℂ (FreeAlgebra.ι ℂ '' {T : Letter | admitted N l T}), FreeAlgebra.lift ℂ lam P = 1 ∧
      ∀ x : ℂ × ℂ, ∀ T, admitted N l T →
        (f T - lam T • (1 : Module.End ℂ (ℂ × ℂ))) (FreeAlgebra.lift ℂ f P x) = 0 := by
  rintro ⟨P, hP, h1, hk⟩
  have hcase : ∀ T, admitted N l T → f T = 0 ∨ f T = LinearMap.inl ℂ ℂ ℂ ∘ₗ LinearMap.snd ℂ ℂ ℂ := fun T hT => by
    by_cases h : T = Letter.U
    · exact Or.inr (h ▸ hU)
    · exact Or.inl (hf T hT h)
  have := SSAdm.eigen_of_two_step (A := {T | admitted N l T}) (Z := ⊥) (f := f) (lam := lam)
    (fun T _ z hz => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]; exact Submodule.zero_mem _) hP h1 (x := (0, 1))
    (fun T hT => (Submodule.mem_bot ℂ).2 (hk _ T hT))
    (fun S hS T hT => by
      rcases hcase S hS with a | a <;> rcases hcase T hT with b | b <;> simp [a, b, hl S hS, hl T hT])
    Letter.U trivial
  simp [hU, hl Letter.U trivial] at this

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.H3

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def JHol (X : Tower Ω ε) : Prop :=
  ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs

def IsRoot (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (a b : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧
    X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m

def Kum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)) : Prop :=
  ∃ (f : X.Kˣ) (a b : ℂ → ℂ) (M : ℕ), 0 < M ∧ AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f ∧
    IsRoot X (l ^ n) f a b ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
      a (mob (ofSL δ) z) * b z =
        Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * (a z * b (mob (ofSL δ) z))

def Near {V : Type} (φ ψ : SL(2, ℤ) → V) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, φ δ = ψ δ

def R1 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (x : X.Khat l) (h : ℂ → ℤ_[l]) : Prop :=
  ∀ n : ℕ, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ ∧ ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
    PadicInt.toZModPow n (h (mob (ofSL δ) z) - h z) = χ δ

def Rel (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (b : X.Fn l) (F : ℂ → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], R1 X l (b u) (fun z => MvPolynomial.eval u (F z))

open Classical in

def cj (m : Matrix (Fin 2) (Fin 2) ℤ) (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  if h : ∃ δ' : SL(2, ℤ), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m then h.choose else 1

def IsCoc {R : Type} [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (c : SL(2, ℤ) → MvPolynomial (Fin 2) R) : Prop :=
  (∀ γ ∈ Γ, (c γ).IsHomogeneous w) ∧
    ∀ γ ∈ Γ, ∀ δ ∈ Γ, c (γ * δ) = slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ

def IsFam (l w : ℕ) (Γ : Subgroup SL(2, ℤ)) (Φ : (n : ℕ) → SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  (∀ n δ, (Φ n δ).IsHomogeneous w) ∧
  (∀ n, ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M,
    Φ n (δ * δ') = Φ n δ + Φ n δ') ∧
  (∀ n, ∀ γ ∈ Γ, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ n (γ * δ * γ⁻¹))) (Φ n)) ∧
  ∀ n, Near (fun δ => MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (Φ (n + 1) δ)) (Φ n)

def mon (R : Type) [CommRing R] (w : ℕ) (i : Fin (w + 1)) : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 ^ (i : ℕ) * MvPolynomial.X 1 ^ (w - (i : ℕ))

def cf (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (i k : Fin (w + 1)) : ℤ :=
  MvPolynomial.coeff (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))) (slP m (mon ℤ w k))

def SSPotS (S : Letter → Prop) (R : Type) [CommRing R] (N l w : ℕ) (lam : Letter → R) : Prop :=
  ∃ P ∈ Algebra.adjoin R (FreeAlgebra.ι R '' {T | S T}), FreeAlgebra.lift R lam P = 1 ∧ ∀ F ∈ Pot R w (Gam N l), ∀ T : Letter, S T →
    (opL R N l T - lam T • (1 : Module.End R (ℂ → MvPolynomial (Fin 2) R)))
      (FreeAlgebra.lift R (opL R N l) P F) ∈ Triv R w (Gam N l)

def SSBS (S : Letter → Prop) (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E]
    (lam : Letter → E) : Prop :=
  ∃ P ∈ Algebra.adjoin E (FreeAlgebra.ι E '' {T | S T}), FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, S T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

def abelian₂ (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] :
    Submodule E ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
  Submodule.span E {p | ∃ b F, Rel X l b F ∧
    p = ((1 : E) ⊗ₜ[ℤ_[l]] b, fun z => MvPolynomial.map (algebraMap ℤ_[l] E) (F z))}

def deh : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Polynomial ℂ := MvPolynomial.aeval ![Polynomial.X, 1]

def cocP (Γ : Subgroup SL(2, ℤ)) (F : ℂ → MvPolynomial (Fin 2) ℂ) : Γ → Polynomial ℂ := fun γ =>
  deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I)

theorem isRoot_one (X : Tower Ω ε) (m : ℕ) (h : ((fun _ => 1 : ℂ → ℂ) : Mero) ≠ 0) :
    IsRoot X m 1 (fun _ => 1) (fun _ => 1) :=
  ⟨differentiableOn_const 1, differentiableOn_const 1, h, by simp⟩

end GlobalTheory.KZ.H3
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PsType

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def IsEig (π : Representation ℂ G V) (H : Set G) (θ : G → ℂ) (v : V) : Prop := ∀ h ∈ H, π h v = θ h • v

def aug (π : Representation ℂ G V) (H : Set G) (θ : G → ℂ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ h ∈ H, ∃ w : V, x = π h w - θ h • w}

structure Datum [TopologicalSpace G] (H : Set G) (θ : G → ℂ) : Prop where
  one : (1 : G) ∈ H
  mul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H
  inv : ∀ a ∈ H, a⁻¹ ∈ H
  compact : IsCompact H
  val_one : θ 1 = 1
  val_mul : ∀ a ∈ H, ∀ b ∈ H, θ (a * b) = θ a * θ b
  near : ∃ U ∈ nhds (1 : G), ∀ g ∈ U, g ∈ H → θ g = 1

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Triv (χ : kˣ →* ℂˣ) (x : k) : Prop :=
  ∀ u : kˣ, valuation k (u : k) = 1 → valuation k ((u : k) - 1) ≤ valuation k x → χ u = 1

def Ordered (ψ : Fin n → kˣ →* ℂˣ) : Prop :=
  ∀ i a b j : Fin n, i ≤ a → a ≤ b → b ≤ j → ∀ x : k, Triv (ψ i / ψ j) x → Triv (ψ a / ψ b) x

def grp (ψ : Fin n → kˣ →* ℂˣ) : Set (GL (Fin n) k) :=
  {g | g ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (g.val i j)}

open Classical in

def ev (χ : kˣ →* ℂˣ) (x : k) : ℂ :=
  if h : valuation k x = 1 then (χ (Units.mk0 x fun h0 => by simp [h0] at h) : ℂ) else 1

def nxt (ψ : Fin n → kˣ →* ℂˣ) (m : Fin n) : kˣ →* ℂˣ :=
  if h : (m : ℕ) + 1 < n then ψ ⟨(m : ℕ) + 1, h⟩ else 1

def minor (g : GL (Fin n) k) (m : Fin n) : k := (g.val.toSquareBlockProp fun i => i ≤ m).det

def theta (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) : ℂ := ∏ m, ev (ψ m / nxt ψ m) (minor g m)

def HasVec {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : Fin n → kˣ →* ℂˣ) (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ IsEig π (grp ψ) (theta ψ) v

def Agree (ψ ω : Fin n → kˣ →* ℂˣ) : Prop := ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = ω i u

def strip (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k) (m : ℕ) : Set (GL (Fin n) k) :=
  {g | ∀ i j : Fin n, if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j}

def Cut (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) : Prop := ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ¬ Triv (ψ i / ψ j) 1

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def zerosIn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}

def zmult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def zsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∑ᶠ ρ ∈ zerosIn χ t T, (zmult χ ρ : ℂ) * f ρ

def zsumR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ) : ℝ :=
  ∑ᶠ ρ ∈ zerosIn χ t T, (zmult χ ρ : ℝ) * f ρ

def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)

def rayI {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {I | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔮 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)}

def rayP {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {I | ∃ a : 𝓞 K, a - 1 ∈ 𝔮 ∧
    (I : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)}

def rayNo {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : ℕ := (rayP 𝔮).relIndex (rayI 𝔮)

def rayPrimes {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (X : ℝ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ¬ v.asIdeal ∣ 𝔮 ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
    ∃ I ∈ rayP 𝔮, (I : FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)}

def NormOne (d M p : ℕ) : Prop :=
  ∃ A B : ℤ, A ^ 2 + (d : ℤ) * B ^ 2 = 4 * (p : ℤ) ∧ (M : ℤ) ∣ B ∧ (2 * (M : ℤ)) ∣ A - 2 - B

open Classical in

def normPrimes (d M : ℕ) (X Y : ℝ) : Finset ℕ :=
  (Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun p => p.Prime ∧ NormOne d M p)

end GlobalTheory.Mem.An
end
end

