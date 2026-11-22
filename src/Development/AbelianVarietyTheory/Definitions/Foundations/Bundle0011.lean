import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.SumMulCoPtSbEqSumInv
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.Glue

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def zt (ε : Ω →+* ℂ) (l n : ℕ) : Ω := eOm ε (1 / (l : ℚ) ^ n)

def Stab (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) : Prop := ∀ x, s x ∈ A ↔ x ∈ A

def InZl (ε : Ω →+* ℂ) (l n : ℕ) (F : Ω) : Prop := ∃ D : ℕ, ¬ l ∣ D ∧ (D : Ω) * F ∈ Subring.closure {zt ε l n}

open Classical in

def IsNT (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  ∃ τ : (ZMod (l ^ n))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, τ a (zt ε l n) = zt ε l n ^ (a : ZMod (l ^ n)).val) ∧
    (l : Ω) ^ (n - m) * F' = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m]), τ a F

def KT (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) : Subfield X.K :=
  RingHom.eqLocusField (X.sl (ofSL (ModularGroup.T ^ L))).toRingEquiv.toRingHom (RingHom.id X.K)

variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

structure IsCusp (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) : Prop where
  int : ∀ x, x ∈ A ↔ IsInt p (j x)
  alg : ∀ x, IsAlgZp p (j x)
  root : ∀ n, j (zt ε p n) = T.ζ n
  dense : ∀ (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p k e (j a)
  down : ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x)
  up : ∀ (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x)

structure IsIo (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ)
    (ψ : O0 p →+* Ωl) (io : KT X (p ^ n) →+* Ωl) : Prop where
  ev : ∀ (y : KT X (p ^ n)) (S : Finset Ω),
    (∀ r, (X.exp y).coeff r ∈ A ∧ (X.exp y).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) →
    ∃ x', Ev ψ (fun r : ℤ => j ((X.exp y).coeff ((r : ℚ) / (p : ℚ) ^ n))) (io y) x'
  gal : ∀ (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω), g (T.qq n) = T.qq n → (∀ x, g (j x) = j (s x)) →
    ∀ y y' : KT X (p ^ n), (y' : X.K) = X.gal s y → g (io y) = io y'

def IsNTr (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  1 ≤ m ∧ m ≤ n ∧ F ∈ IntermediateField.adjoin ℚ {zt ε l n} ∧ IsNT ε l n m F F'

theorem InZl.mem_adjoin {l n : ℕ} {F : Ω} (h : InZl ε l n F) : F ∈ IntermediateField.adjoin ℚ {zt ε l n} := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨D, hD, hF⟩ := h
  have hD0 : (D : Ω) ≠ 0 := by
    rintro h0
    exact hD (by rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero _)
  have h1 : (D : Ω) * F ∈ IntermediateField.adjoin ℚ {zt ε l n} :=
    (Subring.closure_le (t := (IntermediateField.adjoin ℚ {zt ε l n}).toSubring)).2
      (IntermediateField.subset_adjoin ℚ _) hF
  have h2 := mul_mem (inv_mem (natCast_mem (IntermediateField.adjoin ℚ {zt ε l n}) D)) h1
  rwa [inv_mul_cancel_left₀ hD0] at h2

theorem IsNTr.iff_isNT {l n m : ℕ} [NeZero l] {F F' : Ω} (hm : 1 ≤ m) (hmn : m ≤ n) (hF : InZl ε l n F) :
    IsNTr ε l n m F F' ↔ IsNT ε l n m F F' :=
  ⟨fun h => h.2.2.2, fun h => ⟨hm, hmn, hF.mem_adjoin, h⟩⟩

theorem IsNTr.apply_eq_of_mem_adjoin {z F : Ω} (hF : F ∈ IntermediateField.adjoin ℚ {z}) {s t : Ω ≃ₐ[ℚ] Ω} (h : s z = t z) :
    s F = t F := by
  induction hF using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx, h]
  | algebraMap r => rw [AlgEquiv.commutes, AlgEquiv.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem IsNTr.unique {l n m : ℕ} [NeZero l] {F F' F'' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m F F'') : F' = F'' := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨-, -, hF, τ, hτ, e⟩ := h
  obtain ⟨-, -, -, τ', hτ', e'⟩ := h'
  refine mul_left_cancel₀ (pow_ne_zero (n - m) (Nat.cast_ne_zero.2 (NeZero.ne l))) (e.trans (Eq.trans ?_ e'.symm))
  exact Finset.sum_congr rfl fun a _ => IsNTr.apply_eq_of_mem_adjoin hF ((hτ a).trans (hτ' a).symm)

theorem IsNTr.add {l n m : ℕ} [NeZero l] {F F' G G' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m G G') :
    IsNTr ε l n m (F + G) (F' + G') := by
  obtain ⟨h1, h2, hF, τ, hτ, e⟩ := h
  obtain ⟨-, -, hG, τ', hτ', e'⟩ := h'
  refine ⟨h1, h2, add_mem hF hG, τ, hτ, ?_⟩
  rw [mul_add, e, e', ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by
    rw [map_add, IsNTr.apply_eq_of_mem_adjoin hG ((hτ a).trans (hτ' a).symm)]

example (l : ℕ) [NeZero l] (F F' : Ω) : ¬ IsNTr ε l 0 1 F F' ∧ ¬ IsNTr ε l 0 0 F F' ∧ ¬ IsNTr ε l 3 0 F F' :=
  ⟨fun h => by have := h.2.1; omega, fun h => by have := h.1; omega, fun h => by have := h.1; omega⟩

theorem KT.mem_def (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (f : X.K) : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := Iff.rfl

example (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (c : Ω) : X.jK ∈ KT X L ∧ algebraMap Ω X.K c ∈ KT X L :=
  ⟨X.j_inv _, (X.sl _).commutes c⟩

structure IsPlaceIn (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) : Prop where
  int : ∀ x, x ∈ A ↔ IsInt p (j x)
  alg : ∀ x, IsAlgZp p (j x)
  root : ∀ n, j (zt ε p n) = T.ζ n

theorem IsCusp.isPlaceIn {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsCusp ε A T j) :
    IsPlaceIn ε A T j := ⟨h.int, h.alg, h.root⟩

theorem IsPlaceIn.unique {A A' : ValuationSubring Ω} {T T' : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsPlaceIn ε A T j)
    (h' : IsPlaceIn ε A' T' j) : A = A' :=
  ValuationSubring.ext _ _ fun x => (h.int x).trans (h'.int x).symm

theorem IsPlaceIn.mem_nonunits (hc : IsClo p Ωl) {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl}
    (h : IsPlaceIn ε A T j) : ((p : ℕ) : Ω) ∈ A.nonunits := by
  haveI := Basic.charZero_of_isClo hc
  rw [ValuationSubring.mem_nonunits_iff_or]
  refine Or.inr fun hA => Basic.not_cong_one_zero hc 1 one_ne_zero ⟨_, (h.int _).1 hA, ?_⟩
  have hp0 : (p : Ωl) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [map_inv₀, map_natCast, pow_one, mul_inv_cancel₀ hp0, sub_zero]

theorem IsPlaceIn.stab {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} (h : IsPlaceIn ε A T j)
    {g : Gal p Ωl} {s : Ω ≃ₐ[ℚ] Ω} (hs : ∀ x, g (j x) = j (s x)) : Stab A s := fun x => by
  rw [h.int, h.int, ← hs]
  exact ⟨fun hx => by simpa using Basic.isInt_gal g.symm hx, Basic.isInt_gal g⟩

structure IsExpIn (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ)
    (ψ : O0 p →+* Ωl) (io : KT X (p ^ n) →+* Ωl) : Prop where
  place : IsPlaceIn ε A T j
  rebase₂ : IsReb T n ψ
  ev : ∀ (y : KT X (p ^ n)) (S : Finset Ω),
    (∀ r, (X.exp y).coeff r ∈ A ∧ (X.exp y).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) →
    ∃ x', Ev ψ (fun r : ℤ => j ((X.exp y).coeff ((r : ℚ) / (p : ℚ) ^ n))) (io y) x'

def GalTr (X : GlobalTheory.KZ.Tower Ω ε) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ) (io : KT X (p ^ n) →+* Ωl) : Prop :=
  ∀ (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω) (b : ℕ), g (T.qq n) = T.ζ n ^ b * T.qq n → (∀ x, g (j x) = j (s x)) →
    ∀ y y' : KT X (p ^ n), (y' : X.K) = X.sl (ofSL (ModularGroup.T ^ b)) (X.gal s y) → g (io y) = io y'

section

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}

theorem IsIo.isExpIn (h : IsIo X A T j n ψ io) (hj : IsPlaceIn ε A T j) (hψ : IsReb T n ψ) : IsExpIn X A T j n ψ io :=
  ⟨hj, hψ, h.ev⟩

theorem IsExpIn.isIo (h : IsExpIn X A T j n ψ io) (hg : GalTr X T j n io) : IsIo X A T j n ψ io :=
  ⟨h.ev, fun g s hq hs y y' hy => hg g s 0 (by rw [pow_zero, one_mul, hq]) hs y y' (by rw [pow_zero, map_one, X.sl_one, hy])⟩

theorem IsExpIn.par (h : IsExpIn X A T j n ψ io) : ψ (qO p) = T.qq n := h.rebase₂.par

theorem GalTr.coeff_sl_gal (X : GlobalTheory.KZ.Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (b : ℕ) (y : X.K) (r : ℚ) :
    (X.exp (X.sl (ofSL (ModularGroup.T ^ b)) (X.gal s y))).coeff r = eOm ε (r * b) * s ((X.exp y).coeff r) := by
  have he : ∀ i k, ent (ofSL (ModularGroup.T ^ b)) i k = ((!![1, (b : ℤ); 0, 1] i k : ℤ) : ℚ) := fun i k => by
    rw [← ModularGroup.coe_T_zpow, zpow_natCast]; rfl
  have h := X.exp_upper (ofSL (ModularGroup.T ^ b)) (by rw [he]; simp) (X.gal s y) r
  rw [he, he, he, X.gal_exp] at h
  simpa using h

end

end GlobalTheory.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ChiProj
section
noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def chiProj (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : ℕ → K) (c d x : ℤ) (s : ℕ) : K :=
  ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N).val * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s

end GlobalTheory.LambdaValuationPowers
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

def IsActC (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) : Prop :=
  (∀ (g : GQ l) (x : Om l), act g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l)) ∧
    ∀ (g : GQ l) (y : PadicComplex l), ‖act g y‖ = ‖y‖

def IsCyc (χ : GQ l →* ℚ_[l]ˣ) : Prop :=
  ∀ (g : GQ l) (m : ℕ) (ζ : Om l), ζ ^ (l ^ m) = 1 →
    ∃ a : ℕ, ‖(χ g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a

def chiC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l) : PadicComplex l :=
  algebraMap ℚ_[l] (PadicComplex l) ((χ g ^ i : ℚ_[l]ˣ) : ℚ_[l])

def Kinf (K : FinExt l) : IntermediateField ℚ_[l] (Om l) :=
  K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x | ∃ j : ℕ, x ^ (l ^ j) = 1}

def Hinf (K : FinExt l) : Subgroup (GQ l) := (Kinf K).fixingSubgroup

def Gj (K : FinExt l) (j : ℕ) : Subgroup (GQ l) := (Ks K j).fixingSubgroup

def Lev (l j : ℕ) : Prop := 1 ≤ j ∧ (l = 2 → 2 ≤ j)

def IsGen (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (j : ℕ) (g : GQ l) : Prop :=
  g ∈ Gj K j ∧ ‖(χ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ))

def inC (F : IntermediateField ℚ_[l] (Om l)) : Set (PadicComplex l) :=
  (fun x : Om l => (x : PadicComplex l)) '' (F : Set (Om l))

def intC (F : IntermediateField ℚ_[l] (Om l)) : Set (PadicComplex l) := {y | y ∈ inC F ∧ ‖y‖ ≤ 1}

def Ohat (K : FinExt l) : Set (PadicComplex l) := closure (intC (Kinf K))

def Xlev (K : FinExt l) (i : ℕ) : AddSubgroup (PadicComplex l) :=
  AddSubgroup.closure {z | ∃ ζ y : PadicComplex l, IsPrimitiveRoot ζ (l ^ i) ∧
    y ∈ intC (Ks K (i - 1)) ∧ z = ζ * y}

def Xj (K : FinExt l) (j : ℕ) : AddSubgroup (PadicComplex l) :=
  (⨆ (i : ℕ) (_ : j < i), Xlev K i).topologicalClosure

def rho1 (l : ℕ) : ℝ := (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1))

def twAct (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (y : Fin r → PadicComplex l) :
    Fin r → PadicComplex l :=
  chiC χ i g • (U g).mulVec (fun a => act g (y a))

def CocOn {X : Type} [AddCommGroup X] [TopologicalSpace X] (G : Subgroup (GQ l)) (A : GQ l → X → X)
    (M : Set X) (c : GQ l → X) : Prop :=
  ContinuousOn c G ∧ (∀ g ∈ G, c g ∈ M) ∧ ∀ g ∈ G, ∀ h ∈ G, c (g * h) = c g + A g (c h)

def CobOn {X : Type} [AddCommGroup X] (G : Subgroup (GQ l)) (A : GQ l → X → X) (M : Set X)
    (c : GQ l → X) : Prop :=
  ∃ x ∈ M, ∀ g ∈ G, c g = A g x - x

def ball (l : ℕ) [Fact l.Prime] (r : ℕ) : Set (Fin r → PadicComplex l) := {y | ∀ a, ‖y a‖ ≤ 1}

def Frame (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m : ℕ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) : Prop :=
  IsGen χ K m g ∧ (∀ a b, ContinuousOn (fun σ => U σ a b) (Gj K m)) ∧
    (∀ σ ∈ Gj K m, ∀ a b, U σ a b ∈ intC (Ks K m)) ∧
    (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, U (σ * τ) = U σ * U τ) ∧ (∀ σ ∈ Hinf K, U σ = 1) ∧
    ∀ a b, ‖(U g - 1) a b‖ < rho1 l

def HTBasis (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (G : Subgroup (GQ l)) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (J : Set ℤ) : Prop :=
  ∃ (e : Fin r → Fin r → PadicComplex l) (u : Fin r → ℤ), LinearIndependent (PadicComplex l) e ∧
    (∀ k, u k ∈ J) ∧ ∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def admissibleLettersSubalgebra (R : Type) [CommRing R] (N l : ℕ) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | admitted N l T})

def SSPotB (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ admissibleLettersSubalgebra ℂ N l, FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.SSBB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) :
    Prop :=
  ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

theorem iota_mem_admissibleSubalgebra (R : Type) [CommRing R] {N l : ℕ} {T : Letter} (hT : admitted N l T) :
    FreeAlgebra.ι R T ∈ admissibleLettersSubalgebra R N l :=
  Algebra.subset_adjoin ⟨T, hT, rfl⟩

theorem lift_apply_of_mem_admissibleSubalgebra {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {N l : ℕ}
    {f : Letter → Module.End R M} {lam : Letter → R} {x : M} (hx : ∀ T, admitted N l T → f T x = lam T • x)
    {P : FreeAlgebra R Letter} (hP : P ∈ admissibleLettersSubalgebra R N l) :
    FreeAlgebra.lift R f P x = FreeAlgebra.lift R lam P • x := by
  have := SSAdm.lift_sub_smul_mem (A := {T | admitted N l T}) (W := ⊥) (f := f) (lam := lam) (x := x)
    (fun T _ z hz => by rw [(Submodule.mem_bot R).1 hz, map_zero]; exact Submodule.zero_mem _)
    (fun T hT => (Submodule.mem_bot R).2 (sub_eq_zero.2 (hx T hT))) hP
  exact sub_eq_zero.1 ((Submodule.mem_bot R).1 this)

theorem SSPotB_iff_SSPotA {N l w : ℕ} {lam : Letter → ℂ} : SSPotB N l w lam ↔ SSPotA N l w lam := Iff.rfl

theorem Tower.SSBB_iff_SSBA (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E]
    {lam : Letter → E} : X.SSBB N l w E lam ↔ X.SSBA N l w E lam := Iff.rfl

example (N l : ℕ) : FreeAlgebra.ι ℂ Letter.U ∈ admissibleLettersSubalgebra ℂ N l := iota_mem_admissibleSubalgebra ℂ trivial

example (N l : ℕ) : FreeAlgebra.ι ℂ (Letter.T 1) ∉ admissibleLettersSubalgebra ℂ N l := by
  classical
  intro h
  have := SSAdm.lift_congr (A := {T | admitted N l T}) (B := ℂ) (f := fun _ => 0)
    (g := fun T => if admitted N l T then 0 else 1) (fun T hT => (if_pos hT).symm) h
  have hn : ¬ admitted N l (Letter.T 1) := fun h => Nat.not_prime_one h.1
  simp [hn] at this

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.NormOneSevenOneTwo
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.Model

theorem normOne_seven_one_two : NormOne 7 1 2 := by
  refine ⟨1, 1, ?_, ?_, ?_⟩ <;> norm_num

theorem normOne_seven_two : NormOne 7 2 29 := by
  refine ⟨2, 4, ?_, ?_, ?_⟩ <;> norm_num

theorem normOne_dvd {d M p : ℕ} (hd : d % 4 = 3) (h : NormOne d M p) : (M : ℤ) ∣ (p : ℤ) - 1 := by
  obtain ⟨A, B, hN, ⟨b, rfl⟩, ⟨c, hc⟩⟩ := h
  obtain rfl : A = 2 + M * b + 2 * M * c := by linear_combination hc
  obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) = 4 * e - 1 := ⟨((d : ℤ) + 1) / 4, by omega⟩
  refine ⟨b + 2 * c + M * (c * (b + c) + e * b ^ 2), ?_⟩
  have h4 : 4 * ((p : ℤ) - 1) = 4 * ((M : ℤ) * (b + 2 * c + M * (c * (b + c) + e * b ^ 2))) := by
    linear_combination (-1 : ℤ) * hN + ((M : ℤ) ^ 2 * b ^ 2) * he
  linarith

theorem not_normOne : ¬ NormOne 7 2 2 := by
  rintro ⟨A, B, h1, ⟨b, rfl⟩, -⟩
  push_cast at h1
  have h2 : A ≤ 2 := by nlinarith [sq_nonneg b]
  have h3 : -2 ≤ A := by nlinarith [sq_nonneg b]
  have h4 : b ≤ 0 := by nlinarith [sq_nonneg A]
  have h5 : 0 ≤ b := by nlinarith [sq_nonneg A]
  interval_cases A <;> interval_cases b <;> norm_num at h1

theorem span_mem_principalRayGroup_top {K : Type} [Field K] [NumberField K] (a : 𝓞 K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : (I : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    I ∈ rayP (⊤ : Ideal (𝓞 K)) :=
  Subgroup.subset_closure ⟨a, Submodule.mem_top, h⟩

theorem mem_rayI_of_coprime {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (J : Ideal (𝓞 K)) :
    J ≠ 0 → J ⊔ 𝔮 = ⊤ → ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (I : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K) → I ∈ rayI 𝔮 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ u hu =>
    intro _ _ I hI
    rw [Ideal.isUnit_iff] at hu
    subst hu
    have hI1 : I = 1 := Units.ext (by rw [hI, FractionalIdeal.coeIdeal_top, Units.val_one])
    rw [hI1]
    exact one_mem _
  | h₃ a P ha hP ih =>
    intro _ hcop I hI
    have hP0 : P ≠ 0 := hP.ne_zero
    have hPq : ¬ P ∣ 𝔮 := by
      intro hd
      apply hP.not_isUnit
      rw [Ideal.isUnit_iff, eq_top_iff, ← hcop]
      exact sup_le Ideal.mul_le_left (Ideal.le_of_dvd hd)
    have hacop : a ⊔ 𝔮 = ⊤ := by
      rw [eq_top_iff, ← hcop]
      exact sup_le_sup_right Ideal.mul_le_right _
    have hPf : (P : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hP0
    have haf : (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact ha
    have hI' : I = Units.mk0 _ hPf * Units.mk0 _ haf := Units.ext (by
      rw [hI, Units.val_mul, Units.val_mk0, Units.val_mk0, FractionalIdeal.coeIdeal_mul])
    have hu : Units.mk0 _ hPf ∈ rayI 𝔮 :=
      Subgroup.subset_closure ⟨⟨P, Ideal.isPrime_of_prime hP, hP0⟩, hPq, rfl⟩
    rw [hI']
    exact Subgroup.mul_mem _ hu (ih ha hacop _ rfl)

theorem principalRayGroup_le_coprimeIdealGroup {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) : rayP 𝔮 ≤ rayI 𝔮 := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro I ⟨a, ha, hI⟩
  refine mem_rayI_of_coprime 𝔮 _ ?_ ?_ I hI
  · intro h0
    apply I.ne_zero
    rw [hI, h0]
    exact FractionalIdeal.coeIdeal_bot
  · rw [Ideal.eq_top_iff_one]
    have hmem : a - (a - 1) ∈ Ideal.span {a} ⊔ 𝔮 :=
      Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) (Ideal.mem_sup_right ha)
    simpa using hmem

private theorem finite_zeros_in_strip_box_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) (t T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ f ρ = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).reProdIm (isCompact_Icc (a := t - T) (b := t + T))) (by
      rintro ρ ⟨h1, h2, h3, -⟩
      rw [abs_le] at h3
      exact ⟨⟨h1.le, h2.le⟩, ⟨by linarith, by linarith⟩⟩)
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ x)
    (frequently_nhdsWithin_iff.mpr ((accPt_iff_frequently.mp hx).mono fun y hy => ⟨hy.2.2.2.2, hy.1⟩))
  obtain ⟨z, hz⟩ := hne
  exact hz (hzero (Set.mem_univ z))

theorem zerosIn_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t T : ℝ) :
    (zerosIn χ t T).Finite :=
  finite_zeros_in_strip_box_of_differentiable (DirichletCharacter.differentiable_LFunction hχ)
    ⟨2, DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2) (Or.inl hχ) (by norm_num)⟩ t T

private theorem finite_zeros_in_strip_box_of_differentiable' {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) (t T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ T ∧ f ρ = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).reProdIm (isCompact_Icc (a := t - T) (b := t + T))) (by
      rintro ρ ⟨h1, h2, h3, -⟩
      rw [abs_le] at h3
      exact ⟨⟨h1.le, h2.le⟩, ⟨by linarith, by linarith⟩⟩)
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ x)
    (frequently_nhdsWithin_iff.mpr ((accPt_iff_frequently.mp hx).mono fun y hy => ⟨hy.2.2.2.2, hy.1⟩))
  obtain ⟨z, hz⟩ := hne
  exact hz (hzero (Set.mem_univ z))

theorem zerosIn_finite_one {q : ℕ} [NeZero q] (t T : ℝ) :
    (zerosIn (1 : DirichletCharacter ℂ q) t T).Finite := by
  refine (finite_zeros_in_strip_box_of_differentiable' (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
    ⟨1, DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q⟩ t T).subset ?_
  rintro ρ ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, ?_⟩
  have hρ : ρ ≠ 1 := by rintro rfl; simp at h2
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ]
  rw [show DirichletCharacter.LFunctionTrivChar q ρ = 0 from h4, mul_zero]

theorem zmult_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (h : DirichletCharacter.LFunction χ ρ = 0) : 0 < zmult χ ρ := by
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have htop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro ht
    rw [analyticOrderAt_eq_top] at ht
    have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ => hd.analyticAt z
    have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ ρ) ht
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := 2) (Or.inl hχ)
      (by norm_num) (hz (Set.mem_univ 2))
  have h0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    (hd.analyticAt ρ).analyticOrderAt_ne_zero.mpr h
  show 0 < analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ
  rw [Nat.pos_iff_ne_zero]
  intro h'
  apply h0
  rw [← Nat.cast_analyticOrderNatAt htop, h', Nat.cast_zero]

end GlobalTheory.Mem.An.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.CyclotomicQExpansion

open GlobalTheory.KZ GlobalTheory.Glue

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

open Classical in

def thN (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n d : ℕ) (b : X.Fn l) : HahnSeries ℚ Ω :=
  if h : ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ ∧ IsLat 1 φ then
    h.choose else 0

theorem thN_spec (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n d : ℕ) (b : X.Fn l)
    (h : ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ ∧ IsLat 1 φ) :
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧ IsLat 1 (thN X A N l n d b) := by
  rw [thN, dif_pos h]
  exact h.choose_spec

end GlobalTheory.CyclotomicQExpansion
end
end

