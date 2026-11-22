import Mathlib

-- bundled from ReciprocityTheory.DualLattices.RankMapLeRank
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.RankA

variable {S : Type} [CommRing S]

lemma col_mem_range {m n : Type} [Fintype n] [DecidableEq n] (A : Matrix m n S) (y : n) :
    (fun x => A x y) ∈ LinearMap.range A.mulVecLin :=
  ⟨Pi.single y 1, by ext x; simp⟩

lemma factor_of_basis {m n ι : Type} [Fintype ι] (A : Matrix m n S)
    (M : Submodule S (m → S)) (b : Module.Basis ι S M) (hA : ∀ y, (fun x => A x y) ∈ M) :
    A = (Matrix.of fun x l => (b l : m → S) x) *
      Matrix.of fun l y => b.repr ⟨fun x => A x y, hA y⟩ l := by
  ext x y
  have h := congrArg (fun z : M => (z : m → S) x) (b.sum_repr ⟨fun x => A x y, hA y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma rank_map_le [StrongRankCondition S] {K : Type} [Field K] (f : S →+* K) {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n S) [Module.Free S (LinearMap.range A.mulVecLin)]
    [Module.Finite S (LinearMap.range A.mulVecLin)] :
    (A.map f).rank ≤ Module.finrank S (LinearMap.range A.mulVecLin) := by
  obtain ⟨N, hN, P, Q, hPQ⟩ : ∃ N, N = Module.finrank S (LinearMap.range A.mulVecLin) ∧
      ∃ (P : Matrix m (Fin N) S) (Q : Matrix (Fin N) n S), A = P * Q :=
    ⟨_, rfl, _, _, factor_of_basis A _ (Module.finBasis S _) (col_mem_range A)⟩
  rw [← hN]
  have h : A.map f = P.map f * Q.map f := by rw [hPQ, Matrix.map_mul]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))

lemma sum_finrank {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    [StrongRankCondition S] (e : m → Matrix ι ι S)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hsum : ∑ i, e i = 1)
    [∀ i, Module.Free S (LinearMap.range (e i).mulVecLin)]
    [∀ i, Module.Finite S (LinearMap.range (e i).mulVecLin)] :
    ∑ i, Module.finrank S (LinearMap.range (e i).mulVecLin) = Fintype.card ι := by
  let M : m → Submodule S (ι → S) := fun i => LinearMap.range (e i).mulVecLin
  have hmem : ∀ i j (y : M j), e i *ᵥ (y : ι → S) = if i = j then (y : ι → S) else 0 := by
    intro i j y
    obtain ⟨z, hz⟩ := y.2
    simp only [Matrix.mulVecLin_apply] at hz
    rw [← hz, mulVec_mulVec, horth]
    split_ifs with h
    · subst h; rfl
    · exact zero_mulVec _
  have hsum' : ∀ x : ι → S, ∑ i, e i *ᵥ x = x := by
    intro x
    rw [← Matrix.sum_mulVec, hsum, one_mulVec]
  let E : (ι → S) ≃ₗ[S] ((i : m) → M i) :=
    { toFun := fun x i => ⟨e i *ᵥ x, x, rfl⟩
      map_add' := fun x y => by ext i : 1; apply Subtype.ext; simp [mulVec_add]
      map_smul' := fun c x => by ext i : 1; apply Subtype.ext; simp [mulVec_smul]
      invFun := fun y => ∑ i, (y i : ι → S)
      left_inv := fun x => hsum' x
      right_inv := fun y => by
        ext i : 1; apply Subtype.ext
        simp only [Matrix.mulVec_sum, hmem, Finset.sum_ite_eq, Finset.mem_univ, if_true] }
  have h1 := E.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype] at h1
  exact h1.symm

lemma free_range_idem [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι S)
    (he : e * e = e) :
    Module.Free S (LinearMap.range e.mulVecLin) ∧ Module.Finite S (LinearMap.range e.mulVecLin) := by
  let s : (ι → S) →ₗ[S] LinearMap.range e.mulVecLin := e.mulVecLin.rangeRestrict
  have hs : s ∘ₗ (LinearMap.range e.mulVecLin).subtype = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨_, y, rfl⟩ := x
    simp [s, Matrix.mulVec_mulVec, he]
  have : Module.Projective S (LinearMap.range e.mulVecLin) :=
    Module.Projective.of_split (LinearMap.range e.mulVecLin).subtype s hs
  have : Module.Finite S (LinearMap.range e.mulVecLin) :=
    Module.Finite.of_surjective s (LinearMap.surjective_rangeRestrict _)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

end ReciprocityTheory.PGsh.Up.RankA
end
end

-- bundled from ReciprocityTheory.DualLattices.SmallLevelClassSet
section
noncomputable section

open Polynomial Matrix
open scoped TensorProduct

namespace ReciprocityTheory.PGsh

def stdJ (D : Type*) [CommRing D] (g : ℕ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D :=
  Matrix.fromBlocks 0 (-1) 1 0

def ExistsPointLeviLogNormSqPos : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (g : ℕ)
    (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D),
    Eᵀ = -E → (∀ i, E i i = 0) → IsUnit E.det → c ≠ 0 →
    Φᵀ * stdJ D g * Φ = c • E →
    let Ht : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inl id
    let Bt : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inr id
    let hb : Matrix (Fin g ⊕ Fin g) (Fin g) D := (Eᵀ)⁻¹ * Htᵀ
    let ι := algebraMap D (FractionRing D)
    (∀ f : Fin g → D, ∃ t : Fin g ⊕ Fin g → D, Ht *ᵥ t = c • f) ∧
    Ht * hb = 0 ∧ Bt * hb = c • (1 : Matrix (Fin g) (Fin g) D) ∧ hbᵀ * E * hb = 0 ∧
    (∀ t : Fin g ⊕ Fin g → FractionRing D, Ht.map ι *ᵥ t = 0 →
      ∃ x : Fin g → FractionRing D, hb.map ι *ᵥ x = t) ∧
    (∀ x : Fin g → FractionRing D, (∃ w : Fin g ⊕ Fin g → D, hb.map ι *ᵥ x = ι ∘ w) →
      ∃ y : Fin g → D, c • x = ι ∘ y)

abbrev extModR (R K V : Type*) [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] : Module R (ExteriorAlgebra K V) :=
  Module.compHom _ (algebraMap R K)

attribute [local instance] extModR

def detLat (R : Type*) {K V : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] [Module R V] (n : ℕ) (L : Submodule R V) : Submodule R (ExteriorAlgebra K V) :=
  Submodule.span R {w | ∃ v : Fin n → V, (∀ i, v i ∈ L) ∧ w = ExteriorAlgebra.ιMulti K n v}

def DeterminantLatticeStatement : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
    [IsScalarTower R K V] (e : ℕ) (a : Fin (e + 1) → R), Function.Injective a →
    ∀ x : Module.End K V,
      (List.ofFn fun s => x - algebraMap R K (a s) • (1 : Module.End K V)).prod = 0 →
    ∀ H Fil : Submodule R V,
      (∃ (r : ℕ) (bs : Module.Basis (Fin (e + 1) × Fin r) R H),
        ∀ j l, (bs (j, l) : V) = (x ^ (j : ℕ)) (bs (0, l))) →
      Submodule.span K (H : Set V) = ⊤ → Fil ≤ H → (∀ v ∈ Fil, x v ∈ Fil) →
      (∀ (c : R) (v : V), c ≠ 0 → v ∈ H → c • v ∈ Fil → v ∈ Fil) →
      let u : Module.End K V := x - algebraMap R K (a 0) • (1 : Module.End K V)
      let P0 : Module.End K V := (List.ofFn fun s : Fin e =>
        x - algebraMap R K (a s.succ) • (1 : Module.End K V)).prod
      let c0 : K := ∏ s : Fin e, (algebraMap R K (a 0) - algebraMap R K (a s.succ))
      let e0 : Module.End K V := c0⁻¹ • P0
      let Ps : Fin (e + 1) → Module.End K V := fun s => (List.ofFn fun t : Fin e =>
        x - algebraMap R K (a (s.succAbove t)) • (1 : Module.End K V)).prod
      let dimFil : Fin (e + 1) → ℕ := fun s =>
        Module.finrank K (Submodule.span K ((Fil.map ((Ps s).restrictScalars R) : Set V)))
      let y : R := ∏ s : Fin e, (a s.succ - a 0) ^ dimFil s.succ
      let H0 : Submodule R V := H ⊓ (LinearMap.ker u).restrictScalars R
      let Fil0 : Submodule R V := Fil.map (e0.restrictScalars R)
      let Lifts : Submodule R V := (H ⊓ Fil.comap (u.restrictScalars R)).map (e0.restrictScalars R)
      let n0 : ℕ := Module.finrank K (LinearMap.ker u)
      detLat R n0 H0 = Ideal.span {y} • Submodule.span R
          {w | ∃ (f : Fin (dimFil 0) → V) (l : Fin (n0 - dimFil 0) → V), (∀ i, f i ∈ Fil0) ∧
            (∀ j, l j ∈ Lifts) ∧
            w = ExteriorAlgebra.ιMulti K (dimFil 0) f * ExteriorAlgebra.ιMulti K (n0 - dimFil 0) l} ∧
        H0 = H.map (P0.restrictScalars R) ∧
        ∀ h ∈ H, e0 h = 0 ↔ h ∈ H.map (u.restrictScalars R)

def DualLatticeBaseIdentity : Prop :=
  ∀ (B : Type) [CommRing B] (F : B[X]),
    ∃ Rr : MvPolynomial (Fin 2) B,
      aeval (MvPolynomial.X 0) F - aeval (MvPolynomial.X 1) F =
        (MvPolynomial.X 0 - MvPolynomial.X 1) *
          (aeval (MvPolynomial.X 0) (derivative F) - (MvPolynomial.X 0 - MvPolynomial.X 1) * Rr)

def CommutingRootsStatement : Prop :=
  ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (c : B), IsSMulRegular M c →
    ∀ (Xo Yo Rr : Module.End B M) (F : B[X]), Commute Xo Yo →
      aeval Xo F = 0 → aeval Yo F = 0 →
      (aeval Xo (derivative F) - (Xo - Yo) * Rr) * (Xo - Yo) = aeval Xo F - aeval Yo F →
      ∀ θ κ : M, (Xo - Yo) θ = c • κ →
        (Xo - Yo) (aeval Xo (derivative F) θ - c • Rr κ) = 0 ∧
        ∀ (D' : B[X]) (c₀ : B), aeval Xo (derivative F * D') = c₀ • (1 : Module.End B M) →
          c₀ • θ ∈ LinearMap.ker (Xo - Yo) ⊔ Ideal.span {c} • (⊤ : Submodule B M)

def EigenvectorLiftStatement : Prop :=
  ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (c : B), IsSMulRegular M c →
    ∀ (al : Module.End B M) (s c' : B) (Ps Q : B[X]),
      aeval al ((X - C s) * Ps) = 0 → Ps - C (Ps.eval s) = (X - C s) * Q →
      c = Ps.eval s * c' →
      ∀ m w : M, (al - s • (1 : Module.End B M)) m = c • w →
        (al - s • (1 : Module.End B M)) (m + c' • aeval al Q w) = 0

def SaturatedDualStatement : Prop :=
  ∀ (B T : Type) [CommRing B] [IsDomain B] [ValuationRing B] [AddCommGroup T] [Module B T]
    [Module.Free B T] [Module.Finite B T] (p : B), p ≠ 0 →
    (∀ b : B, b ≠ 0 → ∃ m : ℕ, b ∣ p ^ m) →
    ∀ NN : Submodule B T, (∀ (b : B) (t : T), b ≠ 0 → b • t ∈ NN → t ∈ NN) →
    ∀ J : Submodule B (Module.Dual B T), J.FG → J ≤ NN.dualAnnihilator →
      (∀ φ ∈ NN.dualAnnihilator, ∃ b : B, b ≠ 0 ∧ b • φ ∈ J) →
    ∀ c₀ : B,
      (∀ (m : ℕ) (θ : T), (∀ φ ∈ J, φ θ ∈ Ideal.span {p ^ m}) →
        c₀ • θ ∈ NN ⊔ Ideal.span {p ^ m} • (⊤ : Submodule B T)) →
      ∀ φ ∈ NN.dualAnnihilator, c₀ • φ ∈ J

def EigenIntegralityStatement : Prop := DualLatticeBaseIdentity ∧ CommutingRootsStatement ∧ EigenvectorLiftStatement ∧ SaturatedDualStatement

def IsTateSeries {O : Type*} [CommRing O] (ϖ : O) {d : Type*} (g : MvPowerSeries d O) : Prop :=
  ∀ N : ℕ, {α : d →₀ ℕ | MvPowerSeries.coeff α g ∉ Ideal.span {ϖ ^ N}}.Finite

def newtonPoint {O : Type*} [CommRing O] (ϖ : O) (a d m : ℕ)
    (s : Fin m → MvPowerSeries (Fin d) O) : Fin d ⊕ Fin m → MvPowerSeries (Fin d) O
  | Sum.inl j => ϖ ^ a • MvPowerSeries.X j
  | Sum.inr i => s i

def newtonSystem {O : Type*} [CommRing O] (d m : ℕ) (b : Fin m → O)
    (Q : Fin m → MvPowerSeries (Fin d ⊕ Fin m) O) (i : Fin m) : MvPowerSeries (Fin d ⊕ Fin m) O :=
  b i • MvPowerSeries.X (Sum.inr i) + Q i

def NewtonLiftStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O), Irreducible ϖ →
    ∀ (d m a c : ℕ) (b : Fin m → O) (Q : Fin m → MvPowerSeries (Fin d ⊕ Fin m) O),
      c < a → (∀ i, b i ∣ ϖ ^ c) →
      (∀ i (α : Fin d ⊕ Fin m →₀ ℕ), α.degree ≤ 1 → MvPowerSeries.coeff α (Q i) = 0) →
      ∃ s : Fin m → MvPowerSeries (Fin d) O,
        ((∀ i, IsTateSeries ϖ (s i)) ∧
          (∀ i α, MvPowerSeries.coeff α (s i) ∈ Ideal.span {ϖ ^ a}) ∧
          (∀ i, MvPowerSeries.constantCoeff (s i) = 0) ∧
          ∀ i, MvPowerSeries.subst (newtonPoint ϖ a d m s) (newtonSystem d m b Q i) = 0) ∧
        (∀ i (α : Fin d →₀ ℕ), α.degree ≤ 1 → MvPowerSeries.coeff α (s i) = 0) ∧
        ∀ s' : Fin m → MvPowerSeries (Fin d) O,
          (∀ i, IsTateSeries ϖ (s' i)) →
          (∀ i α, MvPowerSeries.coeff α (s' i) ∈ Ideal.span {ϖ ^ a}) →
          (∀ i, MvPowerSeries.constantCoeff (s' i) = 0) →
          (∀ i, MvPowerSeries.subst (newtonPoint ϖ a d m s') (newtonSystem d m b Q i) = 0) →
          s' = s

def NewtonVanishingStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (d m a c : ℕ) (b : Fin m → O) (Q : Fin m → MvPowerSeries (Fin d ⊕ Fin m) O),
      (∀ i, b i ∣ ϖ ^ c) →
      (∀ i (α : Fin d ⊕ Fin m →₀ ℕ), α.degree ≤ 1 → MvPowerSeries.coeff α (Q i) = 0) →
      ∀ s : Fin m → MvPowerSeries (Fin d) O, (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
        (∀ i, MvPowerSeries.subst (newtonPoint ϖ a d m s) (newtonSystem d m b Q i) = 0) →
      ∀ J : Ideal (MvPowerSeries (Fin d ⊕ Fin m) O), (∀ i, newtonSystem d m b Q i ∈ J) →
        (d : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin d ⊕ Fin m) (FractionRing O) ⧸
          J.map (MvPowerSeries.map (algebraMap O (FractionRing O)))) →
        ∀ g ∈ J, MvPowerSeries.subst (newtonPoint ϖ a d m s) g = 0

def NewtonStatement : Prop := NewtonLiftStatement ∧ NewtonVanishingStatement

def TruncatedPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H]
    [FiniteDimensional k H] (d : ℕ) (x : Fin d → H),
    (∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom k H), f ^ p = 0) →
    (∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H)) →
    (∀ y ∈ RingHom.ker (Bialgebra.counitAlgHom k H), ∃ l : Fin d → k,
      y - ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2) →
    (∀ l : Fin d → k, ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) →
    Function.Surjective (MvPolynomial.aeval (R := k) x) ∧
      RingHom.ker (MvPolynomial.aeval (R := k) x) =
        Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ p)

def GroupLikeTrivialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H]
    [FiniteDimensional k H],
    (∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom k H), f ^ p = 0) →
    ∀ (B : Type) [CommRing B] [Algebra k B] (χ : B ⊗[k] H),
      IsGroupLikeElem B χ →
      χ - 1 ∈ RingHom.ker (Bialgebra.counitAlgHom B (B ⊗[k] H)) ^ 2 → χ = 1

def HeightOneHopfStatement : Prop := TruncatedPolynomialStatement ∧ GroupLikeTrivialStatement

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.TensorSpan
section
noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]

def intFun (X : Type) : Submodule R (X → C) where
  carrier := {f | ∀ x, ∃ r : R, algebraMap R C r = f x}
  add_mem' := by
    rintro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r + s, by simp [hr, hs]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c f hf x
    obtain ⟨r, hr⟩ := hf x
    exact ⟨c * r, by simp [hr, Algebra.smul_def]⟩

def tensorSpan {X : Type} (M : Submodule R (X → C)) : Submodule R (X × X → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M, F = fun p => g p.1 * h p.2}

def IsLat {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) : Prop :=
  ∃ B : Matrix X X C, IsUnit B.det ∧ M = Submodule.span R (Set.range fun j x => B x j)

def HasColen (v : Valuation C NNReal) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (c : NNReal) : Prop :=
  ∃ B : Matrix X X C, M = Submodule.span R (Set.range fun j x => B x j) ∧ v B.det = c

def addPull (N : Type) [AddCommGroup N] : (N → C) →ₗ[R] (N × N → C) :=
  LinearMap.funLeft R C (fun p : N × N => p.1 + p.2)

structure HopfOrder (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] where
  carrier : Submodule R (N → C)
  lat : IsLat R carrier
  le_int : carrier ≤ intFun R N
  one_mem : (1 : N → C) ∈ carrier
  mul_mem : ∀ f g, f ∈ carrier → g ∈ carrier → f * g ∈ carrier
  comul : ∀ f ∈ carrier, addPull R N f ∈ tensorSpan R carrier
  antipode : ∀ f ∈ carrier, (fun x => f (-x)) ∈ carrier

variable {R}

def dualLat {X : Type} [Fintype X] (M : Submodule R (X → C)) : Submodule R (X → C) where
  carrier := {u | ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a}
  add_mem' := by
    rintro u w hu hw f hf
    obtain ⟨r, hr⟩ := hu f hf
    obtain ⟨s, hs⟩ := hw f hf
    exact ⟨r + s, by simp [hr, hs, add_mul, Finset.sum_add_distrib]⟩
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  smul_mem' := by
    rintro c u hu f hf
    obtain ⟨r, hr⟩ := hu f hf
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, mul_assoc]

def fourier {N H : Type} [Fintype N] (e : H → N → C) :
    (N → C) →ₗ[R] (H → C) where
  toFun u h := ∑ a, u a * e h a
  map_add' u w := by ext h; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by ext h; simp [Algebra.smul_def, Finset.mul_sum, mul_assoc]

def augIdeal {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) : Submodule R (X → C) :=
  M ⊓ LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : X => C) 0)

def resK {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N → C) →ₗ[R] (K → C) :=
  LinearMap.funLeft R C (fun k : K => (k : N))

def pullQ {N : Type} [AddCommGroup N] (K : AddSubgroup N) : (N ⧸ K → C) →ₗ[R] (N → C) :=
  LinearMap.funLeft R C (QuotientAddGroup.mk : N → N ⧸ K)

def extK {N : Type} [AddCommGroup N] (K : AddSubgroup N) [DecidablePred (· ∈ K)] :
    (K → C) →ₗ[R] (N → C) where
  toFun u a := if h : a ∈ K then u ⟨a, h⟩ else 0
  map_add' u w := by ext a; by_cases h : a ∈ K <;> simp [h]
  map_smul' c u := by ext a; by_cases h : a ∈ K <;> simp [h]

def pushQ {N : Type} [AddCommGroup N] [Fintype N] (K : AddSubgroup N)
    [DecidableEq (N ⧸ K)] : (N → C) →ₗ[R] (N ⧸ K → C) where
  toFun u c := ∑ a ∈ Finset.univ.filter (fun a : N => (a : N ⧸ K) = c), u a
  map_add' u w := by ext c; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext d; simp [Finset.smul_sum]

end ReciprocityTheory.PGsh.L2
end
end

