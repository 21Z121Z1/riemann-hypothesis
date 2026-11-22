import Formalism.CyclotomicNorms.Bundle0001

-- bundled from Formalism.CyclotomicNorms.StatementT
section
open Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

def primeToPart (ℓ : ℕ) {M : Type*} [Monoid M] (x : M) : M :=
  x ^ (ℓ ^ (orderOf x).factorization ℓ *
    (((ℓ ^ (orderOf x).factorization ℓ : ℕ) :
      ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val)

abbrev Fbar (g : ℕ) [Fact g.Prime] : Type := AlgebraicClosure (ZMod g)

def rootsBar {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Multiset (Fbar g) :=
  (f.map (algebraMap (ZMod g) (Fbar g))).roots

def IsGood (N g : ℕ) [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X])
    (χ : PP → J → (ZMod g)ˣ) : Prop :=
  (∀ v, (f v).Monic ∧ (f v).natDegree = N ∧ (f v).coeff 0 ≠ 0) ∧
  (∀ v, Squarefree (f v)) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ BB N g → ∀ v, ∀ x ∈ rootsBar (f v), ∀ y ∈ rootsBar (f v),
    primeToPart ℓ x = primeToPart ℓ y → x = y) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ g → ∀ v j, ∀ x ∈ rootsBar (f v),
    primeToPart ℓ x ≠ primeToPart ℓ (algebraMap (ZMod g) (Fbar g) (χ v j : ZMod g))) ∧
  (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = a) ∧
  (∃ v, ∃ q : (ZMod g)[X], Irreducible q ∧ q ∣ f v ∧ q.natDegree.Prime ∧
    N < 2 * q.natDegree ∧ q.natDegree + 3 ≤ N)

def IrredOn {N ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] (ρ : G →* GL (Fin N) (Fbar ℓ))
    (H : Subgroup G) : Prop :=
  ∀ W : Submodule (Fbar ℓ) (Fin N → Fbar ℓ),
    (∀ h ∈ H, ∀ x ∈ W, Matrix.mulVec (ρ h : Matrix (Fin N) (Fin N) (Fbar ℓ)) x ∈ W) → W = ⊥ ∨ W = ⊤

def IrreducibilityCriterion : Prop :=
  ∀ (N : ℕ) (g : Fin 2 → ℕ) [∀ i, Fact (g i).Prime] (PP : Fin 2 → Type) (J : Type)
    (f : ∀ i, PP i → (ZMod (g i))[X]) (χ : ∀ i, PP i → J → (ZMod (g i))ˣ),
    BB N (g 0) ∩ BB N (g 1) = ∅ → (∀ i, IsGood N (g i) (f i) (χ i)) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (i : Fin 2), ℓ ∉ BB N (g i) →
    ∀ (G : Type) [Group G] (ρ : G →* GL (Fin N) (Fbar ℓ)) (τ φ : PP i → G)
      (ι : PP i → Fbar (g i) →* Fbar ℓ),
      (∀ v, ρ (φ v * τ v * (φ v)⁻¹) = ρ (τ v) ^ (g i)) →
      (∀ v, ∀ x y : Fbar (g i), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime ℓ → (orderOf y).Coprime ℓ →
        ι v x = ι v y → x = y) →
      (∀ v, Matrix.charpoly (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)) =
        ((rootsBar (f i v)).map fun x => X - C (ι v (primeToPart ℓ x))).prod) →
      IrredOn ρ ⊤ ∧
      (∀ (H : Subgroup G) [H.Normal], Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) →
        (∀ v, τ v ∈ H) → IrredOn ρ H) ∧
      (∀ v j, ¬ (Matrix.charpoly (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ))).IsRoot
        (ι v (primeToPart ℓ (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i))))))

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.TWAbsUniform
section
open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

def TWAbsUniform : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e e₀ R' D' m₁ t M₀ : ℕ) (O₀ O : Subring K) [IsDiscreteValuationRing O₀]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O₀)] (w₀ : O₀) (w : O)
    (Sig JJ : Type) [Fintype Sig] [Fintype JJ] (vv : JJ → ℝ)
    (F : ℕ → Sig → MvPolynomial (Fin R' ⊕ Fin R') O₀)
    (f : ℕ → JJ → MvPolynomial (Fin R' ⊕ Fin R') O) (D g : ℕ → JJ → MvPolynomial (Fin R') O),
    ℓ.Prime → 0 < e → 0 < e₀ → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ x : O₀, ‖(x : K)‖ ≤ 1) → (∀ x : O, ‖(x : K)‖ ≤ 1) →
    Irreducible w₀ → Irreducible w → vl ℓ (w₀ : K) = 1 / e₀ → vl ℓ (w : K) = 1 / e →
    (∀ j, ∃ n : ℕ, vv j = n / e) →

    (∀ M, M₀ ≤ M → ∀ s, F M s ∉
      Ideal.span {MvPolynomial.C ((ℓ : O₀) ^ (if ℓ = 2 then 1 else 0) * w₀)} +
        varIdeal O₀ (Fin R' ⊕ Fin R') ^ (D' + 1) + lamIdeal O₀ (Fin R' ⊕ Fin R') ℓ M) →

    (∀ M, M₀ ≤ M → ∀ j,
      MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 0)) (f M j) - D M j * g M j ∈
        lamIdeal O (Fin R') ℓ M ∧
      ((MvPolynomial.constantCoeff (g M j) : O) : K) ≠ 0 ∧
      vl ℓ ((MvPolynomial.constantCoeff (g M j) : O) : K) = vv j ∧
      FewFactors ℓ M m₁ (D M j)) →
    ∀ ε : ℝ, 0 < ε →
      ∃ (M k : ℕ) (e'' e' : Fin R' → ℕ) (z : L), M₀ ≤ M ∧ k ≤ M ∧ (∀ i, e'' i < k ∧ e' i < k) ∧
        IsPrimitiveRoot z (ℓ ^ k) ∧ ∀ sg : Sig ⊕ JJ → ℤˣ,
        (∀ s, MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s) ≠ 0) ∧
        (∀ j, MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j) ≠ 0) ∧
        ∑ s, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s)) ≤
          (if ℓ = 2 then 1 else 0) * (Fintype.card Sig : ℝ) + ε ∧
        (∃ εj : JJ → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
          ∀ j, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j)) ≤ vv j + εj j) ∧
        2 * (t : ℝ) * ∑ i, (vl ℓ (z ^ (ℓ ^ e'' i) - 1) + vl ℓ (z ^ (ℓ ^ e' i) - 1)) ≤ ε

end Formalism.CyclotomicNorms
end
end

