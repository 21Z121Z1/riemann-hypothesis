import Formalism.CharacterColumnKernels.StatementN
import Formalism.CharacterColumnKernels.StatementMF

-- bundled from Formalism.CharacterColumnKernels.CharacterColumnKernelPairSetVariant
section
open Finset Classical

noncomputable section

namespace Formalism.NG

section Cochains
variable {O : Type*} [CommRing O] {D : Type*} [Group D] {M : Type*} [AddCommGroup M] [Module O M]

def coD0 (ρ : Representation O D M) : M →ₗ[O] (D → M) where
  toFun v g := ρ g v - v
  map_add' v w := by ext g; simp only [map_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

def coB1 (ρ : Representation O D M) : Submodule O (D → M) := LinearMap.range (coD0 ρ)

def characterColumnKernelSet (ρ : Representation O D M) : Set (D → M) :=
  {c | ∀ g h, c (g * h) = c g + ρ g (c h)}

def characterColumnKernelPairSetVariant (ρ : Representation O D M) : Set (D → D → M) :=
  {c | ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0}

def characterColumnKernelPairSet (ρ : Representation O D M) : Set (D → D → M) :=
  {c | ∃ b : D → M, ∀ g h, c g h = ρ g (b h) - b (g * h) + b g}

end Cochains

def cup1 {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₂ : Representation O D M₂) (β : M₁ →ₗ[O] M₂ →ₗ[O] N) (a : D → M₁) (b : D → M₂) :
    D → D → N :=
  fun g h => β (a g) (ρ₂ g (b h))

def IsEquivPairing {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (ρN : Representation O D N)
    (β : M₁ →ₗ[O] M₂ →ₗ[O] N) : Prop :=
  ∀ g m n, β (ρ₁ g m) (ρ₂ g n) = ρN g (β m n)

def IsEquivMap {O D M M' : Type*} [CommRing O] [Group D] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (ρ : Representation O D M) (ρ' : Representation O D M')
    (f : M →ₗ[O] M') : Prop :=
  ∀ g m, f (ρ g m) = ρ' g (f m)

def StatCupKill : Prop :=
  ∀ (O D M₁ M₂ M₂' N N' M₁'' M₂'' P : Type*) [CommRing O] [Group D]
    [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂] [Module O M₂] [AddCommGroup M₂'] [Module O M₂']
    [AddCommGroup N] [Module O N] [AddCommGroup N'] [Module O N'] [AddCommGroup M₁''] [Module O M₁'']
    [AddCommGroup M₂''] [Module O M₂''] [AddCommGroup P] [Module O P]
    (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (ρ₂' : Representation O D M₂')
    (ρN : Representation O D N) (ρN' : Representation O D N') (ρ₁'' : Representation O D M₁'')
    (ρ₂'' : Representation O D M₂'') (ρP : Representation O D P)
    (β : M₁ →ₗ[O] M₂ →ₗ[O] N) (β' : M₁ →ₗ[O] M₂' →ₗ[O] N') (γ : M₁'' →ₗ[O] M₂'' →ₗ[O] P)
    (j : M₂ →ₗ[O] M₂') (ι : N →ₗ[O] N') (π : M₁ →ₗ[O] M₁'') (φ : M₂ →ₗ[O] M₂'') (ψ : N →ₗ[O] P),
    IsEquivPairing ρ₁ ρ₂ ρN β → IsEquivPairing ρ₁ ρ₂' ρN' β' → IsEquivMap ρ₂ ρ₂' j →
    IsEquivMap ρN ρN' ι → IsEquivMap ρ₁ ρ₁'' π → IsEquivMap ρ₂ ρ₂'' φ → IsEquivMap ρN ρP ψ →
    (∀ m n, ι (β m n) = β' m (j n)) → (∀ m n, γ (π m) (φ n) = ψ (β m n)) →
    (∀ z ∈ characterColumnKernelPairSetVariant ρN, (fun g h => ι (z g h)) ∈ characterColumnKernelPairSet ρN' → z ∈ characterColumnKernelPairSet ρN) →
    ∀ (a : D → M₁) (b : D → M₂) (e : M₂'), a ∈ characterColumnKernelSet ρ₁ → b ∈ characterColumnKernelSet ρ₂ →
      (∀ g, j (b g) = ρ₂' g e - e) →
      cup1 ρ₂'' γ (fun g => π (a g)) (fun g => φ (b g)) ∈ characterColumnKernelPairSet ρP

abbrev ColFree (A : Type*) [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (ι : Type*) (j : ℕ) : Type _ :=
  Ymod r χ E × (ι → A × (Fin j → A) × A)

def colGen {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [DecidableEq ι] {j : ℕ} (y : Ymod r χ E) (l : ι)
    (c : A) (s : Fin j → A) (c₀ : A) : ColFree A r χ E ι j :=
  (y, Pi.single l (c, s, c₀))

def colRel {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι] (D : ι → Subgroup G)
    (j : ℕ) (Kc : ι → Fin j → G → A) (k0 : ι → G → A) : Submodule A (ColFree A r χ E ι j) :=
  Submodule.span A
    ({z | ∃ l, z = colGen 0 l E 0 0} ∪
     {z | ∃ l a, z = colGen 0 l 0 (Pi.single a (1 - e₁)) 0} ∪
     {z | ∃ l, z = colGen 0 l 0 0 (algebraMap T' A δ - E)} ∪
     {z | ∃ l, ∃ g ∈ D l, z = colGen ⟨ycoc r χ E g, Submodule.subset_span ⟨g, rfl⟩⟩ l
        ((((χ g)⁻¹ : T'ˣ) : T') • r g - 1)
        (fun a => -(algebraMap T' A δ * Kc l a g)) (-(algebraMap T' A δ * k0 l g))})

abbrev ColNN {A : Type*} [Ring A] {T' : Type*} [CommRing T'] [Algebra T' A] {G : Type*} [Group G]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [DecidableEq ι] (D : ι → Subgroup G)
    (j : ℕ) (Kc : ι → Fin j → G → A) (k0 : ι → G → A) : Type _ :=
  ColFree A r χ E ι j ⧸ colRel r χ E e₁ δ D j Kc k0

def colD {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V]
    (r : G →* A) (χ : G →* T'ˣ) (D : Subgroup G) : V →ₗ[K] (D → V) where
  toFun v g := ((((χ g)⁻¹ : T'ˣ) : T') • r g) • v - v
  map_add' v w := by ext g; simp only [smul_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_comm]

def StatColumn : Prop :=
  ∀ (A T' K V G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V] [FiniteDimensional K V]
    [Module T' V] [IsScalarTower T' A V]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : ι → Subgroup G) (j : ℕ) (Kc : ι → Fin j → G → A) (k0 : ι → G → A),
    E * E = algebraMap T' A δ * E → e₁ * e₁ = e₁ →
    ∀ δx : K, δx ≠ 0 → (∀ v : V, δ • v = δx • v) →
    Module.finrank K (LinearMap.range (DistribSMul.toLinearMap K V E)) = 1 →
    Module.finrank K (LinearMap.range (DistribSMul.toLinearMap K V e₁)) = 1 →
    (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap K V E), η ≠ 0 →
      ∃ g : G, ((((χ g)⁻¹ : T'ˣ) : T') • r g) • η ≠ η) →
    (∀ l, ∃ L : Submodule K (D l → V),
      LinearMap.range (colD (K := K) (V := V) r χ (D l)) ≤ L ∧
      (∀ a, ∀ s ∈ LinearMap.range (DistribSMul.toLinearMap K V e₁),
        (fun g : D l => Kc l a g • s) ∈ L) ∧
      (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap K V E), (fun g : D l => k0 l g • s) ∈ L) ∧
      Module.rank K (L ⧸ (LinearMap.range (colD (K := K) (V := V) r χ (D l))).comap L.subtype) ≤
        (j + Module.finrank K (LinearMap.ker (colD (K := K) (V := V) r χ (D l))) : ℕ)) →
    ∃ φ : ColNN r χ E e₁ δ D j Kc k0 →ₗ[A] V, φ ≠ 0

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.StatOntoLattice
section
open Polynomial

noncomputable section

namespace Formalism.NG

universe u

def StatBurnside : Prop :=
  ∀ (k A V : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V], IsSimpleModule A V →
    (∀ φ : V →ₗ[A] V, ∃ c : k, ∀ v, φ v = c • v) →
    Function.Surjective (fun a : A => DistribSMul.toLinearMap k V a)

def StatOntoLattice : Prop :=
  ∀ (O A L : Type*) [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A] [AddCommGroup L] [Module O L]
    [Module.Free O L] [Module.Finite O L] (φ : A →ₐ[O] Module.End O L),
    (∀ f : Module.End O L, ∃ a : A,
      f - φ a ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O (Module.End O L))) →
    Function.Surjective φ

def IdempotentLift : Prop :=
  ∀ (O A B : Type*) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Ring A] [Algebra O A] [Module.Finite O A]
    [Ring B] (f : A →+* B), Function.Surjective f →
    (∀ x : A, f x = 0 → ∃ n : ℕ, x ^ n ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O A)) →
    ∀ e₁ e₂ : B, IsIdempotentElem e₁ → IsIdempotentElem e₂ → e₁ * e₂ = 0 → e₂ * e₁ = 0 →
      ∃ E₁ E₂ : A, IsIdempotentElem E₁ ∧ IsIdempotentElem E₂ ∧ E₁ * E₂ = 0 ∧ E₂ * E₁ = 0 ∧
        f E₁ = e₁ ∧ f E₂ = e₂

def StatRankMod : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsLocalRing O] (r : Type) [Fintype r] [DecidableEq r]
    (e : Matrix r r O), IsIdempotentElem e →
    (e.map (IsLocalRing.residue O)).rank = (e.map (algebraMap O (FractionRing O))).rank

def StatSplitAlg : Prop :=
  ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin P.natDegree → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = P.natDegree.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin P.natDegree → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃! φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i

def StatSplitFibre : Prop :=
  ∀ (T T' K : Type*) [CommRing T] [CommRing T'] [Algebra T T'] [Field K] (P : T[X]), P.Monic →
    ∀ (rr : Fin P.natDegree → T'), P.map (algebraMap T T') = ∏ i, (X - C (rr i)) →
      Algebra.adjoin T (Set.range rr) = ⊤ →
    ∀ (b : Module.Basis (Fin P.natDegree.factorial) T T') (x : T →+* K) (a : Fin P.natDegree → K),
      Function.Injective a → P.map x = ∏ i, (X - C (a i)) →
      ∀ c : Fin P.natDegree.factorial → K,
        (∀ φ : T' →+* K, φ.comp (algebraMap T T') = x → ∑ k, c k * φ (b k) = 0) → c = 0

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.StatementBC
section
open Finset

noncomputable section

namespace Formalism.NG

def StatVccBaseChange : Prop :=
  ∀ (O O' : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (X : Type*) (T : Subalgebra O (X → O)) (T' : Subalgebra O' (X → O')),
      (T' : Set (X → O')) = Submodule.span O' ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O))) →
    ∀ (Z : Set X) (x : X), vcc T' Z x = e * vcc T Z x

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.StatementMult
section
open Classical

noncomputable section

namespace Formalism.NG

universe u v

section Mult
variable (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M]

abbrev csFactor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) : Type u :=
  s i.succ ⧸ (s (Fin.castSucc i)).comap (s i.succ).subtype

def csMult (s : CompositionSeries (Submodule R M)) (S : Type v) [AddCommGroup S] [Module R S] : ℕ :=
  (Finset.univ.filter fun i : Fin s.length => Nonempty (csFactor R M s i ≃ₗ[R] S)).card

def IsFullSeries (s : CompositionSeries (Submodule R M)) : Prop := s.head = ⊥ ∧ s.last = ⊤

def compMult (S : Type v) [AddCommGroup S] [Module R S] : ℕ :=
  if h : ∃ s : CompositionSeries (Submodule R M), IsFullSeries R M s then
    csMult R M (Classical.choose h) S
  else 0

end Mult

def StatCsMultIndep : Prop :=
  ∀ (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (S : Type v) [AddCommGroup S]
    [Module R S] (s₁ s₂ : CompositionSeries (Submodule R M)),
    IsFullSeries R M s₁ → IsFullSeries R M s₂ → csMult R M s₁ S = csMult R M s₂ S

def StatCompMultEq : Prop :=
  ∀ (R : Type*) [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (S : Type v) [AddCommGroup S]
    [Module R S] (s : CompositionSeries (Submodule R M)),
    IsFullSeries R M s → compMult R M S = csMult R M s S

def StatEpsMult : Prop :=
  ∀ (O Λ : Type*) (M : Type u) (S : Type v) [CommRing O] [Ring Λ] [Algebra O Λ] [AddCommGroup M]
    [Module Λ M] [Module O M] [IsScalarTower O Λ M] [AddCommGroup S] [Module Λ S] (ε : Λ),
    IsIdempotentElem ε →
    (∀ (T : Type u) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower O Λ T],
      IsSimpleModule Λ T →
      Module.length O (epsImg O (M := T) ε) = if Nonempty (T ≃ₗ[Λ] S) then 1 else 0) →
    IsFiniteLength Λ M →
    Module.length O (epsImg O (M := M) ε) = compMult Λ M S

def StatEpsMultHom : Prop :=
  ∀ (O Λ : Type*) (M : Type u) (S : Type v) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Ring Λ] [Algebra O Λ] [AddCommGroup M]
    [Module Λ M] [Module O M] [IsScalarTower O Λ M] [AddCommGroup S] [Module Λ S] (ε : Λ),
    IsIdempotentElem ε → [SMulCommClass Λ O (EpsDual O Λ (KO O) ε)] →
    (∀ (T : Type u) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower O Λ T],
      IsSimpleModule Λ T →
      Module.length O (epsImg O (M := T) ε) = if Nonempty (T ≃ₗ[Λ] S) then 1 else 0) →
    IsFiniteLength Λ M →
    Module.length O (M →ₗ[Λ] EpsDual O Λ (KO O) ε) = compMult Λ M S

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.StatementNG
section
open Finset

noncomputable section

namespace Formalism.NG

def StatNGlobal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      (m g : Type) [Fintype m] [Fintype g] [DecidableEq g] (P : Matrix m g R'),
    (∀ Θ : Matrix g g R', ∃ f ∈ T', ∀ x', algebraMap O (FractionRing O) (f x') =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    (∀ x', p x' ∉ Z → ∃ φ : Coker P →ₗ[R'] EvalSp O d R' x', φ ≠ 0) →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (t : ℕ) (bl : d → Fin (t + 1)), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      ((Fintype.card g * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
    ∀ (ℓ : ℕ) (what₂ cols Q : Finset ℕ) (lenRow : ℕ → ℕ∞) (e' : ℕ → ℕ) (j : ℕ → ℕ) (vδ : ℕ∞)
      (h0 : ℕ → ℕ∞) (s : ℕ∞) (Sha : ℕ → ℕ∞) (vhE : ℕ∞) (cB : ℕ) (deg : ℕ → ℕ) (H0 : ℕ∞)
      (vζ : ℕ → ℕ∞),
      let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
      Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk 0) P))) ≤
        ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
          4 * (Fintype.card {a // bl a = 0} : ℕ∞) * ((cols.card : ℕ∞) + 1) * vδ →
      (∀ c : Fin (t + 1), c ≠ 0 →
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk c) P))) ≤
          (if (c : ℕ) = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) else Sha ((c : ℕ) - 1)) +
            eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
            (cols.card : ℕ∞) * H0 + ∑ z ∈ Q, vζ z) →
      vcc T Z (p π') ≤
        ∑ w ∈ what₂, lenRow w +
          ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
          ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
          (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
          4 * ((Fintype.card {a // bl a = 0} : ℕ∞) + t) * ((cols.card : ℕ∞) + 1) * vδ +
          (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ z ∈ Q, vζ z

def LocalSubalgebraEtaBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ (Z Zg : Finset X), Zg ⊆ Z → ∀ (a : Module.End (FractionRing O) V) (A : ℤ),
      (∀ v ∈ L, a v ∈ L) → (∀ f : T, a * act f = act f * a) →
      (∀ x ∈ Zg, ∀ v ∈ Vx T act x, a v = (A : FractionRing O) • v) →
      (∀ x ∈ Z, x ∉ Zg → ∀ v ∈ Vx T act x, a v = 0) →
    ∀ B : X → ℕ∞, (∀ x ∈ Zg, vcc T (Z : Set X) x ≤ B x) →
      Module.length O (CongMod T act L (Zg : Set X)) ≤
        ∑ x ∈ Zg, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) *
          (B x + IsDiscreteValuationRing.addVal O (A : O))

end Formalism.NG
end
end

