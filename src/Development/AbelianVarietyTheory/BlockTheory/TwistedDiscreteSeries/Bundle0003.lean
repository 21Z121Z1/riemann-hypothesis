import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentTerms
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lattices
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def MapsInto (x : Matrix κ ι k) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ v ∈ M', x *ᵥ v ∈ M

def InjMod (ϖ : 𝒪[k]) (x : Matrix κ ι k) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  MapsInto x M' M ∧ ∀ v ∈ M', x *ᵥ v ∈ ϖ • M → v ∈ ϖ • M'

def act (g : GL ι k) (M : Submodule 𝒪[k] (ι → k)) : Submodule 𝒪[k] (ι → k) :=
  M.map ((Matrix.mulVecLin g.val).restrictScalars 𝒪[k])

def stdLat (k : Type) [Field k] [ValuativeRel k] (ι : Type) : Submodule 𝒪[k] (ι → k) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)

def IsReps (ϖ : 𝒪[k]) (M : Submodule 𝒪[k] (ι → k)) (T : Finset (ι → k)) : Prop :=
  (∀ t ∈ T, t ∈ M) ∧ ∀ v ∈ M, ∃! t, t ∈ T ∧ v - t ∈ ϖ • M

def SuppIn (Ψ : Matrix κ ι k → ℂ) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ x, Ψ x ≠ 0 → MapsInto x M' M

def PeriodicMod (ϖ : 𝒪[k]) (Ψ : Matrix κ ι k → ℂ) (M' : Submodule 𝒪[k] (ι → k))
    (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ x y, MapsInto y M' M → Ψ (x + (ϖ : k) • y) = Ψ x

def SuppInj (ϖ : 𝒪[k]) (Ψ : Matrix κ ι k → ℂ) (M' : Submodule 𝒪[k] (ι → k))
    (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ x, Ψ x ≠ 0 → InjMod ϖ x M' M

end Lattices

section Chain
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def aux (k : Type) [Field k] (n : Type) [DecidableEq n] {c : ℕ} (i : Fin c) : n ⊕ Fin c → k :=
  Pi.single (Sum.inr i) 1

def inX (k : Type) [Field k] [ValuativeRel k] (n : Type) (c : ℕ) : (n → k) →ₗ[𝒪[k]] (n ⊕ Fin c → k) where
  toFun v := Sum.elim v 0
  map_add' v w := by ext (r | r) <;> simp
  map_smul' a v := by ext (r | r) <;> simp

def chainLat (ϖ : 𝒪[k]) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔
    Submodule.span 𝒪[k] (Set.range fun i : Fin c => (ϖ : k) ^ (i.val + 1) • aux k n i)

def Yle (k : Type) [Field k] [ValuativeRel k] (n : Type) (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {v | ∀ l : Fin c, i < l.val + 1 → v (Sum.inr l) = 0}
  add_mem' hv hw l hl := by simp [hv l hl, hw l hl]
  zero_mem' l _ := rfl
  smul_mem' a v hv l hl := by simp [hv l hl]

def pt (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  basePt c x₀ + Matrix.of fun r s =>
    Sum.elim (fun _ => 0) (fun j : Fin (c + 1) => Fin.cases 0 (fun i => y i r) j) s

def expo (c d : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 c, (i * d + i * (i - 1) / 2)

def term (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x₀ : Matrix n n' k) (w : Fin c → (n ⊕ Fin c → k)) : ℂ :=
  Ψ (pt x₀ fun i => ((ϖ : k) ^ (i.val + 2))⁻¹ • w i) *
    (starRingEnd ℂ) (ψ ((∑ i : Fin c, w i (Sum.inr i) / (ϖ : k) ^ (i.val + 1)) / (ϖ : k)) : ℂ)

variable [MeasurableSpace k] [BorelSpace k]

def OneClass (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (ν : Measure k) (n : Type) [Fintype n] [DecidableEq n]
    (hc : 1 ≤ c) (L' : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)), Submodule.IsLattice k Λ →
    ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      SuppIn Ψ (chainLat ϖ (c + 1) L') Λ → PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') Λ →
      opE ψ ν 1 Ψ ≠ 0 →
        (∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) =
          Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}) ∧
        (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ ∧
        (∃ u ∈ N k n c 1, act u Λ = chainLat ϖ c (Λ.comap (inX k n c))) ∧
        ∃ r ∈ R k n c 1, Λ = act r (chainLat ϖ c (stdLat k n))

def OneCoset (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (ν : Measure k) (n : Type) [Fintype n] [DecidableEq n]
    (c : ℕ) (L' : Submodule 𝒪[k] (n' → k)) : Prop :=
  (∀ (μ : kˣ →* ℂˣ), ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      SuppIn Φ (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) →
      PeriodicMod ϖ Φ (chainLat ϖ (c + 1) L') (chainLat ϖ c (stdLat k n)) →
      ∀ (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
        act h' (chainLat ϖ (c + 1) L') = chainLat ϖ (c + 1) L' →
        opE ψ ν 1 (om μ h' h Φ) ≠ 0 →
          ∃ r ∈ R k n c 1, ∃ t : GL (n ⊕ Fin c) k,
            act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) ∧ h = r * t) ∧
  ∀ J : Subgroup (GL (n ⊕ Fin c) k),
    (∀ j ∈ J, act j (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n)) →
    (∀ j : GL (n ⊕ Fin c) k, act j (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) →
      MapsInto (j.val - 1) (chainLat ϖ c (stdLat k n)) (ϖ • chainLat ϖ c (stdLat k n)) → j ∈ J) →
    ∃ T : Finset (GL (n ⊕ Fin c) k),
      (∀ t ∈ T, act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n)) ∧
      ∀ h : GL (n ⊕ Fin c) k,
        (∃ r ∈ R k n c 1, ∃ t : GL (n ⊕ Fin c) k,
            act t (chainLat ϖ c (stdLat k n)) = chainLat ϖ c (stdLat k n) ∧ h = r * t) ↔
          ∃ r ∈ R k n c 1, ∃ t ∈ T, ∃ j ∈ J, h = r * t * j

open Classical in

def FunMod (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (ν : Measure k) (n : Type) [Fintype n] [DecidableEq n]
    (c : ℕ) (L' : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (L : Submodule 𝒪[k] (n → k)), Submodule.IsLattice k L →
    ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      SuppIn Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L) →
      PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L) →
        SuppIn (opE ψ ν 1 Ψ) L' L ∧ PeriodicMod ϖ (opE ψ ν 1 Ψ) L' L ∧
        (∃ T : Fin c → Finset (n ⊕ Fin c → k),
          ∀ i, IsReps ϖ (chainLat ϖ c L ⊓ Yle k n c (i.val + 1)) (T i)) ∧
        (L ≤ stdLat k n →
          (∀ T : Fin c → Finset (n ⊕ Fin c → k),
            (∀ i, IsReps ϖ (chainLat ϖ c L ⊓ Yle k n c (i.val + 1)) (T i)) →
            ∀ x₀ : Matrix n n' k, MapsInto x₀ L' L →
              opE ψ ν 1 Ψ x₀ =
                (resCard k : ℂ) ^ expo c (Fintype.card n) /
                  (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup : ℂ) ^ c *
                ∑ w ∈ Fintype.piFinset T, term ϖ ψ Ψ x₀ w) ∧
          ∀ x₀ : Matrix n n' k,
            ∃ z ∈ Subring.closure ({ζ : ℂ | ζ ^ ringChar 𝓀[k] = 1} ∪ Set.range Ψ),
              opE ψ ν 1 Ψ x₀ =
                (resCard k : ℂ) ^ expo c (Fintype.card n) /
                  (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup : ℂ) ^ c * z)

def InjSupp (ϖ : 𝒪[k]) (ψ : AddChar k Circle) (ν : Measure k) (n : Type) [Fintype n] [DecidableEq n]
    (c : ℕ) (L' : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (L : Submodule 𝒪[k] (n → k)), Submodule.IsLattice k L →
    ∀ Ψ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      SuppIn Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L) →
      PeriodicMod ϖ Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L) →
      SuppInj ϖ Ψ (chainLat ϖ (c + 1) L') (chainLat ϖ c L) →
        SuppInj ϖ (opE ψ ν 1 Ψ) L' L

end Chain

def Shape : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (hc : 1 ≤ c)
    (ϖ : 𝒪[k]) (_ : Irreducible ϖ) (ψ : AddChar k Circle) (_ : HasConductor ψ 1)
    (ν : Measure k) (_ : IsUnitVol ν)
    (L' : Submodule 𝒪[k] (n' → k)) (_ : Submodule.IsLattice k L'),
    OneClass ϖ ψ ν n hc L' ∧ OneCoset ϖ ψ ν n c L' ∧ FunMod ϖ ψ ν n c L' ∧ InjSupp ϖ ψ ν n c L'

example (d : ℕ) : expo 2 d = 3 * d + 1 := by
  simp [expo, Finset.sum_Icc_succ_top]; ring

open Classical in

example {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ϖ : 𝒪[k])
    (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) :
    SuppIn (fun x => if MapsInto x M' M then 1 else 0) M' M ∧
      PeriodicMod ϖ (fun x => if MapsInto x M' M then 1 else 0) M' M := by
  refine ⟨fun x hx => by by_contra h; simp [h] at hx, fun x y hy => ?_⟩
  have : MapsInto (x + (ϖ : k) • y) M' M ↔ MapsInto x M' M := by
    refine forall₂_congr fun v hv => ?_
    rw [Matrix.add_mulVec, Matrix.smul_mulVec]
    exact M.add_mem_iff_left (M.smul_mem ϖ (hy v hv))
  simp only [this]

end GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PositiveTwistAverage
section
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsUnramUnitary (η : kˣ →* ℂˣ) : Prop := IsUnram η ∧ ∀ x, ‖(η x : ℂ)‖ = 1

def omTw {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ η' η : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) : Matrix b a k → ℂ := fun x =>
  (η' (Matrix.GeneralLinearGroup.det g) : ℂ) * ((η (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) * om μ g h Φ x

def perp {m : Type} [Fintype m] (ψ : AddChar k Circle) (U₀ : Submodule 𝒪[k] (m → k)) : AddSubgroup (m → k) where
  carrier := {β | ∀ u ∈ U₀, ψ (u ⬝ᵥ β) = 1}
  add_mem' := fun {x y} hx hy u hu => by
    rw [dotProduct_add, AddChar.map_add_eq_mul, hx u hu, hy u hu, one_mul]
  zero_mem' := fun u _ => by simp
  neg_mem' := fun {x} hx u hu => by rw [dotProduct_neg, AddChar.map_neg_eq_inv, hx u hu, inv_one]

def IsReps {V : Type} [AddCommGroup V] (D B : AddSubgroup V) (T : Finset V) : Prop :=
  (∀ t ∈ T, t ∈ D) ∧ ∀ β ∈ D, ∃! t, t ∈ T ∧ β - t ∈ B

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A A' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']

def IsPosTw (ψ : AddChar k Circle) (η : kˣ →* ℂˣ) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ, IsNEquiv ψ p σ (b φ)) ∧ ∀ (g : GL n k) φ v, b (π g φ) (σ (embX c g) v) =
    (η (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * b φ v

def IsColLift (μ : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) P') (π : Representation ℂ (GL n k) P)
    (θ : P' →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] P) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) φ, ∀ Ψ ∈ SB (Matrix n n' k), θ (π' g φ) (om μ g h Ψ) = π h (θ φ Ψ)

def IsRowLift (μ η' η : kˣ →* ℂˣ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (σ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) A')
    (ϑ : A →ₗ[ℂ] (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) →ₗ[ℂ] A') : Prop :=
  ∀ (g : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k) F,
    ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ϑ (σ h F) (omTw μ η' η g h Φ) = σ' g (ϑ F Φ)

variable [MeasurableSpace k] [BorelSpace k]

def avg (ν : Measure k) (μ η' η : kˣ →* ℂˣ) (p : ℕ) (C : Submodule 𝒪[k] (n' → k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ := fun x =>
  ∫ u in (C : Set (n' → k)), omTw μ η' η (rowE (c + 1) p u) 1 Φ x ∂(Measure.pi fun _ => ν)

def RrIs (ψ : AddChar k Circle) (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (μ η' η : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (θ : P' →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] P) (b : P → A → ℂ) (φ : P') (F : A)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∀ z', IsQuotInt ν μX μG p (fun h => b (θ φ (opE ψ ν p (omTw μ η' η 1 h Φ))) (σ h F)) z' ↔ z' = z

def TargetFormulas (ψ : AddChar k Circle) (ν : Measure k) (μX : Measure (GL n k))
    (μG : Measure (GL (n ⊕ Fin c) k)) (μ η' η : kˣ →* ℂˣ) (p : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (U : Subgroup (GL (n ⊕ Fin c) k))
    (C₀ U₀ B₁ : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (P P' A : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A] [Module ℂ A]
    (π : Representation ℂ (GL n k) P) (π' : Representation ℂ (GL n' k) P')
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (θ : P' →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] P)
    (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (φ : P') (F : A),
    IsSmoothRep π → IsSmoothRep π' → IsSmoothRep σ → IsColLift μ π' π θ → IsPosTw ψ η p π σ b →
    (∀ u ∈ U, σ u F = F) →
    (∀ C : Submodule 𝒪[k] (n' → k), C.IsLattice k → C₀ ≤ C → ∃ z,
      RrIs ψ ν μX μG μ η' η (p + 1) σ θ (fun φ₁ v => exUp ν p σ (b φ₁) v) φ F Φ z ∧
      RrIs ψ ν μX μG μ η' η p σ θ (fun φ₁ v => b φ₁ v) φ F (avg ν μ η' η p C Φ) z) ∧
    (∀ T : Finset (n' → k), IsReps (perp ψ U₀) B₁.toAddSubgroup T → ∃ w : (n' → k) → ℂ,
      (∀ β ∈ T, RrIs ψ ν μX μG μ η' η (p + 1) σ θ (fun φ₁ v => exUp ν p σ (b φ₁) v) φ F
        (omTw μ η' η (colE (c + 1) (p + 1) β) 1 Φ) (w β)) ∧
      RrIs ψ ν μX μG μ η' η p σ θ (fun φ₁ v => b φ₁ v) φ F Φ
        ((((Measure.pi fun _ : n' => ν).real (B₁ : Set (n' → k)) : ℝ) : ℂ) * ∑ β ∈ T, w β))

def SourceFormulas (ψ : AddChar k Circle) (ν : Measure k) (μ η' η : kˣ →* ℂˣ) (p : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (U : Subgroup (GL (n ⊕ Fin c) k))
    (C₀ U₀ B₁ : Submodule 𝒪[k] (n' → k)) : Prop :=
  ∀ (P' A A' : Type) [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    (π' : Representation ℂ (GL n' k) P') (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (σ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) A')
    (ϑ : A →ₗ[ℂ] (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) →ₗ[ℂ] A')
    (b' : P' →ₗ[ℂ] A' →ₗ[ℂ] ℂ) (φ : P') (F : A),
    IsSmoothRep π' → IsSmoothRep σ → IsSmoothRep σ' → IsRowLift μ η' η σ σ' ϑ → IsPosTw ψ η' p π' σ' b' →
    (∀ u ∈ U, σ u F = F) →
    (∀ C : Submodule 𝒪[k] (n' → k), C.IsLattice k → C₀ ≤ C →
      exUp ν p σ' (b' φ) (ϑ F Φ) = b' φ (ϑ F (avg ν μ η' η p C Φ))) ∧
    (∀ T : Finset (n' → k), IsReps (perp ψ U₀) B₁.toAddSubgroup T →
      b' φ (ϑ F Φ) = (((Measure.pi fun _ : n' => ν).real (B₁ : Set (n' → k)) : ℝ) : ℂ) *
        ∑ β ∈ T, exUp ν p σ' (b' φ) (ϑ F (omTw μ η' η (colE (c + 1) (p + 1) β) 1 Φ)))

def UniformExchange : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p < c →
  ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → IsSelfDual ψ ν →
  ∀ (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)), μX.IsHaarMeasure → μG.IsHaarMeasure →
  ∀ (μ η' η : kˣ →* ℂˣ), Continuous μ → IsUnramUnitary η' → IsUnramUnitary η →
  ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
  ∀ U : Subgroup (GL (n ⊕ Fin c) k), IsOpen (U : Set (GL (n ⊕ Fin c) k)) →
  ∃ C₀ U₀ B₁ : Submodule 𝒪[k] (n' → k), C₀.IsLattice k ∧ U₀.IsLattice k ∧ B₁.IsLattice k ∧
    (∀ u ∈ U₀, omTw μ η' η (rowE (c + 1) p u) 1 Φ = Φ) ∧
    (∀ β ∈ B₁, omTw μ η' η (colE (c + 1) (p + 1) β) 1 Φ = Φ) ∧
    B₁.toAddSubgroup ≤ perp ψ U₀ ∧ (∃ T, IsReps (perp ψ U₀) B₁.toAddSubgroup T) ∧
    TargetFormulas ψ ν μX μG μ η' η p Φ U C₀ U₀ B₁ ∧ SourceFormulas ψ ν μ η' η p Φ U C₀ U₀ B₁

omit [MeasurableSpace k] [BorelSpace k] in

theorem omTw_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) : omTw μ 1 1 g h Φ = om μ g h Φ := by
  funext x; simp [omTw]

omit [MeasurableSpace k] [BorelSpace k] in

theorem isPosTw_one (ψ : AddChar k Circle) (p : ℕ) (π : Representation ℂ (GL n k) P)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) :
    IsPosTw ψ 1 p π σ b ↔ IsPos ψ p π σ b := by
  simp [IsPosTw, IsPos]

omit [MeasurableSpace k] [BorelSpace k] in

theorem isUnramUnitary_one : IsUnramUnitary (1 : kˣ →* ℂˣ) := ⟨fun _ _ => rfl, fun _ => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
end
end

