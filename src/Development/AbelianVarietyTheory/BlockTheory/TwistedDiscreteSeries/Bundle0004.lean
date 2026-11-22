import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundaryVanishingPullback
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.IndefiniteRowSideFullHecke.RankStratification

def pullRep {Γ X : Type} [Group Γ] [TopologicalSpace X] (τ : Γ → X → X)
    (hc : ∀ γ, Continuous (τ γ)) (h1 : ∀ x, τ 1 x = x) (hm : ∀ γ δ x, τ (γ * δ) x = τ δ (τ γ x)) :
    Representation ℂ Γ (SB X) where
  toFun γ :=
    { toFun := fun Φ => ⟨fun x => Φ.1 (τ γ x), Φ.2.1.comp_continuous (hc γ),
        Φ.2.2.comp_homeomorph
          { toFun := τ γ, invFun := τ γ⁻¹
            left_inv := fun x => by rw [← hm, mul_inv_cancel, h1]
            right_inv := fun x => by rw [← hm, inv_mul_cancel, h1]
            continuous_toFun := hc γ, continuous_invFun := hc γ⁻¹ }⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_)
    show Φ.1 (τ 1 x) = Φ.1 x
    rw [h1]
  map_mul' γ δ := by
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_)
    show Φ.1 (τ (γ * δ) x) = Φ.1 (τ δ (τ γ x))
    rw [hm]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Model

variable {a b : ℕ}

def move (γ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    Matrix (Fin b) (Fin a) k :=
  (γ.2⁻¹ : GL (Fin b) k).val * x * γ.1.val

theorem continuous_move (γ : GL (Fin a) k × GL (Fin b) k) : Continuous (move γ) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem move_one (x : Matrix (Fin b) (Fin a) k) : move 1 x = x := by simp [move]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem move_mul (γ δ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    move (γ * δ) x = move δ (move γ x) := by
  simp [move, Matrix.mul_assoc]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem rank_move (γ : GL (Fin a) k × GL (Fin b) k) (x : Matrix (Fin b) (Fin a) k) :
    (move γ x).rank = x.rank := by
  unfold move
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units γ.1),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units γ.2⁻¹)]

variable (k) in

abbrev Stratum (a b r : ℕ) : Type := {x : Matrix (Fin b) (Fin a) k // x.rank = r}

def omChar (a b : ℕ) (μ : kˣ →* ℂˣ) : GL (Fin a) k × GL (Fin b) k →* ℂˣ :=
  (detChar (Fin a) (μ⁻¹ * absPow k ((b : ℂ) / 2))).comp (MonoidHom.fst _ _) *
    (detChar (Fin b) (μ * absPow k (-(a : ℂ) / 2))).comp (MonoidHom.snd _ _)

def omRep (a b : ℕ) (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin a) k × GL (Fin b) k) (SB (Matrix (Fin b) (Fin a) k)) :=
  twist (pullRep move continuous_move move_one move_mul) (omChar a b μ)

def omStratum (a b r : ℕ) (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin a) k × GL (Fin b) k) (SB (Stratum k a b r)) :=
  twist (pullRep (fun γ x => ⟨move γ x.1, (rank_move γ x.1).trans x.2⟩)
      (fun γ => ((continuous_move γ).comp continuous_subtype_val).subtype_mk _)
      (fun x => Subtype.ext (move_one x.1)) (fun γ δ x => Subtype.ext (move_mul γ δ x.1)))
    (omChar a b μ)

def omStratumG (a b r : ℕ) (μ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin a) k) (SB (Stratum k a b r)) :=
  (omStratum a b r μ).comp (MonoidHom.inl _ _)

end Model

def NoBoundaryMaps {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ r : ℕ, r < a → ∀ f : (omStratumG a (a + t) r μ).IntertwiningMap (contra π), f.toLinearMap = 0

def AvoidsExponents {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ j : ℕ, ¬ InSupport π (μ * absPow k (-(((t : ℂ) + 1) / 2 + (j : ℂ))))

def charProd {u a : ℕ} (d : Fin (u + 1) → ℕ) (hd : ∑ i, d i = a) {V₀ : Type} [AddCommGroup V₀]
    [Module ℂ V₀] (π₀ : Representation ℂ (GL (Fin (d 0)) k) V₀) (χ : Fin u → kˣ →* ℂˣ) :=
  parInd (stdBlocks d hd)
    (twist (π₀.comp (Pi.evalMonoidHom (fun i => GL (Fin (d i)) k) 0))
      (∏ i : Fin u, (detChar (Fin (d i.succ)) (χ i)).comp
        (Pi.evalMonoidHom (fun i => GL (Fin (d i)) k) i.succ)))

def LiftConclusion {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ (GL (Fin (a + t)) k) V'),
    IsSmooth π' → π'.IsIrreducible →
    (∃ q : (omRep a (a + t) μ).IntertwiningMap (extTensor (contra π) π'), q.toLinearMap ≠ 0) →
      Nonempty (π'.Equiv (prod₂ π (detRep (Fin t) μ))) ∧
      (prod₂ π (detRep (Fin t) μ)).IsIrreducible ∧ IsUnitarisable (prod₂ π (detRep (Fin t) μ)) ∧
      Module.finrank ℂ ((omRep a (a + t) μ).IntertwiningMap (extTensor (contra π) π')) = 1

def BoundaryVanishing : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a t : ℕ), 1 ≤ a → 1 ≤ t → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → IsUnitaryChar μ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin a) k) V),
      IsSmooth π → π.IsIrreducible → IsUnitarisable π →
      (AvoidsExponents t μ π ∨ a ≤ t) → NoBoundaryMaps t μ π

def BoundaryVanishingVariant : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a t : ℕ), 1 ≤ a → 1 ≤ t → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → IsUnitaryChar μ →
    ∀ (u : ℕ) (d : Fin (u + 1) → ℕ) (hd : ∑ i, d i = a), d 0 ≤ t → (∀ i : Fin u, d i.succ ≤ t + 1) →
    ∀ (V₀ : Type) [AddCommGroup V₀] [Module ℂ V₀] (π₀ : Representation ℂ (GL (Fin (d 0)) k) V₀),
      IsSmooth π₀ → π₀.IsIrreducible → IsUnitarisable π₀ →
    ∀ χ : Fin u → kˣ →* ℂˣ, (∀ i, IsSmoothChar (χ i)) → (∀ i, IsUnitaryChar (χ i)) →
      NoBoundaryMaps t μ (charProd d hd π₀ χ)

def LiftVariant : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a t : ℕ), 1 ≤ a → 1 ≤ t → ∀ μ : kˣ →* ℂˣ, IsSmoothChar μ → IsUnitaryChar μ →
    ∀ (u : ℕ) (d : Fin (u + 1) → ℕ) (hd : ∑ i, d i = a), d 0 ≤ t → (∀ i : Fin u, d i.succ ≤ t + 1) →
    ∀ (V₀ : Type) [AddCommGroup V₀] [Module ℂ V₀] (π₀ : Representation ℂ (GL (Fin (d 0)) k) V₀),
      IsSmooth π₀ → π₀.IsIrreducible → IsUnitarisable π₀ →
    ∀ χ : Fin u → kˣ →* ℂˣ, (∀ i, IsSmoothChar (χ i)) → (∀ i, IsUnitaryChar (χ i)) →
      LiftConclusion t μ (charProd d hd π₀ χ)

example (a b : ℕ) : ∃ φ : SB (Stratum k a b 0), φ ≠ 0 := by
  have hs : Subsingleton (Stratum k a b 0) := ⟨fun x y => Subtype.ext (by
    have key : ∀ z : Stratum k a b 0, z.1 = 0 := fun z => by
      have h0 : LinearMap.range z.1.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 z.2
      apply Matrix.toLin'.injective
      rw [map_zero]
      exact LinearMap.range_eq_bot.1 h0
    rw [key x, key y])⟩
  refine ⟨⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩, fun h => ?_⟩
  simpa using congrFun (congrArg Subtype.val h) ⟨0, Matrix.rank_zero⟩

example (μ : kˣ →* ℂˣ) : ¬ AvoidsExponents 1 μ (detRep (Fin 1) (μ * absPow k (-1))) := by
  intro h
  have := inSupport_detRep (N := 1) (μ * absPow k (-1)) 0
  apply h 0
  simpa using this

end GlobalTheory.IndefiniteRowSideFullHecke.RankStratification
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GodementJacquetZeta
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces

def FinInSupport {F n Y : Type} [Field F] [Fintype n] [DecidableEq n] [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL n F) Y) (χ : Fˣ →* ℂˣ) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n) (a : Fin s), d a = 1 ∧
    ∃ (Z : Type) (_ : AddCommGroup Z) (_ : Module ℂ Z)
      (ρ : Representation ℂ (Levi F fun a => Fin (d a)) Z),
      ρ.IsIrreducible ∧ IsSubquotient ρ (jacU e τ) ∧
        ∀ (g : GL (Fin (d a)) F) (z : Z),
          ρ (Pi.mulSingle a g) z = (χ (GeneralLinearGroup.det g) : ℂ) • z

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

def IsLevelOneConstituent (σ : Representation ℂ (GL n k) V) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (GL n 𝓀[k]) Y) : Prop :=
  τ.IsIrreducible ∧ ∃ f : Y →ₗ[ℂ] V, Function.Injective f ∧
    ∀ (g : GL n 𝒪[k]) (y : Y),
      σ (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) (f y) =
        f (τ (GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g) y)

def HasTamePart (μ : kˣ →* ℂˣ) (χ : 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∀ u : 𝒪[k]ˣ, μ (Units.map (algebraMap 𝒪[k] k).toMonoidHom u) =
    χ (Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom u)

def AvoidsTame (σ : Representation ℂ (GL n k) V) (χ : 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (GL n 𝓀[k]) Y),
    IsLevelOneConstituent σ τ ∧ ¬ FinInSupport τ χ ∧ ¬ FinInSupport τ χ⁻¹

def TypedPlace (σ : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) : Prop :=
  ∃ χ : 𝓀[k]ˣ →* ℂˣ, HasTamePart μ χ⁻¹ ∧ AvoidsTame σ χ

def TwistPlace (σ : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) : Prop :=
  IsSpherical σ ∧ ¬ IsUnram μ

abbrev blockSizes (r t j : ℕ) : Fin (j + 1) → ℕ := Fin.cons r fun _ => t

theorem sum_blockSizes (r t j : ℕ) : ∑ a, blockSizes r t j a = r + j * t := by
  simp [Fin.sum_univ_succ]

def chainLevi {r : ℕ} (t : ℕ) {j : ℕ} (σ : Representation ℂ (GL (Fin r) k) V)
    (μ : Fin j → kˣ →* ℂˣ) :
    Representation ℂ (Levi k fun a => Fin (blockSizes r t j a)) V :=
  twist (σ.comp (Pi.evalMonoidHom (fun a => GL (Fin (blockSizes r t j a)) k) 0))
    (∏ i : Fin j, (detChar (Fin (blockSizes r t j i.succ)) (μ i)).comp
      (Pi.evalMonoidHom (fun a => GL (Fin (blockSizes r t j a)) k) i.succ))

def chain {r : ℕ} (t : ℕ) {j : ℕ} (σ : Representation ℂ (GL (Fin r) k) V) (μ : Fin j → kˣ →* ℂˣ) :=
  parInd (stdBlocks (blockSizes r t j) (sum_blockSizes r t j)) (chainLevi t σ μ)

def NoHighTwist (π : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) (t : ℕ) : Prop :=
  ∀ e : ℝ, ((t : ℝ) + 1) / 2 ≤ e →
    ¬ InSupport π (μ * absPow k (e : ℂ)) ∧ ¬ InSupport π (μ * absPow k (-(e : ℂ))) ∧
    ¬ InSupport π (μ⁻¹ * absPow k (e : ℂ)) ∧ ¬ InSupport π (μ⁻¹ * absPow k (-(e : ℂ)))

def NoUnramTwist (π : Representation ℂ (GL n k) V) (μ : kˣ →* ℂˣ) : Prop :=
  ∀ ν : kˣ →* ℂˣ, IsUnram ν → ¬ InSupport π (μ * ν)

variable [MeasurableSpace k] [BorelSpace k]

def gjIntegrand (π : Representation ℂ (GL n k) V) (Φ : Matrix n n k → ℂ) (v : V)
    (l : smoothPart π.dual) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * (l : Module.Dual ℂ V) (π g v) *
    (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)

def gjZeta (ν : Measure k) (π : Representation ℂ (GL n k) V) (Φ : Matrix n n k → ℂ) (v : V)
    (l : smoothPart π.dual) (s : ℂ) : ℂ :=
  ∫ g, gjIntegrand π Φ v l s g ∂(volGL ν n)

def IsGJFactor (ν : Measure k) (π : Representation ℂ (GL n k) V) (P : Polynomial ℂ) : Prop :=
  P.eval 0 = 1 ∧
  (∀ Φ ∈ SB (Matrix n n k), ∀ (v : V) (l : smoothPart π.dual),
    ∃ (c : ℝ) (N : ℕ) (Q : Polynomial ℂ), ∀ s : ℂ, c < s.re →
      Integrable (gjIntegrand π Φ v l s) (volGL ν n) ∧
      gjZeta ν π Φ v l s * P.eval ((resCard k : ℂ) ^ (-s)) * ((resCard k : ℂ) ^ (-s)) ^ N =
        Q.eval ((resCard k : ℂ) ^ (-s))) ∧
  ∃ (m : ℕ) (Φ : Fin m → Matrix n n k → ℂ) (v : Fin m → V) (l : Fin m → smoothPart π.dual) (c : ℝ),
    (∀ i, Φ i ∈ SB (Matrix n n k)) ∧ ∀ s : ℂ, c < s.re →
      (∑ i, gjZeta ν π (Φ i) (v i) (l i) s) * P.eval ((resCard k : ℂ) ^ (-s)) = 1

end Local

def ChainSupport : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (μs : Fin j → kˣ →* ℂˣ) (μ : kˣ →* ℂˣ),
    IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ →
    (∀ i, IsSmoothChar (μs i) ∧ IsUnitaryChar (μs i)) → IsSmoothChar μ → IsUnitaryChar μ →
    (TypedPlace σ μ ∨ TwistPlace σ μ ∨ (IsSpherical σ ∧ r ≤ t)) →
    (chain t σ μs).IsIrreducible ∧ IsUnitarisable (chain t σ μs) ∧ NoHighTwist (chain t σ μs) μ t

def RamifiedSupport : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (μ : kˣ →* ℂˣ),
    IsSmooth σ → σ.IsIrreducible → IsSmoothChar μ → (TypedPlace σ μ ∨ TwistPlace σ μ) →
    NoUnramTwist σ μ

def LocalFactors : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    (∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
      (μ : kˣ →* ℂˣ),
      IsSmooth σ → σ.IsIrreducible → IsSmoothChar μ → (TypedPlace σ μ ∨ TwistPlace σ μ) →
      IsGJFactor ν (twist σ (detChar (Fin r) μ⁻¹)) 1 ∧
        IsGJFactor ν (twist (contra σ) (detChar (Fin r) μ)) 1) ∧
    (∀ (μ' μ : kˣ →* ℂˣ) (χ' χ : 𝓀[k]ˣ →* ℂˣ), HasTamePart μ' χ'⁻¹ → HasTamePart μ χ⁻¹ → χ' ≠ χ →
      IsGJFactor ν (detRep (Fin 1) (μ' / μ)) 1 ∧ IsGJFactor ν (detRep (Fin 1) (μ / μ')) 1) ∧
    ∀ μ'₀ μ₀ ξ : kˣ →* ℂˣ, IsUnram μ'₀ → IsUnram μ₀ →
      (μ'₀ * ξ) / (μ₀ * ξ) = μ'₀ / μ₀ ∧ IsUnram ((μ'₀ * ξ) / (μ₀ * ξ))

def GoodSupport : Prop := ChainSupport ∧ RamifiedSupport ∧ LocalFactors

section Examples

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

example {N : ℕ} (μ : kˣ →* ℂˣ) : ¬ NoUnramTwist (detRep (Fin (N + 1)) μ) μ := fun h =>
  h _ (isUnram_absPow k _) (inSupport_detRep μ 0)

example {N : ℕ} {μ : kˣ →* ℂˣ} (h : ¬ IsUnram μ) : TwistPlace (detRep (Fin N) (1 : kˣ →* ℂˣ)) μ :=
  ⟨isSpherical_detRep fun _ _ => rfl, h⟩

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IrreducibleTensorCharacter
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IrreducibleTensorCharacter

def firstLast {n β : ℕ} (h : β ≤ n) : Fin β ⊕ Fin (n - β) ≃ Fin n :=
  stdSum (Nat.add_sub_cancel' h)

section

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CentralExponentBoundOver : Prop :=
  ∀ (n β : ℕ) (_ : 1 ≤ β) (hβn : β ≤ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π₀ : Representation ℂ (GL (Fin n) k) V),
    π₀.IsIrreducible → IsUnitarisable π₀ → IsSmooth π₀ →
    ∀ (S : Type) [AddCommGroup S] [Module ℂ S] (s : Representation ℂ (GL (Fin β) k) S)
      (S' : Type) [AddCommGroup S'] [Module ℂ S'] (s' : Representation ℂ (GL (Fin (n - β)) k) S'),
      (extTensor s s').IsIrreducible →
      IsSubquotient (extTensor s s') (jac₂ (firstLast hβn) π₀) →
      ∀ (ω : kˣ →* ℂˣ) (c : ℝ), HasCentralChar s ω →
        (∀ z : kˣ, ‖(ω z : ℂ)‖ = nabs k z ^ (-((β : ℝ) * c))) →
        c ≤ ((n : ℝ) - (β : ℝ)) / 2

end

def CentralExponentBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    CentralExponentBoundOver k

section Sharp

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tensorChar {G H : Type} [Group G] [Group H] (χ : G →* ℂˣ) (ψ : H →* ℂˣ) :
    (ofChar (χ.comp (MonoidHom.fst G H) * ψ.comp (MonoidHom.snd G H))).IntertwiningMap
      (extTensor (ofChar χ) (ofChar ψ)) where
  toLinearMap := (TensorProduct.lid ℂ ℂ).symm.toLinearMap
  isIntertwining' g := by
    ext
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply, extTensor_tmul,
      ofChar_apply, mul_one, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
    apply (TensorProduct.lid ℂ ℂ).injective
    simp

end Sharp

end GlobalTheory.IndefiniteRowSideFullHecke.IrreducibleTensorCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound

def InTrivialRange (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) : Prop :=
  ∀ i, (q : ℝ) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ (q : ℝ) ^ (((n : ℝ) - 1) / 2)

def SatakeTrivialBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (α : Fin n → ℂˣ),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsSpherical π → HasSatake π α →
      InTrivialRange (resCard k) α

section Hecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def diagJ (n : ℕ) (ϖ : kˣ) (j : ℕ) : GL (Fin n) k :=
  diagT k (Fin n) fun i => if (i : ℕ) < j then ϖ else 1

def HeckeEigen (π : Representation ℂ (GL (Fin n) k) V) (v : V) (t : GL (Fin n) k) (c : ℂ) : Prop :=
  ∃ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)),
    (∀ g : GL (Fin n) k, (g : GL (Fin n) k ⧸ KO k (Fin n)) ∈ S ↔
      ∃ a ∈ KO k (Fin n), ∃ b ∈ KO k (Fin n), g = a * t * b) ∧
    ∑ x ∈ S, π x.out v = c • v

end Hecke

def SatakeTrivialBoundHecke : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (v : V) (ϖ : kˣ) (α : Fin n → ℂˣ),
    IsUnitarisable π → v ≠ 0 → v ∈ fixed π (KO k (Fin n)) → valuation k (ϖ : k) = uniformizer k →
    (∀ j : ℕ, 1 ≤ j → j ≤ n → HeckeEigen π v (diagJ n ϖ j)
      ((((resCard k : ℝ) ^ ((j : ℝ) * ((n : ℝ) - j) / 2) : ℝ) : ℂ) *
        (Finset.univ.val.map fun i => (α i : ℂ)).esymm j)) →
      InTrivialRange (resCard k) α

section Basic₂

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

example (n : ℕ) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    IsSmooth (detRep (Fin n) (1 : kˣ →* ℂˣ)) ∧ (detRep (Fin n) (1 : kˣ →* ℂˣ)).IsIrreducible ∧
    IsUnitarisable (detRep (Fin n) (1 : kˣ →* ℂˣ)) ∧ IsSpherical (detRep (Fin n) (1 : kˣ →* ℂˣ)) ∧
    HasSatake (detRep (Fin n) (1 : kˣ →* ℂˣ))
      fun i => (1 : kˣ →* ℂˣ) ϖ * absPow k (((i : ℕ) : ℂ) - ((n : ℂ) - 1) / 2) ϖ := by
  have h : IsUnram (1 : kˣ →* ℂˣ) := fun _ _ => rfl
  refine ⟨(isSmooth_ofChar_iff _).2 (isSmoothChar_of_isUnram h).detChar, isIrreducible_ofChar _,
    (isUnitarisable_ofChar_iff _).2 fun g => by simp, isSpherical_detRep h, hasSatake_detRep h hϖ⟩

example (q : ℕ) (α : Fin 1 → ℂˣ) : InTrivialRange q α ↔ ‖(α 0 : ℂ)‖ = 1 := by
  simp only [InTrivialRange, Fin.forall_fin_one, Nat.cast_one, sub_self, zero_div, neg_zero,
    Real.rpow_zero]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound
end
end

