import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymChain
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

namespace SymData

def SupportAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    h ∈ stabLat ((S.T t).bas (j + 1) c (by omega)) → ∀ x₀ e,
      (S.T t).Phi j c H ((h⁻¹).val * affPt p x₀ e) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ ((S.T t).lev (j + 1) c (by omega)).J, h = r * u

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

def ClassAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j c H)) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ stabLat ((S.T t).bas (j + 1) c (by omega)), h = r * u

def OneIndexAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j c H)) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) c p, ∃ u ∈ ((S.T t).lev (j + 1) c (by omega)).J, h = r * u

def ExchangeAt : Prop :=
  ∀ j c (H : j + c = s) (p : ℕ), 1 ≤ p → p ≤ c → p ≤ S.ρ + 1 → ∃ C : ℝ, 0 < C ∧
    opE S.ψ ν p ((S.T t).Phi j c H) = (C : ℂ) • opE S.ψ ν 1 ((S.T t).Phi j c H)

end SymData

def Average : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j : ℕ), ∃ U : Finset (P.iter t μ hμ (j + 1)).J, U.Nonempty ∧
      P.iterPhi t μ hμ j = ∑ u ∈ U, ((P.iter t μ hμ (j + 1)).lam u : ℂ) •
        om (μ (j + 1)) 1 (u : GL (Ix r t (j + 1)) k) ((TypeDatum.principal k r).iterPhi t μ hμ j)

def AllPositions : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν ∧ S.ExchangeAt t ν

end GlobalTheory.SymChain
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.LocFlat
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

section Ops
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] {c : ℕ}

def colAt (n' : Type) (c p : ℕ) (y : n → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 (Matrix.of fun r i => if i.val + 1 = p then y r else 0) 0 0

def rowAt (n : Type) (c p : ℕ) (u : n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 0 (Matrix.of fun l s => if l.val + 1 = p then u s else 0) 0

def flCol (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix n (n' ⊕ Unit) k) : ℂ :=
  opE ψ ν p (fun z => Φ (z + colAt n' c p fun r => x r (Sum.inr ()))) x.toCols₁

def flRow (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Unit) n' k) : ℂ :=
  opE ψ ν p (fun z => Φ (z + rowAt n c p (x (Sum.inr ())))) x.toRows₁

def contr (ψ : AddChar k Circle) (ν : Measure k) (Ψ₁ : Matrix n (n' ⊕ Unit) k → ℂ) (Ψ₂ : Matrix (n'' ⊕ Unit) n k → ℂ)
    (p : Matrix n n' k × Matrix n'' n k) : ℂ :=
  ∫ u : n → k, Ψ₂ (fromRows p.2 (Matrix.of fun _ => u)) *
    hat ψ ν (-1) (fun y => Ψ₁ (fromCols p.1 (Matrix.of fun r _ => y r))) u ∂(Measure.pi fun _ => ν)

end Ops

section Chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def SupportAt : Prop :=
  ∀ j c (H : j + 1 + c = s) (p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k,
    h ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)) → ∀ x₀ e,
      (S.T t).Phi j (c + 1) (by omega) ((h⁻¹).val * affPt p x₀ e) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) p, ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J, h = r * u

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

def ClassAt : Prop :=
  ∀ j c (H : j + 1 + c = s) (p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j (c + 1) (by omega))) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) p, ∃ u ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)), h = r * u

def CosetAt : Prop :=
  ∀ j c (H : j + 1 + c = s) (p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j (c + 1) (by omega))) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) p, ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J, h = r * u

def SamePos : Prop :=
  ∀ j c (H : j + 1 + c = s) (p : ℕ), 1 ≤ p → p ≤ c → p ≤ S.ρ → ∃ C : ℝ, 0 < C ∧
    opE S.ψ ν (p + 1) ((S.T t).Phi j (c + 1) (by omega)) = (C : ℂ) • opE S.ψ ν p ((S.T t).Phi j (c + 1) (by omega))

open Classical in

def PureCol : Prop :=
  ∀ j c (H : j + 1 + c = s) (r : ℕ), c + 1 = 2 * r → ∃ C : ℝ, 0 < C ∧ ∀ x,
    flCol S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x =
      (C : ℂ) * (S.T t).entry S.ψ ν j c H 1 1 x.toCols₁ *
        (if (fun a => x a (Sum.inr ())) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹ then 1 else 0)

open Classical in

def PureRow : Prop :=
  ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∃ C : ℝ, 0 < C ∧ ∀ x,
    flRow S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x =
      (C : ℂ) * (S.T t).entry S.ψ ν j c H 1 1 x.toRows₁ *
        (if x (Sum.inr ()) ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) then 1 else 0)

def SuppCol : Prop :=
  ∀ j c (H : j + 1 + c = s) (r : ℕ), c + 1 = 2 * r → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k,
    flCol S.ψ ν (r + 1) (om (S.μ (j + 1)) 1 h ((S.T t).Phi j (c + 1) (by omega))) ≠ 0 →
      ∃ β, ∃ q ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) (r + 1), ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J,
        h = colE (c + 1) (r + 1) β * q * u

def DoubleStep : Prop :=
  ∀ j c (H : j + 1 + 1 + c = s) (r : ℕ), c = 2 * r →
    (∀ h : GL (XIx (Fin κ) t (j + 1 + 1) ⊕ Fin (c + 1)) k,
      contr S.ψ ν (flCol S.ψ ν (r + 1 + 1) ((S.T t).Phi j (c + 1 + 1) (by omega)))
        (flRow S.ψ ν (r + 1) (om (S.μ (j + 1 + 1)) 1 h ((S.T t).Phi (j + 1) (c + 1) (by omega)))) ≠ 0 →
      ∃ q ∈ R k (XIx (Fin κ) t (j + 1 + 1)) (c + 1) (r + 1),
        ∃ u ∈ ((S.T t).lev (j + 1 + 1) (c + 1) (by omega)).J, h = q * u) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ p,
      contr S.ψ ν (flCol S.ψ ν (r + 1 + 1) ((S.T t).Phi j (c + 1 + 1) (by omega)))
        (flRow S.ψ ν (r + 1) ((S.T t).Phi (j + 1) (c + 1) (by omega))) p =
      (C : ℂ) * (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 p.1 * (S.T t).entry S.ψ ν (j + 1) c H 1 1 p.2

end Chain

def SymCollapse : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
      SuppCol S t ν ∧ PureCol S t ν ∧ PureRow S t ν ∧ DoubleStep S t ν

def ContrFactor : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k),
    Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure →
  ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (M : Type) [AddCommGroup M] [Module ℂ M]
    (B : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] SB (Matrix (n'' ⊕ Unit) n k) →ₗ[ℂ] M),
    (∀ (u₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂', (∀ x, Ψ₁'.1 x = (ψ (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) * Ψ₁.1 x) →
      (∀ x, Ψ₂'.1 x = Ψ₂.1 (x + fromRows 0 (Matrix.of fun _ => u₀))) → B Ψ₁' Ψ₂' = B Ψ₁ Ψ₂) →
    (∀ (y₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂', (∀ x, Ψ₁'.1 x = Ψ₁.1 (x + fromCols 0 (Matrix.of fun r _ => y₀ r))) →
      (∀ x, Ψ₂'.1 x = (ψ (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) * Ψ₂.1 x) → B Ψ₁' Ψ₂' = B Ψ₁ Ψ₂) →
    ∃ Λ : SB (Matrix n n' k × Matrix n'' n k) →ₗ[ℂ] M, ∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix n n' k × Matrix n'' n k),
      Ξ.1 = contr ψ ν Ψ₁.1 Ψ₂.1 ∧ B Ψ₁ Ψ₂ = Λ Ξ

end GlobalTheory.LocFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCompactParahoric
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParHecke.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem isReps_central {g : GL (A ⊕ D) k} (hg : ∀ j, j * g = g * j) : IsReps g {1} (fun _ => 1) := by
  refine ⟨fun j hj => ?_, fun j hj => ⟨1, ⟨by simp, ?_⟩, fun y hy => by simpa using hy.1⟩⟩
  · rw [Finset.mem_singleton] at hj
    subst hj
    refine ⟨one_mem _, ?_⟩
    have : (1 : GL (A ⊕ D) k).1.toBlocks₂₂ = 1 := by
      ext i j; simp [toBlocks₂₂, Matrix.one_apply]
    rw [this]; simp
  · rw [hg j]; simpa using hj

theorem isTOp_central {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V)
    (ξ : kˣ →* ℂˣ) {g : GL (A ⊕ D) k} (hg : ∀ j, j * g = g * j) {x : V} (hx : x ∈ typeSpace π ξ) (y : V) :
    IsTOp π ξ g x y ↔ y = π g x := by
  constructor
  · intro h
    simpa using h _ _ (isReps_central hg)
  · rintro rfl R d ⟨h1, h2⟩
    obtain ⟨j₀, ⟨hj₀, -⟩, hu⟩ := h2 1 (one_mem _)
    have hR : R = {j₀} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hj₀, fun j hj => hu j ⟨hj, ?_⟩⟩
      rw [hg j]
      have := inv_mem (h1 j hj).1
      simpa using this
    subst hR
    rw [Finset.sum_singleton, hg j₀, map_mul, Module.End.mul_apply, hx j₀ (h1 j₀ hj₀).1 _ (h1 j₀ hj₀).2,
      map_smul, smul_smul]
    simp

theorem comm_one (j g : GL (Empty ⊕ Unit) k) : j * g = g * j := by
  ext (a | a) (b | b)
  · exact a.elim
  · exact a.elim
  · exact b.elim
  · simp [Matrix.mul_apply, mul_comm]

theorem det_one_block (g : GL (Empty ⊕ Unit) k) : g.1.det = g.1 (.inr ()) (.inr ()) := by
  rw [← det_submatrix_equiv_self (Equiv.emptySum Empty Unit).symm]
  simp [Matrix.det_unique]

theorem one_mem_type (χ : kˣ →* ℂˣ) : (1 : ℂ) ∈ typeSpace (detRep (Empty ⊕ Unit) χ) χ := fun g _ d hd => by
  have : GeneralLinearGroup.det g = d := by
    ext
    rw [hd, GeneralLinearGroup.val_det_apply, det_one_block]
    simp [Matrix.det_unique, toBlocks₂₂]
  simp [detRep, this]

theorem isGen_rank_one (χ : kˣ →* ℂˣ) (ϖ : kˣ) (b : ℂˣ) :
    IsGen (detRep (Empty ⊕ Unit) χ) χ ϖ {b} (1 : ℂ) ↔ b = χ ϖ := by
  have hd : ∀ s : Finset Unit, GeneralLinearGroup.det (mtor (A := Empty) ϖ (indic s)) = ϖ ^ s.card := by
    intro s
    ext
    rw [GeneralLinearGroup.val_det_apply, det_one_block, mtor, val_torusElt]
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp [indic]
    · have : s = {()} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun _ _ => rfl⟩
      subst this
      simp [indic]
  constructor
  · rintro ⟨-, -, h⟩
    have := (isTOp_central _ χ (fun j => comm_one j _) (one_mem_type χ) _).1 (h {()})
    ext
    simpa [detRep, hd, genVal, Multiset.esymm, Multiset.powersetCard_one] using this
  · rintro rfl
    refine ⟨one_mem_type χ, by simp, fun s => ?_⟩
    rw [isTOp_central _ χ (fun j => comm_one j _) (one_mem_type χ)]
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp [detRep, hd, genVal, Multiset.esymm]
    · have : s = {()} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, fun _ _ => rfl⟩
      subst this
      simp [detRep, hd, genVal, Multiset.esymm, Multiset.powersetCard_one]

theorem isCoType_rank_one (χ : kˣ →* ℂˣ) : IsCoType (detRep (Empty ⊕ Unit) χ) χ LinearMap.id := by
  intro j hj d hd v
  have := one_mem_type χ j hj d hd
  have h2 : detRep (Empty ⊕ Unit) χ j v = v • detRep (Empty ⊕ Unit) χ j 1 := by
    rw [← map_smul]; simp
  rw [LinearMap.id_apply, h2, this]
  simp [mul_comm]

theorem omTwo_self {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (u : Matrix b a k → ℂ) : omTwo μ μ g h u = om μ⁻¹ g h u := by
  simp [omTwo]

theorem omTwo_apply {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μS μT : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (u : Matrix b a k → ℂ) (x : Matrix b a k) :
    omTwo μS μT g h u x = (((μT (GeneralLinearGroup.det g))⁻¹ * μS (GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      om 1 g h u x := by
  simp [omTwo, om]
  field_simp

theorem liftS_diag (ξ : kˣ →* ℂˣ) (ψ : Matrix D D' k → ℂ) (y : Matrix D D' k) (hy : ∀ i j, y i j ∈ 𝒪[k]) :
    liftS ξ ψ (fromBlocks (1 : Matrix A A k) 0 0 y) = ψ y := by
  have h : InSupp (fromBlocks 1 0 0 y : Matrix (A ⊕ D) (A ⊕ D') k) := by
    refine ⟨?_, by simp, fun i j => by simp⟩
    rintro (i | i) (j | j)
    · exact one_int i j
    · exact zero_mem _
    · exact zero_mem _
    · exact hy i j
  have : Units.mk0 _ h.det_ne = 1 := by ext; simp
  simp [liftS, schur, datum, dif_pos h, this]

theorem segL_one (ϖ : kˣ) (z : ℂˣ) : segL ϖ z 1 = {z} := by
  have : absPow k 0 ϖ = 1 := by ext; simp [val_absPow]
  simp [segL, this]

theorem exists_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G)
    (ho : IsOpen (J : Set G)) (hc : IsCompact (J : Set G)) (g : G) :
    ∃ R : Finset G, (∀ j ∈ R, j ∈ J) ∧ ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J := by
  classical
  haveI : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology ho
  let f : G → G ⧸ J := fun j => QuotientGroup.mk (j * g)
  have hf : Continuous f := QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  have hfin : (f '' J).Finite := (hc.image hf).finite_of_discrete
  have hex : ∀ c ∈ f '' J, ∃ j ∈ J, f j = c := fun c hc => hc
  choose! s hs hs' using hex
  refine ⟨hfin.toFinset.image s, ?_, fun j hj => ⟨s (f j), ⟨?_, ?_⟩, ?_⟩⟩
  · intro j hj
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hj
    exact hs c (hfin.mem_toFinset.1 hc)
  · exact Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨j, hj, rfl⟩)
  · exact QuotientGroup.eq.1 (hs' (f j) ⟨j, hj, rfl⟩)
  · rintro y ⟨hy, hy'⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hy
    have : f (s c) = f j := QuotientGroup.eq.2 hy'
    rw [← this, hs' c (hfin.mem_toFinset.1 hc)]

theorem isOpen_parahoric : IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  have : (parahoric k A D : Set (GL (A ⊕ D) k)) = (KO k (A ⊕ D) : Set _) ∩
      ⋂ i, ⋂ j, (fun g : GL (A ⊕ D) k => g.1 (.inr i) (.inl j)) ⁻¹' {x : k | valuation k x < 1} := by
    ext g; simp [mem_parahoric]
  rw [this]
  refine SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  refine IsOpen.preimage (Units.continuous_val.matrix_elem _ _) ?_
  simpa [Valuation.restrict_lt_one_iff] using (valuation k).isOpen_ball 1

theorem isCompact_parahoric : IsCompact (parahoric k A D : Set (GL (A ⊕ D) k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_parahoric)
    fun _ h => (mem_parahoric.1 h).1

theorem det_lower_ne {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 := by
  obtain ⟨h, hh, rfl⟩ := hj
  intro h0
  have e1 : (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k) h).1.toBlocks₂₂ =
      (algebraMap 𝒪[k] k).mapMatrix h.1.toBlocks₂₂ := rfl
  rw [e1, ← RingHom.map_det] at h0
  have h1 : h.1.toBlocks₂₂.det = 0 := Subtype.ext h0
  set u := GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]) h with hu
  have h21 : u.1.toBlocks₂₁ = 0 := by
    ext i j
    exact hh (i := .inr i) (j := .inl j) (show false < true by decide)
  have h22 : u.1.toBlocks₂₂.det = 0 := by
    have : u.1.toBlocks₂₂ = (IsLocalRing.residue 𝒪[k]).mapMatrix h.1.toBlocks₂₂ := rfl
    rw [this, ← RingHom.map_det, h1, map_zero]
  have := u.det_ne_zero
  rw [← fromBlocks_toBlocks u.1, h21, det_fromBlocks_zero₂₁, h22, mul_zero] at this
  exact this rfl

theorem exists_isReps (g : GL (A ⊕ D) k) : ∃ R d, IsReps g R d := by
  classical
  obtain ⟨R, h1, h2⟩ := exists_reps _ isOpen_parahoric isCompact_parahoric g
  refine ⟨R, fun j => if h : j.1.toBlocks₂₂.det ≠ 0 then Units.mk0 _ h else 1, fun j hj => ⟨h1 j hj, ?_⟩, h2⟩
  simp [det_lower_ne (h1 j hj)]

theorem isTOp_unique {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V)
    (ξ : kˣ →* ℂˣ) (g : GL (A ⊕ D) k) {x y y' : V} (h : IsTOp π ξ g x y) (h' : IsTOp π ξ g x y') : y = y' := by
  obtain ⟨R, d, hR⟩ := exists_isReps g
  rw [h R d hR, h' R d hR]

theorem exists_isRepsK (g : GL D k) : ∃ R, IsRepsK g R := by
  classical
  obtain ⟨R, h1, h2⟩ := exists_reps (KO k D) SplitFlip.isOpen_KO SplitFlip.isCompact_KO g
  refine ⟨R.image (· * g), ?_, fun κ hκ => ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨j, h1 j hj, 1, one_mem _, by simp⟩
  · obtain ⟨j, ⟨hj, hj'⟩, hu⟩ := h2 κ hκ
    refine ⟨j * g, ⟨Finset.mem_image_of_mem _ hj, hj'⟩, ?_⟩
    rintro y ⟨hy, hy'⟩
    obtain ⟨j2, hj2, rfl⟩ := Finset.mem_image.1 hy
    rw [hu j2 ⟨hj2, hy'⟩]

theorem exists_isHgt {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ H : GL n k → ℝ, IsHgt ϖ H := by
  refine ⟨fun g => (sphSection k n (1 - (Fintype.card n : ℂ) / 2) (io k n (g, 1))).re, fun κ hκ g => ⟨?_, ?_⟩, fun e => ?_⟩
  · have := sphSection_io_biinv (1 - (Fintype.card n : ℂ) / 2) g hκ (one_mem _)
    rw [mul_one] at this
    simp only [this]
  · have := sphSection_io_biinv (1 - (Fintype.card n : ℂ) / 2) g (one_mem _) hκ
    rw [one_mul] at this
    simp only [this]
  · simp only [sphSection_torusElt hϖ]
    have : -((Fintype.card n : ℂ) / 2 + (1 - (Fintype.card n : ℂ) / 2)) * ((∑ i, |e i| : ℤ) : ℂ) =
        ((-(sumAbs e) : ℤ) : ℂ) := by
      simp [sumAbs]
    rw [this, Complex.cpow_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_zpow, Complex.ofReal_re]

end GlobalTheory.ParHecke.Model

end
end

