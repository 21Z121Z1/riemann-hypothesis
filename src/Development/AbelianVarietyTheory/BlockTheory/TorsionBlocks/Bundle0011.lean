import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.OneSquareLeaf.LeafOneSquareFree
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.HarderNarasimhan.Bundle0002
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.RootsOfUnityDivisibility
section
noncomputable section

open NumberField IsDedekindDomain Finset
open Formalism.PairingDivisionLocalBalance (wt Pl)
open Formalism.DivisionValues (vw conjPl)
open Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts (SquareCoefficientsCondition)

namespace GlobalTheory.IndefiniteRowSideFullHecke.RootsOfUnityDivisibility

section Field

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def ValGe_vw (w : Pl K) (x : K) (t : ℝ) : Prop := x = 0 ∨ -t ≤ (vw w x : ℝ)

def IsRootOfOne (x : K) : Prop := ∃ n : ℕ, 0 < n ∧ x ^ n = 1

def DividesPow (q c : ℕ) (g : K) : Prop :=
  IsIntegral ℤ g ∧ ∃ g' : K, IsIntegral ℤ g' ∧ g * g' = (q : K) ^ c

def UnitAway (q : ℕ) (x : K) : Prop := x ≠ 0 ∧ ∀ w : Pl K, vw w (q : K) = 0 → vw w x = 0

def NewPlaceFactor (q : ℕ) (x : K) : Prop :=
  ∃ (g a : K) (c : ℕ) (n : ℤ), DividesPow q c g ∧ UnitAway q a ∧
    (x = g * (q : K) ^ n * a ∨ x = g⁻¹ * (q : K) ^ n * a)

def EpsShape {Sq : Type} (Q : Finset Sq) (qq : Sq → ℕ) (E : K) : Prop :=
  ∃ (ζ : K) (x : Sq → Fin 2 → K), IsRootOfOne ζ ∧ (∀ v ∈ Q, ∀ i, NewPlaceFactor (qq v) (x v i)) ∧
    E = ζ * ∏ v ∈ Q, ∏ i, x v i

def UShape {Sq : Type} (S0 Q : Finset Sq) (cc qq : Sq → ℕ) (U : K) : Prop :=
  ∃ (ζ : K) (g g' x : Sq → K), IsRootOfOne ζ ∧
    (∀ v ∈ S0, DividesPow (qq v) (cc v) (g v) ∧ DividesPow (qq v) (cc v) (g' v)) ∧
    (∀ v ∈ Q, NewPlaceFactor (qq v) (x v)) ∧
    U = ζ * (∏ v ∈ S0, g v / g' v) * ∏ v ∈ Q, x v

end Field

def classNorm {H : Type} {D : ℕ} (G : Matrix (Fin D) (Fin D) ℚ) (R : Finset H) (Γ : H → ℕ)
    (I : H → Fin D → ℂ) : ℂ :=
  ∑ x ∈ R, (∑ k, ∑ l, I x k * (starRingEnd ℂ) (I x l) * (G k l : ℂ)) / (Γ x : ℂ)

def SquareInputs {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {Mu Sq H : Type}
    (μ0 : Mu) (μD : Bool → Mu) (μ : Pl K → Mu) (W1 : Set (Pl K)) (ch : Pl K → Bool)
    (S0 : Finset Sq) (QQ : Pl K → Finset Sq) (cc qq : Sq → ℕ) (Se Sd : Finset ℕ) (dl : Pl K → ℝ)
    (a' e p q : ℕ) (c c0 : Mu → ℂ) (u : Mu → ℕ → ℂ) (L eps : Mu → ℤ → ℂ) (Gam : ℤ → ℂ)
    (D : ℕ) (G : Matrix (Fin D) (Fin D) ℚ) (I I' : Mu → H → Fin D → ℂ) (R : Mu → Pl K → Finset H)
    (Γ : Mu → H → ℕ) (Om Om' A A' : ℂ)
    (zA zA' : K) (zT : ℤ → K) (zTd : Bool → ℤ → K) (zTw : Pl K → ℤ → K) (gT : ℤ → Pl K → ℤ)
    (N0 : ℤ → ℕ → ℝ) : Prop :=

  (2 * (p + q) + 1 < e ∧ 2 * (p + q) + 1 < a') ∧

  (Om ≠ 0 ∧ Om' ≠ 0 ∧ A ≠ 0 ∧ A' ≠ 0 ∧ G.PosDef ∧
    ∀ s ∈ Icc (1 - ((e : ℤ) + q - p)) 0, Gam s ≠ 0 ∧ Gam (1 - s) ≠ 0) ∧

  (∀ w : Pl K, ∀ ν : Mu, (ν = μ0 ∨ ν = μ w) →

    (∀ s ∈ Icc (1 : ℤ) ((a' : ℤ) + e), L ν s ≠ 0) ∧ (∀ k ∈ Icc 1 (p + q), u ν k ≠ 0) ∧

    c ν * ∏ k ∈ Icc (1 : ℤ) q, L ν (e + k) =
      (∏ k ∈ Icc 1 (p + q), u ν k) * c0 ν * ∏ k ∈ Icc (1 : ℤ) p, L ν ((e : ℤ) + q - k + 1) ∧

    ((∀ h k, I ν h k = c0 ν * I' ν h k) ∧ I ν ≠ 0 ∧ I' ν ≠ 0) ∧

    (∀ x ∈ R ν w, 0 < Γ ν x ∧
      (∀ k, ∃ z z' : K, I ν x k = Om * σ z ∧ I' ν x k = Om' * σ z' ∧
        ValGe_vw w z (dl w) ∧ ValGe_vw (conjPl w) z (dl w) ∧
        ValGe_vw w z' (dl w) ∧ ValGe_vw (conjPl w) z' (dl w)) ∧
      ∀ k l, ValGe_vw w (((G k l / (Γ ν x : ℚ) : ℚ)) : K) (dl w)) ∧

    classNorm G (R ν w) (Γ ν) (I ν) =
      A * ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((a' : ℤ) + e - (p + q)), L ν s ∧
    classNorm G (R ν w) (Γ ν) (I' ν) =
      A' * ∏ s ∈ Icc (1 + ((e : ℤ) + q - p)) ((a' : ℤ) + e - (p + q)), L ν s ∧

    (∀ s ∈ Icc (1 - ((e : ℤ) + q - p)) 0,
      eps ν s ≠ 0 ∧ Gam s * L ν s = eps ν s * Gam (1 - s) * L ν (1 - s))) ∧

  (∀ w : Pl K,
    σ zA * ((‖Om‖ ^ 2 : ℝ) : ℂ) = classNorm G (R μ0 w) (Γ μ0) (I μ0) ∧
    σ zA' * ((‖Om'‖ ^ 2 : ℝ) : ℂ) = classNorm G (R μ0 w) (Γ μ0) (I' μ0)) ∧

  (∀ s ∈ Icc (1 : ℤ) ((a' : ℤ) + e),
    zT s ≠ 0 ∧ (∀ l ∈ Sd, 0 ≤ N0 s l) ∧
    (∀ b, zTd b s ≠ 0 ∧ σ (zTd b s) * L μ0 s = σ (zT s) * L (μD b) s) ∧
    ∀ w : Pl K, -wt Sd (N0 s) w ≤ ((vw w (zT s) + gT s w : ℤ) : ℝ) ∧
      ∀ b, -wt Sd (N0 s) w ≤ ((vw w (zTd b s) + gT s w : ℤ) : ℝ)) ∧

  (∀ w ∈ W1,
    (∀ s ∈ Icc (1 : ℤ) ((a' : ℤ) + e),
      σ (zTw w s) * L μ0 s = σ (zT s) * L (μ w) s ∧
      -wt Sd (N0 s) w ≤ ((vw w (zTw w s) + gT s w : ℤ) : ℝ) ∧
      ((vw w (zTw w s) + gT s w : ℤ) : ℝ) ≤
        ((vw w (zTd (ch w) s) + gT s w : ℤ) : ℝ) + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) ∧
    (∀ s ∈ Icc (1 - ((e : ℤ) + q - p)) 0,
      ∃ E : K, EpsShape (QQ w) qq E ∧ eps (μ w) s = σ E * eps μ0 s) ∧
    (∀ k ∈ Icc 1 (p + q), ∃ U : K, UShape S0 (QQ w) cc qq U ∧ u (μ w) k = σ U * u μ0 k))

def CommonInputs {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {Mu Sq : Type}
    (μ0 : Mu) (μ : Pl K → Mu) (W1 : Set (Pl K)) (S0 : Finset Sq) (QQ : Pl K → Finset Sq)
    (cc qq ee : Sq → ℕ) (Se Sd : Finset ℕ) (dl : Pl K → ℝ) : Prop :=
  (∀ x : K, σ (star x) = (starRingEnd ℂ) (σ x)) ∧
  (∀ w, w ∉ W1 → μ w = μ0) ∧
  (∀ v ∈ S0, IsPrimePow (qq v) ∧ cc v ≤ ee v) ∧
  (∀ w ∈ W1, Disjoint (QQ w) S0 ∧ ∀ v ∈ QQ w, IsPrimePow (qq v) ∧ vw w (qq v : K) = 0) ∧
  (∀ l ∈ Se, l.Prime) ∧ (∀ l ∈ Sd, l.Prime) ∧
  (∀ w, 0 ≤ dl w ∧ dl (conjPl w) = dl w)

def ValuationOfRatio : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (m N : ℕ) (Mu Sq : Type)
    (H : Fin m × Fin m → Type)
    (μ0 : Mu) (μD : Bool → Mu) (μ : Pl K → Mu) (W1 : Set (Pl K)) (ch : Pl K → Bool)
    (S0 : Finset Sq) (QQ : Pl K → Finset Sq) (cc qq ee : Sq → ℕ) (Se Sd : Finset ℕ) (dl : Pl K → ℝ)
    (a' e p q : Fin m × Fin m → ℕ) (c c0 : Fin m × Fin m → Mu → ℂ) (u : Fin m × Fin m → Mu → ℕ → ℂ)
    (L eps : Fin m × Fin m → Mu → ℤ → ℂ) (Gam : Fin m × Fin m → ℤ → ℂ)
    (D : Fin m × Fin m → ℕ) (G : ∀ ij, Matrix (Fin (D ij)) (Fin (D ij)) ℚ)
    (I I' : ∀ ij, Mu → H ij → Fin (D ij) → ℂ) (R : ∀ ij, Mu → Pl K → Finset (H ij))
    (Γ : ∀ ij, Mu → H ij → ℕ) (Om Om' A A' : Fin m × Fin m → ℂ)
    (zA zA' : Fin m × Fin m → K) (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
    (zTw : Fin m × Fin m → Pl K → ℤ → K) (gT : Fin m × Fin m → ℤ → Pl K → ℤ)
    (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
    (r0 : Fin m × Fin m → K) (rw : Pl K → Fin m × Fin m → K),
    CommonInputs σ μ0 μ W1 S0 QQ cc qq ee Se Sd dl →
    (∀ ij, SquareInputs σ μ0 μD μ W1 ch S0 QQ cc qq Se Sd dl (a' ij) (e ij) (p ij) (q ij)
      (c ij) (c0 ij) (u ij) (L ij) (eps ij) (Gam ij) (D ij) (G ij) (I ij) (I' ij) (R ij) (Γ ij)
      (Om ij) (Om' ij) (A ij) (A' ij) (zA ij) (zA' ij) (zT ij) (zTd ij) (zTw ij) (gT ij) (N0 ij)) →

    (∀ ij, (a' ij + 2 * e ij) + a' ij ≤ 2 * N) → (∀ ij, p ij + q ij + 1 ≤ m) →

    (∀ ij, σ (r0 ij) * c ij μ0 = c ij μ0) →
    (∀ w ij, σ (rw w ij) * c ij μ0 = c ij (μ w)) →
    SquareCoefficientsCondition r0 rw Se Sd (fun ij => (a' ij + 2 * e ij) + a' ij) (fun ij => a' ij + e ij)
      (fun ij => p ij + q ij) N S0 cc qq ee zA zA' zT zTd gT ch N0 dl

def RatioInField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (Mu Sq H : Type)
    (μ0 : Mu) (μD : Bool → Mu) (μ : Pl K → Mu) (W1 : Set (Pl K)) (ch : Pl K → Bool)
    (S0 : Finset Sq) (QQ : Pl K → Finset Sq) (cc qq ee : Sq → ℕ) (Se Sd : Finset ℕ) (dl : Pl K → ℝ)
    (a' e p q : ℕ) (c c0 : Mu → ℂ) (u : Mu → ℕ → ℂ) (L eps : Mu → ℤ → ℂ) (Gam : ℤ → ℂ)
    (D : ℕ) (G : Matrix (Fin D) (Fin D) ℚ) (I I' : Mu → H → Fin D → ℂ) (R : Mu → Pl K → Finset H)
    (Γ : Mu → H → ℕ) (Om Om' A A' : ℂ)
    (zA zA' : K) (zT : ℤ → K) (zTd : Bool → ℤ → K) (zTw : Pl K → ℤ → K) (gT : ℤ → Pl K → ℤ)
    (N0 : ℤ → ℕ → ℝ),
    CommonInputs σ μ0 μ W1 S0 QQ cc qq ee Se Sd dl →
    SquareInputs σ μ0 μD μ W1 ch S0 QQ cc qq Se Sd dl a' e p q c c0 u L eps Gam D G I I' R Γ
      Om Om' A A' zA zA' zT zTd zTw gT N0 →
    c μ0 ≠ 0 ∧ ∀ w, ∃ r : K, r ≠ 0 ∧ σ r * c μ0 = c (μ w)

section Basic₂

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_one' (w : Pl K) : vw w (1 : K) = 0 := by
  simp [vw, FractionalIdeal.count_one]

example (σ : K →+* ℂ) :
    SquareInputs σ (Mu := Unit) (Sq := Unit) (H := Unit) () (fun _ => ()) (fun _ => ()) Set.univ
      (fun _ => true) ∅ (fun _ => ∅) (fun _ => 0) (fun _ => 2) ∅ ∅ (fun _ => 0) 6 6 1 1
      (fun _ => 3) (fun _ => 3) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1)
      1 1 (fun _ _ _ => 3) (fun _ _ _ => 1) (fun _ _ => {()}) (fun _ _ => 1) 3 1 9 1
      1 1 (fun _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨by norm_num, ⟨by norm_num, by norm_num, by norm_num, by norm_num, Matrix.PosDef.one, by simp⟩,
    ?_, ?_, ?_, ?_⟩
  · intro w ν _
    refine ⟨by simp, by simp, by simp, ⟨by simp, ?_, ?_⟩, ?_, ?_, ?_, by simp⟩
    · intro h; have := congrFun (congrFun h ()) 0; simp at this
    · intro h; have := congrFun (congrFun h ()) 0; simp at this
    · intro x _
      refine ⟨one_pos, fun k => ⟨1, 1, by simp, by simp, ?_, ?_, ?_, ?_⟩, fun k l => ?_⟩
      all_goals first
        | (right; simp [vw_one']; done)
        | (right; rw [Subsingleton.elim k l]; simp [vw_one'])
    · simp [classNorm, map_ofNat]; norm_num
    · simp [classNorm]
  · intro w
    constructor
    · simp [classNorm, map_ofNat]; norm_num
    · simp [classNorm]
  · intro s _
    simp [wt, vw_one']
  · intro w _
    refine ⟨fun s _ => by simp [wt, vw_one'], fun s _ => ⟨1, ⟨1, fun _ _ => 1, ⟨1, one_pos, by simp⟩, by simp, by simp⟩, by simp⟩,
      fun k _ => ⟨1, ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, ⟨1, one_pos, by simp⟩, by simp, by simp, by simp⟩, by simp⟩⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.RootsOfUnityDivisibility
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SpreadComposition
section
open NumberField
open scoped Matrix ComplexOrder
open Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TotallyDefiniteSelfDualLattices

section Space

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {ν : ℕ}

def form (J : Matrix (Fin ν) (Fin ν) E) (x y : Fin ν → E) : E :=
  (fun a => IsCMField.complexConj E (y a)) ⬝ᵥ (J *ᵥ x)

def TotallyPosDef (J : Matrix (Fin ν) (Fin ν) E) : Prop :=
  (∀ a b, IsCMField.complexConj E (J a b) = J b a) ∧ ∀ φ : E →+* ℂ, (J.map φ).PosDef

def IsSelfDualLattice (J : Matrix (Fin ν) (Fin ν) E) (L : Submodule (𝓞 E) (Fin ν → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin ν → E)) = ⊤ ∧
    ∀ x : Fin ν → E, x ∈ L ↔ ∀ y ∈ L, form J x y ∈ (1 : Submodule (𝓞 E) E)

end Space

def SpreadLe {ν : ℕ} (lam : DomWeight ν) (R : ℝ) : Prop :=
  ∀ i j : Fin ν, ((lam.w i - lam.w j : ℤ) : ℝ) ≤ R

section Sum

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι C : Type} [Fintype ι] {ν N : ℕ}

def comp (lam : ι → DomWeight ν) (e : Fin N ≃ C × VVIdx lam) (c : C) : (Fin N → K) →ₗ[K] VV K lam :=
  (bVV K lam).equivFun.symm.toLinearMap ∘ₗ LinearMap.funLeft K K fun i => e.symm (c, i)

def sumLat (emb : ι → E →+* K) (lam : ι → DomWeight ν) (L : C → Submodule (𝓞 E) (Fin ν → E))
    (e : Fin N ≃ C × VVIdx lam) : Submodule (𝓞 K) (Fin N → K) :=
  ⨅ c : C, (delAt emb lam (L c)).comap ((comp lam e c).restrictScalars (𝓞 K))

open Classical in

def sumGram [StarRing K] (emb : ι → E →+* K) (lam : ι → DomWeight ν) (J : Matrix (Fin ν) (Fin ν) E)
    (e : Fin N ≃ C × VVIdx lam) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun p q =>
    if (e p).1 = (e q).1 then pairV emb lam J (bVV K lam (e p).2) (bVV K lam (e q).2) else 0

end Sum

def IsDualFrame {N : ℕ} (G X' : Matrix (Fin N) (Fin N) ℂ) : Prop := X' * X'ᴴ = Gᵀ

example {E : Type} [Field E] [NumberField E] [IsCMField E] {ν : ℕ} :
    TotallyPosDef (1 : Matrix (Fin ν) (Fin ν) E) := by
  refine ⟨fun a b => ?_, fun φ => ?_⟩
  · by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [Matrix.map_one _ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one

example {E : Type} [Field E] [NumberField E] [IsCMField E] {ν : ℕ} :
    IsSelfDualLattice (1 : Matrix (Fin ν) (Fin ν) E)
      (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  classical
  have hs : ∀ a : Fin ν, (Pi.single a 1 : Fin ν → E) ∈
      Submodule.pi Set.univ fun _ : Fin ν => (1 : Submodule (𝓞 E) E) := by
    intro a b _
    by_cases h : b = a
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun x => ⟨fun hx y hy => ?_, fun hx a _ => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin ν)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    simpa using hs a
  · unfold form
    rw [Matrix.one_mulVec]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨u, hu⟩ := Submodule.mem_one.mp (hx a trivial)
    obtain ⟨w, hw⟩ := Submodule.mem_one.mp (hy a trivial)
    refine Submodule.mem_one.mpr ⟨IsCMField.ringOfIntegersComplexConj E w * u, ?_⟩
    rw [map_mul, hu]
    congr 1
    show ((IsCMField.ringOfIntegersComplexConj E w : 𝓞 E) : E) = IsCMField.complexConj E (y a)
    rw [IsCMField.coe_ringOfIntegersComplexConj, ← hw]
  · have := hx _ (hs a)
    unfold form at this
    rw [Matrix.one_mulVec] at this
    have h2 : (fun b => IsCMField.complexConj E ((Pi.single a 1 : Fin ν → E) b)) = Pi.single a 1 := by
      funext b
      by_cases h : b = a
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [h2] at this
    simpa using this

def Statement : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [IsCMField E]
    [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K],
    (∃ v₀ : InfinitePlace K, ∀ a : K, v₀.embedding (star a) = (starRingEnd ℂ) (v₀.embedding a)) →
  ∀ (ι : Type) [Fintype ι] (emb : ι → E →+* K) (ν : ℕ), 1 ≤ ν →
  ∀ (J : Matrix (Fin ν) (Fin ν) E), TotallyPosDef J →
  ∀ (lam : ι → DomWeight ν) (R : ℝ), 1 ≤ R → (∀ τ, SpreadLe (lam τ) R) →
  ∀ (C : Type) [Fintype C] [Nonempty C] (L : C → Submodule (𝓞 E) (Fin ν → E)),
    (∀ c, IsSelfDualLattice J (L c)) →
  ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X' : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ),
    (∀ v, IsDualFrame ((sumGram emb lam J e).map v.embedding) (X' v)) →
    Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts.TestLatticeCondition N X' (dualFr (sumLat emb lam L e))
      (4 * (Fintype.card ι : ℝ) * (ν : ℝ) * R * Real.log ((ν : ℝ) * R))

end GlobalTheory.IndefiniteRowSideFullHecke.TotallyDefiniteSelfDualLattices
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WittIndexParallel
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParallelSig {D : D7} (V : HSp D) (p q : ℕ) : Prop :=
  ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (V.gram.map τ) p q

def nu (m j : ℕ) : ℕ := if j < m then ⌈((m : ℚ) - 1 - j) / 2⌉₊ else 0

def OddRankWitt (D : D7) : Prop :=
  ∀ (V : HSp D) (p q : ℕ), Odd V.rank → p + q = V.rank → q < p → ParallelSig V p q →
    Formalism.MainNotions.KudlaSiegelWeil.WittIdx V q

def RowSpaceWitt (D : D7) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → Formalism.MainNotions.KudlaSiegelWeil.WittIdx (D.sp.W j : HSp D) (D.R.m - j)

def ChainWitt (D : D7) : Prop :=
  ∀ t : ℕ, Odd t → D.R.r + 5 ≤ t → ∀ j : ℕ, j ≤ D.R.m →
    ∀ (Y : HSp D) (p : ℕ), Y.rank = D.R.r + j * t → p + nu D.R.m j = D.R.r + j * t →
      ParallelSig Y p (nu D.R.m j) →
        Formalism.MainNotions.KudlaSiegelWeil.WittIdx Y (nu D.R.m j) ∧
        ((nu D.R.m j : ℚ) ≤ (D.R.m : ℚ) / 2 ∧ (D.R.m : ℚ) / 2 < (t : ℚ) / 2) ∧
        (1 ≤ j → (nu D.R.m j : ℚ) ≤ (D.R.m : ℚ) / 2 - 1)

def WittIndexStatement : Prop :=
  ∀ D : D7, OddRankWitt D ∧ RowSpaceWitt D ∧ ChainWitt D

theorem nu_eq (m j : ℕ) : nu m j = (m - j) / 2 := by
  unfold nu
  split_ifs with h
  · obtain ⟨c, rfl⟩ : ∃ c, m = j + c + 1 := ⟨m - j - 1, by omega⟩
    have e : (((j + c + 1 : ℕ) : ℚ) - 1 - j) / 2 = (c : ℚ) / 2 := by push_cast; ring
    rw [e]
    apply le_antisymm
    · rw [Nat.ceil_le, div_le_iff₀ (by norm_num)]
      have : c ≤ (j + c + 1 - j) / 2 * 2 := by omega
      exact_mod_cast this
    · by_contra hlt
      have h1 : (c : ℚ) / 2 ≤ (⌈(c : ℚ) / 2⌉₊ : ℚ) := Nat.le_ceil _
      rw [div_le_iff₀ (by norm_num)] at h1
      have h2 : c ≤ ⌈(c : ℚ) / 2⌉₊ * 2 := by exact_mod_cast h1
      omega
  · omega

theorem parallelSig_of_sigOK {D : D7} {V : HSp D} {p q : ℕ} (h : V.SigOK) (hs : ∀ τ, V.sig τ = (p, q)) :
    ParallelSig V p q := fun τ => by
  have := h τ
  rwa [hs τ] at this

example (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Odd (D.sp.W j).rank ∧ (D.R.k + j - 1) + (D.R.m - j) = (D.sp.W j).rank ∧ D.R.m - j < D.R.k + j - 1 ∧
      ParallelSig (D.sp.W j : HSp D) (D.R.k + j - 1) (D.R.m - j) := by
  have hr := D.sp.W_rank j h1 h2
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  unfold Ranks.r at hr
  refine ⟨⟨a + b - 1, by omega⟩, by omega, by omega,
    parallelSig_of_sigOK (D.sp.W_sig j) (D.sp.W_sigval j h1 h2)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

end
end

