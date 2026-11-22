import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlagVolumeFiltration
section
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise NNReal ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair

section Objects
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ}

variable (k n) in

def flagSub (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {y | ∀ l : Fin c, i ≤ l.val → y (Sum.inr l) = 0}
  zero_mem' _ _ := rfl
  add_mem' h h' l hl := by simp [h l hl, h' l hl]
  smul_mem' s y h l hl := by simp [h l hl]

def latStep (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) := L ⊓ flagSub k n c i

def interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Submodule 𝒪[k] (n → k) := L.comap (inX k n c)

def qStep (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : Set (n ⊕ Fin c → k) :=
  {y | q.inv • y ∈ latStep L i}

def IsDepthOne (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Prop :=
  ∀ i : Fin c, (fun y : n ⊕ Fin c → k => y (Sum.inr i)) '' (latStep L (i.val + 1) : Set (n ⊕ Fin c → k)) =
    {t : k | (q.1 : k) * t ∈ 𝒪[k]}

def flagIn (c i : ℕ) (y : n ⊕ Fin i → k) : n ⊕ Fin c → k :=
  Sum.elim (fun r => y (Sum.inl r)) fun l => if h : l.val < i then y (Sum.inr ⟨l.val, h⟩) else 0

def refLat (c : ℕ) (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔ Submodule.span 𝒪[k] {y | ∃ i, 1 ≤ i ∧ i ≤ c ∧ y = avec k n c i}

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def stabN (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Subgroup (GL (n ⊕ Fin c) k) := N k n c 1 ⊓ latStab L

def InCoset (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (h₀ h : GL (n ⊕ Fin c) k) : Prop :=
  ∃ r ∈ R k n c 1, ∃ κ ∈ latStab L₀, h = r * h₀ * κ

def IsTheta {M' M : Type} [AddCommGroup M'] [Module ℂ M'] [AddCommGroup M] [Module ℂ M] (μ : kˣ →* ℂˣ)
    (π' : Representation ℂ (GL n' k) M') (π : Representation ℂ (GL n k) M)
    (θ : M' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] M) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (v : M') (Ψ Ψ' : SB (Matrix n n' k)), Ψ'.1 = om μ g h Ψ.1 →
    θ (π' g v) Ψ' = π h (θ v Ψ)

def DiesOnRam (P : Pair k n') (Ξ : Matrix n n' k → ℂ) : Prop :=
  ∃ hΞ : Ξ ∈ SB (Matrix n n' k),
    ∀ (M' M : Type) [AddCommGroup M'] [Module ℂ M'] [AddCommGroup M] [Module ℂ M] (μ : kˣ →* ℂˣ), IsUnram μ →
      ∀ (π' : Representation ℂ (GL n' k) M') (π : Representation ℂ (GL n k) M)
        (θ : M' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] M), IsTheta μ π' π θ →
        ∀ φ ∈ EqForm π', φ ∈ Mram k n' M' → θ (φ P) ⟨Ξ, hΞ⟩ = 0

variable [MeasurableSpace k] [BorelSpace k]

def volStep (ν : Measure k) (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : ℝ≥0∞ :=
  (Measure.pi fun _ : n ⊕ Fin i => ν) {y | flagIn c i y ∈ qStep q L i}

def volAll (ν : Measure k) (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : ℝ :=
  ∏ i ∈ Finset.Icc 1 c, (volStep ν q L i).toReal

def volStabN (ν : Measure k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : ℝ≥0∞ :=
  volN ν n c 1 {u | (u : GL (n ⊕ Fin c) k) ∈ latStab L}

def unf (ψ : AddChar k Circle) (ν : Measure k) (q : Unif k) (P : Pair k n')
    (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Matrix n n' k → ℂ :=
  opE ψ ν 1 (latInd (gluedS q (c + 1) P.ker P.vec) L)

end Objects

section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (q : Unif k)

def DatumTranslate : Prop :=
  ∀ (μ : kˣ →* ℂˣ) (P : Pair k n') (L'₀ : Submodule 𝒪[k] (n' ⊕ Fin (c + 1) → k)) [L'₀.IsLattice k]
    (L₀ L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    h' • L'₀ = gluedS q (c + 1) P.ker P.vec → h • L₀ = L → ∀ x,
      latInd (gluedS q (c + 1) P.ker P.vec) L x =
        (((μ (GeneralLinearGroup.det h'))⁻¹ : ℂˣ) : ℂ) * (μ (GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h') ^ (-((Fintype.card n : ℝ) + c) / 2) : ℝ) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h) ^ (((Fintype.card n' : ℝ) + c + 1) / 2) : ℝ) : ℂ) *
          om μ h' h (latInd L'₀ L₀) x

def StabGlued : Prop :=
  ∀ P : Pair k n,
    (∀ i j : Fin c, j.val = i.val + 1 →
      (fun u : GL (n ⊕ Fin c) k => u.val (Sum.inr i) (Sum.inr j)) ''
        (stabN (gluedS q c P.ker P.vec) : Set (GL (n ⊕ Fin c) k)) = (𝒪[k] : Set k)) ∧
    R k n c 1 ⊓ latStab (gluedS q c P.ker P.vec) =
      stabN (gluedS q c P.ker P.vec) ⊔ (MulAction.stabilizer (GL n k) P).map (embX c) ∧
    Disjoint (stabN (gluedS q c P.ker P.vec)) ((MulAction.stabilizer (GL n k) P).map (embX c)) ∧
    ∀ g ∈ MulAction.stabilizer (GL n k) P, ∀ u ∈ stabN (gluedS q c P.ker P.vec),
      embX c g * u * (embX c g)⁻¹ ∈ stabN (gluedS q c P.ker P.vec)

def NormalForm : Prop :=
  ∀ (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L.IsLattice k], IsDepthOne q L →
    ∃ η : n → k, (∃ u ∈ N k n c 1, L = u • gluedS q c (interX L) η) ∧
      ∀ η' : n → k, (∃ u ∈ N k n c 1, L = u • gluedS q c (interX L) η') → η' - η ∈ interX L

def OneOrbit : Prop :=
  (∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
    ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂) ∧
  ∀ (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k),
    h₀ • L₀ = gluedS q c Q.ker Q.vec → ∀ h : GL (n ⊕ Fin c) k,
      (∃ u ∈ N k n c 1, ∃ (L'' : Submodule 𝒪[k] (n → k)) (f'' : n → k), IsGlue L'' f'' ∧
        h • L₀ = u • gluedS q c L'' f'') ↔ InCoset L₀ h₀ h

def StabCoords : Prop :=
  ∀ Q : Pair k n, Set.BijOn
    (fun (u : GL (n ⊕ Fin c) k) (i : Fin c) => u.val *ᵥ avec k n c (i.val + 1) - avec k n c (i.val + 1))
    (stabN (gluedS q c Q.ker Q.vec) : Set (GL (n ⊕ Fin c) k))
    {y | ∀ i : Fin c, (i.val = 0 → y i = 0) ∧ (1 ≤ i.val → y i ∈ qStep q (gluedS q c Q.ker Q.vec) i.val)}

def DetValuations : Prop :=
  ∀ (P : Pair k n') (Q : Pair k n) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    h' • refLat (c + 1) P.lat = gluedS q (c + 1) P.ker P.vec → h • refLat c Q.lat = gluedS q c Q.ker Q.vec →
      valuation k (h'.val.det) = valuation k (q.inv ^ c) ∧ valuation k (h.val.det) = valuation k (q.inv ^ (c - 1)) ∧
      ∀ μ : kˣ →* ℂˣ, IsUnram μ →
        μ (GeneralLinearGroup.det h') * (μ (GeneralLinearGroup.det h))⁻¹ = (μ q.unit)⁻¹

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

def Vanishing : Prop :=
  ∀ (P : Pair k n') (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L.IsLattice k], ¬ IsDepthOne q L → unf ψ ν q P L = 0

open Classical in

def NormalValue : Prop :=
  ∀ (P : Pair k n') (L'' : Submodule 𝒪[k] (n → k)) [L''.IsLattice k] (η : n → k),
    (∀ i ∈ Finset.Icc 1 c, volStep ν q (gluedS q c L'' η) i ≠ 0 ∧ volStep ν q (gluedS q c L'' η) i ≠ ∞) ∧
    (∀ x : Matrix n n' k, unf ψ ν q P (gluedS q c L'' η) x = (volAll ν q (gluedS q c L'' η) : ℂ) *
      if (∀ y ∈ P.ker, x *ᵥ y ∈ L'') ∧ x *ᵥ P.vec - η ∈ L'' then 1 else 0) ∧
    (q.1 • η ∉ L'' → unf ψ ν q P (gluedS q c L'' η) = 0)

def SplitCase : Prop :=
  ∀ (P : Pair k n') (L'' : Submodule 𝒪[k] (n → k)) [L''.IsLattice k] (η : n → k), η ∈ L'' →
    (∀ x : Matrix n n' k, unf ψ ν q P (gluedS q c L'' η) x =
      (volAll ν q (gluedS q c L'' η) : ℂ) * latInd P.lat L'' x) ∧
    (∀ g ∈ latStab P.lat, ∀ x : Matrix n n' k,
      unf ψ ν q P (gluedS q c L'' η) (x * g.val) = unf ψ ν q P (gluedS q c L'' η) x) ∧
    DiesOnRam P (unf ψ ν q P (gluedS q c L'' η))

def GluedCase : Prop :=
  ∀ (P : Pair k n') (L'' : Submodule 𝒪[k] (n → k)) [L''.IsLattice k] (f'' : n → k), f'' ∉ L'' → q.1 • f'' ∈ L'' →
    ∃ Q : Pair k n, Q.lat = L'' ⊔ Submodule.span 𝒪[k] {f''} ∧ Q.HasVal f'' 1 ∧ Q.ker = L'' ∧
      gluedS q c L'' f'' = gluedS q c Q.ker Q.vec ∧
      ∀ x : Matrix n n' k, unf ψ ν q P (gluedS q c L'' f'') x =
        (volAll ν q (gluedS q c L'' f'') : ℂ) * phiOne P Q x

def OneCoset : Prop :=
  ∀ (P : Pair k n') (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k),
    h₀ • L₀ = gluedS q c Q.ker Q.vec → ∀ h : GL (n ⊕ Fin c) k, ¬ InCoset L₀ h₀ h →
      DiesOnRam P (unf ψ ν q P (h • L₀))

def Volumes : Prop :=
  ∀ Q : Pair k n,
    ∏ i ∈ Finset.Ico 1 c, volStep ν q (gluedS q c Q.ker Q.vec) i = volStabN ν (gluedS q c Q.ker Q.vec) ∧
    volStabN ν (gluedS q c Q.ker Q.vec) ≠ 0 ∧ volStabN ν (gluedS q c Q.ker Q.vec) ≠ ∞ ∧
    volAll ν q (gluedS q c Q.ker Q.vec) / (volStabN ν (gluedS q c Q.ker Q.vec)).toReal =
      (volStep ν q (gluedS q c Q.ker Q.vec) c).toReal ∧
    (IsSelfDual ψ ν → ∃ e : ℤ, (volStep ν q (gluedS q c Q.ker Q.vec) c).toReal = (resCard k : ℝ) ^ e)

def CosetWeight : Prop :=
  ∀ (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k], μG (latStab L₀ : Set (GL (n ⊕ Fin c) k)) = 1 →
    ∀ (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k), h₀ • L₀ = gluedS q c Q.ker Q.vec →
      (μX (MulAction.stabilizer (GL n k) Q : Set (GL n k)) ≠ 0 ∧
        μX (MulAction.stabilizer (GL n k) Q : Set (GL n k)) ≠ ∞) ∧
      ∀ f : GL (n ⊕ Fin c) k → ℂ,
        (∀ (g : GL n k), ∀ u ∈ N k n c 1, ∀ h, ∀ κ ∈ latStab L₀, f (embX c g * u * h * κ) =
          ((nabs k (GeneralLinearGroup.det g) ^ ((c : ℝ) - 1) : ℝ) : ℂ) * f h) →
        (∀ h, ¬ InCoset L₀ h₀ h → f h = 0) → ∀ z : ℂ, IsQuotInt ν μX μG 1 f z ↔
          z = f h₀ / (((volStabN ν (gluedS q c Q.ker Q.vec)).toReal : ℂ) *
            ((μX (MulAction.stabilizer (GL n k) Q : Set (GL n k))).toReal : ℂ))

def UnfoldedIntegral : Prop :=
  ∀ (M' M A : Type) [AddCommGroup M'] [Module ℂ M'] [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A]
    (μ : kˣ →* ℂˣ), IsUnram μ →
    ∀ (π' : Representation ℂ (GL n' k) M') (π : Representation ℂ (GL n k) M)
      (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (θ : M' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] M), IsTheta μ π' π θ →
    ∀ b : M →ₗ[ℂ] A →ₗ[ℂ] ℂ, IsPos ψ 1 π σ b →
    ∀ (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
      (L'₀ : Submodule 𝒪[k] (n' ⊕ Fin (c + 1) → k)) [L'₀.IsLattice k]
      (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k], μG (latStab L₀ : Set (GL (n ⊕ Fin c) k)) = 1 →
    ∀ (F : sphVecs σ L₀) (P : Pair k n') (Q : Pair k n) (h' : GL (n' ⊕ Fin (c + 1)) k) (h₀ : GL (n ⊕ Fin c) k),
      h' • L'₀ = gluedS q (c + 1) P.ker P.vec → h₀ • L₀ = gluedS q c Q.ker Q.vec →
    ∀ φ ∈ EqForm π', φ ∈ Mram k n' M' →
      ∃ (hE : ∀ h : GL (n ⊕ Fin c) k, opE ψ ν 1 (om μ h' h (latInd L'₀ L₀)) ∈ SB (Matrix n n' k))
        (h₁ : phiOne P Q ∈ SB (Matrix n n' k)), ∀ z : ℂ,
        IsQuotInt ν μX μG 1 (fun h => b (θ (φ P) ⟨_, hE h⟩) (σ h F)) z ↔
          z = (μ (GeneralLinearGroup.det h') : ℂ) * (((μ (GeneralLinearGroup.det h₀))⁻¹ : ℂˣ) : ℂ) *
            ((nabs k (GeneralLinearGroup.det h') ^ (((Fintype.card n : ℝ) + c) / 2) : ℝ) : ℂ) *
            ((nabs k (GeneralLinearGroup.det h₀) ^ (-((Fintype.card n' : ℝ) + c + 1) / 2) : ℝ) : ℂ) *
            ((volStep ν q (gluedS q c Q.ker Q.vec) c).toReal : ℂ) /
            ((μX (MulAction.stabilizer (GL n k) Q : Set (GL n k))).toReal : ℂ) *
            b (θ (φ P) ⟨_, h₁⟩) (vecAt σ F (gluedS q c Q.ker Q.vec))

end Statements

def Statement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (c : ℕ), 1 ≤ c → ∀ (q : Unif k) (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ν : Measure k, ν.IsAddHaarMeasure →
      DatumTranslate k n n' c q ∧ StabGlued k n c q ∧ StabGlued k n' (c + 1) q ∧
      Vanishing k n n' c q ψ ν ∧ NormalForm k n c q ∧ NormalValue k n n' c q ψ ν ∧ SplitCase k n n' c q ψ ν ∧
      GluedCase k n n' c q ψ ν ∧
      (OneOrbit k n c q ∧ OneCoset k n n' c q ψ ν ∧ StabCoords k n c q ∧ Volumes k n c q ψ ν ∧
        CosetWeight k n c q ν) ∧
      UnfoldedIntegral k n n' c q ψ ν ∧ DetValuations k n n' c q

section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} {c : ℕ}

example (hc : 1 ≤ c) (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) : interX (gluedS q c L η) = L := by
  ext x
  rw [← gluedLat_one]
  exact inX_mem_gluedLat le_rfl hc

example (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : latStep L c = L := by
  refine inf_eq_left.2 fun y _ l hl => ?_
  exact absurd l.2 (by omega)

example (i : ℕ) (y : n ⊕ Fin i → k) : flagIn c i y ∈ flagSub k n c i := fun l hl => by
  simp [flagIn, not_lt.2 hl]

example [Fintype n] [DecidableEq n] (g : GL n k) (x : n → k) : g • x = g.val *ᵥ x := rfl

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling
open scoped NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Blocks

variable (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

def parahoric : Subgroup (GL (A ⊕ D) k) :=
  ((parab 𝓀[k] (two (Equiv.refl (A ⊕ D)))).comap
      (GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]))).map
    (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k))

variable {k A D D'}

theorem mem_parahoric {g : GL (A ⊕ D) k} : g ∈ parahoric k A D ↔
    g ∈ KO k (A ⊕ D) ∧ ∀ i j, valuation k (g.1 (.inr i) (.inl j)) < 1 := by
  have hl : ∀ x : A, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D))) (Sum.inl x) = false := by
    intro x
    have e : (Sum.inl x : A ⊕ D) = GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D)) ⟨false, x⟩ := by simp
    rw [e, GlobalTheory.SmGL.blk_apply]
  have hr : ∀ x : D, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D))) (Sum.inr x) = true := by
    intro x
    have e : (Sum.inr x : A ⊕ D) = GlobalTheory.SmGL.two (Equiv.refl (A ⊕ D)) ⟨true, x⟩ := by simp
    rw [e, GlobalTheory.SmGL.blk_apply]
  have hval : ∀ z : 𝒪[k], IsLocalRing.residue 𝒪[k] z = 0 ↔ valuation k (z : k) < 1 := by
    intro z
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨h, rfl⟩, fun i j => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_parab] at hh
    have h0 := hh (Sum.inr i) (Sum.inl j) (by rw [hl, hr]; decide)
    simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply] at h0 ⊢
    exact (hval _).mp h0
  · rintro ⟨⟨h, rfl⟩, hv⟩
    refine ⟨h, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_parab]
    intro i j hij
    rcases i with i | i <;> rcases j with j | j <;> simp only [hl, hr, lt_self_iff_false] at hij
    · exact absurd hij (by decide)
    · have h0 := hv i j
      simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply] at h0 ⊢
      exact (hval _).mpr h0

def typeSpace {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (A ⊕ D) k) V) (ξ : kˣ →* ℂˣ) :
    Submodule ℂ V where
  carrier := {f | ∀ g ∈ parahoric k A D, ∀ d : kˣ, (d : k) = g.1.toBlocks₂₂.det → π g f = (ξ d : ℂ) • f}
  add_mem' hf hf' g hg d hd := by rw [map_add, hf g hg d hd, hf' g hg d hd, smul_add]
  zero_mem' g _ d _ := by simp
  smul_mem' c f hf g hg d hd := by rw [map_smul, hf g hg d hd, smul_comm]

def InSupp (x : Matrix (A ⊕ D) (A ⊕ D') k) : Prop :=
  (∀ i j, x i j ∈ 𝒪[k]) ∧ valuation k x.toBlocks₁₁.det = 1 ∧ ∀ i j, valuation k (x (.inr i) (.inl j)) < 1

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype D] [DecidableEq D] [Fintype D']
  [DecidableEq D'] in
theorem InSupp.det_ne {x : Matrix (A ⊕ D) (A ⊕ D') k} (h : InSupp x) : x.toBlocks₁₁.det ≠ 0 := by
  intro h0
  have h1 := h.2.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

open Classical in

def datum (ξ : kˣ →* ℂˣ) (x : Matrix (A ⊕ D) (A ⊕ D') k) : ℂ :=
  if h : InSupp x then (((ξ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

end Blocks

section Section

variable {k} {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [MeasurableSpace k]

def dblDatum (Φ₁ Φ₂ : Matrix b a k → ℂ) (y : Matrix b (a ⊕ a) k) : ℂ :=
  Φ₁ y.toCols₁ * starRingEnd ℂ (Φ₂ (-y.toCols₂))

def swSection (ν : Measure k) (μ : kˣ →* ℂˣ) (Φ₁ Φ₂ : Matrix b a k → ℂ) (h : GL (a ⊕ a) k) : ℂ :=
  ∫ x : Matrix b a k, om μ h (1 : GL b k) (dblDatum Φ₁ Φ₂) (fromCols x (-x)) ∂(volM ν b a)

def flatSection (ν : Measure k) (μ : kˣ →* ℂˣ) (Φ₁ Φ₂ : Matrix b a k → ℂ) (s : ℂ) (h : GL (a ⊕ a) k) : ℂ :=
  swSection ν μ Φ₁ Φ₂ h *
    npow (iwAbs (absRatio k a) (KO k (a ⊕ a)) h) (s - ((Fintype.card b : ℂ) - (Fintype.card a : ℂ)) / 2)

end Section

abbrev Blocks (l t : ℕ) : Type := Σ _ : Fin l, Fin t

variable {k}

abbrev blockRep {l : ℕ} (t : ℕ) (μ : Fin l → kˣ →* ℂˣ) :=
  multiProd (m := fun _ : Fin l => Fin t) (X := fun _ => ℂ) (Equiv.refl (Blocks l t)) fun i => detRep (Fin t) (μ i)

abbrev chainRep {r l : ℕ} (t : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin r) k) V) (μ : Fin l → kˣ →* ℂˣ) :=
  ind₂ (Equiv.refl (Fin r ⊕ Blocks l t)) (extTensor σ (blockRep t μ))

def IsInvForm {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ (∀ v, v ≠ 0 → 0 < (B v v).re) ∧ ∀ g v w, B (ρ g v) (ρ g w) = B v w

def blockParam {l : ℕ} (t : ℕ) (ϖ : kˣ) (μ : Fin l → kˣ →* ℂˣ) (μ' : kˣ →* ℂˣ) (x : Blocks l t) : ℂˣ :=
  μ x.1 ϖ / μ' ϖ * absPow k (((x.2 : ℕ) : ℂ) - ((t : ℂ) - 1) / 2) ϖ

def blockL {l : ℕ} (t : ℕ) (ϖ : kˣ) (μ : Fin l → kˣ →* ℂˣ) (μ' : kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  lFactor (resCard k) (blockParam t ϖ μ μ') s * lFactor (resCard k) (blockParam t ϖ μ μ')⁻¹ s

def zetaAt (q i : ℕ) : ℝ := (1 - ((q : ℝ) ^ i)⁻¹)⁻¹

def volAdd [MeasurableSpace k] (ν : Measure k) (r : ℕ) : ℝ :=
  (volM ν (Fin r) (Fin r)).real (Units.val '' (KO k (Fin r) : Set (GL (Fin r) k)))

def stepValue [MeasurableSpace k] (ν : Measure k) (r : ℕ) {l : ℕ} (t : ℕ) (ϖ : kˣ) (μ : Fin l → kˣ →* ℂˣ)
    (μ' : kˣ →* ℂˣ) : ℂ :=
  ((volAdd ν r * ((resCard k : ℝ) ^ (r * ((l + 1) * t)))⁻¹ : ℝ) : ℂ) * blockL t ϖ μ μ' ((1 + (t : ℂ)) / 2) /
    ((∏ i ∈ Finset.Ioc t ((l + 1) * t), zetaAt (resCard k) i : ℝ) : ℂ)

def ChainStep : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r t l : ℕ), 1 ≤ r → 1 ≤ t → 1 ≤ l →
  ∀ (ξ : kˣ →* ℂˣ), IsUnitaryChar ξ → IsTame ξ → ¬ IsUnram ξ →
  ∀ (μ₀ : Fin l → kˣ →* ℂˣ) (μ₀' : kˣ →* ℂˣ), (∀ i, IsUnram (μ₀ i) ∧ IsUnitaryChar (μ₀ i)) →
    IsUnram μ₀' → IsUnitaryChar μ₀' →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V),
    IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSpherical σ →
  let q : ℕ := resCard k
  let μ : Fin l → kˣ →* ℂˣ := fun i => μ₀ i * ξ
  let μ' : kˣ →* ℂˣ := μ₀' * ξ
  let π := chainRep t σ μ
  let J := parahoric k (Fin r) (Blocks l t)
  let Φ : Matrix (Fin r ⊕ Blocks (l + 1) t) (Fin r ⊕ Blocks l t) k → ℂ := datum ξ
  let s₀ : ℝ := (t : ℝ) / 2
  let Zj : ℂ := stepValue ν r t ϖ μ μ'
  let idx : ℕ := (parahoric k (Fin r) (Blocks (l + 1) t)).relIndex (KO k (Fin r ⊕ Blocks (l + 1) t))
  let b : ℕ := r + (l + 1) * t

  Module.finrank ℂ (typeSpace π ξ) = 1 ∧

  volAdd ν r = ∏ i ∈ Finset.Icc 1 r, (zetaAt q i)⁻¹ ∧
  (idx : ℝ) = (q : ℝ) ^ (r * ((l + 1) * t)) * (∏ i ∈ Finset.Icc 1 b, (zetaAt q i)⁻¹) /
    ((∏ i ∈ Finset.Icc 1 r, (zetaAt q i)⁻¹) * ∏ i ∈ Finset.Icc 1 ((l + 1) * t), (zetaAt q i)⁻¹) ∧
  (idx : ℂ) * ((∏ i ∈ Finset.Ioc t b, zetaAt q i : ℝ) : ℂ) * Zj = blockL t ϖ μ μ' ((1 + (t : ℂ)) / 2) ∧
  blockL t ϖ μ μ' ((1 + (t : ℂ)) / 2) = ((∏ i : Fin l, ∏ n ∈ Finset.Icc 1 t,
    (‖1 - ((μ i ϖ / μ' ϖ : ℂˣ) : ℂ) * ((q : ℂ) ^ n)⁻¹‖ ^ 2)⁻¹ : ℝ) : ℂ) ∧
  ∀ [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m J = 1 →
  ∀ B, IsInvForm π B → ∀ f ∈ typeSpace π ξ,
  let F : ℂ → GL (Fin r ⊕ Blocks l t) k → ℂ := fun s g =>
    flatSection ν μ' Φ Φ s (io k _ (g, 1)) * starRingEnd ℂ (B (π g f) f)
  let Z : ℂ → ℂ := fun s => ∫ g, F s g ∂m

  (∀ s : ℂ, s₀ - 1 < s.re → Integrable (F s) m) ∧
  (∀ C : Set ℝ, IsCompact C → C ⊆ Set.Ioi (s₀ - 1) →
    ∃ M : GL (Fin r ⊕ Blocks l t) k → ℝ, Integrable M m ∧ ∀ s : ℂ, s.re ∈ C → ∀ g, ‖F s g‖ ≤ M g) ∧
  Integrable (fun g => ‖flatSection ν μ' Φ Φ (((t : ℂ) - 1) / 2) (io k _ (g, 1))‖ * ‖B (π g f) f‖) m ∧

  DifferentiableOn ℂ Z {s | s₀ - 1 < s.re} ∧
  Z s₀ = Zj * B f f ∧
  HasSum (fun c : DoubleCoset.Quotient (J : Set (GL (Fin r ⊕ Blocks l t) k)) (J : Set _) =>
    (m.real (DoubleCoset.doubleCoset c.out (J : Set _) (J : Set _)) : ℂ) * F s₀ c.out) (Zj * B f f)

example {A D D' : Type} [Fintype A] [DecidableEq A] (ξ : kˣ →* ℂˣ) :
    datum ξ (fromBlocks 1 0 0 0 : Matrix (A ⊕ D) (A ⊕ D') k) = 1 := by
  have h : InSupp (fromBlocks 1 0 0 0 : Matrix (A ⊕ D) (A ⊕ D') k) := by
    refine ⟨?_, by simp, fun i j => by simp⟩
    rintro (i | i) (j | j)
    · exact one_int i j
    all_goals exact zero_mem _
  rw [datum, dif_pos h]
  have : Units.mk0 _ h.det_ne = 1 := by ext; simp
  simp [this]

example {D : Type} [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ) :
    (1 : ℂ) ∈ typeSpace (A := Fin 0) (detRep (Fin 0 ⊕ D) ξ) ξ := fun g _ d hd => by
  have : GeneralLinearGroup.det g = d := by
    ext
    rw [hd, GeneralLinearGroup.val_det_apply, ← det_submatrix_equiv_self (Equiv.emptySum (Fin 0) D).symm]
    rfl
  simp [detRep, this]

end GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
end
end

