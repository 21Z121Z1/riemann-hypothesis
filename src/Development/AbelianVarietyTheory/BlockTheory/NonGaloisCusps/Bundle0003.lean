import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.CoboundaryTransfers.Statement

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.JumpMultiplicityDual
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Core

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Ops

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def mulPeriod (b : BdR) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

example (c : K) : mulPeriod (Qp := Qp) (LL := LL) (V := V) (algebraMap K BdR c) =
    mulVdR (Qp := Qp) (LL := LL) (V := V) (BdR := BdR) c := rfl

def mapdR {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR :=
  AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)

def tdR : BdRˣ := (PD.t_unit.map PD.ι).unit

example : ((tdR PD : BdRˣ) : BdR) = PD.ι PD.t := rfl

variable (ρ : Representation LL G V)

def filDdR (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) := DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a

def jumpMult (τ : K →ₐ[Qp] LL) (a : ℤ) : ℕ :=
  Module.finrank LL (↥(FildR PD ρ τ a) ⧸ (FildR PD ρ τ (a + 1)).comap (FildR PD ρ τ a).subtype)

def resEmb (K₀ : Type) [Field K₀] [Algebra Qp K₀] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (τ : K →ₐ[Qp] LL) : K₀ →ₐ[Qp] LL :=
  τ.comp (IsScalarTower.toAlgHom Qp K₀ K)

end Ops

variable [TopologicalSpace G] (LL O : Type) [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL]

def CrysDeRhamCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → IsDR PD T.ρ

def SpanCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    DdR PD T.ρ = ⨆ c : K, ((Dcris PD T.ρ).map (ιV PD (LL := LL) (V := T.V))).map
      (mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) c)

def BaseChangeInjCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    ∀ (m : ℕ) (c : Fin m → K), LinearIndependent K₀ c →
      ∀ x : Fin m → T.V ⊗[Qp] B, (∀ j, x j ∈ Dcris PD T.ρ) →
        ∑ j, mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) (c j)
          (ιV PD (LL := LL) (V := T.V) (x j)) = 0 → ∀ j, x j = 0

def ComponentCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ τ : K →ₐ[Qp] LL,
    ∃ e : ↥(DcrisL PD T.ρ (resEmb K₀ τ)) ≃ₗ[LL] ↥(DdRE PD T.ρ τ),
      ∀ x : ↥(DcrisL PD T.ρ (resEmb K₀ τ)),
        ιV PD (LL := LL) (V := T.V) (x : T.V ⊗[Qp] B) - (e x : T.V ⊗[Qp] BdR) ∈
          ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ'

def OntoCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    (Dcris PD T.ρ).map (ιV PD (LL := LL) (V := T.V)) = DdR PD T.ρ

def ComparisonInjCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsDR PD T.ρ →
    ∀ (m : ℕ) (x : Fin m → T.V ⊗[Qp] BdR), (∀ j, x j ∈ DdR PD T.ρ) →
      (∀ c : Fin m → K,
        ∑ j, mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) (c j) (x j) = 0 → ∀ j, c j = 0) →
      ∀ b : Fin m → BdR,
        ∑ j, mulPeriod (Qp := Qp) (LL := LL) (V := T.V) (b j) (x j) = 0 → ∀ j, b j = 0

def FilteredCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsDR PD T.ρ → ∀ n : ℤ,
    FilV PD (LL := LL) (V := T.V) n =
      ⨆ (a : ℤ) (b : BdR) (_ : b ∈ PD.Fil (n - a)),
        (filDdR PD T.ρ a).map (mulPeriod (Qp := Qp) (LL := LL) (V := T.V) b)

def LatticeCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsDR PD T.ρ →
    FilV PD (LL := LL) (V := T.V) 0 =
      ⨆ (a : ℤ) (b : BdR) (_ : b ∈ PD.Fil 0),
        (filDdR PD T.ρ a).map
          (mulPeriod (Qp := Qp) (LL := LL) (V := T.V) (((tdR PD ^ (-a) : BdRˣ) : BdR) * b))

def StrictCore : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (f : T₀.V →ₗ[LL] T₁.V) (g : T₁.V →ₗ[LL] T₂.V),
    (∀ s x, f (T₀.ρ s x) = T₁.ρ s (f x)) → (∀ s x, g (T₁.ρ s x) = T₂.ρ s (g x)) →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsDR PD T₀.ρ → IsDR PD T₁.ρ → IsDR PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (∀ x ∈ FildR PD T₀.ρ τ a, mapdR (Qp := Qp) (BdR := BdR) f x = 0 → x = 0) ∧
      (FildR PD T₀.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) f) =
        FildR PD T₁.ρ τ a ⊓ LinearMap.ker (mapdR (Qp := Qp) (BdR := BdR) g) ∧
      (FildR PD T₁.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) g) = FildR PD T₂.ρ τ a

def DualCore : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (β : T.V →ₗ[LL] T'.V →ₗ[LL] LL),
    (∀ s x y, β (T.ρ s x) (T'.ρ s y) = β x y) → Function.Bijective β.flip → IsDR PD T.ρ →
    IsDR PD T'.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (IsJumpV PD T'.ρ τ a ↔ IsJumpV PD T.ρ τ (-a)) ∧
      jumpMult PD T'.ρ τ a = jumpMult PD T.ρ τ (-a)

def TensorCore : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (e : T.V ⊗[LL] T'.V ≃ₗ[LL] T''.V),
    (∀ s x y, T''.ρ s (e (x ⊗ₜ[LL] y)) = e (T.ρ s x ⊗ₜ[LL] T'.ρ s y)) →
    IsDR PD T.ρ → IsDR PD T'.ρ →
    IsDR PD T''.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (c : ℤ),
      (IsJumpV PD T''.ρ τ c ↔ ∃ a b : ℤ, IsJumpV PD T.ρ τ a ∧ IsJumpV PD T'.ρ τ b ∧ c = a + b) ∧
      (Function.support fun a : ℤ => jumpMult PD T.ρ τ a * jumpMult PD T'.ρ τ (c - a)).Finite ∧
      jumpMult PD T''.ρ τ c = ∑ᶠ a : ℤ, jumpMult PD T.ρ τ a * jumpMult PD T'.ρ τ (c - a)

def TwistCore : Prop :=
  ∀ T T' : LocLat G Qp LL O, IsTwistRep (cycLL PD LL) T.ρ T'.ρ → IsDR PD T.ρ →
    IsDR PD T'.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (IsJumpV PD T'.ρ τ (a - 1) ↔ IsJumpV PD T.ρ τ a) ∧
      jumpMult PD T'.ρ τ (a - 1) = jumpMult PD T.ρ τ a

end Core

section Local

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

def CrysDeRham : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → CrysDeRhamCore (P.PD K) ↥LL.1 ↥(OL LL)

def DeRhamSpan : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → SpanCore (P.PD K) ↥LL.1 ↥(OL LL)

def BaseChangeInj : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → BaseChangeInjCore (P.PD K) ↥LL.1 ↥(OL LL)

def ComponentIso : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ComponentCore (P.PD K) ↥LL.1 ↥(OL LL)

def UnramifiedOnto : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → K0 K = K.1 →
    OntoCore (P.PD K) ↥LL.1 ↥(OL LL)

def ComparisonInj : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ComparisonInjCore (P.PD K) ↥LL.1 ↥(OL LL)

def ComparisonFiltered : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → FilteredCore (P.PD K) ↥LL.1 ↥(OL LL)

def PlusLattice : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → LatticeCore (P.PD K) ↥LL.1 ↥(OL LL)

def Strictness : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → StrictCore (P.PD K) ↥LL.1 ↥(OL LL)

def DualJumps : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → DualCore (P.PD K) ↥LL.1 ↥(OL LL)

def TensorJumps : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → TensorCore (P.PD K) ↥LL.1 ↥(OL LL)

def TwistJumps : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → TwistCore (P.PD K) ↥LL.1 ↥(OL LL)

def PotCrysDeRham : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL →
    ∀ (K' : FinExt l) (h : K.1 ≤ K'.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      IsCrys (P.PD K') (T.ρ.comp (Subgroup.inclusion (GK_le h))) → IsDR (P.PD K) T.ρ

def DeRhamComparison : Prop :=
  CrysDeRham l P ∧ DeRhamSpan l P ∧ BaseChangeInj l P ∧ ComponentIso l P ∧ UnramifiedOnto l P ∧
    ComparisonInj l P ∧ ComparisonFiltered l P ∧ PlusLattice l P ∧ Strictness l P ∧
    DualJumps l P ∧ TensorJumps l P ∧ TwistJumps l P ∧ PotCrysDeRham l P

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

abbrev rk : ℕ := finrank O ↥T.L.T

abbrev letterModule (i : ZMod n) : Module (PowerSeries O) ↥(W.Nl T i) :=
  Module.compHom _ (Pi.constRingHom (ZMod n) (PowerSeries O))

attribute [local instance] letterModule

open Module in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul (i : ZMod n) (c : PowerSeries O)
    (x : ↥(W.Nl T i)) :
    ((c • x : ↥(W.Nl T i)) : W.DD T) = (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • (x : W.DD T) := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Submodule.map (_root_.Formalism.BasicNotions.letE i • LinearMap.id) (W.N T) := hx
  obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp hx'
  change (Pi.constRingHom (ZMod n) (PowerSeries O) c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y) =
    (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y)
  rw [smul_smul, smul_smul]
  congr 1
  unfold _root_.Formalism.BasicNotions.letE
  ext j : 1
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

abbrev LetterBasis (i : ZMod n) : Type := Basis (Fin (rk T)) (PowerSeries O) ↥(W.Nl T i)

def LettersDecompose : Prop := iSupIndep (W.Nl T) ∧ ⨆ i, W.Nl T i = W.N T

def LettersFree : Prop := ∀ i : ZMod n, Nonempty (LetterBasis W T i)

def GlobalBasis : Prop :=
  ∃ b : Basis (Fin (rk T)) (LetA O n) ↥(W.N T),
    LinearIndependent W.EE (fun j => (b j : W.DD T)) ∧
      Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) = ⊤

def phiPullLetter (i : ZMod n) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (W.Nl T (i - 1) : Set (W.DD T)))

def LetterSandwich (M₀ h₀ : ℕ) : Prop :=
  ∀ i : ZMod n, (∀ y ∈ W.Nl T i, W.Q ^ h₀ • y ∈ phiPullLetter W T i) ∧
    (∀ z ∈ phiPullLetter W T i, W.Q ^ M₀ • z ∈ W.Nl T i)

def Sandwich (M₀ h₀ : ℕ) : Prop :=
  (∀ x ∈ W.N T, W.Q ^ M₀ • W.φD T x ∈ W.N T) ∧ (∀ y ∈ W.N T, W.Q ^ h₀ • y ∈ W.φpull T)

variable {W T}

def rowMul {i : ZMod n} (b : LetterBasis W T i)
    (R : Matrix (Fin (rk T)) (Fin (rk T)) (PowerSeries O)) (k : Fin (rk T)) : W.DD T :=
  ((∑ j, R j k • b j : ↥(W.Nl T i)) : W.DD T)

def FrobMatrices (b : ∀ i, LetterBasis W T i) (M₀ h₀ : ℕ) : Prop :=
  ∀ i : ZMod n, ∃ R R' : Matrix (Fin (rk T)) (Fin (rk T)) (PowerSeries O),
    (∀ k, W.Q ^ M₀ • W.φD T (b (i - 1) k : W.DD T) = rowMul (b i) R k) ∧
      R * R' = (W.Q i ^ (M₀ + h₀)) • (1 : Matrix _ _ _) ∧
      R' * R = (W.Q i ^ (M₀ + h₀)) • (1 : Matrix _ _ _)

def GammaMatrices (b : ∀ i, LetterBasis W T i) : Prop :=
  ∀ (g : W.Gam) (i : ZMod n), ∃ Gm : GL (Fin (rk T)) (PowerSeries O),
    ∀ k, W.γD T g (b i k : W.DD T) = rowMul (b i) (Gm : Matrix _ _ _) k

variable (W T)

def Matrices : Prop :=
  ∀ b : ∀ i, LetterBasis W T i,
    GammaMatrices b ∧ (∃ M₀ h₀, FrobMatrices b M₀ h₀) ∧
      ∀ M₀ h₀, FrobMatrices b M₀ h₀ → LetterSandwich W T M₀ h₀

def FreeAt : Prop :=
  LettersDecompose W T ∧ LettersFree W T ∧ GlobalBasis W T ∧
    (∃ M₀ h₀, Sandwich W T M₀ h₀) ∧ Matrices W T

theorem phi_letE (i : ZMod n) : W.φA (letE (i - 1)) = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [LocWach.φA, letφ, letE]
  · have h' : j - 1 ≠ i - 1 := fun e => h (sub_left_injective e)
    simp [LocWach.φA, letφ, letE, h, h']

end Generic

def LettersFreeOfRank (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → FreeAt (H.W K s LL h) T

end GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TensorLatticeUnitPart
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Bilinear

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

def extBil (b : M →ₗ[O] M' →ₗ[O] M'') (u : R ⊗[O] M) (w : R ⊗[O] M') : R ⊗[O] M'' :=
  TensorProduct.map (LinearMap.mul' O R) (TensorProduct.lift b)
    (TensorProduct.tensorTensorTensorComm O R M R M' (u ⊗ₜ[O] w))

theorem extBil_tmul (b : M →ₗ[O] M' →ₗ[O] M'') (r r' : R) (x : M) (y : M') :
    extBil R b (r ⊗ₜ[O] x) (r' ⊗ₜ[O] y) = (r * r') ⊗ₜ[O] b x y := by
  simp [extBil]

def extForm (b : M →ₗ[O] M' →ₗ[O] O) (u : R ⊗[O] M) (w : R ⊗[O] M') : R :=
  TensorProduct.rid O R (extBil R b u w)

theorem extForm_tmul (b : M →ₗ[O] M' →ₗ[O] O) (r r' : R) (x : M) (y : M') :
    extForm R b (r ⊗ₜ[O] x) (r' ⊗ₜ[O] y) = b x y • (r * r') := by
  simp [extForm, extBil_tmul]

end Bilinear

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (i.f.coprod i'.f) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

def IsTensorLat {T T' T'' : LocLat G Qp LL O} (b : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] ↥T''.L.T) : Prop :=
  Function.Bijective (TensorProduct.lift b) ∧
    ∀ (g : G) (x : ↥T.L.T) (y : ↥T'.L.T), b (T.actT g x) (T'.actT g y) = T''.actT g (b x y)

variable (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def UnitAt (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one, E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun a : W.EE => a • e) ∧
      W.φD W.one e = e ∧ (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}

example (E : EtTie W RA RW inclR φR gR πA) : ∃ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ := by
  obtain ⟨_, e₀, h, _⟩ := E.one_e
  exact ⟨e₀, h⟩

def SumAt : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → IsSumLat i i' →
      IsCrys PD T''.ρ ∧
      Function.Bijective ((W.map i).coprod (W.map i')) ∧
      (∀ x y, W.φD T'' (W.map i x + W.map i' y) = W.map i (W.φD T x) + W.map i' (W.φD T' y)) ∧
      (∀ (g : W.Gam) x y,
        W.γD T'' g (W.map i x + W.map i' y) = W.map i (W.γD T g x) + W.map i' (W.γD T' g y)) ∧
      ∀ z, z ∈ W.N T'' ↔ ∃ x ∈ W.N T, ∃ y ∈ W.N T', z = W.map i x + W.map i' y

def TensorAt (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (b : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] ↥T''.L.T),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → IsTensorLat b →
      IsCrys PD T''.ρ ∧
      ∃ β : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'',
        (∀ x y, E.jD T'' (β x y) = extBil RW b (E.jD T x) (E.jD T' y)) ∧
        Function.Bijective (TensorProduct.lift β) ∧
        (∀ x y, W.φD T'' (β x y) = β (W.φD T x) (W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (β x y) = β (W.γD T g x) (W.γD T' g y)) ∧
        W.N T'' = Submodule.span (LetA O n) {z | ∃ x ∈ W.N T, ∃ y ∈ W.N T', z = β x y} ∧
        ∃ βN : ↥(W.N T) →ₗ[LetA O n] ↥(W.N T') →ₗ[LetA O n] ↥(W.N T''),
          (∀ x y, (βN x y : W.DD T'') = β (x : W.DD T) (y : W.DD T')) ∧
          Function.Bijective (TensorProduct.lift βN)

def DualAt (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL),
    IsCrys PD T.ρ → IsDualLat T.L T'.L Pr →
      IsCrys PD T'.ρ ∧
      ∃ PT : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O,
        (∀ x y, algebraMap O LL (PT x y) = Pr (x : T.V) (y : T'.V)) ∧
        ∃ β : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.EE,
          (∀ x y, E.ioE (β x y) = extForm RW PT (E.jD T x) (E.jD T' y)) ∧
          Function.Bijective β ∧ Function.Bijective β.flip ∧
          (∀ x y, β (W.φD T x) (W.φD T' y) = W.φE (β x y)) ∧
          (∀ (g : W.Gam) x y, β (W.γD T g x) (W.γD T' g y) = W.γE g (β x y)) ∧
          (∀ y, y ∈ W.N T' ↔
            ∀ x ∈ W.N T, ∃ a : LetA O n, β x y = algebraMap (LetA O n) W.EE a) ∧
          ∀ f : ↥(W.N T) →ₗ[LetA O n] LetA O n, ∃ y ∈ W.N T',
            ∀ x : ↥(W.N T), β (x : W.DD T) y = algebraMap (LetA O n) W.EE (f x)

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

def UnitPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    UnitAt (H.W K s LL h) (F.E K s LL h).tie

def SumPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), SumAt (H.W K s LL h)

def TensorPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    TensorAt (H.W K s LL h) (F.E K s LL h).tie

def DualPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    DualAt (H.W K s LL h) (F.E K s LL h).tie

def WachMonoidal : Prop :=
  UnitPart l P AI H F ∧ SumPart l P H ∧ TensorPart l P AI H F ∧ DualPart l P AI H F

end GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
end
end

