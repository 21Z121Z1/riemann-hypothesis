import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.CoboundaryTransfers.Statement
import Formalism.WeaklyAdmissibleFiltrations.Statement

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

variable {l : ℕ} [Fact l.Prime]

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

abbrev Emb (K LL : FinExt l) : Type := ↥K.1 →ₐ[ℚ_[l]] ↥LL.1

def embeddingRestrictMaxUnramified {K LL : FinExt l} (τ : Emb K LL) : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)

section Objects

variable (P : LocPrime l) {K LL : FinExt l}

abbrev iota (T : Lat K LL) : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  ιV (P.PD K) (LL := ↥LL.1) (V := T.V)

abbrev filV (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  FilV (P.PD K) (LL := ↥LL.1) (V := T.V) a

abbrev mulK (T : Lat K LL) (c : ↥K.1) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  mulVdR (Qp := ℚ_[l]) (K := ↥K.1) (BdR := P.R.BdR) (LL := ↥LL.1) (V := T.V) c

def filD (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  DdR (P.PD K) T.ρ ⊓ filV P T a

def tdR (K : FinExt l) : P.R.BdRˣ := ((P.PD K).t_unit.map (P.PD K).ι).unit

def offComp (T : Lat K LL) (τ : Emb K LL) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  Submodule.span ↥LL.1 {z | ∃ (c : ↥K.1), ∃ y ∈ DdR (P.PD K) T.ρ, z = mulK P T c y - τ c • y}

def mapdR {T T' : Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T'.V ⊗[ℚ_[l]] P.R.BdR :=
  AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)

end Objects

section Shapes

variable {K LL : FinExt l}

def IsSES {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V) : Prop :=
  (∀ σ x, f (T₀.ρ σ x) = T₁.ρ σ (f x)) ∧ (∀ σ x, g (T₁.ρ σ x) = T₂.ρ σ (g x)) ∧
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

def IsDualRep {T T' : Lat K LL} (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1) : Prop :=
  (∀ σ x y, β (T.ρ σ x) (T'.ρ σ y) = β x y) ∧ Function.Bijective β.flip

def IsTensorRep {T₁ T₂ T₃ : Lat K LL} (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V) : Prop :=
  ∀ σ x y, T₃.ρ σ (e (x ⊗ₜ[↥LL.1] y)) = e (T₁.ρ σ x ⊗ₜ[↥LL.1] T₂.ρ σ y)

def SubSES (P : LocPrime l) {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (g : T₁.V →ₗ[↥LL.1] T₂.V) (A₀ : Submodule ↥LL.1 (T₀.V ⊗[ℚ_[l]] P.R.BdR))
    (A₁ : Submodule ↥LL.1 (T₁.V ⊗[ℚ_[l]] P.R.BdR))
    (A₂ : Submodule ↥LL.1 (T₂.V ⊗[ℚ_[l]] P.R.BdR)) : Prop :=
  (∀ x ∈ A₀, mapdR P f x = 0 → x = 0) ∧
    (∀ y, (∃ x ∈ A₀, mapdR P f x = y) ↔ (y ∈ A₁ ∧ mapdR P g y = 0)) ∧
    (∀ z, (∃ y ∈ A₁, mapdR P g y = z) ↔ z ∈ A₂)

end Shapes

section At

variable (P : LocPrime l) (K LL : FinExt l)

def CrysDeRhamAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → IsDR (P.PD K) T.ρ

def DdRSpanAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    DdR (P.PD K) T.ρ = Submodule.span ↥LL.1
      {z | ∃ (c : ↥K.1), ∃ x ∈ Dcris (P.PD K) T.ρ, z = mulK P T c (iota P T x)}

def DdRInjAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    ∀ (m : ℕ) (c : Fin m → ↥K.1) (x : Fin m → T.V ⊗[ℚ_[l]] P.R.B),
      LinearIndependent ↥(K0 K) c → (∀ i, x i ∈ Dcris (P.PD K) T.ρ) →
      ∑ i, mulK P T (c i) (iota P T (x i)) = 0 → ∀ i, x i = 0

def ComponentIsoAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → ∀ τ : Emb K LL,
    ∃ e : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)) ≃ₗ[↥LL.1] ↥(DdRE (P.PD K) T.ρ τ),
      ∀ x : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)), iota P T (x : T.V ⊗[ℚ_[l]] P.R.B) - (e x : T.V ⊗[ℚ_[l]] P.R.BdR) ∈ offComp P T τ

def UnramOntoAt : Prop :=
  K.1 ≤ MaximalUnramifiedExtension l → ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    (Dcris (P.PD K) T.ρ).map (iota P T) = DdR (P.PD K) T.ρ

def FilZeroAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ →
    filV P T 0 = Submodule.span ↥LL.1
      {z | ∃ (a : ℤ), ∃ b ∈ (P.PD K).Fil 0, ∃ d ∈ filD P T a,
        z = mulVR T (((tdR P K ^ (-a) : P.R.BdRˣ) : P.R.BdR) * b) d}

def StrictAt : Prop :=
  ∀ (T₀ T₁ T₂ : Lat K LL) (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V), IsSES f g →
    IsDR (P.PD K) T₀.ρ → IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    ∀ (τ : Emb K LL) (a : ℤ), SubSES P f g
      (FildR (P.PD K) T₀.ρ τ a) (FildR (P.PD K) T₁.ρ τ a) (FildR (P.PD K) T₂.ρ τ a)

def DualJumpsAt : Prop :=
  ∀ (T T' : Lat K LL) (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1), IsDualRep β →
    IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ a ↔ IsJumpV (P.PD K) T.ρ τ (-a)) ∧
        multV (P.PD K) T'.ρ τ a = multV (P.PD K) T.ρ τ (-a)

def TensorJumpsAt : Prop :=
  ∀ (T₁ T₂ T₃ : Lat K LL) (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V), IsTensorRep e →
    IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    IsDR (P.PD K) T₃.ρ ∧ ∀ (τ : Emb K LL) (c : ℤ),
      (IsJumpV (P.PD K) T₃.ρ τ c ↔
        ∃ a b : ℤ, IsJumpV (P.PD K) T₁.ρ τ a ∧ IsJumpV (P.PD K) T₂.ρ τ b ∧ a + b = c) ∧
      ∀ S : Finset ℤ, JumpsInV (P.PD K) T₁.ρ τ (S : Set ℤ) →
        multV (P.PD K) T₃.ρ τ c =
          ∑ a ∈ S, multV (P.PD K) T₁.ρ τ a * multV (P.PD K) T₂.ρ τ (c - a)

def TwistJumpsAt : Prop :=
  ∀ T T' : Lat K LL, IsTwistRep (cycLL (P.PD K) ↥LL.1) T.ρ T'.ρ → IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ (a - 1) ↔ IsJumpV (P.PD K) T.ρ τ a) ∧
        multV (P.PD K) T'.ρ τ (a - 1) = multV (P.PD K) T.ρ τ a

def PotCrysDeRhamAt : Prop :=
  ∀ (T : Lat K LL) (K' : FinExt l) (hK : K.1 ≤ K'.1),
    IsCrys (P.PD K') (T.ρ.comp (Subgroup.inclusion (GK_le hK))) → IsDR (P.PD K) T.ρ

def FilteredIsoAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ →
    (∀ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → T.V ⊗[ℚ_[l]] P.R.BdR),
      LinearIndependent ↥K.1 b → (∀ i, d i ∈ DdR (P.PD K) T.ρ) →
      ∑ i, mulVR T (b i) (d i) = 0 → ∀ i, d i = 0) ∧
    Submodule.span ↥LL.1 {z | ∃ (b : P.R.BdR), ∃ d ∈ DdR (P.PD K) T.ρ, z = mulVR T b d} = ⊤ ∧
    ∀ n : ℤ, filV P T n = Submodule.span ↥LL.1
      {z | ∃ (a : ℤ), ∃ b ∈ (P.PD K).Fil (n - a), ∃ d ∈ filD P T a, z = mulVR T b d}

def StrictWholeAt : Prop :=
  ∀ (T₀ T₁ T₂ : Lat K LL) (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V), IsSES f g →
    IsDR (P.PD K) T₀.ρ → IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    ∀ a : ℤ, SubSES P f g (filD P T₀ a) (filD P T₁ a) (filD P T₂ a)

def GradedHodgeTateAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ → ∀ (a : ℤ), ∀ x ∈ filV P T a,
    (∀ σ, actVdR (P.PD K) T.ρ σ x - x ∈ filV P T (a + 1)) →
    ∃ d ∈ filD P T a, x - d ∈ filV P T (a + 1)

end At

def OverGood (C : FinExt l → FinExt l → Prop) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → C K LL

section Good

variable (l) (P : LocPrime l)

def CrysDeRham : Prop := OverGood (CrysDeRhamAt P)
def DdRSpan : Prop := OverGood (DdRSpanAt P)
def DdRInj : Prop := OverGood (DdRInjAt P)
def ComponentIso : Prop := OverGood (ComponentIsoAt P)
def UnramOnto : Prop := OverGood (UnramOntoAt P)
def FilZero : Prop := OverGood (FilZeroAt P)
def Strict : Prop := OverGood (StrictAt P)
def DualJumps : Prop := OverGood (DualJumpsAt P)
def TensorJumps : Prop := OverGood (TensorJumpsAt P)
def TwistJumps : Prop := OverGood (TwistJumpsAt P)
def PotCrysDeRham : Prop := OverGood (PotCrysDeRhamAt P)
def FilteredIso : Prop := OverGood (FilteredIsoAt P)
def StrictWhole : Prop := OverGood (StrictWholeAt P)
def GradedHodgeTate : Prop := OverGood (GradedHodgeTateAt P)

def DeRhamComparison : Prop :=
  CrysDeRham l P ∧ DdRSpan l P ∧ ComponentIso l P ∧ UnramOnto l P ∧ FilZero l P ∧ Strict l P ∧
    DualJumps l P ∧ TensorJumps l P ∧ TwistJumps l P ∧ PotCrysDeRham l P

def DeRhamComparisonFull : Prop :=
  DeRhamComparison l P ∧ DdRInj l P ∧ FilteredIso l P ∧ StrictWhole l P ∧ GradedHodgeTate l P

def DeRhamComparisonAllFields : Prop :=
  ∀ K LL : FinExt l, CrysDeRhamAt P K LL ∧ DdRSpanAt P K LL ∧ ComponentIsoAt P K LL ∧
    UnramOntoAt P K LL ∧ FilZeroAt P K LL ∧ StrictAt P K LL ∧ DualJumpsAt P K LL ∧
    TensorJumpsAt P K LL ∧ TwistJumpsAt P K LL ∧ PotCrysDeRhamAt P K LL ∧ DdRInjAt P K LL ∧
    FilteredIsoAt P K LL ∧ StrictWholeAt P K LL ∧ GradedHodgeTateAt P K LL

end Good

example (P : LocPrime l) {K LL : FinExt l} (T : Lat K LL) (τ : Emb K LL) (a : ℤ) :
    FildR (P.PD K) T.ρ τ a ≤ filD P T a :=
  inf_le_inf_right _ inf_le_left

example (P : LocPrime l) {K LL : FinExt l} (T : Lat K LL) :
    (Dcris (P.PD K) T.ρ).map (iota P T) ≤ DdR (P.PD K) T.ρ := by
  rintro _ ⟨x, hx, rfl⟩
  have key : ∀ g y, actVdR (P.PD K) T.ρ g (iota P T y) = iota P T (actVB (P.PD K) T.ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, actVB, ιV, (P.PD K).ι_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  simp only [Dcris, DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hx ⊢
  intro g
  rw [key, hx]

end GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GammaStableInverse
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Inv

variable {A D : Type} [CommRing A] [AddCommGroup D] [Module A D]

def invSub (a : A) (M : Submodule A D) : Submodule A D where
  carrier := {x | ∃ k : ℕ, a ^ k • x ∈ M}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨j + k, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact M.smul_mem _ hj
    · rw [pow_add, mul_smul]
      exact M.smul_mem _ hk
  smul_mem' := by
    rintro c x ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [smul_comm]
    exact M.smul_mem _ hk

theorem invSub_le {a : A} {M M' : Submodule A D} (h : M ≤ invSub a M') :
    invSub a M ≤ invSub a M' := by
  rintro x ⟨k, hk⟩
  obtain ⟨j, hj⟩ := h hk
  exact ⟨j + k, by rwa [pow_add, mul_smul]⟩

end Inv

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N₁ : Submodule (LetA O n) (W.DD T))

def HasCommonBasis : Prop :=
  ∃ (ι : Type) (b : Module.Basis ι (LetA O n) ↥N₁) (b' : Module.Basis ι W.EE (W.DD T)),
    ∀ j, b' j = (b j : W.DD T)

def GammaStable : Prop := W.γ T '' (N₁ : Set (W.DD T)) = (N₁ : Set (W.DD T))

def GammaTrivialModPi : Prop :=
  ∀ x ∈ N₁, ∃ y ∈ N₁, W.γ T x - x = (letπ : LetA O n) • y

def phiSpan : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (W.φD T '' (N₁ : Set (W.DD T)))

def FrobeniusIsoAwayQ : Prop := invSub W.Q (phiSpan W T N₁) = invSub W.Q N₁

def WachUniqueAt : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ N₁ : Submodule (LetA O n) (W.DD T),
    HasCommonBasis W T N₁ → GammaStable W T N₁ → GammaTrivialModPi W T N₁ →
      FrobeniusIsoAwayQ W T N₁ → N₁ = W.N T

end Generic

def WachUnique (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), WachUniqueAt (H.W K s LL h)

def WachUniqueOfJumps (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (M hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ),
    IsCrys (P.PD K) T.ρ →
    (∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
      (∀ c : ↥(K0 K), τ (algebraMap ↥(K0 K) ↥K.1 c) = (H.W K s LL h).emb i c) →
        JumpsInV (P.PD K) T.ρ τ (Set.Icc (-(M i : ℤ)) (hi i : ℤ))) →
    ∀ N₁ : Submodule (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ((H.W K s LL h).DD T),
      HasCommonBasis (H.W K s LL h) T N₁ → GammaStable (H.W K s LL h) T N₁ →
        GammaTrivialModPi (H.W K s LL h) T N₁ → FrobeniusIsoAwayQ (H.W K s LL h) T N₁ →
          N₁ = (H.W K s LL h).N T

end GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def IsLaurent (u : ℤ → M) : Prop := ∃ m : ℤ, ∀ k < m, u k = 0

def serMul (f : PowerSeries L) (u : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • u (k - (j : ℤ))

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_finite (f : PowerSeries L) {u : ℤ → M}
    (hu : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent u) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j f • u (k - (j : ℤ))).Finite := by
  obtain ⟨m, hm⟩ := hu
  refine (Set.finite_Iic (k - m).toNat).subset ?_
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Iic]
  by_contra h
  push_neg at h
  exact hj (by rw [hm _ (by omega), smul_zero])

open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one (u : ℤ → M) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul (1 : PowerSeries L) u = u := by
  funext k
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul
  rw [finsum_eq_single _ 0 (fun j hj => by simp [PowerSeries.coeff_one, hj])]
  simp

variable (L) in

def serSpan (S : Set (ℤ → M)) : Submodule L (ℤ → M) :=
  Submodule.span L {w | ∃ (f : PowerSeries L) (u : ℤ → M), u ∈ S ∧ IsLaurent u ∧ w = serMul f u}

def shiftSer (a : ℤ) (F : Submodule L M) : Submodule L (ℤ → M) where
  carrier := {u | (∀ k < -a, u k = 0) ∧ ∀ k, u k ∈ F}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => F.zero_mem⟩
  add_mem' := by
    rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
    exact ⟨fun k hk => by simp [hu k hk, hw k hk], fun k => F.add_mem (hu' k) (hw' k)⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨fun k hk => by simp [hu k hk], fun k => F.smul_mem c (hu' k)⟩

def gradedSer (F : ℤ → Submodule L M) : Submodule L (ℤ → M) := ⨆ a : ℤ, shiftSer a (F a)

example (a : ℤ) (F : Submodule L M) (d : M) (hd : d ∈ F) :
    (Pi.single (-a) d : ℤ → M) ∈ shiftSer a F := by
  refine ⟨fun k hk => Pi.single_eq_of_ne (ne_of_lt hk) _, fun k => ?_⟩
  by_cases h : k = -a
  · subst h; simpa using hd
  · simp [Pi.single_eq_of_ne h]

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def Dlet (i : ZMod n) : Submodule LL (T.V ⊗[Qp] B) := DcrisL PD T.ρ (W.emb i)

def FilLet (i : ZMod n) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] B) :=
  Dlet W T i ⊓
    (FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ').comap
      (ιV PD (LL := LL) (V := T.V))

def toDR (F : Submodule LL (T.V ⊗[Qp] B)) : Submodule LL (T.V ⊗[Qp] BdR) :=
  F.map (ιV PD (LL := LL) (V := T.V))

def Nlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL (Set.range (W.levN T i ζ))

def IsExpansion (i : ZMod n) (ζ : LL) (y : W.DD T) (u : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  IsLaurent u ∧ ∃ (m : ℕ) (hy : W.Q ^ m • y ∈ W.N T),
    serMul (W.lev i ζ (W.Q ^ m)) u = W.levN T i ζ ⟨W.Q ^ m • y, hy⟩

def phiNlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL {u | ∃ y ∈ W.N T, IsExpansion W T i ζ (W.φD T y) u}

variable (PD) in

def phiSer (j : ℕ) (u : ℤ → T.V ⊗[Qp] B) : ℤ → T.V ⊗[Qp] BdR :=
  fun k => ιV PD (LL := LL) (V := T.V)
    ((((PD.p : LL) ^ j) ^ k) • ((φVB PD (LL := LL) (V := T.V)) ^ j) (u k))

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.levN_mem_Nlev (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) :
    W.levN T i ζ x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.Nlev W T i ζ := by
  refine Submodule.subset_span ⟨1, W.levN T i ζ x, ⟨x, rfl⟩, ?_,
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one _).symm⟩
  obtain ⟨m, hm⟩ := W.levN_supp T i ζ x
  exact ⟨m, hm⟩

end Generic

section Statement

variable {l : ℕ} [Fact l.Prime]

def resEmb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1) : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IntermediateField.inclusion h.2.2.1)

def LatticeAtLevels (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      (∀ j : ℕ, j < s → IsPrimitiveRoot ζ (l ^ j) →
        Nlev (H.W K s LL h) T i ζ =
          shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i))) ∧
      (∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ →
        phiNlev (H.W K s LL h) T i ζ =
            shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i)) ∧
          Nlev (H.W K s LL h) T i ζ =
            gradedSer fun a =>
              toDR (PD := P.PD K) T (FilLet (H.W K s LL h) T i (resEmb h τ) a)) ∧
      (∀ j : ℕ, 1 ≤ j → IsPrimitiveRoot ζ (l ^ (s + j)) →
        Nlev (H.W K s LL h) T i ζ =
            serSpan ↥LL.1 (phiSer (P.PD K) T j ''
              (serSpan ↥LL.1 (Set.range
                ((C.C K s LL h).tie.levB T (i - (j : ZMod _)) (ζ ^ (l ^ j)))) :
                  Set (ℤ → T.V ⊗[ℚ_[l]] P.R.B))) ∧
          ∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h (i - (j : ZMod _)) (ζ ^ (l ^ j)) τ →
            Nlev (H.W K s LL h) T i ζ =
              gradedSer fun a =>
                toDR (PD := P.PD K) T
                  ((FilLet (H.W K s LL h) T (i - (j : ZMod _)) (resEmb h τ) a).map
                    ((φVB (P.PD K) (LL := ↥LL.1) (V := T.V)) ^ j)))

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
end
end

