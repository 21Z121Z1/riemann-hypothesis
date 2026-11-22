import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.CoboundaryTransfers.Statement

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TensorMultiplication
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Maps

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem actVB_mulVB (ρ : Representation LL G V) (g : G) (c : K₀) (x : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (LL := LL) c x) = mulVB (K₀ := K₀) (LL := LL) c (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, mulVB]
  | add a b ha hb => simp only [map_add, ha, hb]

omit [IsScalarTower Qp K₀ B] in

theorem comm_smul [SMulCommClass Qp K₀ B] (c : K₀) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (c • x) =
      mulVB (K₀ := K₀) (LL := LL) c (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp [mulVB, TensorProduct.smul_tmul', Algebra.smul_def]
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

def DcrisK (ρ : Representation LL G V) : Submodule K₀ (B ⊗[Qp] V) where
  carrier := {x | TensorProduct.comm Qp B V x ∈ Dcris PD ρ}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact (Dcris PD ρ).add_mem ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    rw [comm_smul (LL := LL), actVB_mulVB, hx g]

def compMap (ρ : Representation LL G V) : B ⊗[K₀] ↥(DcrisK PD ρ) →ₗ[B] B ⊗[Qp] V :=
  LinearMap.liftBaseChange B (DcrisK PD ρ).subtype

variable (B) in

def mapVB (f : V →ₗ[LL] V') : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

def Equivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

variable (Qp B LL V V') in

def mulTens : (V ⊗[Qp] B) ⊗[LL] (V' ⊗[Qp] B) →ₗ[LL] (V ⊗[LL] V') ⊗[Qp] B :=
  (AlgebraTensorModule.map (LinearMap.id : V ⊗[LL] V' →ₗ[LL] V ⊗[LL] V') (LinearMap.mul' Qp B)).comp
    (AlgebraTensorModule.tensorTensorTensorComm Qp Qp LL LL V B V' B).toLinearMap

theorem mulTens_tmul (v : V) (v' : V') (b b' : B) :
    mulTens Qp B LL V V' ((v ⊗ₜ[Qp] b) ⊗ₜ[LL] (v' ⊗ₜ[Qp] b')) = (v ⊗ₜ[LL] v') ⊗ₜ[Qp] (b * b') := by
  simp [mulTens]

def mulDcris (ρ : Representation LL G V) (ρ' : Representation LL G V') :
    ↥(Dcris PD ρ) ⊗[LL] ↥(Dcris PD ρ') →ₗ[LL] (V ⊗[LL] V') ⊗[Qp] B :=
  (mulTens Qp B LL V V').comp (TensorProduct.map (Dcris PD ρ).subtype (Dcris PD ρ').subtype)

def balK (ρ : Representation LL G V) (ρ' : Representation LL G V') :
    Submodule LL (↥(Dcris PD ρ) ⊗[LL] ↥(Dcris PD ρ')) :=
  Submodule.span LL {z | ∃ (c : K₀) (x cx : ↥(Dcris PD ρ)) (y cy : ↥(Dcris PD ρ')),
    (cx : V ⊗[Qp] B) = mulVB (K₀ := K₀) (LL := LL) c (x : V ⊗[Qp] B) ∧
    (cy : V' ⊗[Qp] B) = mulVB (K₀ := K₀) (LL := LL) c (y : V' ⊗[Qp] B) ∧
    z = cx ⊗ₜ[LL] y - x ⊗ₜ[LL] cy}

end Maps

def InvB : Prop := ∀ b : B, (∀ g, PD.actB g b = b) ↔ ∃ c : K₀, algebraMap K₀ B c = b

theorem invB_holds : InvB PD := fun b =>
  ⟨PD.invB b, by
    rintro ⟨c, rfl⟩ g
    exact (PD.actB g).commutes c⟩

variable (LL : Type) [Field LL] [Algebra Qp LL]

def DcrisFinite : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), FiniteDimensional LL ↥(Dcris PD ρ)

def Comparison : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → Function.Bijective (compMap PD ρ)

def CrysSub : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V' →ₗ[LL] V),
    Equivariant ρ' ρ f → Function.Injective f → IsCrys PD ρ → IsCrys PD ρ'

def CrysQuot : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V →ₗ[LL] V'),
    Equivariant ρ ρ' f → Function.Surjective f → IsCrys PD ρ → IsCrys PD ρ'

def CrysSum : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.prod ρ')

def CrysTensor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.tprod ρ')

def CrysDual : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → IsCrys PD ρ.dual

def DcrisExact : Prop :=
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] (ρ₀ : Representation LL G V₀)
    (V₁ : Type) [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [FiniteDimensional LL V₁] (ρ₁ : Representation LL G V₁)
    (V₂ : Type) [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [FiniteDimensional LL V₂] (ρ₂ : Representation LL G V₂)
    (f : V₀ →ₗ[LL] V₁) (g : V₁ →ₗ[LL] V₂),
    Equivariant ρ₀ ρ₁ f → Equivariant ρ₁ ρ₂ g →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    (∀ x ∈ Dcris PD ρ₀, mapVB B f x = 0 → x = 0) ∧
      (Dcris PD ρ₀).map (mapVB B f) = Dcris PD ρ₁ ⊓ LinearMap.ker (mapVB B g) ∧
      (Dcris PD ρ₁).map (mapVB B g) = Dcris PD ρ₂

def DcrisTensor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' →
    LinearMap.range (mulDcris PD ρ ρ') = Dcris PD (ρ.tprod ρ') ∧
      LinearMap.ker (mulDcris PD ρ ρ') = balK PD ρ ρ'

def LetterDim : Prop :=
  Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀ →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), IsCrys PD ρ →
    ∀ τ₀ : K₀ →ₐ[Qp] LL, finrank LL ↥(DcrisL PD ρ τ₀) = finrank LL V

def FormalismAt : Prop :=
  InvB PD ∧ (DcrisFinite PD LL ∧ FontaineLe PD LL) ∧ Comparison PD LL ∧
    CrysSub PD LL ∧ CrysQuot PD LL ∧ CrysSum PD LL ∧ CrysTensor PD LL ∧ CrysDual PD LL ∧
    DcrisExact PD LL ∧ DcrisTensor PD LL ∧ LetterDim PD LL

end Generic

def FontaineFormalism (l : ℕ) [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ K LL : FinExt l, FormalismAt (P.PD K) ↥LL.1

example (l : ℕ) [Fact l.Prime] (P : LocPrime l) (h : FontaineFormalism l P) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys (P.PD K) T.ρ) :
    Function.Bijective (compMap (P.PD K) T.ρ) ∧ IsCrys (P.PD K) T.ρ.dual :=
  ⟨(h K LL).2.2.1 T.V T.ρ hT, (h K LL).2.2.2.2.2.2.2.1 T.V T.ρ hT⟩

end GlobalTheory.IndefiniteRowSideFullHecke.TensorMultiplication
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

def extMul {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']
    (m : M ⊗[O] M' →ₗ[O] M'') (x : R ⊗[O] M) (y : R ⊗[O] M') : R ⊗[O] M'' :=
  m.baseChange R ((AlgebraTensorModule.distribBaseChange O R M M').symm (x ⊗ₜ[R] y))

theorem extMul_tmul {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']
    (m : M ⊗[O] M' →ₗ[O] M'') (r r' : R) (a : M) (a' : M') :
    extMul R m (r ⊗ₜ[O] a) (r' ⊗ₜ[O] a') = (r * r') ⊗ₜ[O] m (a ⊗ₜ[O] a') := by
  simp [extMul]

def extPair {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (β : M →ₗ[O] M' →ₗ[O] O) (x : R ⊗[O] M) (y : R ⊗[O] M') : R :=
  TensorProduct.rid O R (extMul R (TensorProduct.lift β) x y)

theorem extPair_tmul {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (β : M →ₗ[O] M' →ₗ[O] O) (r r' : R) (a : M) (a' : M') :
    extPair R β (r ⊗ₜ[O] a) (r' ⊗ₜ[O] a') = β a a' • (r * r') := by
  simp [extPair, extMul_tmul]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (fun p : T.V × T'.V => i.f p.1 + i'.f p.2) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

def IsTensorLat {T T' T'' : LocLat G Qp LL O} (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T) : Prop :=
  ∀ (g : G) (x : ↥T.L.T) (y : ↥T'.L.T),
    m (T.actT g x ⊗ₜ[O] T'.actT g y) = T''.actT g (m (x ⊗ₜ[O] y))

def SumFor (W : LocWach PD LL O v n) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L), IsSumLat i i' →
      ∃ σ : (W.DD T × W.DD T') ≃ₗ[W.EE] W.DD T'',
        (∀ x y, σ (x, y) = W.map i x + W.map i' y) ∧
        (∀ x y, W.φD T'' (σ (x, y)) = σ (W.φD T x, W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (σ (x, y)) = σ (W.γD T g x, W.γD T' g y)) ∧
        ∀ x y, σ (x, y) ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T')

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def UnitFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one,
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun c : W.EE => c • e) ∧
      W.φD W.one e = e ∧
      (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}

def TensorFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T, IsTensorLat m →
      ∃ μ : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'',
        (∀ x y, E.jD T'' (μ x y) = extMul RW m.toLinearMap (E.jD T x) (E.jD T' y)) ∧
        Function.Bijective (TensorProduct.lift μ) ∧
        (∀ x y, W.φD T'' (μ x y) = μ (W.φD T x) (W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (μ x y) = μ (W.γD T g x) (W.γD T' g y)) ∧
        ∃ ν : ↥(W.N T) ⊗[LetA O n] ↥(W.N T') ≃ₗ[LetA O n] ↥(W.N T''),
          ∀ (x : ↥(W.N T)) (y : ↥(W.N T')),
            ((ν (x ⊗ₜ[LetA O n] y) : ↥(W.N T'')) : W.DD T'') = μ (x : W.DD T) (y : W.DD T')

def DualFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ (T T' : LocLat G Qp LL O), IsCrys PD T.ρ →
    ∀ Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL, IsDualLat T.L T'.L Pr →
      ∃ (β : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O) (b : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.EE),
        (∀ (x : ↥T.L.T) (y : ↥T'.L.T), Pr (x : T.V) (y : T'.V) = algebraMap O LL (β x y)) ∧
        (∀ x y, E.ioE (b x y) = extPair RW β (E.jD T x) (E.jD T' y)) ∧
        Function.Bijective b ∧ Function.Bijective b.flip ∧
        (∀ x y, b (W.φD T x) (W.φD T' y) = W.φE (b x y)) ∧
        (∀ (g : W.Gam) x y, b (W.γD T g x) (W.γD T' g y) = W.γE g (b x y)) ∧
        (∀ y, y ∈ W.N T' ↔
          ∀ x ∈ W.N T, ∃ a : LetA O n, b x y = algebraMap (LetA O n) W.EE a) ∧
        ∃ δ : ↥(W.N T') ≃ₗ[LetA O n] Module.Dual (LetA O n) ↥(W.N T),
          ∀ (x : ↥(W.N T)) (y : ↥(W.N T')),
            b (x : W.DD T) (y : W.DD T') = algebraMap (LetA O n) W.EE (δ y x)

example {T T' T'' : LocLat G Qp LL O} (μ : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'')
    (ν : ↥(W.N T) ⊗[LetA O n] ↥(W.N T') ≃ₗ[LetA O n] ↥(W.N T''))
    (hν : ∀ (x : ↥(W.N T)) (y : ↥(W.N T')),
      ((ν (x ⊗ₜ[LetA O n] y) : ↥(W.N T'')) : W.DD T'') = μ (x : W.DD T) (y : W.DD T')) :
    W.N T'' = Submodule.span (LetA O n) {z | ∃ x ∈ W.N T, ∃ y ∈ W.N T', z = μ x y} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw⟩ := ν.surjective ⟨z, hz⟩
    have hz' : z = ((ν w : ↥(W.N T'')) : W.DD T'') := by rw [hw]
    rw [hz']
    clear hw hz' hz
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [hν]; exact Submodule.subset_span ⟨x, x.2, y, y.2, rfl⟩
    | add a b ha hb => rw [map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hb
  · rw [Submodule.span_le]
    rintro z ⟨x, hx, y, hy, rfl⟩
    have := hν ⟨x, hx⟩ ⟨y, hy⟩
    simp only at this
    rw [← this]
    exact (ν _).2

end Generic

def UnitPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), UnitFor (F.E K s LL h).tie

def SumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), SumFor (H.W K s LL h)

def TensorPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), TensorFor (F.E K s LL h).tie

def DualPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), DualFor (F.E K s LL h).tie

def UnitSumTensorDual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  UnitPart l P AI H F ∧ SumPart l P H ∧ TensorPart l P AI H F ∧ DualPart l P AI H F

end GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachCrystallineComparison
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

def serSMul {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]
    (f : PowerSeries LL) (d : ℕ → M) (k : ℕ) : M :=
  ∑ j ∈ Finset.range (k + 1), PowerSeries.coeff j f • d (k - j)

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def CmpIso (W : LocWach PD LL O v n) (l : ℕ) (T : LocLat G Qp LL O) : Prop :=
  (∀ x : ↥(W.N T), W.cmp T x = 0 ↔ ∃ y : ↥(W.N T), x = (letπ : LetA O n) • y) ∧
  Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T x) = Dcris PD T.ρ ∧
  (∀ i : ZMod n, Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x))
      = DcrisL PD T.ρ (W.emb i)) ∧
  (∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
    W.cmp T ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ =
      (l : LL) ^ m • φVB PD (LL := LL) (V := T.V) (W.cmp T x))

def ExpGen (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (ex : ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B)) : Prop :=
  (∀ (x : ↥(W.N T)) (k : ℤ), k < 0 → ex x k = 0) ∧
  (∀ d : ℕ → T.V ⊗[Qp] B, (∀ k, d k ∈ DcrisL PD T.ρ (W.emb i)) →
    ∃ (m : ℕ) (f : Fin m → PowerSeries LL) (x : Fin m → ↥(W.N T)),
      ∀ k : ℕ, d k = ∑ a, serSMul (f a) (fun r : ℕ => ex (x a) (r : ℤ)) k)

def ExpInj (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (ex : ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B)) : Prop :=
  letI : Algebra (LetA O n) (PowerSeries LL) := (W.lev i ζ).toRingHom.toAlgebra
  ∀ (m : ℕ) (f : Fin m → PowerSeries LL) (x : Fin m → ↥(W.N T)),
    (∀ k : ℕ, ∑ a, serSMul (f a) (fun r : ℕ => ex (x a) (r : ℤ)) k = 0) →
      (∑ a, f a ⊗ₜ[LetA O n] x a : PowerSeries LL ⊗[LetA O n] ↥(W.N T)) = 0

example (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    (∀ y : ↥(W.N T), W.cmp T ((letπ : LetA O n) • y) = 0) ∧
    Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T x) ≤ Dcris PD T.ρ :=
  ⟨W.cmp_π T, Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact W.cmp_mem T x)⟩

end Generic

def WachCrisComparison (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    CmpIso (H.W K s LL h) l T ∧
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (j : ℕ), j < s →
      IsPrimitiveRoot ζ (l ^ j) →
        ExpGen (H.W K s LL h) T i ((C.C K s LL h).tie.levB T i ζ) ∧
        ExpInj (H.W K s LL h) T i ζ ((C.C K s LL h).tie.levB T i ζ)

def WachCrisComparisonSpan (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    CmpIso (H.W K s LL h) l T ∧
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (j : ℕ), j < s →
      IsPrimitiveRoot ζ (l ^ j) → ExpGen (H.W K s LL h) T i ((C.C K s LL h).tie.levB T i ζ)

theorem WachCrisComparison.span {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    {H : LocHW l P} {F : LocFon l P AI H} {C : LocCmpT l P AI H F}
    (hc : WachCrisComparison l P AI H F C) : WachCrisComparisonSpan l P AI H F C :=
  fun K s LL h T hT => ⟨(hc K s LL h T hT).1, fun i ζ j hj hζ => ((hc K s LL h T hT).2 i ζ j hj hζ).1⟩

end GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison
end
end

