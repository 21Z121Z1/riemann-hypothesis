import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Polynomial
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev plF (PP : Pl D.host.E) : HeightOneSpectrum (𝓞 D.host.F) := PP.under (𝓞 D.host.F)

def IsInertPl (PP : Pl D.host.E) : Prop :=
  Formalism.UG.IsInertAt D.host.F D.host.E (plF PP) PP

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v', v' ≠ v →
    ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levX (R : RealDat D A Ks) (t : T) : Subgroup (Bridge.Gf D.sp.X') := (levEnv D.sp.X' R.βX (R.datXt t)).J

def IsInertDC (R : RealDat D A Ks) (t : T) (PP : Pl D.host.E) (x : Bridge.Gf D.sp.X') (B : Finset (Bridge.Gf D.sp.X')) : Prop :=
  IsInertPl PP ∧ PP ∉ R.Sb ∧ PP ∉ R.Q t ∧ LocAt D.sp.X' (plF PP) x ∧ (∀ b ∈ B, LocAt D.sp.X' (plF PP) b) ∧
    Bridge.IsDC (levX R t) x B

abbrev InertIx (R : RealDat D A Ks) (t : T) : Type :=
  {a : Pl D.host.E × Bridge.Gf D.sp.X' × Finset (Bridge.Gf D.sp.X') // IsInertDC R t a.1 a.2.1 a.2.2}

def IsInertOp (R : RealDat D A Ks) (t : T) (i : InertIx R t) (U : Module.End ℂ (R.HX t).H) : Prop :=
  ∀ f, (R.HX t).e (U f) = Bridge.dcOp i.1.2.2 ((R.HX t).e f)

theorem IsInertOp.unique {R : RealDat D A Ks} {F : Face D A} (hC : R.Char F) {t : T} {i : InertIx R t}
    {U U' : Module.End ℂ (R.HX t).H} (h : IsInertOp R t i U) (h' : IsInertOp R t i U') : U = U' :=
  LinearMap.ext fun f => (hC.models.HX t).1 ((h f).trans (h' f).symm)

def HasResC (A : FamIn D.what₂.LL G Pl0 T D.R.m) (p : Pl0 → D.what₂.LL[X]) (x : A.ok A.μ0 × ℕ → ℂ) : Prop :=
  ∀ P : A.ok A.μ0, Col.heckePoly (A.fam.R A.μ0).n (A.fam.R A.μ0).q x P =
    (p ((A.fam.R A.μ0).pl P) * (A.fam.R A.μ0).blockProd P).map D.what₂.embLL

section Fam

variable (R : RealDat D A Ks) {I : T → Type} (lab : ∀ t, I t → InertIx R t)
  (hE : ∀ t, (A.ok t × ℕ) ⊕ I t → Module.End ℂ R.HE.H)

def IntwSplit : Prop :=
  ∀ t (i : A.ok t × ℕ) (f : (A.MtildeCSD t).Forms),
    R.Th t (R.jX t (A.heckeR t i f)) = hE t (Sum.inl i) (R.Th t (R.jX t f))

def IntwInert : Prop :=
  ∀ t (i : I t) (U : Module.End ℂ (R.HX t).H), IsInertOp R t (lab t i) U →
    R.Th t ∘ₗ U = hE t (Sum.inr i) ∘ₗ R.Th t

def Comm : Prop := Col.PairComm (hE A.μ0)

def Parts : Prop :=
  ∀ p : A.fam.base.Ix, R.EEp p = Col.eigSum (hE A.μ0) fun x => HasResC A p.1 fun i => x (Sum.inl i)

def RowsAt : Prop :=
  ∃ hE : ∀ t, (A.ok t × ℕ) ⊕ I t → Module.End ℂ R.HE.H, IntwSplit R hE ∧ IntwInert R lab hE ∧ Comm R hE ∧ Parts R hE

end Fam

def HeckeRows (R : RealDat D A Ks) : Prop := RowsAt R (I := InertIx R) fun _ i => i

def HeckeRowsSplit (R : RealDat D A Ks) : Prop := RowsAt R (I := fun _ => Empty) fun _ i => i.elim

theorem eigSum_comp {V I J : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {op : I → Module.End ℂ V}
    (hc : Col.PairComm op) (φ : J → I) (C : (J → ℂ) → Prop) :
    Col.eigSum op (fun x => C fun j => x (φ j)) = Col.eigSum (fun j => op (φ j)) C := by
  have hle : ∀ C' : (J → ℂ) → Prop,
      Col.eigSum op (fun x => C' fun j => x (φ j)) ≤ Col.eigSum (fun j => op (φ j)) C' := fun C' =>
    iSup₂_le fun x hx => le_trans (le_iInf fun j => Col.eigAt_le op x (φ j))
      (Col.eigAt_le_eigSum (op := fun j => op (φ j)) (C := C') (x := fun j => x (φ j)) hx)
  have hs : Col.SplitOver op := fun i => Module.End.iSup_maxGenEigenspace_eq_top (op i)
  have h1 := Col.isCompl_eigSum hc hs fun x => C fun j => x (φ j)
  have h2 : Disjoint (Col.eigSum (fun j => op (φ j)) C) (Col.eigSum (fun j => op (φ j)) fun y => ¬ C y) :=
    Col.disjoint_eigSum (fun j j' => hc (φ j) (φ j')) fun _ h h' => h' h
  exact eq_of_le_of_inf_le_of_le_sup (hle C)
    (le_of_eq_of_le (h2.mono_right (hle fun y => ¬ C y)).eq_bot bot_le)
    (le_of_le_of_eq le_top h1.sup_eq_top.symm)

theorem HeckeRows.rowsAt {R : RealDat D A Ks} (h : HeckeRows R) {I : T → Type} (lab : ∀ t, I t → InertIx R t) :
    RowsAt R lab := by
  obtain ⟨hE, h1, h2, h3, h4⟩ := h
  refine ⟨fun t i => hE t (Sum.map id (lab t) i), h1, fun t i U hU => h2 t (lab t i) U hU, fun i j => h3 _ _, fun p => ?_⟩
  rw [h4 p]
  exact eigSum_comp h3 (Sum.map id (lab A.μ0)) fun x => HasResC A p.1 fun i => x (Sum.inl i)

theorem HeckeRows.split {R : RealDat D A Ks} (h : HeckeRows R) : HeckeRowsSplit R := h.rowsAt _

def Statement : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → HeckeRows R

def StatementAt (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → HeckeRows R

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InertLocalIndices
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Polynomial
open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertLocalIndices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def InertOver (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Formalism.L2.DIV.Pl D.host.E) : Prop :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = P.asIdeal

def LocAt (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Bridge.Gf V) : Prop :=
  ∀ v' : HeightOneSpectrum (𝓞 D.host.F), v' ≠ v →
    (Units.val (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).map
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v') (AlgHom.id D.host.F D.host.E)) = 1

theorem locAt_one (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : LocAt V v 1 := by
  intro v' _
  simp only [OneMemClass.coe_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def HasResC (A : FamIn D.what₂.LL G Pl0 T D.R.m) (p : Pl0 → D.what₂.LL[X]) (x : A.ok A.μ0 × ℕ → ℂ) : Prop :=
  ∀ P : A.ok A.μ0, Col.heckePoly (A.fam.R A.μ0).n (A.fam.R A.μ0).q x P =
    (p P.1 * (A.fam.R A.μ0).blockProd P).map D.what₂.embLL

theorem hasResC_map (p : Pl0 → D.what₂.LL[X]) (x : A.ok A.μ0 × ℕ → D.what₂.LL) :
    HasResC A p (fun i => D.what₂.embLL (x i)) ↔ (A.fam.R A.μ0).HasRes p x := by
  refine forall_congr' fun P => ?_
  have h : Col.heckePoly (A.fam.R A.μ0).n (A.fam.R A.μ0).q (fun i => D.what₂.embLL (x i)) P =
      (Col.heckePoly (A.fam.R A.μ0).n (A.fam.R A.μ0).q x P).map D.what₂.embLL := by
    unfold Col.heckePoly
    rw [Col.map_heckePolyOf]
  exact (Eq.congr h rfl).trans (Polynomial.map_injective _ D.what₂.embLL.injective).eq_iff

variable (R : RealDat D A Ks)

abbrev levX (t : T) : Subgroup (Bridge.Gf D.sp.X') := (levEnv D.sp.X' R.βX (R.datXt t)).J

structure InertIx (t : T) where

  v : HeightOneSpectrum (𝓞 D.host.F)

  P : Formalism.L2.DIV.Pl D.host.E
  inert : InertOver v P
  offG : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
  offS : P ∉ R.Sb
  offQ : P ∉ R.Q t

  x : Bridge.Gf D.sp.X'
  loc : LocAt D.sp.X' v x

def InertIx.unit (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Formalism.L2.DIV.Pl D.host.E) (h1 : InertOver v P)
    (h2 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (h3 : P ∉ R.Sb) (h4 : P ∉ R.Q t) : InertIx R t :=
  ⟨v, P, h1, h2, h3, h4, 1, locAt_one _ _⟩

def InertTie (TI : ∀ t, InertIx R t → Module.End ℂ (R.HX t).H) : Prop :=
  ∀ (t : T) (i : InertIx R t), ∃ reps : Finset (Bridge.Gf D.sp.X'),
    Bridge.IsDC (levX R t) i.x reps ∧ (∀ a ∈ reps, LocAt D.sp.X' i.v a) ∧
      ∀ f : (R.HX t).H, (R.HX t).e (TI t i f) = Bridge.dcOp reps ((R.HX t).e f)

def IntwSplit (t : T) (i : A.ok t × ℕ) (S : Module.End ℂ R.HE.H) : Prop :=
  ∀ f : (A.MtildeCSD t).Forms, R.Th t (R.jX t (A.heckeR t i f)) = S (R.Th t (R.jX t f))

def SplitRows : Prop :=
  ∃ hE : ∀ t : T, A.ok t × ℕ → Module.End ℂ R.HE.H,
    (∀ t i, IntwSplit R t i (hE t i)) ∧
    Col.PairComm (hE A.μ0) ∧
    ∀ p : A.fam.base.Ix, R.EEp p = Col.eigSum (hE A.μ0) (HasResC A p.1)

abbrev SphIx (t : T) : Type := (A.ok t × ℕ) ⊕ InertIx R t

def FullRowsFor (TI : ∀ t, InertIx R t → Module.End ℂ (R.HX t).H) : Prop :=
  ∃ hE : ∀ t : T, SphIx R t → Module.End ℂ R.HE.H,
    (∀ t i, IntwSplit R t i (hE t (Sum.inl i))) ∧
    (∀ t i, R.Th t ∘ₗ TI t i = hE t (Sum.inr i) ∘ₗ R.Th t) ∧
    Col.PairComm (hE A.μ0) ∧
    ∀ p : A.fam.base.Ix, R.EEp p = Col.eigSum (hE A.μ0) fun x => HasResC A p.1 fun i => x (Sum.inl i)

def FullRows : Prop :=
  ∀ TI : ∀ t, InertIx R t → Module.End ℂ (R.HX t).H, InertTie R TI → FullRowsFor R TI

def HeckeRows (F : Face D A) : Prop :=
  R.Char F → SplitRows R ∧ FullRows R

end GlobalTheory.IndefiniteRowSideFullHecke.InertLocalIndices

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LocalTransferIntertwiners
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.InertSphericalIndices

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsInertPl (P : Pl D.host.E) : Prop :=
  Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal

def IsLocA (V : HSp D) (P : Pl D.host.E) (α : GA D V) : Prop :=
  α ∈ GfC V ∧ ∃ ε : AF D.host.F, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧
    ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (mt V α - 1) a b = (mt V α - 1) a b

def IsLocF (V : HSp D) (P : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ α : GA D V, IsLocA V P α ∧ (x : GL _ _) = finHom V α

def InertIx (V : HSp D) : Type := {y : Pl D.host.E × Bridge.Gf V // IsInertPl y.1 ∧ IsLocF V y.1 y.2}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (A) in

abbrev SphIx (j : Fin D.R.m) (t : T) : Type := (A.ok t × ℕ) ⊕ InertIx (Vc D j)

variable (R : RealDat D A Ks) (F : Face D A)

def IsSphOp (j : Fin D.R.m) (t : T) : SphIx A j t → Module.End ℂ (R.HV j t).H → Prop
  | Sum.inl i, TV => ∀ f : (A.MtCSD j t).Forms, TV (R.jV j t f) = R.jV j t (A.heckeL j t i f)
  | Sum.inr y, TV => ∃ B : Finset (Bridge.Gf (Vc D j)),
      Bridge.IsDC (levEnv (Vc D j) (R.βV j) (R.datVt j t)).J y.1.2 B ∧ (∀ a ∈ B, IsLocF (Vc D j) y.1.1 a) ∧
        ∀ f, (R.HV j t).e (TV f) = Bridge.dcOp B ((R.HV j t).e f)

variable (A) in

def HasResC (j : Fin D.R.m) (Sg : Pl0 → D.what₂.LL[X]) (x : SphIx A j A.μ0 → ℂ) : Prop :=
  ∀ P : A.ok A.μ0, Formalism.L2.Col.heckePolyOf (A.r + A.t) (A.q P) (fun k => x (Sum.inl (P, k))) =
    (Sg P * (A.fam.L j A.μ0).blockProd P).map D.what₂.embLL

abbrev OpsV : Type := ∀ (j : Fin D.R.m) (t : T), SphIx A j t → Module.End ℂ (R.HV j t).H

abbrev OpsW : Type := ∀ (j : Fin D.R.m) (t : T), SphIx A j t → Module.End ℂ (R.HW j (sg0 D A)).H

def Intw (TV : OpsV R) (hW : OpsW R) : Prop :=
  ∀ j t i, R.thG j t ∘ₗ TV j t i = hW j t i ∘ₗ R.thG j t

def Comm (hW : OpsW R) : Prop := ∀ j, Formalism.L2.Col.PairComm (hW j A.μ0)

def Parts (hW : OpsW R) : Prop :=
  ∀ j (p : A.fam.base.Ix), R.Wp j p =
    Formalism.L2.Col.eigSum (hW j A.μ0) (HasResC A j (trLift A.r D.R.m A.t A.q A.etaVal p.1))

def HeckeOps : Prop :=
  ∃ (TV : OpsV R) (hW : OpsW R), (∀ j t i, IsSphOp R j t i (TV j t i)) ∧ Intw R TV hW ∧ Comm R hW ∧ Parts R hW

def HeckeLifts : Prop := R.Char F → HeckeOps R

def goodPr (j : Fin D.R.m) : Module.End ℂ (R.HW j (sg0 D A)).H :=
  ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW j (sg0 D A) g

def IsOpW (j : Fin D.R.m) (α : GA D (Wc D j)) (TW : Module.End ℂ (R.HW j (sg0 D A)).H) : Prop :=
  ∃ B : Finset (GA D (Wc D j)), Bridge.IsDC (levG _ (R.βW j) (R.datWp j R.triv)) α B ∧
    ∀ f, (R.HW j (sg0 D A)).e (TW f) = heckeOn (R.MW j (sg0 D A)) B ((R.HW j (sg0 D A)).e f)

def IsTransfer (j : Fin D.R.m) (t : T) : SphIx A j t → Module.End ℂ (R.HW j (sg0 D A)).H → Prop
  | Sum.inl i, H => ∃ TW : ℕ → Module.End ℂ (R.HW j (sg0 D A)).H,
      (∀ a ≤ (Wc D j).rank, ∃ α, IsHeckeAt (Wc D j) (R.pl i.1) a α ∧ IsOpW R j α⁻¹ (TW a)) ∧
      ((-1) ^ i.2 * (A.q i.1 : ℂ) ^ (i.2 * (i.2 - 1) / 2)) • H =
        ∑ a ∈ Finset.range (min i.2 (Wc D j).rank + 1),
          ((-1) ^ a * (A.q i.1 : ℂ) ^ (a * (a - 1) / 2) *
            (D.what₂.embLL (A.etaVal i.1 : D.what₂.LL) * (A.q i.1 : ℂ) ^ ((A.t + 1) / 2)) ^ a *
            D.what₂.embLL (((A.fam.L j t).blockProd i.1).coeff (i.2 - a))) • (TW a * goodPr R j)
  | Sum.inr y, H => H ∈ Submodule.span ℂ
      {H' | ∃ α TW, IsLocA (Wc D j) y.1.1 α ∧ IsOpW R j α TW ∧ H' = TW * goodPr R j}

def HeckeOpsNamed : Prop :=
  ∃ (TV : OpsV R) (hW : OpsW R), (∀ j t i, IsSphOp R j t i (TV j t i)) ∧ (∀ j t i, IsTransfer R j t i (hW j t i)) ∧
    Intw R TV hW ∧ Comm R hW ∧ Parts R hW

def HeckeLiftsNamed : Prop := R.Char F → HeckeOpsNamed R

theorem HasResC.zero {j : Fin D.R.m} {Sg : Pl0 → D.what₂.LL[X]} {x : SphIx A j A.μ0 → ℂ} (h : HasResC A j Sg x) (P : A.ok A.μ0) :
    x (Sum.inl (P, 0)) = D.what₂.embLL ((Sg P * (A.fam.L j A.μ0).blockProd P).coeff 0) := by
  have h0 := congrArg (fun f : ℂ[X] => f.coeff 0) (h P)
  simp only [Formalism.L2.Col.heckePolyOf, finset_sum_coeff, coeff_C_mul_X_pow, coeff_map] at h0
  rw [← h0, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
  · intro hb
    simp at hb

end GlobalTheory.IndefiniteRowSideFullHecke.InertSphericalIndices

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LocalizationParts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalHeckeLifts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLocAt (V : HSp D) (PP : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ (f : AE D) (α : GA D V), Formalism.L2.JoinChr.IsPlIdem D f PP ∧ α ∈ GfC V ∧ Mult.SuppF V f α ∧ (x : GL _ _) = finHom V α

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev levV (R : RealDat D A Ks) (j : Fin D.R.m) (t : T) : Subgroup (Bridge.Gf (Vc D j)) :=
  (levEnv (Vc D j) (R.βV j) (R.datVt j t)).J

def IsInertOp (R : RealDat D A Ks) (j : Fin D.R.m) (t : T)
    (a : Pl D.host.E × Bridge.Gf (Vc D j) × Finset (Bridge.Gf (Vc D j))) : Prop :=
  Lev.IsConjPl a.1 a.1 ∧ a.1 ∉ R.Sb ∧ a.1 ∉ R.Q t ∧ IsLocAt (Vc D j) a.1 a.2.1 ∧
    (∀ y ∈ a.2.2, IsLocAt (Vc D j) a.1 y) ∧ Bridge.IsDC (levV R j t) a.2.1 a.2.2

abbrev InertOp (R : RealDat D A Ks) (j : Fin D.R.m) (t : T) : Type := {a // IsInertOp R j t a}

abbrev SphOp (R : RealDat D A Ks) (j : Fin D.R.m) (t : T) : Type := (A.ok t × ℕ) ⊕ InertOp R j t

abbrev OpW (R : RealDat D A Ks) : Type :=
  ∀ (j : Fin D.R.m) (t : T), SphOp R j t → Module.End ℂ (R.HW j (sg0 D A)).H

def Intertwines (R : RealDat D A Ks) (hW : OpW R) : Prop :=
  ∀ (j : Fin D.R.m) (t : T),
    (∀ (i : A.ok t × ℕ) (f : (A.MtCSD j t).Forms),
      R.thG j t (R.jV j t (A.heckeL j t i f)) = hW j t (Sum.inl i) (R.thG j t (R.jV j t f))) ∧
    ∀ a : InertOp R j t, ∃ TV : Module.End ℂ (R.HV j t).H,
      (∀ x, (R.HV j t).e (TV x) = Bridge.dcOp a.1.2.2 ((R.HV j t).e x)) ∧
        R.thG j t ∘ₗ TV = hW j t (Sum.inr a) ∘ₗ R.thG j t

def Commutes (R : RealDat D A Ks) (hW : OpW R) : Prop := ∀ j, Formalism.L2.Col.PairComm (hW j A.μ0)

def HasResC {K : Type} [Field K] [NumberField K] [StarRing K] (B : BlockDat K G Pl0) (σ : K →+* ℂ)
    (Sg : Pl0 → K[X]) (x : B.Pl × ℕ → ℂ) : Prop :=
  ∀ P, Formalism.L2.Col.heckePoly B.n B.q x P = (Sg (B.pl P) * B.blockProd P).map σ

def Parts (R : RealDat D A Ks) (hW : OpW R) : Prop :=
  ∀ (j : Fin D.R.m) (p : A.fam.base.Ix),
    R.Wp j p = Formalism.L2.Col.eigSum (hW j A.μ0) fun x =>
      HasResC (A.fam.L j A.μ0) D.what₂.embLL (trLift A.r D.R.m A.t A.q A.etaVal p.1) fun i => x (Sum.inl i)

def HeckeLiftsAt (R : RealDat D A Ks) : Prop :=
  ∃ hW : OpW R, Intertwines R hW ∧ Commutes R hW ∧ Parts R hW

def HeckeLifts : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → HeckeLiftsAt R

end GlobalTheory.IndefiniteRowSideFullHecke.LocalHeckeLifts

end
end

