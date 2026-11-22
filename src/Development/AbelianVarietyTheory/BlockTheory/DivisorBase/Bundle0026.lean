import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataRRMetric

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BaseSetLabels
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseSetLabels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (D) in

abbrev Eig : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

variable (D) in

def IsBaseSet (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ v, v ∈ S ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal

def dualEig (c : Eig D) : Eig D := fun P d => c P (dualLab d)

section Concrete

variable (R : RealDat D A Ks) (F : Face D A) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def EEc (P : LevelP R.Pg D.R.r ℂ) (c : Eig D) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) S c ⊓ R.EEat P).comap R.HE.e

def Wc' (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (c : Eig D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) S c ⊓
    R.Wat i (sg0 D A) P).comap (R.HW i (sg0 D A)).e

def OccW (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (c : Eig D) : Prop :=
  c ∈ IxFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) S (R.eWf i (sg0 D A))

def OccE (P : LevelP R.Pg D.R.r ℂ) (c : Eig D) : Prop :=
  dualEig c ∈ IxFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) S R.e0

abbrev conjugateBaseLevel : LevelP R.Pg D.R.r ℂ := R.levL F false (sg0 D A)

def hPol (c : Eig D) (P : Pl0) : ℂ[X] :=
  Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)

def IsLabel (c : Eig D) (p : A.fam.base.Ix) : Prop :=
  ∀ P ∈ A.ok A.μ0, RealDat.polW (A := A) p.1 P = hPol R c P

def Occurs (c : Eig D) : Prop :=
  (∃ i, OccW R S i (conjugateBaseLevel R F) c) ∨ OccE R S R.triv c ∨ ∃ b, OccE R S (R.levR F b) c

def SplitDetermines : Prop :=
  ∀ c c', Occurs R F S c → Occurs R F S c' → (∀ P ∈ A.ok A.μ0, hPol R c P = hPol R c' P) → c = c'

end Concrete

section Ties

variable (R : RealDat D A Ks) (F : Face D A) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {X : DivX D} (E : EigIdx D X)
  (eig : E.Pi → Eig D) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H)
  (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H)

def TieIdx : Prop :=
  Function.Injective eig ∧ ∀ c, c ∈ Set.range eig ↔ ∃ i, OccW R S i (conjugateBaseLevel R F) c

def TieRows : Prop :=
  Function.Injective jE ∧ LinearMap.range jE = (R.EEat (R.levR F true)).comap R.HE.e ∧
    ∀ π, (DV.EEcpart D E π).map jE = EEc R S (R.levR F true) (eig π)

def TieLifts : Prop :=
  ∀ i, Function.Injective (jW i) ∧
    LinearMap.range (jW i) = (R.Wat i (sg0 D A) (conjugateBaseLevel R F)).comap (R.HW i (sg0 D A)).e ∧
    ∀ π, (DV.sum₃ E ((i : ℕ) + 1) π).map (jW i) = Wc' R S i (conjugateBaseLevel R F) (eig π)

def Tied : Prop :=
  IsBaseSet D S ∧ TieIdx R F S E eig ∧ TieRows R F S E eig jE ∧ TieLifts R F S E eig jW

def HasLabel : Prop := ∀ π, ∃ p, IsLabel R (eig π) p

def LabelInj : Prop := ∀ π π' p, IsLabel R (eig π) p → IsLabel R (eig π') p → π = π'

def PartRows : Prop := ∀ π p, IsLabel R (eig π) p → (DV.EEcpart D E π).map jE ≤ R.EEp p

def PartLifts : Prop :=
  ∀ (i : Fin D.R.m) π p, IsLabel R (eig π) p → (DV.sum₃ E ((i : ℕ) + 1) π).map (jW i) ≤ R.Wp i p

def PartsAt : Prop :=
  HasLabel R E eig ∧ LabelInj R E eig ∧ PartRows R E eig jE ∧ PartLifts R E eig jW

end Ties

def PartsSt (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (s : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (X : DivX D) (E : EigIdx D X) (eig : E.Pi → Eig D)
    (jE : D.what₂.EE →ₗ[ℂ] R.HE.H) (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H),
    A.fam.Ok s → R.Char F → Tied R F S E eig jE jW → PartsAt R E eig jE jW

section Basic₂

variable {R : RealDat D A Ks} {F : Face D A} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {X : DivX D} {E : EigIdx D X}
  {eig : E.Pi → Eig D} {jE : D.what₂.EE →ₗ[ℂ] R.HE.H}
  {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

example : dualLab (splitLab 3 1) = [1, 0, 0] := by decide

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.BaseSetLabels

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PinnedIntegrability
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PinnedIntegrability

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def integrand (i : Fin D.R.m) (t : T) (f : GA D (Vc D i) → (R.cV i).W) (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)) :
    GA D (Vc D i) → ℂ :=
  fun h => thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i e (f h)))

structure Pinned : Prop where
  lev : R.toLevCh.Is A.μ0
  inf : R.models_inf
  vpos : RealDat.models_vpos (D := D)
  cV : R.models_cV
  HV : R.models_HV
  νV : R.models_νV
  BV : R.models_BV
  order : R.models_order
  ωP : R.thP_ωP
  vP : R.thP_vP
  pt_theta : R.thP_pt_theta
  ioP : R.thP_ioP

def IntegrableAll : Prop :=
  ∀ (i : Fin D.R.m) (t : T), ∀ f ∈ LinearMap.range (R.extV i t), ∀ (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)),
    IntegrableOn (integrand R i t f e g) (R.fdV i t) (R.νV i t)

end

def ThetaIntegrandIntegrable : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    Pinned R → IntegrableAll R

end GlobalTheory.IndefiniteRowSideFullHecke.PinnedIntegrability

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisedDualSystem
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def dualSys (c : Sys D) : Sys D := fun P d => c P (dualLab d)

open Classical in

def badF (R : RealDat D A Ks) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def partE (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (c : Sys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) (badF R) c ⊓ R.EEat P

def partW (R : RealDat D A Ks) (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (c : Sys D) :
    Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) (badF R) c ⊓
    R.Wat i (sg0 D A) P

def OccE (R : RealDat D A Ks) (c : Sys D) : Prop :=
  dualSys c ∈ IxFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R) R.e0

def OccW (R : RealDat D A Ks) (i : Fin D.R.m) (c : Sys D) : Prop :=
  c ∈ IxFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (badF R)
    (R.eWf i (sg0 D A))

def Occ (R : RealDat D A Ks) (c : Sys D) : Prop := OccE R c ∨ ∃ i, OccW R i c

def polAt (R : RealDat D A Ks) (c : Sys D) (P : Pl0) : ℂ[X] :=
  Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)

def IsLabel (R : RealDat D A Ks) (c : Sys D) (p : A.fam.base.Ix) : Prop :=
  ∀ P ∈ A.ok A.μ0, polAt R (dualSys c) P = RealDat.polE (A := A) p.1 P

def SplitDet (R : RealDat D A Ks) : Prop :=
  ∀ c c' : Sys D, Occ R c → Occ R c' →
    (∀ P : Pl0, Formalism.IndefR.Bridge.SplitOff (R.pl P) (R.Sb : Set (Pl D.host.E)) → polAt R c P = polAt R c' P) → c = c'

variable {X : DivX D}

def IndexTie (R : RealDat D A Ks) (E : EigIdx D X) (sys : E.Pi → Sys D) : Prop :=
  Function.Injective sys ∧ (∀ c, Occ R (sys c)) ∧ ∀ s, Occ R s → ∃ c, sys c = s

def RowTie (R : RealDat D A Ks) (F : Face D A) (E : EigIdx D X) (sys : E.Pi → Sys D) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H) : Prop :=
  Function.Injective jE ∧ LinearMap.range jE = (R.EEat (R.levR F true)).comap R.HE.e ∧
    ∀ c, (DV.EEcpart D E c).map jE = (partE R (R.levR F true) (sys c)).comap R.HE.e

def LiftTie (R : RealDat D A Ks) (F : Face D A) (E : EigIdx D X) (sys : E.Pi → Sys D)
    (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H) : Prop :=
  ∀ i : Fin D.R.m, Function.Injective (jW i) ∧
    LinearMap.range (jW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e ∧
    ∀ c, (DV.sum₃ E ((i : ℕ) + 1) c).map (jW i) =
      (partW R i (R.levL F false (sg0 D A)) (sys c)).comap (R.HW i (sg0 D A)).e

def PartsOf (R : RealDat D A Ks) (E : EigIdx D X) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H) (piOf : E.Pi → A.fam.base.Ix) : Prop :=
  Function.Injective piOf ∧
    (∀ c, (DV.EEcpart D E c).map jE ≤ R.EEp (piOf c)) ∧
    ∀ (i : Fin D.R.m) c, (DV.sum₃ E ((i : ℕ) + 1) c).map (jW i) ≤ R.Wp i (piOf c)

def PartsRow (R : RealDat D A Ks) (F : Face D A) (E : EigIdx D X) : Prop :=
  ∀ s : ℕ, A.fam.Ok s → R.Char F →
    SplitDet R ∧
    ∀ (sys : E.Pi → Sys D) (jE : D.what₂.EE →ₗ[ℂ] R.HE.H)
      (jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H),
      IndexTie R E sys → RowTie R F E sys jE → LiftTie R F E sys jW →
        ∃ piOf : E.Pi → A.fam.base.Ix, (∀ c, IsLabel R (sys c) (piOf c)) ∧ PartsOf R E jE jW piOf

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

example : dualLab (splitLab 3 1) = [1, 0, 0] := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def resLow {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    MMap M →ₗ[ℂ] MultilinearMap ℂ (fun ρ : D.what₂.Tau => lowT M ρ) (GA D V → ℂ) :=
  MultilinearMap.compLinearMapₗ fun ρ => (lowT M ρ).subtype

def ResInjAt {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m), ∀ U ∈ R.Wall i (sg0 D A),
    (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, U (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) = 0) → U = 0

def ResInj : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.models_inf → ResInjAt R

theorem ResInj.of_char (h : ResInj) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F) : ResInjAt R :=
  h D G Pl0 T A Ks R hR.models.inf

end GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityChar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityChar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def VanishesOnLowest {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (U : MMap M) : Prop :=
  ∀ v : ∀ ρ, lowT M ρ, U (fun ρ => (v ρ : M.sm ρ)) = 0

def ResInjAt (R : RealDat D A Ks) : Prop :=
  ∀ i : Fin D.R.m, ∀ U ∈ R.Wall i (sg0 D A), VanishesOnLowest (R.MW i (sg0 D A)) U → U = 0

end

def ResInj : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.models_inf → R.models_order → ResInjAt R

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ResInj.of_char (h : ResInj) (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F) : ResInjAt R :=
  h D G Pl0 T A Ks R hR.lev hR.models.inf hR.models.order

theorem ResInjAt.ext {R : RealDat D A Ks} (h : ResInjAt R) (i : Fin D.R.m) {U U' : MMap (R.MW i (sg0 D A))}
    (hU : U ∈ R.Wall i (sg0 D A)) (hU' : U' ∈ R.Wall i (sg0 D A))
    (e : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, U (fun ρ => v ρ) = U' (fun ρ => v ρ)) : U = U' := by
  refine sub_eq_zero.1 (h i _ (Submodule.sub_mem _ hU hU') fun v => ?_)
  rw [MultilinearMap.sub_apply, e v, sub_self]

theorem ResInjAt.good {R : RealDat D A Ks} (h : ResInjAt R) (i : Fin D.R.m) {U : MMap (R.MW i (sg0 D A))}
    (hU : U ∈ R.Wat i (sg0 D A) R.triv) (e : VanishesOnLowest (R.MW i (sg0 D A)) U) : U = 0 :=
  h i U (goodPart_le _ _ _ _ _ hU) e

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityChar

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RowsOfLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

section Abstract

variable {G K V : Type} [Group G] [Fintype G] [Field K] [AddCommGroup V] [Module ℂ V]

def typePart (ρ : Representation ℂ G V) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ V where
  carrier := {x | ∀ g : P, ρ (g : G) x = σ ((ψ g : Kˣ) : K) • x}
  add_mem' := by
    intro x y hx hy g
    rw [map_add, hx g, hy g, smul_add]
  zero_mem' := by
    intro g
    rw [map_zero, smul_zero]
  smul_mem' := by
    intro a x hx g
    rw [map_smul, hx g, smul_comm]

open Classical in

def typeIdem (ρ : Representation ℂ G V) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) : V →ₗ[ℂ] V :=
  (Nat.card P : ℂ)⁻¹ • ∑ g : P, (σ ((ψ g : Kˣ) : K))⁻¹ • ρ (g : G)

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowsOfLevel (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (x : R.HE.H),
    R.HE.e x ∈ R.EEat (R.levR F b) ↔
      ∀ g : (F.lvl b).P, R.gE (g : G) x = D.what₂.embLL (((F.lvl b).ψ g : D.what₂.LLˣ) : D.what₂.LL) • x

def RowsOfLevelIdem (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ b : Bool, (R.EEat (R.levR F b)).comap R.HE.e =
    LinearMap.range (typeIdem R.gE D.what₂.embLL (F.lvl b).P (F.lvl b).ψ)

def RowsOfLevelCx (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ b : Bool, (R.toCx F).EEl b = LinearMap.range (typeIdem (R.gEx F) A.v0.embedding (F.lvl b).P (F.lvl b).ψ)

def RowsOfLevelAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → RowsOfLevel R F

end GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ThetaKernelFiring
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernel (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i))
    (φ : WO (Vc D i) (Wc D i) → ℂ) : ℂ :=
  thetaKO (R.ωP i t) h g φ

def Pinned (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 ∧ R.models_inf ∧ RealDat.models_vpos (D := D) ∧ R.models_cV ∧ R.models_HV ∧ R.models_νV ∧
    R.models_BV ∧ R.models_order ∧ R.thP_ωP ∧ R.thP_vP ∧ R.thP_pt_theta ∧ R.thP_ioP

def FiresAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H) : Prop :=
  (∀ (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)),
    IntegrableOn (fun h => kernel R i t g h (R.ptP i t (R.ioP i e (R.extV i t x h)))) (R.fdV i t) (R.νV i t)) ∧
  ∃ Θ ∈ R.Wall i (sg0 D A), ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
    Θ (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Lift.thetaPInt (R.νV i t) (R.fdV i t) (kernel R i t) (R.ptP i t) (R.ioP i) (R.extV i t x) (PiTensorProduct.tprod ℂ v)

def Fires (R : RealDat D A Ks) : Prop := ∀ (i : Fin D.R.m) (t : T) (x : (R.HV i t).H), FiresAt R i t x

def ThetaFiresFor (R : RealDat D A Ks) : Prop := Pinned R → Fires R

def ThetaFires : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ThetaFiresFor R

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedRowsIdempotent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.TypedRowsIdempotent

section TypeVec

variable {G K V : Type} [Group G] [Field K] [AddCommGroup V] [Module ℂ V]

def typePart (ρ : Representation ℂ G V) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ V where
  carrier := {x | ∀ g : P, ρ (g : G) x = σ ((ψ g : Kˣ) : K) • x}
  add_mem' hx hy g := by rw [map_add, hx g, hy g, smul_add]
  zero_mem' g := by rw [map_zero, smul_zero]
  smul_mem' c x hx g := by rw [map_smul, hx g, smul_comm]

open Classical in

def typeIdem [Fintype G] (ρ : Representation ℂ G V) (σ : K →+* ℂ) (P : Subgroup G) (ψ : P →* Kˣ) : V →ₗ[ℂ] V :=
  ((Nat.card P : ℂ))⁻¹ • ∑ g : P, σ (((ψ g)⁻¹ : Kˣ) : K) • ρ (g : G)

example (ρ : Representation ℂ G V) (σ : K →+* ℂ) : typePart ρ σ ⊥ 1 = ⊤ := by
  refine eq_top_iff.2 fun x _ g => ?_
  have : (g : G) = 1 := Subgroup.mem_bot.1 g.2
  simp [this]

end TypeVec

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowsOfLevel (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (x : R.HE.H), R.HE.e x ∈ R.EEat (R.levR F b) ↔
    ∀ g : (F.lvl b).P, R.gE (g : G) x = D.what₂.embLL (((F.lvl b).ψ g : D.what₂.LLˣ) : D.what₂.LL) • x

def RowsOfLevelIdem (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ b : Bool, (R.EEat (R.levR F b)).comap R.HE.e =
    LinearMap.range (typeIdem R.gE D.what₂.embLL (F.lvl b).P (F.lvl b).ψ)

def RowsOfLevelCx (R : RealDat D A Ks) (F : Face D A) : Prop :=
  ∀ (b : Bool) (x : (R.toCx F).EE), x ∈ (R.toCx F).EEl b ↔
    ∀ g : (F.lvl b).P, R.gEx F (g : G) x = A.v0.embedding (((F.lvl b).ψ g : D.what₂.LLˣ) : D.what₂.LL) • x

def RowsOfLevelOfChar (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → RowsOfLevel R F

end GlobalTheory.IndefiniteRowSideFullHecke.TypedRowsIdempotent

end
end

