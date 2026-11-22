import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOK

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.ExistsLeftInvOfIndep
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Bes

variable {A T : HSp D} {ι : A.V →ₗ[D.host.E] T.V} (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A T ι)
  (P : Matrix (Fin d.ρ) (Fin T.rank) D.host.E)

def aCo (n : GA D T) (i : Fin d.ρ) : Fin d.ρ → AE D :=
  (P.map (incA D)).mulVec ((subOne T n).mulVec (ratV fun k => d.e k i))

def bCo (n : GA D T) : Fin d.ρ → AE D := (P.map (incA D)).mulVec ((subOne T n).mulVec (ratV d.z))

def CoOK (n : GA D T) : Prop :=
  (∀ i, (subOne T n).mulVec (ratV fun k => d.e k i) = (d.e.map (incA D)).mulVec (aCo d P n i)) ∧
    (subOne T n).mulVec (ratV d.z) = (d.e.map (incA D)).mulVec (bCo d P n)

def bcF (n : GA D T) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D)
    ((∑ i : Fin d.ρ, ∑ j : Fin d.ρ, if j.1 = i.1 + 1 then incA D (d.c i) * aCo d P n j i else 0) +
      ∑ i : Fin d.ρ, if i.1 + 1 = d.ρ then incA D (d.c i) * bCo d P n i else 0))

variable {d P}

end Bes

end Formalism.IndefR.Mi

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOKg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def FramesOKg (Rl : RealDat3 D A3 Ks) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
    (NormalFrames (betaY Rl) e ev z κ s Rl.Pg Rl.Pg ∧ NormalFrame0 (betaY Rl 0) Rl.Pg Rl.Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaY Rl 0) (Rl.βW i) eW ι Rl.Pg

end Formalism.IndefR.Mi

end
end

