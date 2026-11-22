import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FDMSubCompact
import ReciprocityTheory.AdeleApproximation.AdeleIntA

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.RestrictedBlockMemBlockTriangular
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Matrix NumberField IsDedekindDomain
open Formalism.IndefR.Datum (LowZero topL omegaG omegaQ omegaK)

namespace Formalism.IndefR.Fin.LevelGroupLemmas

section Mat
variable {κ : Type} [CommRing κ]

end Mat

section GlobalTheory
variable {κ : Type} [CommRing κ]

end GlobalTheory

section Omega
variable {D : D7}

def valG {a : ℕ} (L : LevDat D.host.E ℂ a) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1)) : ℂ :=
  ((ext1 L.P.H L.P.chi (fun PP => upperLeftBlock L.hr (g PP)) : ℂˣ) : ℂ) *
    (∏ PP : ↥L.Pg, ∏ c ∈ Finset.range L.s,
      ((L.cg (c + 1) PP.1 (dBlk (blkOf L.r L.t) (c + 1) (g PP)) : ℂˣ) : ℂ)) *
    ∏ PP : ↥L.Pg, (((χj PP.1 (Matrix.GeneralLinearGroup.det (g PP))) : ℂˣ) : ℂ)⁻¹

end Omega

section Conj
variable {D : D7}

end Conj

section Q
variable {D : D7}

end Q

section Det
variable {κ : Type} [CommRing κ]

end Det

section Lev
open scoped TensorProduct
variable {D : D7}

def levUnit {n : ℕ} (L : LevDat D.host.E ℂ n) (x : ∀ PP : Pl D.host.E, GL (Fin n) (kP PP)) : ℂˣ :=
  ext1 L.P.H L.P.chi (fun PP : ↥L.Pg => upperLeftBlock L.hr (x PP.1)) *
    (∏ PP ∈ L.Pg, ∏ c ∈ Finset.range L.s, L.cg (c + 1) PP (dBlk (blkOf L.r L.t) (c + 1) (x PP))) *
    ∏ PP ∈ L.Q, L.xq PP (dBlk (blk2 L.r) 1 (x PP))

end Lev

section Laws
variable {D : D7}

end Laws

section Bridge
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

end Bridge

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.VacExApp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC Formalism.IndefR.Eqv
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

end Gen

variable {D : D7}

theorem AF_ext' {p q : AF D.host.F} (h1 : fstA D.host.F p = fstA D.host.F q) (h2 : sndA D.host.F p = sndA D.host.F q) :
    p = q :=
  Prod.ext h1 h2

theorem expand_cE (z : AE D) :
    z = ∑ k, (cE D.host.F D.host.E z k) ⊗ₜ[D.host.F] (Module.finBasis D.host.F D.host.E k) := by
  conv_lhs => rw [← (bA D.host.F D.host.E).sum_equivFun z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem mapFin_zero_iff {m n : ℕ} (x : Mx D m n) : x.map (finPart D) = 0 ↔ ∀ i j, finPart D (x i j) = 0 :=
  ⟨fun h i j => by simpa using congrFun (congrFun h i) j, fun h => by ext i j; simpa using h i j⟩

def Ps (m n : ℕ) (p : Fin m → Fin n → Fin (nE D) → AF D.host.F) : Mx D m n :=
  Matrix.of fun i j => (cE D.host.F D.host.E).symm (p i j)

theorem continuous_Ps {m n : ℕ} : Continuous (Ps (D := D) m n) :=
  continuous_matrix fun i j =>
    (cE D.host.F D.host.E).symm.continuous.comp ((continuous_apply j).comp (continuous_apply i))

def boxB (D : D7) (m n : ℕ) : Set (Mx D m n) :=
  Ps m n '' Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
    (fun a : Af D.host.F => pairA D.host.F 0 a) '' Ohat D.host.F

theorem isCompact_boxB (m n : ℕ) : IsCompact (boxB D m n) := by
  have hc : Continuous fun a : Af D.host.F => pairA D.host.F 0 a := by
    unfold pairA; exact continuous_const.prodMk continuous_id
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    (isCompact_Ohat D.host.F).image hc).image continuous_Ps

theorem nsmul_pairA (N : ℕ) (a : Af D.host.F) : N • pairA D.host.F 0 a = pairA D.host.F 0 (N • a) := by
  refine AF_ext' ?_ ?_
  · rw [map_nsmul]; show N • (0 : Ainf D.host.F) = 0; exact nsmul_zero N
  · rw [map_nsmul]; rfl

def infiniteTranslateSubgroup {m n : ℕ} (Λ : AddSubgroup (Mx D m n)) : AddSubgroup (Mx D m n) where
  carrier := {w | ∃ u ∈ Λ, (w - u).map (finPart D) = 0}
  add_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u + u', Λ.add_mem hu hu', (mapFin_zero_iff _).2 fun i j => ?_⟩
    have h1 := (mapFin_zero_iff _).1 ha i j
    have h2 := (mapFin_zero_iff _).1 hb i j
    have : (a + b - (u + u')) i j = (a - u) i j + (b - u') i j := by
      simp only [Matrix.sub_apply, Matrix.add_apply]; abel
    rw [this, map_add, h1, h2, add_zero]
  zero_mem' := ⟨0, Λ.zero_mem, by simp⟩
  neg_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨-u, Λ.neg_mem hu, (mapFin_zero_iff _).2 fun i j => ?_⟩
    have h1 := (mapFin_zero_iff _).1 ha i j
    have : (-a - -u) i j = -((a - u) i j) := by simp only [Matrix.sub_apply, Matrix.neg_apply]; abel
    rw [this, map_neg, h1, neg_zero]

end Formalism.IndefR.Fin.VacEx
end
end

