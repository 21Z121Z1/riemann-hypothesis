import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle0003
import Formalism.LocalRingCardinality.DataKerI

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem emb_mul {R : Ranks} (H : Host R) (g g' : R.GG) (x : H.E) : H.emb (g * g') x = H.emb g (H.sigmaOf g' x) := by
  show H.φ₀ ((H.sigmaOf (g * g')) x) = H.φ₀ ((H.sigmaOf g) ((H.sigmaOf g') x))
  simp only [Formalism.BasicNotions.Host.sigmaOf, map_mul, AlgEquiv.mul_apply]

theorem sigmaOf_pow {R : Ranks} (H : Host R) (g : R.GG) (s : ℕ) (x : H.E) :
    H.sigmaOf (g ^ s) x = ((H.sigmaOf g) ^ s) x := by
  simp only [Formalism.BasicNotions.Host.sigmaOf, map_pow]

variable {p : ℕ} [Fact p.Prime] {W Qq Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [Field Kf]

def PosCompat {R : Ranks} (H : Host R) (h : R.MA) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    (iw : Fin (nOrb (zPsi R.toFrame h)) → (H.E →+* Qq)) (iK : Kf →+* ℂ_[p]) (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) : Prop :=
  ∀ (v : Fin (nOrb (zPsi R.toFrame h))) (s : Fin (orderOf (zPsi R.toFrame h))) (x : H.E),
    iK (ι ((σ ^ s.val) (iw v x))) =
      lamV lam (H.emb (((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) * R.cc ^ s.val) x)

theorem posCompat_of_base {R : Ranks} (H : Host R) (h : R.MA) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    (iw : Fin (nOrb (zPsi R.toFrame h)) → (H.E →+* Qq)) (iK : Kf →+* ℂ_[p]) (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p])
    (hbase : ∀ v x, iK (ι (iw v x)) = lamV lam (H.emb ((orbRep (zPsi R.toFrame h) v : R.Psi) : R.GG) x))
    (hfrob : ∀ v x, σ (iw v x) = iw v (H.sigmaOf ((c0, h) : R.GG) x)) :
    PosCompat H h ι σ iw iK lam := by
  intro v s x
  have key : ∀ (k : ℕ) (y : H.E), (σ ^ k) (iw v y) = iw v ((H.sigmaOf ((c0, h) : R.GG) ^ k) y) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih =>
      intro y
      rw [pow_succ, pow_succ]
      show (σ ^ k) (σ (iw v y)) = iw v ((H.sigmaOf ((c0, h) : R.GG) ^ k) (H.sigmaOf ((c0, h) : R.GG) y))
      rw [hfrob, ih]
  have e1 : ((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) * R.cc ^ s.val =
      ((orbRep (zPsi R.toFrame h) v : R.Psi) : R.GG) * ((c0, h) : R.GG) ^ s.val := by
    rw [posG_apply, Subgroup.coe_mul, Subgroup.coe_pow, mul_assoc]
    congr 1
    show ((1, h) : R.GG) ^ s.val * (c0, 1) ^ s.val = ((c0, h) : R.GG) ^ s.val
    ext <;> simp
  rw [e1, emb_mul, sigmaOf_pow, key, hbase]

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

abbrev gatOfLevelP (L : ColLevel R F E sp gp C A clsLat) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) : GAtP p :=
  gatOfLevel L hS nV r lam0 dom hk I ψ (repP L p) e

def gatOfLevelP_tie (L : ColLevel R F E sp gp C A clsLat) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) :
    Formalism.L2.Herm.GLevTie L (gatOfLevelP L hS nV r lam0 dom hk I ψ e) :=
  gatOfLevel_tie L hS nV r lam0 dom hk I ψ (repP L p) e (repP_mk L p) (repP_over L p)

end Level

section Record

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

abbrev gatRecP (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) : GAtP p :=
  gatRec D u h hS r L I ψ (repP L p) e

def gatRecP_lev (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) :
    Formalism.L2.Herm.GLevTie L (gatRecP D u h hS r L I ψ e) :=
  gatRec_lev D u h hS r L I ψ (repP L p) e (repP_mk L p) (repP_over L p)

end Record

end Formalism.L2.G
end
end

