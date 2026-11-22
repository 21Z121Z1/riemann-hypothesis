import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

structure Places (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) where
  quad : Module.finrank F E = 2
  loc : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p
  L : ∀ p, LocE (loc p).Fp (loc p).Ep
  L_cj : ∀ p, (L p).cj = (loc p).cj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

namespace Places

variable (A : Places F E sig) {n : ℕ}

def bc (p : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) : Fin n → (A.loc p).Ep := fun i => (A.loc p).ιE (x i)

def lat (p : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (A.L p).O (Fin n → (A.loc p).Ep) :=
  Submodule.span (A.L p).O (A.bc p '' (Λ : Set (Fin n → E)))

def Ext (p : HeightOneSpectrum (𝓞 F)) (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) : Prop :=
  ∀ x, g' (A.bc p x) = A.bc p (g x)

def rat (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | ∀ p, ∃ g' ∈ K p, A.Ext p g g'}
  one_mem' := fun p => ⟨1, (K p).one_mem, fun _ => rfl⟩
  mul_mem' := by
    intro a b ha hb p
    obtain ⟨a', ha1, ha2⟩ := ha p
    obtain ⟨b', hb1, hb2⟩ := hb p
    refine ⟨a' * b', (K p).mul_mem ha1 hb1, fun x => ?_⟩
    change a' (b' (A.bc p x)) = A.bc p (a (b x))
    rw [hb2 x, ha2 (b x)]
  inv_mem' := by
    intro a ha p
    obtain ⟨a', ha1, ha2⟩ := ha p
    refine ⟨a'⁻¹, (K p).inv_mem ha1, fun x => ?_⟩
    have h := ha2 (a.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    change a'.symm (A.bc p x) = A.bc p (a.symm x)
    rw [← h, LinearEquiv.symm_apply_apply]

end Places

structure GFrames (A : Places F E sig) (r k : ℕ) where
  Hm : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E
  f : Fin (r + 1) → Fin (k + 2 * r + 1) → E
  f' : Fin (r + 1) → Fin (k + 2 * r + 1) → E
  es : Fin r → Fin (k + 2 * r + 1) → E
  es' : Fin r → Fin (k + 2 * r + 1) → E
  c : ∀ p, ((A.loc p).Fp)ˣ
  S : ∀ p, Frames (A.L p) r k
  Hm_eq : ∀ p, (S p).Hm = Hm.map (A.loc p).ιE
  f_eq : ∀ p (a : Fin (r + 1)), algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • (S p).f a = A.bc p (f a)
  f'_eq : ∀ p (a : Fin (r + 1)), algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • (S p).f' a = A.bc p (f' a)
  es_eq : ∀ p (a : Fin r), (S p).es a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)
  es'_eq : ∀ p (a : Fin r), (S p).es' a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es' a)
  c_unit : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite
  gg_fin : {p | (S p).gg = true}.Finite

namespace GFrames

variable {A : Places F E sig} {r k : ℕ} (G : GFrames A r k)

abbrev V (_ : GFrames A r k) : Type := Fin (k + 2 * r + 1) → E

abbrev GLV : Type := G.V ≃ₗ[E] G.V

abbrev Lt : Type := Submodule (𝓞 E) G.V

abbrev Dat : Type := ∀ p, (G.S p).Datum

def N : Subgroup G.GLV := A.rat fun p => (G.S p).N

def N' : Subgroup G.GLV := A.rat fun p => (G.S p).N'

def St : Subgroup G.GLV := A.rat fun p => (G.S p).St

def K0 : Subgroup G.GLV := A.rat fun p => (G.S p).K0

def H0 : Subgroup G.GLV := A.rat fun p => (G.S p).H0

def stabD (d : G.Dat) : Subgroup G.GLV :=
  A.rat fun p => (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV (d p)

def IsTerm (d : G.Dat) (Λ : G.Lt) : Prop :=
  Submodule.IsLattice E Λ ∧ ∀ p, (G.S p).IsTerm (d p) (A.lat p Λ)

def DRel (d d' : G.Dat) : Prop :=
  ∃ g : G.GLV, ∀ p, ∃ g' ∈ (G.S p).H0, A.Ext p g g' ∧ g' • d p = d' p

def LRel (Λ Λ' : G.Lt) : Prop := ∃ g ∈ G.St, Λ.map ((g : G.V →ₗ[E] G.V).restrictScalars (𝓞 E)) = Λ'

def stabL (Λ : G.Lt) : Subgroup G.GLV :=
  A.rat fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)

def mu (Λ : G.Lt) : ℝ := invVol G.K0 (G.stabL Λ)

def om (d : G.Dat) (Λ : G.Lt) : ℂ := ∏ᶠ p, (G.S p).om (d p) (A.lat p Λ)

def amp (d : G.Dat) (P : G.Lt → Prop) : ℂ :=
  ∑' o : Quot G.LRel, if G.IsTerm d o.out ∧ P o.out then (G.mu o.out : ℂ) * G.om d o.out else 0

def mass (d : G.Dat) (P : G.Lt → Prop) : ℝ≥0∞ :=
  ∑' o : Quot G.LRel, if G.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (G.mu o.out) else 0

def sumD (φ : G.Dat → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' o : Quot G.DRel, if ∃ Λ, G.IsTerm o.out Λ then
    (((G.stabD o.out : Set G.GLV).encard : ℝ≥0∞))⁻¹ * φ o.out else 0

def Gen (d : G.Dat) (Λ : G.Lt) : Prop := ∀ p, (G.S p).BBzero (d p) (A.lat p Λ)

def Om : Set (HeightOneSpectrum (𝓞 F)) := {p | (G.S p).Hp ≠ 1}

def Ht : ℝ := ∏ᶠ p, (G.S p).Hp

def ngen (d₁ : G.Dat) (Λ₁ : G.Lt) : ℝ≥0∞ :=
  G.sumD fun d => G.mass d fun Λ => G.Gen d Λ ∧
    ∀ p, ∃ h ∈ (G.S p).St, (G.S p).Fr (d p) (A.lat p Λ) = h • (G.S p).Fr (d₁ p) (A.lat p Λ₁)

def Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j)

def D (l : Fin (r + 2)) : E := lead G.Zh l

def TT : E := (∑ i, ∑ j, G.f (Fin.last r) i * G.Hm i j * sig (G.f (Fin.last r) j)) *
  ∑ i, ∑ j, G.f' (Fin.last r) i * G.Hm i j * sig (G.f' (Fin.last r) j)

def Gr : E := G.D (Fin.last (r + 1)) * sig (G.D (Fin.last (r + 1))) -
  G.TT * (G.D (Fin.last r).castSucc * sig (G.D (Fin.last r).castSucc))

end GFrames

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise

namespace GlobalTheory.HL

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

structure Coord (P : LocNG.FPair H r) (S : Frames M.L r k) where
  e : V ≃ₗ[E] S.V
  h_eq : ∀ x y, S.h (e x) (e y) = H.h x y
  f_eq : ∀ a, S.f a = e (P.A.f a)
  f'_eq : ∀ a, S.f' a = e (P.B.f a)
  es_eq : ∀ a, S.es a = e (P.A.es a)
  es'_eq : ∀ a, S.es' a = e (P.B.es a)
  T_eq : (S.T : F) = P.A.T
  T'_eq : (S.T' : F) = P.B.T
  gg_none : M.split = none → S.gg = false
  gg_some : ∀ g, M.split = some g → S.gg = true ∧ S.ϖ = g.q

namespace Coord

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

def grp : (V ≃ₗ[E] V) ≃* S.GLV where
  toFun g := (c.e.symm.trans g).trans c.e
  invFun g := (c.e.trans g).trans c.e.symm
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' a b := by ext v; simp

def lat (Λ : Submodule M.L.O V) : Submodule M.L.O S.V :=
  Λ.map ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O)

def inn (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) : Submodule M.L.O S.V :=
  c.lat ((L.comap ((H.mkW f).restrictScalars M.L.O)).map ((H.perp (H.X f)).subtype.restrictScalars M.L.O))

def dat (d : LocNG.Datum P) : S.Datum :=
  (c.inn P.A.f d.L, c.inn P.B.f d.L',
    {p | ∃ (x' : ↥(H.perp (H.X P.B.f))) (x : ↥(H.perp (H.X P.A.f))), p = (c.e x', c.e x) ∧
      ((M.split = none ∧ H.mkW P.B.f x' ∈ d.L' ∧ H.mkW P.A.f x ∈ d.L) ∨
        (H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io)})

end Coord

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.IdxInt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Frames

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def Ysp (J : ℕ) : Submodule E S.V := S.spanTo S.f J ⊔ S.spanTo S.f' J

def refB (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup (S.V × S.V) :=
  ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
    (Λ.toAddSubgroup.map (algebraMap F E S.th • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom).comap
      (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

def refU (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup S.V :=
  Λ.toAddSubgroup ⊓ (perp L S.Hm (S.Ysp J)).toAddSubgroup

def refT : AddSubgroup E :=
  (AddMonoidHom.id E + (L.cj : E →+* E).toAddMonoidHom).ker ⊓
    L.O.toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap F E ((S.ϖ : F) ^ S.a)))

abbrev MW : Type := (S.V × S.V) × S.V × E

def refA (J : ℕ) (Λ : Submodule L.O S.V) : AddSubgroup S.MW :=
  (S.refB J Λ).prod ((S.refU J Λ).prod S.refT)

def sOf (w : S.MW) : E := algebraMap F E 2⁻¹ * S.h w.2.1 w.2.1 + w.2.2

def Mv (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V) (w : S.MW) : Prop :=
  S.IsMove J d Λ w.1.1 w.1.2 w.2.1 (S.sOf w)

def MvTo (J : ℕ) (d : S.Datum) (Λ Λ₁ : Submodule L.O S.V) (w : S.MW) : Prop :=
  S.Mv J d Λ w ∧ (Λ₁ : Set S.V) = S.moved Λ w.1.1 w.2.1 (S.sOf w)

def NoLeak (Λ : Submodule L.O S.V) (u : S.V) : Prop := ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1

def InZ (u : S.V) : Prop := ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)

def chiM (j : Fin r) (d : S.Datum) (Λ : Submodule L.O S.V) (b : S.V × S.V) (u : S.V) : ℂ :=
  L.psi0 (-(algebraMap F E S.th⁻¹ *
    S.h (S.h b.1 (S.es j) • S.fr d Λ j.succ + S.h b.2 (S.es' j) • S.fr' d Λ j.succ) u))

def cK (β βJ : ℕ) : ℝ := (S.q : ℝ) ^ S.a * β / βJ

def kern (β J βJ : ℕ) (d : S.Datum) (Λ Λ₁ : Submodule L.O S.V) : ℝ :=
  S.cK β βJ * (cint (S.refA J Λ) (ind (S.MvTo J d Λ Λ₁))).re

end GlobalTheory.HL.Frames
end
end

