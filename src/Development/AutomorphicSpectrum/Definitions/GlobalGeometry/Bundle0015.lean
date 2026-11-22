import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Formalism.LocalToGlobal.Divisibility.Frames
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.HarderNarasimhan.StatementPl
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AbsAZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

structure LevelLaws (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (V : HSp D)
    (dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r) : Prop where

  hostD : H.d = D.host.d

  levA : l.A = 1

  sig : V.SigOK
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  chiTriv : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1
  dictU : ∀ σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK V l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif V (dict σ) Kf th hr ∧ ∀ g τ k, ‖dmin ((U σ).X (dict σ g).1).Gm (dict σ g).2 τ k‖ = 1
  xiAbs : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D

def absA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i)

def SizeRows (D : D7) (M : ℕ) (S L : ℝ) : Prop :=
  16 ≤ D.R.f ∧ 2 ≤ L ∧ 1 ≤ S ∧ Real.log D.R.r ≤ L ∧ Real.log D.R.f ≤ 2 * L ∧
    Real.log (dE D.host.E) ≤ 4 * D.R.f * L ∧ Real.log (Ideal.absNorm D.host.ccK) ≤ 4 * L ∧
    Real.log M ≤ 30 * L ∧ Real.log S ≤ 3 * L

def petProd {σ : c.F →+* ℂ} (U : Unf Xo c σ D.R.r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ D.R.r) (t : ℝ)
    (f g : Rul Xo c) : ℂ :=
  ((t ^ 2 : ℝ) : ℂ) * ∫ q : AutQ V, starRingEnd ℂ (rdU U f (dict q.out).1 (dict q.out).2) *
    rdU U g (dict q.out).1 (dict q.out).2 ∂(muQ1 V)

open Classical in

def gramAt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (V : HSp D)
    (dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r) (t : ℝ) {N : ℕ} (b : Fin N → Rul Xo c)
    (σ : c.F →+* ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  if GoodEmb c σ then Matrix.of fun i j => petProd (U σ) V (dict σ) t (b i) (b j)
  else (Matrix.of fun i j => petProd (U ((starRingEnd ℂ).comp σ)) V (dict ((starRingEnd ℂ).comp σ)) t (b i) (b j))ᵀ

def latCoord (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {N : ℕ}
    (b : Module.Basis (Fin N) c.F (cusp Xo c U a n)) : Submodule (𝓞 c.F) (Fin N → c.F) :=
  (GlobalTheory.AllWt.supLat (cusp Xo c U a n)).map (b.equivFun.toLinearMap.restrictScalars (𝓞 c.F))

end GlobalTheory.CompanionTheory.Ar.abelian₂
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
section
open Module NumberField IsDedekindDomain MeasureTheory
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.Lat

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

variable {K L Rl : Type} [Field K] [Field L] [AddCommGroup Rl] [Module K Rl]

open Classical in

def basV (C : Submodule K Rl) (i : Fin (finrank K C)) : C :=
  if _h : Module.Finite K C then Module.finBasis K C i else 0

open Classical in

def crdV (C : Submodule K Rl) : C →ₗ[K] (Fin (finrank K C) → K) :=
  if _h : Module.Finite K C then (Module.finBasis K C).equivFun.toLinearMap else 0

open Classical in

def resL (C C' : Submodule K Rl) (f : Rl →ₗ[K] Rl) : C →ₗ[K] C' :=
  if h : ∀ x ∈ C, f x ∈ C' then f.restrict h else 0

def matV (C C' : Submodule K Rl) (f : Rl →ₗ[K] Rl) : Matrix (Fin (finrank K C')) (Fin (finrank K C)) K :=
  Matrix.of fun k i => crdV C' (resL C C' f (basV C i)) k

variable (φ : K →+* L)

def bcVec (C : Submodule K Rl) (x : C) : Fin (finrank K C) → L := fun i => φ (crdV C x i)

def bcMap (C C' : Submodule K Rl) (f : Rl →ₗ[K] Rl) : (Fin (finrank K C) → L) →ₗ[L] (Fin (finrank K C') → L) :=
  ((matV C C' f).map φ).mulVecLin

def bcLat (C : Submodule K Rl) (M : Set Rl) : Submodule (𝓞 L) (Fin (finrank K C) → L) :=
  Submodule.span (𝓞 L) (bcVec φ C '' {x : C | (x : Rl) ∈ M})

theorem bcLat_mono (C : Submodule K Rl) {M M' : Set Rl} (h : M ⊆ M') : bcLat φ C M ≤ bcLat φ C M' :=
  Submodule.span_mono (Set.image_mono fun _ hx => h hx)

theorem bcMap_bcVec (C C' : Submodule K Rl) [Module.Finite K C] (f : Rl →ₗ[K] Rl) (x : C) :
    bcMap φ C C' f (bcVec φ C x) = bcVec φ C' (resL C C' f x) := by
  have hC : Module.Finite K C := inferInstance
  have hx : x = ∑ i, crdV C x i • basV C i := by
    simp only [crdV, basV, dif_pos hC]
    exact ((Module.finBasis K C).sum_equivFun x).symm
  funext k
  conv_rhs => rw [hx]
  simp only [bcMap, bcVec, matV, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply,
    map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

open Classical in

def preF (z : L) : K := if h : ∃ a, φ a = z then h.choose else 0

theorem preF_spec {z : L} (h : ∃ a, φ a = z) : φ (preF φ z) = z := by
  unfold preF; rw [dif_pos h]; exact h.choose_spec

end BC

section OLat

variable {K Rl : Type} [Field K] [NumberField K] [CommRing Rl] [Algebra K Rl] [Algebra (𝓞 K) Rl] [IsScalarTower (𝓞 K) K Rl]

def supLat (C : Submodule K Rl) (Vs : HeightOneSpectrum (𝓞 K) → Set (Rl → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) :
    Submodule (𝓞 K) Rl :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_supLat (C : Submodule K Rl) (Vs : HeightOneSpectrum (𝓞 K) → Set (Rl → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (f : Rl) : f ∈ supLat C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hf, h⟩
    exact ⟨⟨f, hf⟩, h, rfl⟩

end OLat

section SecZ

variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

def secWZ (e : ι → ℤ) : Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

theorem secWZ_nat (e : ι → ℕ) : secWZ pts mapR borR (fun i => (e i : ℤ)) = secW pts mapR borR e := by
  have hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ), ((∏ i, t i ^ (e i : ℤ) : (p.R)ˣ) : p.R) = wchar e t := fun p t => by
    simp [wchar]
  ext f
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' h => by rw [h2 p t y y' h, hw]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p t y y' h => by rw [h2 p t y y' h, hw]⟩

end SecZ

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

abbrev ExZ (E : Type) [Field E] : Type := (E →+* ℂ) × ℕ → ℤ

def exZ (Dw : Datum H) (a : ExZ E) (n : ℕ) : Ix Dw → ℤ
  | none => n
  | some x => a (x.1, x.2)

variable (Xo : Moduli Dw l) (c : Coeff l)

def secZ (a : ExZ E) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  secWZ (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (exZ Dw a n)

theorem secZ_nat (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : secZ Xo c (fun x => (a x : ℤ)) n = sec Xo c a n := by
  have he : exZ Dw (fun x => (a x : ℤ)) n = fun i => (ex Dw a n i : ℤ) := funext fun i => by cases i <;> rfl
  unfold secZ sec
  rw [he, secWZ_nat]

variable {Xo c} {r : ℕ}

open Classical in

def laZ {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : ExZ E) (n : ℕ) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then
      a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) + ((n / 2 : ℕ) : ℤ)
    else -a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) - ((n / 2 : ℕ) : ℤ)

theorem laZ_nat {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    laZ U (fun x => (a x : ℤ)) n = laU U a n := rfl

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspZ (a : ExZ E) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  secZ Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a n)).comap (rdU (U σ))

theorem cuspZ_nat (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cuspZ U (fun x => (a x : ℤ)) n = cusp Xo c U a n := by
  unfold cuspZ cusp
  rw [secZ_nat]
  rfl

def latZ (a : ExZ E) (n : ℕ) : Submodule (𝓞 c.F) (Rul Xo c) :=
  supLat (cuspZ U a n) (valSet Xo c (algCls Xo c)) fun la => isVal_valSet la

theorem mem_latZ (a : ExZ E) (n : ℕ) (f : Rul Xo c) :
    f ∈ latZ U a n ↔ f ∈ cuspZ U a n ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f :=
  mem_supLat _ _ _ f

def lieZ (Dw : Datum H) (x : ℝ) (a : ExZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieZ_nat (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : lieZ Dw x (fun y => (a y : ℤ)) = lieFac Dw x a := by
  simp [lieZ, lieFac]

def supZ (x : ℝ) (σ : c.F →+* ℂ) (a : ExZ E) (n : ℕ) (f : Rul Xo c) : ENNReal :=
  ENNReal.ofReal (lieZ Dw x a) * supE (U σ).X (laZ (U σ) a n) (rdU (U σ) f)

end Forms

section Pet

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r)

abbrev rk (a : ExZ D.host.E) (n : ℕ) : ℕ := finrank c.F (cuspZ U a n)

def ML {L : Type} [Field L] (φ : c.F →+* L) (a : ExZ D.host.E) (n : ℕ) : Submodule (𝓞 L) (Fin (rk U a n) → L) :=
  bcLat φ (cuspZ U a n) (latZ U a n : Set (Rul Xo c))

def fn (σ : c.F →+* ℂ) (f : Rul Xo c) (q : AutQ W) : ℂ :=
  rdU (U σ) f (dict σ q.out).1 (dict σ q.out).2

def petZ (σ : c.F →+* ℂ) (a : ExZ D.host.E) (f g : Rul Xo c) : ℂ :=
  ((lieZ Dw (xiR D) a ^ 2 : ℝ) : ℂ) * ∫ q, starRingEnd ℂ (fn U W dict σ f q) * fn U W dict σ g q ∂(muQ1 W)

def gramG (σ : c.F →+* ℂ) (a : ExZ D.host.E) (n : ℕ) : Matrix (Fin (rk U a n)) (Fin (rk U a n)) ℂ :=
  Matrix.of fun k k' => petZ U W dict σ a (basV (cuspZ U a n) k : Rul Xo c) (basV (cuspZ U a n) k' : Rul Xo c)

open Classical in

def gramZ (σ : c.F →+* ℂ) (a : ExZ D.host.E) (n : ℕ) : Matrix (Fin (rk U a n)) (Fin (rk U a n)) ℂ :=
  if GoodEmb c σ then gramG U W dict σ a n else (gramG U W dict ((starRingEnd ℂ).comp σ) a n)ᵀ

def XZ {L : Type} [Field L] (φ : c.F →+* L) (a : ExZ D.host.E) (n : ℕ) (v : InfinitePlace L) :
    Matrix (Fin (rk U a n)) (Fin (rk U a n)) ℂ :=
  frameOf (gramZ U W dict (v.embedding.comp φ) a n)

def MF (a : ExZ D.host.E) (n : ℕ) : Submodule (𝓞 c.F) (Fin (rk U a n) → c.F) :=
  bcLat (RingHom.id c.F) (cuspZ U a n) (latZ U a n : Set (Rul Xo c))

def XF (a : ExZ D.host.E) (n : ℕ) (v : InfinitePlace c.F) : Matrix (Fin (rk U a n)) (Fin (rk U a n)) ℂ :=
  frameOf (gramZ U W dict v.embedding a n)

end Pet

end GlobalTheory.CompanionTheory.Ar.Rec.Lat
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EvLApply
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Forms

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

abbrev WZ (E : Type) [Field E] : Type := (E →+* ℂ) × ℕ → ℤ

def exZ (Dw : Datum H) (a : WZ E) : Ix Dw → ℤ
  | none => 0
  | some x => a (x.1, x.2)

def secWZ {K : Type} [Field K] {ι : Type} [Fintype ι] (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop)
    (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop) (e : ι → ℤ) :
    Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
    f p y' = (∏ i, ((t i ^ e i : (p.R)ˣ) : p.R)) * f p y}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

def latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]
    (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) :
    Submodule (𝓞 K) R :=
  (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem mem_latIn {K R : Type} [Field K] [NumberField K] [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) (f : R) : f ∈ latIn C Vs hV ↔ f ∈ C ∧ ∀ la, ∀ v ∈ Vs la, 0 ≤ v f :=
  ⟨fun ⟨g, hg, e⟩ => e ▸ ⟨g.2, hg⟩, fun h => ⟨⟨f, h.1⟩, h.2, rfl⟩⟩

variable (Xo : Moduli Dw l) (c : Coeff l)

def secZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secWZ (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (exZ Dw a)

theorem secZ_nat (a : (E →+* ℂ) × ℕ → ℕ) : secZ Xo c (fun x => (a x : ℤ)) = sec Xo c a 0 := by
  have h : ∀ (S : Type) [CommRing S] (t : Ix Dw → Sˣ),
      (∏ i, ((t i ^ exZ Dw (fun x => (a x : ℤ)) i : Sˣ) : S)) = wchar (ex Dw a 0) t := by
    intro S _ t
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i <;> simp [exZ, ex]
  ext f
  refine and_congr Iff.rfl (forall_congr' fun p => forall_congr' fun t => forall_congr' fun y => forall_congr' fun y' =>
    forall_congr' fun _ => ?_)
  rw [h]

variable {Xo c} in
open Classical in

def laZ {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : WZ E) (k : U.Comp) : Wt (U.X k).Ψ r :=
  fun τ j => if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0)
    else -a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ))

theorem laZ_nat {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) :
    laZ U (fun x => (a x : ℤ)) = laU U a 0 := by
  funext k τ j
  simp [laZ, laU]

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspZ (a : WZ E) : Submodule c.F (Rul Xo c) :=
  secZ Xo c a ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laZ (U σ) a)).comap (rdU (U σ))

theorem cuspZ_nat (a : (E →+* ℂ) × ℕ → ℕ) : cuspZ Xo c U (fun x => (a x : ℤ)) = cusp Xo c U a 0 := by
  unfold cuspZ cusp
  simp only [secZ_nat, laZ_nat]

variable {Xo c}

def evL (h : GenFrEx Xo c) (Z : Comp Xo c) : Rul Xo c →ₗ[c.F] Om Z :=
  evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)

theorem evL_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : evL h Z f = evC h Z f := rfl

def cuspOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule c.F (Rul Xo c) :=
  cuspZ Xo c U a ⊓ ⨅ (Z' : Comp Xo c) (_ : Z' ≠ Z), LinearMap.ker (evL h Z')

def latOn (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) : Submodule (𝓞 c.F) (Rul Xo c) :=
  latIn (cuspOn U h a Z) (valSet Xo c (algCls Xo c)) isVal_valSet

def volL (h : GenFrEx Xo c) (a : WZ E) (Z : Comp Xo c) (Dn : ℕ) : ℝ :=
  limsup (fun n : ℕ => (Dn.factorial : ℝ) * (Module.finrank c.F (cuspOn U h (n • a) Z) : ℝ) / (n : ℝ) ^ Dn) atTop

def lieFacZ (Dw : Datum H) (x : ℝ) (a : WZ E) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

variable {D : D7} (W : HSp D) (dict : ∀ σ, GA D W → Σ k, Frame ((U σ).X k).Ψ r)

def ipAll (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  ∫ q, jFn W σ (rdU (U σ)) (dict σ) (fun _ => 1) f q * conj (jFn W σ (rdU (U σ)) (dict σ) (fun _ => 1) g q) ∂(muQ1 W)

open Classical in

def ipOn (x : ℝ) (a : WZ E) (e : Rul Xo c) (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  let z : ℂ := ((lieFacZ Dw x a ^ 2 : ℝ) : ℂ) * ipAll U W dict (goodOf c σ) f g / ipAll U W dict (goodOf c σ) e e
  if GoodEmb c σ then z else conj z

open Classical in

def ipGl (x : ℝ) (a : WZ E) (σ : c.F →+* ℂ) (f g : Rul Xo c) : ℂ :=
  let z : ℂ := ((lieFacZ Dw x a ^ 2 : ℝ) : ℂ) * ipAll U W dict (goodOf c σ) f g
  if GoodEmb c σ then z else conj z

def volU (e : Rul Xo c) (σ : c.F →+* ℂ) : ℝ :=
  ∫ q, Complex.normSq (jFn W (goodOf c σ) (rdU (U (goodOf c σ))) (dict (goodOf c σ)) (fun _ => 1) e q) ∂(muQ1 W)

end Forms

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FlatDeterminantSections

open Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable (D : D7) (i : Fin D.R.m)

abbrev pJ : ℕ := (D.R.sigW ((i : ℕ) + 1)).1

abbrev qJ : ℕ := (D.R.sigW ((i : ℕ) + 1)).2
end

section Flat

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} (T : Core D)

open Classical in

def detA (τ : D.host.E →+* ℂ) : (D.host.E →+* ℂ) × ℕ → ℕ := fun x => if x.1 = τ then 1 else 0

def IsDetSec (j : ℕ) (τ τ' : D.host.E →+* ℂ) (s : T.R j) : Prop :=
  IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) s ∧
    ∀ (p : TRing T.Q.c.F) (t : Ix (T.Q.Dw j) → (p.R)ˣ) (y y' : FrPt (T.Q.Xo j) T.Q.c p.R), FrBor t y y' →
      wchar (ex (T.Q.Dw j) (detA τ') 0) t * s p y' = wchar (ex (T.Q.Dw j) (detA τ) 0) t * s p y

def IsFlatGen (j : ℕ) (τ : D.what₂.Tau) (s : T.R j) : Prop :=
  IsDetSec T j (DV.tauEmb D τ) (conjEmb (DV.tauEmb D τ)) s ∧
    ∃ s' : T.R j, IsDetSec T j (conjEmb (DV.tauEmb D τ)) (DV.tauEmb D τ) s' ∧ s * s' ≠ 0 ∧ s * (s * s') = s ∧
      ∀ f ∈ sec (T.Q.Xo j) T.Q.c 0 0, ∃ a : T.Q.c.F, f * (s * s') = a • (s * s')

def FlatEx : Prop := ∀ (i : Fin D.R.m) (τ : D.what₂.Tau), ∃ s, IsFlatGen T ((i : ℕ) + 1) τ s

def finN (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (s : T.R j) : ℝ := ⨆ y : T.PtM j la, T.nrmM j la y s

open Classical in

def laFlat (j : ℕ) (σ : T.Q.c.F →+* ℂ) (τ : D.host.E →+* ℂ) (k : (T.U j σ).Comp) : Wt ((T.U j σ).X k).Ψ D.R.r :=
  fun ρ _ => if ρ.1 = relab T.Q.c σ τ then 1 else 0

def infN (j : ℕ) (τ : D.what₂.Tau) (σ : T.Q.c.F →+* ℂ) (s : T.R j) : ℝ :=
  lieFac (T.Q.Dw j) (xiR D) (detA (DV.tauEmb D τ)) / lieFac (T.Q.Dw j) (xiR D) (detA (conjEmb (DV.tauEmb D τ))) *
    supN (T.U j (goodOf T.Q.c σ)).X (laFlat T j (goodOf T.Q.c σ) (DV.tauEmb D τ)) (rdU (T.U j (goodOf T.Q.c σ)) s)

def degFr (j : ℕ) (τ : D.what₂.Tau) (s : T.R j) : ℝ :=
  -((∑ᶠ la, Real.log (finN T j la s)) + ∑ σ : T.Q.c.F →+* ℂ, Real.log (infN T j τ σ s)) / (finrank ℚ T.Q.c.F : ℝ)

variable (D) in

def vd (l : ℕ) : ℝ := ((discr D.host.E).natAbs.factorization l : ℝ) / (finrank ℚ D.host.E : ℝ)

variable (D) in

def flDefect (i : Fin D.R.m) : ℝ :=
  (qJ D i : ℝ) * (vd D 2 * Real.log 2 + vd D D.host.q * Real.log D.host.q - vd D D.host.d * Real.log D.host.d)

def flatGen (hF : FlatEx T) (i : Fin D.R.m) (τ : D.what₂.Tau) : T.R ((i : ℕ) + 1) := (hF i τ).choose

def c1W (hF : FlatEx T) (i : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  degFr T ((i : ℕ) + 1) τ (flatGen T hF i τ) + flDefect D i

def FlatDegIndep : Prop :=
  ∀ (i : Fin D.R.m) (τ : D.what₂.Tau) (s s' : T.R ((i : ℕ) + 1)), IsFlatGen T ((i : ℕ) + 1) τ s → IsFlatGen T ((i : ℕ) + 1) τ s' →
    degFr T ((i : ℕ) + 1) τ s = degFr T ((i : ℕ) + 1) τ s'

end Flat

end GlobalTheory.CompanionTheory.Ar.Rec.FlatDeterminantSections
end
end

