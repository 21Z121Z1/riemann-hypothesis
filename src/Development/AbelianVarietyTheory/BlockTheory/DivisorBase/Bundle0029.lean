import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LogFactorialIndices.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def hook (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  Formalism.LatticeIndexTer.hookProd (YoungDiagram.ofRowLens (((List.range n).map a).insertionSort (· ≥ ·)) List.sortedGE_insertionSort)

variable (D) in

def hookSum (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log
    ((hook ((Wc D i).sig (tauE D ρ)).1 (aPl D i ((Wc D i).sig (tauE D ρ)).1 ρ) : ℝ) *
      (hook ((Wc D i).sig (tauE D ρ)).2 (aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 ρ) : ℝ))

variable (D) in

def logSize (b : ℝ) : ℝ := Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ))

variable (D) in

def IsSize (i : Fin D.R.m) (b : ℝ) : Prop :=
  (∀ ρ : D.what₂.Tau, 0 < (((D.hc ρ).e i : ℚ) : ℝ) ∧ (((D.hc ρ).e i : ℚ) : ℝ) ≤ 2 * b ∧
    (∀ l, 0 ≤ (((D.hc ρ).v l : ℚ) : ℝ) ∧ (((D.hc ρ).v l : ℚ) : ℝ) ≤ b) ∧
    ∀ l, |(((D.hc ρ).b l : ℚ) : ℝ) - (((D.hc ρ).e i : ℚ) : ℝ)| ≤ b) ∧
  ∀ l, ((D.R.k : ℝ) * b) ^ 8 ≤ (D.host.g l : ℝ)

def zeroOff {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} (X : Comp → Data E r) :
    Submodule ℂ (FDSec X) where
  carrier := {P | ∀ k x, x ∉ (X k).dom → P k x = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {P Q} hP hQ k x hx => by
    show P k x + Q k x = 0
    rw [hP k x hx, hQ k x hx, add_zero]
  smul_mem' := fun a P hP k x hx => by
    show a * P k x = 0
    rw [hP k x hx, mul_zero]

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def level (F : Face D A) : Option Bool → LevelP R.Pg D.R.r ℂ
  | none => R.triv
  | some b => R.levL F b (sg0 D A)

open Classical in

def finS : Finset (HeightOneSpectrum (𝓞 D.host.F)) := R.Pg.image fun PP => PP.under (𝓞 D.host.F)

def PrimeToHost : Prop :=
  ∀ PP ∈ R.Pg, ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def IsHecke (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D (Wc D i))) : Prop :=
  Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (finS R) P d Rp

def cuspPart (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (finS R) c

def IsAdelicScalar (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (l : ℝ) : Prop :=
  ∀ U ∈ cuspPart R i c, ∃ y : (R.HV i A.μ0).H,
    (∀ f, ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) U (R.thF i A.μ0 f) = ⟪y, f⟫_ℂ) ∧ R.thF i A.μ0 y = (l : ℂ) • U

def coordV (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) : (R.HV i A.μ0).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i A.μ0

def srcAt (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (R.HV i A.μ0).H :=
  ⨅ (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) (p : P.H),
    LinearMap.ker ((actL (Vc D i) (R.βV i) (R.datVt i A.μ0) p.1 - ((P.chi p : ℂˣ) : ℂ) • LinearMap.id) ∘ₗ coordV R i ℓ)

def IsSrcProj (e : (R.HV i A.μ0).H →ₗ[ℂ] (R.HV i A.μ0).H) : Prop :=
  ∀ ℓ y, coordV R i ℓ (e y) =
    gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (coordV R i ℓ y)

def ipSrc (P : LevelP R.Pg D.R.r ℂ) (x y : (R.HV i A.μ0).H) : ℂ := ((Nat.card P.H : ℕ) : ℂ)⁻¹ * ⟪y, x⟫_ℂ

def chiDet (g : G) : ℂˣ := ∏ PP : R.Pg, R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP))

end Adelic

section Geometric

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev Sec : Type := FDSec (C.U ((i : ℕ) + 1) O.s0).X

def cuspC : Submodule ℂ (Sec O) :=
  holSub (C.U ((i : ℕ) + 1) O.s0).X (laU (C.U ((i : ℕ) + 1) O.s0) (wtA κ) κ.n) ⊓ zeroOff _

def unitVal (P : Sec O) (g : GA D (Wc D i)) : ℂ :=
  (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * P (O.dict g).1 (O.dict g).2

def ipSec (P : LevelP R.Pg D.R.r ℂ) (S S' : Sec O) : ℂ :=
  ((Nat.card P.H : ℕ) : ℂ)⁻¹ * (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) *
    ∫ g in R.fdW i, unitVal O κ S g * star (unitVal O κ S' g) ∂(R.νW i)

variable (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

def dict : Sec O →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) • adel (Wc D i) O.dict (muPin (Wc D i) O.dict O.mu cc)

def goodAt (P : LevelP R.Pg D.R.r ℂ) : Submodule ℂ (Sec O) :=
  cuspC O κ ⊓ LinearMap.ker ((R.eWf i (sg0 D A) - LinearMap.id) ∘ₗ dict O κ cc) ⊓
    ⨅ p : P.H, LinearMap.ker
      ((actL (Wc D i) (R.βW i) (R.datWp i R.triv) p.1 - ((P.chi p : ℂˣ) : ℂ) • LinearMap.id) ∘ₗ dict O κ cc)

def partAt (P : LevelP R.Pg D.R.r ℂ) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (Sec O) :=
  goodAt O κ cc P ⊓ ⨅ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D (Wc D i))) (_ : IsHecke R i Q d Rp),
    LinearMap.ker ((heckeLin (Wc D i) Rp - c Q d • LinearMap.id) ∘ₗ dict O κ cc)

def IsRepSystem (v₀ : (R.MW i (sg0 D A)).Vec) (h : O.Cl' () → GA D (Vc D i)) : Prop :=
  ∃ J' : Subgroup (Bridge.Gf (Vc D i)), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) ∧
    PlaceEx R i A.μ0 h O.c0' ∧ ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧
    ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

def IsSecLift (h : O.Cl' () → GA D (Vc D i)) (th : (R.HV i A.μ0).H →ₗ[ℂ] Sec O) : Prop :=
  ∀ (x₀ : A.fam.amb.FL i A.μ0) (x : O.Cl' () → VsV D i O.c'.F), Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x →
    ∃ f ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank,
      IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io x f ∧
      th (jVx R i A.μ0 x₀) = rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f

def ActsByScalar (th : (R.HV i A.μ0).H →ₗ[ℂ] Sec O) (e : (R.HV i A.μ0).H →ₗ[ℂ] (R.HV i A.μ0).H)
    (P : LevelP R.Pg D.R.r ℂ) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (l : ℝ) : Prop :=
  ∀ S ∈ partAt O κ cc P c, ∃ y ∈ srcAt R i P,
    (∀ f ∈ srcAt R i P, ipSec O κ P (th (e f)) S = ipSrc R i P f y) ∧ th (e y) = (l : ℂ) • S

structure DictClauses (F : Face D A) (v₀ : (R.MW i (sg0 D A)).Vec) : Prop where
  inj : ∀ S ∈ cuspC O κ, dict O κ cc S = 0 → S = 0
  integrable : ∀ S ∈ cuspC O κ, ∀ S' ∈ cuspC O κ,
    IntegrableOn (fun g => unitVal O κ S g * star (unitVal O κ S' g)) (R.fdW i) (R.νW i)
  cuspidal : ∃ δ : cuspC O κ →ₗ[ℂ] R.Wall i (sg0 D A),
    (∀ S, (δ S : MMap (R.MW i (sg0 D A))) v₀ = dict O κ cc S) ∧
    (∀ S S', ipAt (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) (δ S') (δ S) = ipSec O κ R.triv S S') ∧
    ∀ b, (∀ S : cuspC O κ, (S : Sec O) ∈ goodAt O κ cc (level R F b) →
        (δ S : MMap (R.MW i (sg0 D A))) ∈ R.Wat i (sg0 D A) (level R F b)) ∧
      ∀ c, ∀ S : cuspC O κ, (S : Sec O) ∈ partAt O κ cc (level R F b) c → (δ S : MMap (R.MW i (sg0 D A))) ∈ cuspPart R i c
  proj : ∀ f ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n,
    dict O κ cc (∑ g : G, (RealDat.eC (A := A) (sg0 D A) g * (((chiDet R i g)⁻¹ : ℂˣ) : ℂ)) •
        rdU (C.U ((i : ℕ) + 1) O.s0) (actLev C.Q.c O.lev2 g f)) =
      R.eWf i (sg0 D A) (dict O κ cc (rdU (C.U ((i : ℕ) + 1) O.s0) f))

structure LiftClauses (F : Face D A) (v₀ : (R.MW i (sg0 D A)).Vec) (b : ℝ) (th : (R.HV i A.μ0).H →ₗ[ℂ] Sec O)
    (e : (R.HV i A.μ0).H →ₗ[ℂ] (R.HV i A.μ0).H) : Prop where
  mem : ∀ y, th y ∈ cuspC O κ
  carry : ∃ (u : ℂ) (z : G), ‖u‖ = 1 ∧ z ∈ Subgroup.center G ∧ ∀ y,
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) (dict O κ cc (th y)) = u • R.thF i A.μ0 y v₀
  scalar : ∀ (s : Option Bool) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), partAt O κ cc (level R F s) c ≠ ⊥ →
    ∃ l : ℝ, 0 < l ∧ IsAdelicScalar R i c l ∧ ActsByScalar O κ cc th e (level R F s) c l ∧
      hookSum D i - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * logSize D b ≤ Real.log l

end Geometric

def SectionLiftScalar (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → PrimeToHost R →
  ∀ i : Fin D.R.m, OMPins T R κ v₀ O i →
  ∀ (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ), (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph →
    DictClauses (O i) (κ i) cc F (v₀ i (sg0 D A)) ∧
    ∀ h, IsRepSystem (O i) (v₀ i (sg0 D A)) h →
      (∃! th, IsSecLift (O i) (κ i) h th) ∧ (∃! e, IsSrcProj R i e) ∧
      ∀ b, IsSize D i b → ∀ th e, IsSecLift (O i) (κ i) h th → IsSrcProj R i e →
        LiftClauses (O i) (κ i) cc F (v₀ i (sg0 D A)) b th e

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarSectionLift

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HookProductDictionary
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.HookProductDictionary

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hookProduct (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range (a i), ((a i - j) + ((Finset.Ioo i n).filter fun l => j < a l).card)

theorem hookProduct_pos (n : ℕ) (a : ℕ → ℕ) : 0 < hookProduct n a :=
  Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => by
    have := Finset.mem_range.1 hj
    omega

example : hookProduct 2 (fun i => if i = 0 then 2 else 1) = 3 := by decide

example : hookProduct 2 (fun _ => 2) = 12 := by decide

def mainTerm (D : D7) (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log
    ((hookProduct ((Wc D i).sig (tauE D ρ)).1 (aPl D i ((Wc D i).sig (tauE D ρ)).1 ρ) *
      hookProduct ((Wc D i).sig (tauE D ρ)).2 (aMi D i ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 ρ) : ℕ) : ℝ)

def logSize (D : D7) (b : ℝ) : ℝ :=
  Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def errUnit (D : D7) (b : ℝ) : ℝ := (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * logSize D b

def Sizes (D : D7) (b : ℝ) : Prop :=
  1 ≤ b ∧ (∀ i, ((D.R.k : ℝ) * b) ^ 8 ≤ D.host.g i) ∧ ∀ ρ : D.what₂.Tau,
    (∀ j, 0 < (D.hc ρ).e j ∧ (((D.hc ρ).e j : ℚ) : ℝ) ≤ 2 * b) ∧
    (∀ l, 0 ≤ (D.hc ρ).v l ∧ (((D.hc ρ).v l : ℚ) : ℝ) ≤ b) ∧
    ∀ l j, |(((D.hc ρ).b l - (D.hc ρ).e j : ℚ) : ℝ)| ≤ b

def RegularGaps (D : D7) : Prop :=
  ∀ (ρ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    (D.R.r : ℚ) ≤ Formalism.L2.NTheta.lamAt (D.hc ρ) n - Formalism.L2.NTheta.lamAt (D.hc ρ) (n + 1)

theorem finite_levelPlaces (D : D7) :
    {v : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  have h1 : Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h0
  refine (Ideal.finite_factors h1).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

def levelPlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (finite_levelPlaces D).toFinset

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def IsLevel (F : Face D A) (P : LevelP R.Pg D.R.r ℂ) : Prop :=
  P = R.triv ∨ P = R.levL F false (sg0 D A) ∨ P = R.levL F true (sg0 D A)

def IsSphOp (PP : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (B : Finset (GA D (Wc D i))) : Prop :=
  Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (levelPlaces D) PP d B

def adelicPart (c : EigSys D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv))
      (levelPlaces D) c).comap (R.HW i (sg0 D A)).e

def IsAdelicScalar (c : EigSys D) (l : ℝ) : Prop :=
  adelicPart R i c ≠ ⊥ ∧ ∀ x ∈ adelicPart R i c, R.thG i A.μ0 (LinearMap.adjoint (R.thG i A.μ0) x) = (l : ℂ) • x

abbrev flagV : Bridge.LevDat D (Vc D i) := levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)

def redV : (flagV R i).Q →* G := (R.B.L i A.μ0).act_tie.red

theorem redV_surj : Function.Surjective (redV R i) := (R.B.L i A.μ0).act_tie.red_surj

def srcType (P : LevelP R.Pg D.R.r ℂ) : Set (R.HV i A.μ0).H :=
  {y | ∀ (q : (flagV R i).Q) (hq : R.eG (redV R i q) ∈ P.H),
    Bridge.g0Act (flagV R i).ch q ((R.HV i A.μ0).e y) = ((P.chi ⟨_, hq⟩ : ℂˣ) : ℂ) • (R.HV i A.μ0).e y}

def IsProj (e : (R.HV i A.μ0).H →ₗ[ℂ] (R.HV i A.μ0).H) : Prop :=
  ∀ y, (R.HV i A.μ0).e (e y) = ∑ g : G, RealDat.eC (A := A) (sg0 D A) g •
    Bridge.g0Act (flagV R i).ch (Function.surjInv (redV_surj R i) g) ((R.HV i A.μ0).e y)

def srcInner (P : LevelP R.Pg D.R.r ℂ) (x y : (R.HV i A.μ0).H) : ℂ := ((Nat.card P.H : ℕ) : ℂ)⁻¹ * inner ℂ y x

end Adelic

section Geo

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit fun _ => A.μ0) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

abbrev Sec : Type := FDSec (C.U ((i : ℕ) + 1) O.s0).X

def SameSec (s s' : Sec O) : Prop := ∀ p : FPt (C.U ((i : ℕ) + 1) O.s0).X, s p.1 p.2 = s' p.1 p.2

def holCusp : Submodule ℂ (Sec O) :=
  holSub (C.U ((i : ℕ) + 1) O.s0).X (laU (C.U ((i : ℕ) + 1) O.s0) (wtA κ) κ.n)

def dl : Sec O →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
  (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) • adel (Wc D i) O.dict (muPin (Wc D i) O.dict O.mu cc)

def goodCusp (P : LevelP R.Pg D.R.r ℂ) : Set (Sec O) :=
  {s | s ∈ holCusp O κ ∧ Lev.HasType (Wc D i) (R.βW i) (R.datWp i P) (dl O κ cc s) ∧
    R.eWf i (sg0 D A) (dl O κ cc s) = dl O κ cc s}

def goodCuspPart (P : LevelP R.Pg D.R.r ℂ) (c : EigSys D) : Set (Sec O) :=
  {s | s ∈ goodCusp O κ cc P ∧ ∀ PP d B, IsSphOp R i PP d B → heckeLin (Wc D i) B (dl O κ cc s) = c PP d • dl O κ cc s}

def pet (P : LevelP R.Pg D.R.r ℂ) (s s' : Sec O) : ℂ :=
  ((Nat.card P.H : ℕ) : ℂ)⁻¹ * (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) *
    ∫ g in R.fdW i, dl O κ cc s g * star (dl O κ cc s' g) ∂(R.νW i)

def PetInt (s s' : Sec O) : Prop :=
  IntegrableOn (fun g => dl O κ cc s g * star (dl O κ cc s' g)) (R.fdW i) (R.νW i)

def IsReps (v₀ : (R.MW i (sg0 D A)).Vec) (h : O.Cl' () → GA D (Vc D i)) : Prop :=
  ∃ J' : Subgroup (Bridge.Gf (Vc D i)), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) ∧
    PlaceEx R i A.μ0 h O.c0' ∧ ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧
    ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

def IsSecLift (h : O.Cl' () → GA D (Vc D i)) (th : (R.HV i A.μ0).H →ₗ[ℂ] Sec O) : Prop :=
  ∀ x₀ : A.fam.amb.FL i A.μ0, ∃ (x : O.Cl' () → VsV D i O.c'.F) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'),
    Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x ∧
    f ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank ∧
    IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io x f ∧
    SameSec O (th (jVx R i A.μ0 x₀)) (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f)

def IsAdjAt (P : LevelP R.Pg D.R.r ℂ) (L : (R.HV i A.μ0).H →ₗ[ℂ] Sec O) (s : Sec O) (y : (R.HV i A.μ0).H) : Prop :=
  y ∈ srcType R i P ∧ ∀ x ∈ srcType R i P, PetInt O κ cc (L x) s ∧ pet O κ cc P (L x) s = srcInner R i P x y

def ActsBy (P : LevelP R.Pg D.R.r ℂ) (L : (R.HV i A.μ0).H →ₗ[ℂ] Sec O) (c : EigSys D) (l : ℝ) : Prop :=
  ∀ s ∈ goodCuspPart O κ cc P c, ∃ y, IsAdjAt O κ cc P L s y ∧ SameSec O (L y) ((l : ℂ) • s)

def DictOn (v₀ : (R.MW i (sg0 D A)).Vec) (P : LevelP R.Pg D.R.r ℂ) : Prop :=
  (∀ s ∈ goodCusp O κ cc P, dl O κ cc s = 0 → SameSec O s 0) ∧
  (∀ s ∈ goodCusp O κ cc P, ∃ x : (R.HW i (sg0 D A)).H,
    (R.HW i (sg0 D A)).e x ∈ R.Wat i (sg0 D A) P ∧ (R.HW i (sg0 D A)).e x v₀ = dl O κ cc s) ∧
  ∀ s ∈ goodCusp O κ cc P, ∀ s' ∈ goodCusp O κ cc P, ∀ x x' : (R.HW i (sg0 D A)).H,
    (R.HW i (sg0 D A)).e x v₀ = dl O κ cc s → (R.HW i (sg0 D A)).e x' v₀ = dl O κ cc s' →
      PetInt O κ cc s s' ∧ pet O κ cc P s s' = ((Nat.card P.H : ℕ) : ℂ)⁻¹ * inner ℂ x' x

end Geo

section Main

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit fun _ => A.μ0)

def LiftScalarIdentity (i : Fin D.R.m) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → RegularGaps D →
    ∀ (cc : (T.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ph : ℂ), (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph →
    ∀ h, IsReps (O i) (v₀ i (sg0 D A)) h →
      (∃ th, IsSecLift (O i) (κ i) h th) ∧ (∃ e, IsProj R i e) ∧
      ∀ P, IsLevel R F P →
        DictOn (O i) (κ i) cc (v₀ i (sg0 D A)) P ∧
        ∀ c : EigSys D, (∃ s ∈ goodCuspPart (O i) (κ i) cc P c, ¬ SameSec (O i) s 0) →
          ∃ l : ℝ, 0 < l ∧ IsAdelicScalar R i c l ∧
            (∀ th e, IsSecLift (O i) (κ i) h th → IsProj R i e → ActsBy (O i) (κ i) cc P (th ∘ₗ e) c l) ∧
            ∀ b, Sizes D b → mainTerm D i - 8 * errUnit D b ≤ Real.log l

theorem exists_isReps (i : Fin D.R.m) (hP : OMPins T R κ v₀ O i) : ∃ h, IsReps (O i) (v₀ i (sg0 D A)) h := by
  obtain ⟨h, J', hh⟩ := (hP.2.tuple ()).reps
  exact ⟨h, J', hh⟩

theorem IsAdelicScalar.unique {i : Fin D.R.m} {c : EigSys D} {l l' : ℝ} (h : IsAdelicScalar R i c l)
    (h' : IsAdelicScalar R i c l') : l = l' := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.1
  have h2 : (l : ℂ) • x = (l' : ℂ) • x := (h.2 x hx).symm.trans (h'.2 x hx)
  exact Complex.ofReal_injective (smul_left_injective ℂ hx0 h2)

end Main

end GlobalTheory.IndefiniteRowSideFullHecke.HookProductDictionary
end
end

