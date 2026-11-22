import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DiscreteGL2
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions MeasureTheory GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.V.Lit.JL

def SqInt {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (φ : G → ℂ) : Prop :=
  letI : MeasurableSpace G := borel G
  ∃ (μ : Measure G) (S : Set G), μ.IsHaarMeasure ∧ MeasurableSet S ∧ (∀ g, ∃ γ ∈ Γ, γ * g ∈ S) ∧ ∫⁻ g in S, ‖φ g‖ₑ ^ 2 ∂μ < ⊤

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

variable (F) in

def eId : Ideles F := TR.infId F (Units.map (Pi.constRingHom (InfinitePlace F) ℝ).toMonoidHom (Units.mk0 (Real.exp 1) (Real.exp_ne_zero 1)))

def IsUnitary (ω : HChar F) : Prop := ∀ z : Ideles F, ‖((ω.1 z : ℂˣ) : ℂ)‖ = 1

variable (F) in

def latG : Subgroup (GA F 2) := (ratGL F 2).range ⊔ Subgroup.zpowers (Matrix.GeneralLinearGroup.scalar (Fin 2) (eId F))

variable (F) in

structure DiscG where
  V : Submodule ℂ (TR.Sm F 2)
  aut : ∀ φ ∈ V, TR.IsAutForm φ
  stable : TR.IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, TR.IsStable W → W = ⊥ ∨ W = V
  cen : ∃ ω : HChar F, IsUnitary ω ∧ ∀ (z : Ideles F), ∀ φ ∈ V, ∀ g,
    φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g
  sq : ∀ φ ∈ V, SqInt (latG F) φ.1

def ModIso (V V' : Submodule ℂ (TR.Sm F 2)) : Prop :=
  ∃ T : V ≃ₗ[ℂ] V', ∀ (o : TR.Op F 2) (φ ψ : V), ψ.1 = TR.act o φ.1 → (T ψ).1 = TR.act o (T φ).1

def LocG (V : Submodule ℂ (TR.Sm F 2)) (w : HeightOneSpectrum (𝓞 F)) (τ : SmIrr (GL (Fin 2) (w.adicCompletion F))) : Prop :=
  ∃ f : τ.V →ₗ[ℂ] TR.Sm F 2, f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ g x, f (τ.ρ g x) = TR.finRep F 2 (locGL F 2 w g) (f x)

def HasCen (V : Submodule ℂ (TR.Sm F 2)) (v : InfinitePlace F) (c : ℂ) : Prop := ∀ φ ∈ V, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = c • φ

def IsChr (V : Submodule ℂ (TR.Sm F 2)) (v : InfinitePlace F) (c : ℂ) : Prop :=
  HasCen V v c ∧ ∀ φ ∈ V, TR.Eop v 0 1 φ = 0 ∧ TR.Eop v 1 0 φ = 0

def IsDS (V : Submodule ℂ (TR.Sm F 2)) (v : InfinitePlace F) (m : ℕ) (c : ℂ) : Prop :=
  HasCen V v c ∧ ∃ φ ∈ V, φ ≠ 0 ∧ TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (m + 2)) • φ ∧
    TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)

def Compatible (V : Submodule ℂ (TR.Sm F 2)) : Prop := ∀ v, ∃ c, IsChr V v c ∨ ∃ m, IsDS V v m c

variable (Q : DefQuat F)

def Hv (v : InfinitePlace F) : Subgroup (GL (Fin 2) ℂ) := (Algebra.adjoin ℝ (Set.range (Q.jc v))).toSubmonoid.units

abbrev DA : Type := (∀ v, Hv Q v) × GL (Fin 2) (Af F)

def toHv (v : InfinitePlace F) : Q.Dˣ →* Hv Q v :=
  (Units.map (Q.jc v).toMonoidHom).codRestrict _ fun γ =>
    ⟨Algebra.subset_adjoin ⟨γ, rfl⟩, Algebra.subset_adjoin ⟨(γ⁻¹ : Q.Dˣ), rfl⟩⟩

def toDA : Q.Dˣ →* DA Q := (Pi.monoidHom (toHv Q)).prod Q.toFin

variable {Q} in

def IsScalar (z : Ideles F) (x : DA Q) : Prop :=
  (∀ v, ((x.1 v : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.scalar (Fin 2) ((TR.pInf F (z : Ad F) v : ℝ) : ℂ)) ∧
    (x.2 : Matrix (Fin 2) (Fin 2) (Af F)) = Matrix.scalar (Fin 2) (pFin F (z : Ad F))

def latD : Subgroup (DA Q) := (toDA Q).range ⊔ Subgroup.closure {x | IsScalar (eId F) x}

abbrev RD : Representation ℂ (DA Q) (DA Q → ℂ) := GlobalTheory.PRep.rightReg ℂ (DA Q) ℂ

structure DiscD where
  V : Submodule ℂ (DA Q → ℂ)
  cont : ∀ φ ∈ V, Continuous φ
  left : ∀ φ ∈ V, ∀ γ g, φ (toDA Q γ * g) = φ g
  level : ∀ φ ∈ V, IsOpen {k : GL (Fin 2) (Af F) | RD Q (1, k) φ = φ}
  kfin : ∀ φ ∈ V, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y : ∀ v, Hv Q v => RD Q (y, 1) φ))
  stable : ∀ x, ∀ φ ∈ V, RD Q x φ ∈ V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, (∀ x, ∀ φ ∈ W, RD Q x φ ∈ W) → W = ⊥ ∨ W = V
  cen : ∃ ω : HChar F, IsUnitary ω ∧ ∀ (z : Ideles F) (x : DA Q), IsScalar z x → ∀ φ ∈ V, ∀ g, φ (x * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g
  sq : ∀ φ ∈ V, SqInt (latD Q) φ

variable {Q}

def LocD (V : Submodule ℂ (DA Q → ℂ)) (w : HeightOneSpectrum (𝓞 F)) (τ : SmIrr (GL (Fin 2) (w.adicCompletion F))) : Prop :=
  ∃ f : τ.V →ₗ[ℂ] (DA Q → ℂ), f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ g x, f (τ.ρ g x) = RD Q (1, locGL F 2 w g) (f x)

def symWt (m : ℕ) : DomWeight 2 := ⟨![m, 0], fun i j h => by
  fin_cases i <;> fin_cases j <;> simp_all⟩

open Classical in

def InfD (V : Submodule ℂ (DA Q → ℂ)) (v : InfinitePlace F) (m : ℕ) (c : ℂ) : Prop :=
  ∃ f : nablaSq ℂ 2 (symWt m) →ₗ[ℂ] (DA Q → ℂ), f ≠ 0 ∧ (∀ x, f x ∈ V) ∧ ∀ (g : Hv Q v) x, RD Q (Pi.mulSingle v g, 1) (f x) =
    ((‖((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ : ℝ) : ℂ) ^ ((c - m) / 2) • f (GlobalTheory.Branching.sqRep ℂ 2 (symWt m) g x)

structure Match (π' : DiscD Q) (π : DiscG F) : Prop where
  real : ∀ v, ∃ c, (IsChr π.V v c ∧ InfD π'.V v 0 c) ∨ ∃ m, IsDS π.V v m c ∧ InfD π'.V v m c
  fin : ∀ w τ, LocG π.V w τ ↔ LocD π'.V w τ

end UpperTheory.V.Lit.JL

namespace UpperTheory.V.Lit

open JL

def GlobalJL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F),
    (∀ π' : DiscD Q, ∃ π : DiscG F, Match π' π) ∧ ∀ π : DiscG F, Compatible π.V → ∃ π' : DiscD Q, Match π' π

def DiscreteGL2 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : DiscG F),
    (∃ ρ : TR.CuspSub F 2, ModIso π.V ρ.V) ∨
      ∃ (χ : HChar F) (φ : TR.Sm F 2), (∀ g, φ.1 g = ((chiDet 2 χ g : ℂˣ) : ℂ)) ∧ ModIso π.V (Submodule.span ℂ {φ})

end UpperTheory.V.Lit
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.TyDefs
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lit.Ty

def Dom (P Q : Multiset ℕ) : Prop :=
  P.sum = Q.sum ∧ ∀ j : ℕ, ((Q.sort (· ≥ ·)).take j).sum ≤ ((P.sort (· ≥ ·)).take j).sum

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def SameI (x y : WD h) : Prop :=
  ∃ (n : ℕ) (a b : WDRep h (Fin n → ℂ)) (e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)), WD.mk a = x ∧ WD.mk b = y ∧
    ∀ (s : ↥(Ine (F := E) A)) v, e (a.ρ (ineIncl h s) v) = b.ρ (ineIncl h s) (e v)

variable (h) in

structure Shape : Type 1 where
  r : ℕ
  ρ : Fin r → WD h
  irr : ∀ i, IsIrrWD (ρ i)
  k : Fin r → ℕ
  pos : ∀ i, 1 ≤ k i

namespace Shape

def wd (S : Shape h) : WD h := sumList (List.ofFn fun i => (S.ρ i).lpChar (WD.lpSp h (S.k i)))

open Classical in

def part (S : Shape h) (ρ₀ : WD h) : Multiset ℕ := (Finset.univ.filter fun i => SameI (S.ρ i) ρ₀).val.map S.k

def Below (S' S : Shape h) : Prop := ∀ ρ₀, IsIrrWD ρ₀ → Dom (S.part ρ₀) (S'.part ρ₀)

def Same (S' S : Shape h) : Prop := ∀ ρ₀, IsIrrWD ρ₀ → S'.part ρ₀ = S.part ρ₀

end Shape

def IsIota {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {H V V' : Type} [Group H] [AddCommGroup V] [Module (Qbar l) V]
    [AddCommGroup V'] [Module ℂ V'] (π : Representation (Qbar l) H V) (π' : Representation ℂ H V') : Prop :=
  ∃ f : V ≃+ V', (∀ (z : Qbar l) v, f (z • v) = ι z • f v) ∧ ∀ g v, f (π g v) = π' g (f v)

def ShottonTypes : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : ℕ) [Fact l.Prime], ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (ι : Qbar l ≃+* ℂ) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ), 1 ≤ n → ∀ S : Shape h, S.wd.lpDim = n →
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (Qbar l) W) (σ : Representation (Qbar l) ↥(GlobalTheory.LFun.KGL w n) W),
        σ.IsIrreducible ∧ GlobalTheory.PRep.IsSmooth σ ∧
        ∀ (V : Type) [AddCommGroup V] [Module (Qbar l) V] (π : Representation (Qbar l) (GL (Fin n) (w.adicCompletion E)) V),
          π.IsIrreducible → GlobalTheory.PRep.IsSmooth π → GlobalTheory.PRep.IsAdmissible π →
          ∀ π' : SmIrr (GL (Fin n) (w.adicCompletion E)), IsIota ι π π'.ρ → ∀ S' : Shape h, S'.wd = rc (algNorm π') →
            ((∃ f : W →ₗ[Qbar l] V, Function.Injective f ∧ ∀ k v, f (σ k v) = π k (f v)) → S'.Below S) ∧
            (S'.Same S → Module.finrank (Qbar l) (σ.IntertwiningMap (π.comp (GlobalTheory.LFun.KGL w n).subtype)) = 1)

end UpperTheory.V.Lit.Ty
end
end

