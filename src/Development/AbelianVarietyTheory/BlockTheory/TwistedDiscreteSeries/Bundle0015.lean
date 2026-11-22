import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParameterTransferTypes
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Satake

abbrev Sys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

def SpanAt (V : HSp D) (e : AE D) (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (γ : GA D V) : Prop :=
  (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, IntVec z ∧
    (fun a => finPart D e * (finMat D.sp.cm.sig V.gram γ).mulVec y a) = fun a => finPart D e * M.mulVec z a) ∧
  (∀ z, IntVec z → ∃ y ∈ Formalism.L2.NTheta.LamHat V,
    (fun a => finPart D e * (finMat D.sp.cm.sig V.gram γ).mulVec y a) = fun a => finPart D e * M.mulVec z a)

def IsFlagBasis (V : HSp D) (e : AE D) (B : Matrix (Fin V.rank) (Fin V.rank) (AE D)) : Prop :=
  SpanAt V e (B.map (finPart D)) 1 ∧
    (cA D e = e → ∀ i j : Fin V.rank, (i : ℕ) + j + 1 < V.rank →
      e * ∑ a, ∑ b, cA D (B a i) * incA D (V.gram a b) * B b j = 0)

def IwExp (V : HSp D) (e : AE D) (ϖ : D.host.E) (B : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (γ : GA D V)
    (a : Fin V.rank → ℤ) : Prop :=
  ∃ N : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
    (∀ i, N i i = 1) ∧ (∀ i j, j < i → N i j = 0) ∧
    SpanAt V e (B.map (finPart D) * N * Matrix.diagonal fun i => finPart D (incA D (ϖ ^ a i))) γ

open Classical in

def sphVal {n : ℕ} (inert : Prop) (q : ℕ) (α : Fin n → ℂ) (a : Fin n → ℤ) : ℂ :=
  ∏ i : Fin n, if inert → 2 * (i : ℕ) + 1 < n then
    (α i * (((q : ℝ) ^ (-(((n : ℝ) - 1 - 2 * (i : ℕ)) / 2)) : ℝ) : ℂ)) ^ a i else 1

def HasPar (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : Sys D) (P : HeightOneSpectrum (𝓞 D.host.E)) (s : Multiset ℂ) : Prop :=
  ∃ (α : Fin V.rank → ℂ) (e f : AE D) (ϖ : 𝓞 D.host.E) (B : Matrix (Fin V.rank) (Fin V.rank) (AE D)),
    Finset.univ.val.map α = s ∧ (∀ i, α i ≠ 0) ∧
    IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ IsFlagBasis V e B ∧
    (cA D e = e → (∀ i, α i * α i.rev = 1) ∧ ∀ i, i.rev = i → α i = 1) ∧
    ∀ (d : List ℤ) (Rp : Finset (GA D V)), Hecke₂ V J χ S P d Rp →
      ∃ a : GA D V → Fin V.rank → ℤ, (∀ γ ∈ Rp, IwExp V e (ϖ : D.host.E) B γ (a γ)) ∧
        c P d = ∑ γ ∈ Rp, sphVal (cA D e = e) (Ideal.absNorm P.asIdeal) α (a γ)

def str (x : ℂ) (q t : ℕ) : Multiset ℂ :=
  (Multiset.range t).map fun k => x * (((q : ℝ) ^ (((t : ℝ) - 1) / 2 - (k : ℝ)) : ℝ) : ℂ)

def typeSub (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | HasType V β L F}
  add_mem' := by
    intro F F' hF hF' κ hκ h
    simp only [Pi.add_apply, hF κ hκ h, hF' κ hκ h, mul_add]
  zero_mem' := by intro κ _ h; simp
  smul_mem' := by
    intro a F hF κ hκ h
    simp only [Pi.smul_apply, smul_eq_mul, hF κ hκ h]
    ring

def eigSub (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : Sys D) : Submodule ℂ (GA D V → ℂ) :=
  ⨅ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)) (_ : Hecke₂ V J χ S P d Rp),
    LinearMap.ker (heckeLin V Rp - c P d • LinearMap.id)

example (α : Fin 2 → ℂ) : 4 * sphVal False 4 α ![1, 0] + sphVal False 4 α ![0, 1] = 2 * (α 0 + α 1) := by
  have h1 : (4 : ℝ) ^ (-((1 : ℝ) / 2)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have h2 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have e1 : -((((2 : ℕ) : ℝ) - 1 - 2 * (((0 : Fin 2) : ℕ) : ℝ)) / 2) = -((1 : ℝ) / 2) := by norm_num
  have e2 : -((((2 : ℕ) : ℝ) - 1 - 2 * (((1 : Fin 2) : ℕ) : ℝ)) / 2) = (1 : ℝ) / 2 := by norm_num
  have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  simp only [sphVal, Fin.prod_univ_two, false_imp_iff, if_true, e1, e2, h4, h1, h2]
  simp
  ring

example (x : ℂ) (q t : ℕ) : (str x q t).card = t := by simp [str]

end Satake

section Spaces

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

open Classical in

def badS (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => PP.under (𝓞 D.host.F)

def lvlP : Option Bool → LevelP R.Pg D.R.r ℂ
  | none => R.triv
  | some b => R.levL F b (sg0 D A)

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

def JW : Set (GA D (Wc D i)) := levS _ (R.βW i) (R.datWp i P)

def chW : GA D (Wc D i) → ℂ := levChi _ (R.βW i) (R.datWp i P)

def datV : LevDat D.host.E ℂ (Vc D i).rank := withP (R.datVt i t) P

def JV : Set (GA D (Vc D i)) := levS _ (R.βV i) (datV R i t P)

def chV : GA D (Vc D i) → ℂ := levChi _ (R.βV i) (datV R i t P)

def MW : Submodule ℂ (R.HW i (sg0 D A)).H := (R.Wat i (sg0 D A) P).comap (R.HW i (sg0 D A)).e

def MWc (c : Sys D) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (JW R i P) (chW R i P) (badS R t) c ⊓ R.Wat i (sg0 D A) P).comap
    (R.HW i (sg0 D A)).e

def IxW : Set (Sys D) := IxFull R.θ (R.MW i (sg0 D A)) (JW R i P) (chW R i P) (badS R t) (R.eWf i (sg0 D A))

def cmpV (ℓ : (R.cV i).W →ₗ[ℂ] ℂ) : (R.HV i t).H →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  ℓ.compLeft (GA D (Vc D i)) ∘ₗ R.extV i t

def eV : (GA D (Vc D i) → ℂ) →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (RealDat.eC (A := A) (sg0 D A))

def XV : Submodule ℂ (R.HV i t).H :=
  ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, (typeSub _ (R.βV i) (datV R i t P)).comap (cmpV R i t ℓ)

def V0 : Submodule ℂ (R.HV i t).H :=
  XV R i t P ⊓ ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ, (LinearMap.ker (eV R i t - LinearMap.id)).comap (cmpV R i t ℓ)

def XVc (c' : Sys D) : Submodule ℂ (R.HV i t).H :=
  XV R i t P ⊓ ⨅ ℓ : (R.cV i).W →ₗ[ℂ] ℂ,
    (eigSub _ (JV R i t P) (chV R i t P) (badS R t) c').comap (cmpV R i t ℓ)

def projectedFormsSystemPart (c' : Sys D) : Submodule ℂ (R.HV i t).H := V0 R i t P ⊓ XVc R i t P c'

def Transfer (c c' : Sys D) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), OffS D (badS R t) w → ∃ s : Multiset ℂ,
    HasPar (Wc D i) (JW R i P) (chW R i P) (badS R t) c w s ∧
    HasPar (Vc D i) (JV R i t P) (chV R i t P) (badS R t) c' w
      ((s + str (((R.C.mu0 i * R.xiH t).val w : ℂˣ) : ℂ) (Ideal.absNorm w.asIdeal) D.R.t).map
        fun z => z * (((R.C.eta.val w)⁻¹ : ℂˣ) : ℂ))

def thStar : (R.HW i (sg0 D A)).H →ₗ[ℂ] (R.HV i t).H := LinearMap.adjoint (R.thG i t)

def Z0 : Submodule ℂ (R.HV i t).H := (MW R i P).map (thStar R i t)

def OntoPartAt : Prop :=
  ∀ c ∈ IxW R i t P, (∃ c', Transfer R i t P c c') ∧
    ∀ c', Transfer R i t P c c' → (MWc R i t P c).map (thStar R i t) = projectedFormsSystemPart R i t P c'

def InjPartAt : Prop :=
  ∀ c ∈ IxW R i t P, (∃ c', Transfer R i t P c c') ∧
    ∀ c', Transfer R i t P c c' → Disjoint (projectedFormsSystemPart R i t P c') (LinearMap.ker (R.thG i t))

def SumAt : Prop :=
  (Z0 R i t P = ⨆ (c : IxW R i t P) (c' : Sys D) (_ : Transfer R i t P c c'), projectedFormsSystemPart R i t P c') ∧
    iSupIndep fun c : IxW R i t P => ⨆ (c' : Sys D) (_ : Transfer R i t P c c'), projectedFormsSystemPart R i t P c'

def KerAt : Prop :=
  let I : Set (Sys D) := {c' | (∀ w d, (¬ ∃ Rp, Hecke₂ (Vc D i) (JV R i t P) (chV R i t P) (badS R t) w d Rp) →
    c' w d = 0) ∧ ¬ ∃ c ∈ IxW R i t P, Transfer R i t P c c'}
  (LinearMap.ker (R.thG i t) ⊓ V0 R i t P = ⨆ c' : I, projectedFormsSystemPart R i t P c') ∧ iSupIndep fun c' : I => projectedFormsSystemPart R i t P c'

def AllGoodAt : Prop :=
  ∀ c ∈ IxW R i t P, ∀ c', Transfer R i t P c c' → XVc R i t P c' ≤ V0 R i t P

def BijAt : Prop :=
  Disjoint (MW R i P) (LinearMap.ker (thStar R i t)) ∧
    Module.finrank ℂ (Z0 R i t P) = Module.finrank ℂ (MW R i P)

def ThetaOntoAt : Prop := (V0 R i t P).map (R.thG i t) = MW R i P

def GoodTypes : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
      (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (a : (ZMod (D.host.g k))ˣ),
        algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (a : ZMod (D.host.g k)) = L.gen 1 →
        L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
            ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
          ((R.C.W.om k a ^ (2 * ((j : ℕ) + 1)) : ℂˣ) : ℂ) ∨
        L.teich (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
            ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) =
          (((R.C.W.om k a ^ (2 * ((j : ℕ) + 1)))⁻¹ : ℂˣ) : ℂ)

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  good : GoodTypes R

def LiftOnto : Prop := HidaSetting R F → ∀ i t b, OntoPartAt R i t (lvlP R F b)

def LiftInj : Prop := HidaSetting R F → ∀ i t b, InjPartAt R i t (lvlP R F b)

def ThetaOnto : Prop := HidaSetting R F → ∀ i t b, ThetaOntoAt R i t (lvlP R F b)

def FullEigenspaces : Prop :=
  HidaSetting R F → ∀ i t b, SumAt R i t (lvlP R F b) ∧ KerAt R i t (lvlP R F b) ∧ AllGoodAt R i t (lvlP R F b) ∧
    BijAt R i t (lvlP R F b)

end Spaces

end GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PositiveRowsTuple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain Polynomial
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance factPrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev PlOver (k : Fin 2) : Type := {PP : R.Pg // R.C.P.Div k PP.1}

abbrev Labels (D : D7) : Type := ∀ k : Fin 2, GlobalTheory.GLq.LabelDatum (D.host.g k)

abbrev ResIso : Type := ∀ (k : Fin 2) (PP : PlOver R k), ZMod (D.host.g k) ≃+* kP PP.1.1

abbrev TameLab : Type := ∀ k : Fin 2, PlOver R k → Fin D.R.m → (ZMod (D.host.g k))ˣ

abbrev Tuple : Type := ∀ k : Fin 2, PlOver R k → GlobalTheory.GLq.Gn (D.host.g k) D.R.r → ℂ

def IsTameLab (Lb : Labels D) (iso : ResIso R) (c : TameLab R) : Prop :=
  ∀ (k : Fin 2) (PP : PlOver R k) (j : Fin D.R.m) (u : (ZMod (D.host.g k))ˣ) (u' : (kP PP.1.1)ˣ),
    (u' : kP PP.1.1) = iso k PP (u : ZMod (D.host.g k)) →
      ((R.chi ((j : ℕ) + 1) PP.1.1 u' : ℂˣ) : ℂ) =
        GlobalTheory.GLq.thetaOf (Lb k) 1
          (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (c k PP j : ZMod (D.host.g k)))
          (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))

def IsGoodTuple (Lb : Labels D) (c : TameLab R) (τ : Tuple R) : Prop :=
  ∀ k : Fin 2, ∃ f : PlOver R k → (ZMod (D.host.g k))[X],
    (∀ PP, GlobalTheory.GLq.IsIrr (τ k PP) ∧ GlobalTheory.GLq.HasLabel (Lb k) (τ k PP) (f PP)) ∧
      Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) f (c k) ∧ Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) f fun PP j => (c k PP j)⁻¹

def IsCharOf (iso : ResIso R) (χ : G → D.what₂.LL) (τ : Tuple R) : Prop :=
  ∀ g : G, D.what₂.embLL (χ g) = ∏ k : Fin 2, ∏ᶠ PP : PlOver R k,
    τ k PP (Formalism.UG.bc ((iso k PP).symm : kP PP.1.1 →+* ZMod (D.host.g k)) (R.eG g PP.1))

def GoodTypes : Prop :=
  ∃ (Lb : Labels D) (iso : ResIso R) (c : TameLab R), IsTameLab R Lb iso c ∧
    (∀ χ ∈ A.X, ∃ τ, IsGoodTuple R Lb c τ ∧ IsCharOf R iso χ τ) ∧
    ∀ τ, IsGoodTuple R Lb c τ → ∃ χ ∈ A.X, IsCharOf R iso χ τ

def V0C : Submodule ℂ (R.HX A.μ0).H :=
  Submodule.span ℂ (R.jX A.μ0 '' ((A.fam.R A.μ0).goodF A.X : Set (A.fam.amb.FR A.μ0)))

def UC : Submodule ℂ (R.HX A.μ0).H := V0C R ⊓ LinearMap.ker (R.Th A.μ0)

def KerRational : Prop :=
  Submodule.span ℂ (R.jX A.μ0 '' {x | R.jX A.μ0 x ∈ UC R}) = UC R

def dimRows (b : Bool) : ℕ := Module.finrank ℂ ((R.EEat (R.levR F b)).comap R.HE.e)

def dimQ (b : Bool) : ℕ := (lv (F.fc (R.toCx F).zs) b).dQ A.μ0

theorem dimQ_eq (b : Bool) :
    dimQ R F b = Module.finrank D.what₂.LL ((A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0)) := by
  cases b <;> rfl

theorem pos_iff (b : Bool) : (lv (F.fc (R.toCx F).zs) b).Pos ↔ 0 < dimQ R F b := Iff.rfl

theorem pos_iff_ne_bot (b : Bool) :
    (lv (F.fc (R.toCx F).zs) b).Pos ↔ (A.fam.R A.μ0).inV0 (F.lvl b) ((R.toCx F).Z A.μ0) ≠ ⊥ := by
  rw [pos_iff, dimQ_eq, pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]

def HidaSetting : Prop :=
  R.toLevCh.Is A.μ0 ∧ R.IsGrp F ∧ R.IsFam ∧ R.IsModels ∧ R.IsChain ∧ R.IsThP ∧ R.IsScal F ∧ GoodTypes R

end

def AtScale (eps x0 : ℝ) (D : D7) : Prop :=
  ∃ L : SizeData₂ D, L.sc.eps = eps ∧ x0 ≤ L.sc.x ∧ Nonempty (ParameterChoice' D L) ∧ Formalism.MainNotions.SizesAt L

def AtLargeScale (P : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL], RealDat D A Ks → Face D A → Prop) : Prop :=
  ∀ eps : ℝ, ∃ x0 : ℝ, ∀ D : D7, AtScale eps x0 D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
      HidaSetting R F → P D G Pl0 T A Ks R F

def RowsPos : Prop := AtLargeScale fun _ _ _ _ _ _ _ _ _ _ _ R F => ∀ b, 0 < dimRows R F b

def DimQEq : Prop := AtLargeScale fun _ _ _ _ _ _ _ _ _ _ _ R F => KerRational R → ∀ b, dimQ R F b = dimRows R F b

def QPos : Prop :=
  AtLargeScale fun _ _ _ _ _ _ _ _ _ _ _ R F => KerRational R → ∀ b, (lv (F.fc (R.toCx F).zs) b).Pos

theorem AtScale.mono {eps x0 x1 : ℝ} {D : D7} (h : AtScale eps x1 D) (hx : x0 ≤ x1) : AtScale eps x0 D :=
  let ⟨L, h1, h2, h3⟩ := h
  ⟨L, h1, hx.trans h2, h3⟩

theorem qPos_of (h1 : RowsPos) (h2 : DimQEq) : QPos := by
  intro eps
  obtain ⟨x1, h1⟩ := h1 eps
  obtain ⟨x2, h2⟩ := h2 eps
  refine ⟨max x1 x2, fun D hD G _ _ Pl0 T A Ks _ _ _ R F hS hK b => ?_⟩
  rw [pos_iff, h2 D (hD.mono (le_max_right _ _)) G Pl0 T A Ks R F hS hK b]
  exact h1 D (hD.mono (le_max_left _ _)) G Pl0 T A Ks R F hS b

end GlobalTheory.IndefiniteRowSideFullHecke.PositiveDimensionTuples

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ProjectiveLiftExistence
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def projLift (R : RealDat D A Ks) (t : T) : (R.HX t).H →ₗ[ℂ] MMap (R.MY 0) :=
  postOn (R.MY 0) R.e0 ∘ₗ
    (PiTensorProduct.lift.symm : (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) ≃ₗ[ℂ] MMap (R.MY 0)).toLinearMap ∘ₗ R.thDn t

theorem projLift_apply (R : RealDat D A Ks) (t : T) (x : (R.HX t).H) :
    projLift R t x = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) := rfl

def Represents (R : RealDat D A Ks) (t : T) (y : (R.HX t).H →ₗ[ℂ] R.HE.H) : Prop :=
  ∀ x, R.HE.e (y x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x))

end

def ProjLiftExists : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.grp_record → R.models_HE →
      ∀ t : T, ∃ y : (R.HX t).H →ₗ[ℂ] R.HE.H, Represents R t y

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem chain_Th_iff (R : RealDat D A Ks) : R.chain_Th ↔ ∀ t, Represents R t (R.Th t) := Iff.rfl

theorem Represents.unique {R : RealDat D A Ks} (hE : R.models_HE) {t : T} {y y' : (R.HX t).H →ₗ[ℂ] R.HE.H}
    (h : Represents R t y) (h' : Represents R t y') : y = y' :=
  LinearMap.ext fun x => hE.1 ((h x).trans (h' x).symm)

theorem exists_lift_iff {X N : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup N] [Module ℂ N] {M : HMod X} {V : Submodule ℂ X}
    {ip : X → X → ℂ} (hM : M.Is V ip) (f : N →ₗ[ℂ] X) : (∃ y : N →ₗ[ℂ] M.H, ∀ x, M.e (y x) = f x) ↔ ∀ x, f x ∈ V := by
  obtain ⟨hi, rfl, -⟩ := hM
  constructor
  · rintro ⟨y, hy⟩ x
    exact ⟨y x, hy x⟩
  · intro h
    exact ⟨(LinearEquiv.ofInjective M.e hi).symm.toLinearMap ∘ₗ f.codRestrict _ h, fun x =>
      congrArg Subtype.val ((LinearEquiv.ofInjective M.e hi).apply_symm_apply ⟨f x, h x⟩)⟩

theorem exists_represents_iff {R : RealDat D A Ks} (hE : R.models_HE) (t : T) :
    (∃ y : (R.HX t).H →ₗ[ℂ] R.HE.H, Represents R t y) ↔ ∀ x, projLift R t x ∈ R.EEat R.triv := by
  refine Iff.trans ?_ (exists_lift_iff hE (projLift R t))
  simp only [Represents, projLift_apply]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveLiftExistence

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAdjointScalarParts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def badPlaces (R : RealDat D A Ks) (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun P : HeightOneSpectrum (𝓞 D.host.E) => P.under (𝓞 D.host.F)

def goodPartOff (R : RealDat D A Ks) (i : Fin D.R.m) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : EigSys D) :
    Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) S c ⊓
    R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def IsScalarOnParts (R : RealDat D A Ks) (lam : Fin D.R.m → T → EigSys D → ℝ) : Prop :=
  ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (goodPartOff R i (badPlaces R t)) (lam i t)

def ScalarAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP →
    ∃ lam : Fin D.R.m → T → EigSys D → ℝ, IsScalarOnParts R lam

def ThetaThetaAdjScalar : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ScalarAt R F

theorem gap {Rk : Ranks} (h : HCParam Rk) (j : Fin Rk.m) {n : ℕ} (hn : n < Rk.r) :
    ((Rk.t : ℚ) + 3) / 2 ≤ |Formalism.L2.NTheta.lamAt h n + h.e j| := by
  have hk := Rk.m_add_three_le_k
  have hj := j.2
  have mono : ∀ a d : ℕ, a + d < Rk.r → Formalism.L2.NTheta.lamAt h (a + d) ≤ Formalism.L2.NTheta.lamAt h a := by
    intro a d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (a + d) hd).le.trans (ih (by omega))
  have val : ∀ (c : ℕ) (hc : c < Rk.m), Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
    intro c hc
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg (by omega), dif_pos (by omega)]
    simp
  unfold Ranks.r at hn mono
  by_cases hle : n ≤ Rk.k - 1 + j
  · have h1 := mono n (Rk.k - 1 + j - n) (by omega)
    rw [show n + (Rk.k - 1 + j - n) = Rk.k - 1 + j by omega, val j hj] at h1
    have h2 := h.gap_be j
    exact le_trans (by simp only [Fin.eta] at h1; linarith) (le_abs_self _)
  · have hj1 : (j : ℕ) + 1 < Rk.m := by omega
    have h1 := mono (Rk.k - 1 + (j + 1)) (n - (Rk.k - 1 + (j + 1))) (by omega)
    rw [show Rk.k - 1 + (j + 1) + (n - (Rk.k - 1 + (j + 1))) = n by omega, val _ hj1] at h1
    have h2 := h.gap_eb j hj1
    exact le_trans (by linarith) (neg_le_abs _)

theorem IsScalarOnParts.mem {R : RealDat D A Ks} {lam : Fin D.R.m → T → EigSys D → ℝ} (h : IsScalarOnParts R lam)
    (i : Fin D.R.m) (t : T) (c : EigSys D) {x} (hx : x ∈ goodPartOff R i (badPlaces R t) c) :
    R.thG i t (LinearMap.adjoint (R.thG i t) x) ∈ goodPartOff R i (badPlaces R t) c := by
  rw [h i t c x hx]; exact Submodule.smul_mem _ _ hx

theorem offS_iff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push_neg at hc
    apply h
    have hle : v.asIdeal ≤ (P.under (𝓞 D.host.F)).asIdeal := by
      intro x hx
      obtain ⟨y, hy, hyP⟩ := hc x hx
      have : y = algebraMap _ _ x := RingOfIntegers.ext hy
      subst this
      exact hyP
    have := v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top hle
    rwa [show P.under (𝓞 D.host.F) = v from HeightOneSpectrum.ext this.symm]

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents

end
end

