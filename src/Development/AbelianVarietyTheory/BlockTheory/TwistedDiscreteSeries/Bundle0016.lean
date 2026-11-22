import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

section Abstract

variable {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E]

def HasRationalTest (σ : K →+* ℂ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ e ∈ S, ∀ a, ∃ z : K, σ z = ψ a e

example : HasRationalTest (algebraMap ℚ ℂ) ({Complex.I} : Set ℂ) := by
  refine ⟨1, fun _ => (-Complex.I) • LinearMap.id, fun e he => ?_, ?_⟩
  · simpa using he 0
  · rintro e rfl a
    exact ⟨1, by simp⟩

example : ¬ HasRationalTest (algebraMap ℚ ℂ) ({1, Complex.I} : Set ℂ) := by
  rintro ⟨n, ψ, hinj, hrat⟩
  refine one_ne_zero (hinj 1 fun a => ?_)
  obtain ⟨p, hp⟩ := hrat 1 (by simp) a
  obtain ⟨q, hq⟩ := hrat Complex.I (by simp) a
  have h : ψ a Complex.I = Complex.I * ψ a 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [← hp, ← hq] at h
  have h2 := congrArg Complex.im h
  simp at h2
  rw [← hp]
  have hp0 : p = 0 := by exact_mod_cast h2.symm
  simp [hp0]

end Abstract

section Interface

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}

def RowTest (X : CxData A) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (X.EE →ₗ[ℂ] ℂ)), (∀ e : X.EE, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : Bs.Tup) (x : A.FR t) (a : Fin n), ∃ z : K, Bs.v0.embedding z = ψ a (X.Θ t (X.jR t x))

def rationalRows (X : CxData A) : Set X.EE := {e | ∃ (t : Bs.Tup) (x : A.FR t), X.Θ t (X.jR t x) = e}

def FormsSpan (X : CxData A) : Prop := ∀ t, Submodule.span ℂ (Set.range (X.jR t)) = ⊤

def KerRational (X : CxData A) : Prop :=
  ∀ t, Submodule.span ℂ (X.jR t '' {x : A.FR t | X.Θ t (X.jR t x) = 0}) = LinearMap.ker (X.Θ t)

def KerRationalOfRowTest : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (A : DefAmb Bs) (X : CxData A),
    FormsSpan X → RowTest X → KerRational X

def RatMuOfRowTest : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (A : DefAmb Bs) (X : CxData A)
    (fc : DefSub A → DefFace Bs) (cr : Crd A fc) (b : Bool), X.H2 cr b → RowTest X → X.RATmu cr b

end Interface

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowTestAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → RowTest (R.toCx F)

def RowTestModel (R : RealDat D A Ks) : Prop :=
  ∃ (n : ℕ) (ψ : Fin n → (R.HE.H →ₗ[ℂ] ℂ)), (∀ e : R.HE.H, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : T) (x : A.fam.amb.FR t) (a : Fin n), ∃ z : D.what₂.LL, D.what₂.embLL z = ψ a (R.Th t (R.jX t x))

def twFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E →ₗ[ℂ] ℂ) : Tw s E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.out x))
  map_add' x y := by rw [Tw.out_add, map_add, map_add]
  map_smul' z x := by rw [Tw.out_smul, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

def untwFun (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : Tw s E →ₗ[ℂ] ℂ) : E →ₗ[ℂ] ℂ where
  toFun x := cj s (f (Tw.mkL s E x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' z x := by rw [map_smulₛₗ, map_smul, smul_eq_mul, map_mul, cj_cj]; rfl

theorem test_tw_iff {K E : Type} [Field K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {σ σ' : K →+* ℂ}
    (h : ∀ a, σ' a = cj s (σ a)) {ι : Type} {X : ι → Type} (v : ∀ t, X t → E) :
    (∃ (n : ℕ) (ψ : Fin n → (Tw s E →ₗ[ℂ] ℂ)), (∀ e : Tw s E, (∀ a, ψ a e = 0) → e = 0) ∧
      ∀ t x a, ∃ z : K, σ' z = ψ a (Tw.mk s (v t x))) ↔
    (∃ (n : ℕ) (ψ : Fin n → (E →ₗ[ℂ] ℂ)), (∀ e : E, (∀ a, ψ a e = 0) → e = 0) ∧ ∀ t x a, ∃ z : K, σ z = ψ a (v t x)) := by
  constructor
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => untwFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    refine ⟨z, ?_⟩
    have := congrArg (cj s) ((h z).symm.trans hz)
    rw [cj_cj] at this
    exact this
  · rintro ⟨n, ψ, hinj, hrat⟩
    refine ⟨n, fun a => twFun s (ψ a), fun e he => hinj e fun a => (map_eq_zero (cj s)).1 (he a), fun t x a => ?_⟩
    obtain ⟨z, hz⟩ := hrat t x a
    exact ⟨z, (h z).trans (congrArg (cj s) hz)⟩

theorem rowTest_toCx_iff (R : RealDat D A Ks) (F : Face D A) : RowTest (R.toCx F) ↔ RowTestModel R :=
  test_tw_iff (E := R.HE.H) (twAt D.what₂.embLL A.v0) R.emb0 (ι := T) (X := fun t => A.fam.amb.FR t) fun t x => R.Th t (R.jX t x)

def RowTestAlgAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → ∃ (n : ℕ) (ψ : Fin n → ((R.toCx F).EE →ₗ[ℂ] ℂ)), (∀ e, (∀ a, ψ a e = 0) → e = 0) ∧
    ∀ (t : T) (x : A.fam.amb.FR t) (a : Fin n), IsAlgebraic ℚ (ψ a ((R.toCx F).Θ t ((R.toCx F).jR t x)))

def KerRationalAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → KerRational (R.toCx F)

def RatMuAt (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → ∀ b, (R.toCx F).RATmu F.cr b

end Concrete

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaMultiplicity
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Premises (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 ∧ R.models_inf ∧ RealDat.models_vpos (D := D) ∧ R.models_cV ∧ R.models_HV ∧ R.models_νV ∧
    R.models_BV ∧ R.models_order ∧ R.thP_ωP ∧ R.thP_vP ∧ R.thP_pt_theta ∧ R.thP_ioP

def kernelP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i))
    (Φ : WO (Vc D i) (Wc D i) → ℂ) : ℂ :=
  thetaKO (R.ωP i t) h g Φ

def IsThetaMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, y x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP : LinearMap.range (R.extV i t) →ₗ[ℂ] (LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ)),
      Lift.IsThetaP (R.νV i t) (R.fdV i t) (kernelP R i t) (R.ptP i t) (R.ioP i) (LinearMap.range (R.extV i t)) thP ∧
      ∀ (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
        y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
          thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

def ThetaMultExistsFor (R : RealDat D A Ks) : Prop :=
  Premises R → ∀ (i : Fin D.R.m) (t : T), ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaMult R i t y

end

def ThetaMultExists (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ThetaMultExistsFor R

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaPrimeMultiplicity
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaPrimeMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section At

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def IsThetaPrimeMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, y x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP : LinearMap.range (R.extV i t) →ₗ[ℂ] (LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ)),
      Lift.IsThetaP (R.νV i t) (R.fdV i t)
          (fun (g : GA D (Wc D i)) (h : GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) => thetaKO (R.ωP i t) h g f)
          (R.ptP i t) (R.ioP i) (LinearMap.range (R.extV i t)) thP ∧
        ∀ (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
          y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
            thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

def ThetaPrimeExistsFor (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → R.fam_tie → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta → R.thP_ioP →
    ∀ (i : Fin D.R.m) (t : T), ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaPrimeMult R i t y

set_option maxHeartbeats 1000000 in

theorem IsThetaPrimeMult.integral {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    {y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))} (h : IsThetaPrimeMult R i t y)
    (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    IntegrableOn (fun u : GA D (Vc D i) =>
        R.ωP i t (u, g) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) (R.extV i t x u))) 0) (R.fdV i t) (R.νV i t) ∧
      y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) g =
        ∫ u in R.fdV i t, R.ωP i t (u, g) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) (R.extV i t x u))) 0 ∂(R.νV i t) := by
  obtain ⟨-, thP, h1, h2⟩ := h
  have e1 := h1.integ ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v) g
  have e2 := h1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v) g
  have e3 : (((R.extV i t).rangeRestrict x : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) = R.extV i t x := rfl
  simp only [Lift.thetaPInt, thetaKO, e3] at e1 e2
  exact ⟨e1, (congrFun (h2 x v) g).trans e2⟩

theorem isThetaPrimeMult_thF_iff (R : RealDat D A Ks) :
    (∀ i t, IsThetaPrimeMult R i t (R.thF i t)) ↔ R.thP_thF_mem ∧ R.thP_thF :=
  ⟨fun h => ⟨fun i t => (h i t).1, fun i t => (h i t).2⟩, fun h i t => ⟨h.1 i t, h.2 i t⟩⟩

end At

def ThetaPrimeExists (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ThetaPrimeExistsFor R

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaPrimeMultiplicity

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SizeOK (D : D7) : Prop := 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def transl (R : RealDat D A Ks) (i : Fin D.R.m) (g : G) :
    MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g))

def thetaTranslates (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (MMap (R.MW i (sg0 D A))) :=
  {y | ∃ (g : G) (x : (R.HV i t).H), y = transl R i g (R.thF i t x)}

def SpanAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  Submodule.span ℂ (thetaTranslates R i t) = R.Wall i (sg0 D A)

def goodModel (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def GoodRangeAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  LinearMap.range (R.thG i t) = goodModel R i

def ThetaSpan (R : RealDat D A Ks) (F : Face D A) : Prop :=
  SizeOK D → R.Char F → ∀ i : Fin D.R.m, SpanAt R i A.μ0

def ThetaGoodRange (R : RealDat D A Ks) (F : Face D A) : Prop :=
  SizeOK D → R.Char F → ∀ (i : Fin D.R.m) (t : T), GoodRangeAt R i t

def ThetaGoodRangeGap (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → ∀ (i : Fin D.R.m) (t : T), GoodRangeAt R i t

theorem range_eq_comap_iff {X H M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup H] [Module ℂ H] [AddCommGroup M]
    [Module ℂ M] (e : H →ₗ[ℂ] M) (f : X →ₗ[ℂ] H) (p : X →ₗ[ℂ] M) (U : Submodule ℂ M) (hinj : Function.Injective e)
    (hle : U ≤ LinearMap.range e) (hc : ∀ x, e (f x) = p x) :
    LinearMap.range f = U.comap e ↔ LinearMap.range p = U := by
  have hcomp : e ∘ₗ f = p := LinearMap.ext hc
  rw [← hcomp, LinearMap.range_comp]
  constructor
  · intro h
    rw [h, Submodule.map_comap_eq_self hle]
  · intro h
    rw [← h, Submodule.comap_map_eq_of_injective hinj]

set_option maxHeartbeats 1000000 in

theorem goodRangeAt_iff {R : RealDat D A Ks} (hW : R.models_HW) (hG : R.thP_thG) (i : Fin D.R.m) (t : T) :
    GoodRangeAt R i t ↔
      LinearMap.range (postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) ∘ₗ R.thF i t) = R.Wat i (sg0 D A) R.triv :=
  range_eq_comap_iff (R.HW i (sg0 D A)).e (R.thG i t) _ (R.Wat i (sg0 D A) R.triv) (hW i (sg0 D A)).1
    (le_of_le_of_eq inf_le_left (hW i (sg0 D A)).2.1.symm) (fun x => hG i t x)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TranslateRepresentations
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Space

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)

def LiftsTo (κ : (levEnv V β L).Q) (g₀ : G0 L.Pg L.r) : Prop :=
  rTup β L (Formalism.UG.bc (swapAE D) ((κ : Bridge.Gf V) : GL _ _)) = g₀

def IsTranslate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (g₀ : G0 L.Pg L.r) (F F' : Bridge.Gf V → W) : Prop :=
  (∃ κ, LiftsTo V β L κ g₀) ∧
    ∀ κ, LiftsTo V β L κ g₀ → ∀ h, F' h = ((((levEnv V β L).ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * (κ : Bridge.Gf V))

def IsTransRep {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r)
    (M : HMod (Bridge.Gf V → W)) (ρ : Representation ℂ G M.H) : Prop :=
  ∀ g x, IsTranslate V β L (eG g) (M.e x) (M.e (ρ g x))

variable {V β L}

theorem IsTranslate.unique {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r}
    {F F₁ F₂ : Bridge.Gf V → W} (h₁ : IsTranslate V β L g₀ F F₁) (h₂ : IsTranslate V β L g₀ F F₂) : F₁ = F₂ := by
  obtain ⟨κ, hκ⟩ := h₁.1
  funext h
  rw [h₁.2 κ hκ h, h₂.2 κ hκ h]

theorem IsTransRep.unique {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G]
    {eG : G ≃* G0 L.Pg L.r} {M : HMod (Bridge.Gf V → W)} (hM : Function.Injective M.e) {ρ₁ ρ₂ : Representation ℂ G M.H}
    (h₁ : IsTransRep V β L eG M ρ₁) (h₂ : IsTransRep V β L eG M ρ₂) : ρ₁ = ρ₂ := by
  ext g x
  exact hM ((h₁ g x).unique (h₂ g x))

theorem IsTransRep.eq_of_translate {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {G : Type} [Group G]
    {eG : G ≃* G0 L.Pg L.r} {M : HMod (Bridge.Gf V → W)} (hM : Function.Injective M.e) {ρ : Representation ℂ G M.H}
    (h : IsTransRep V β L eG M ρ) {g : G} {x x' : M.H} (hx : IsTranslate V β L (eG g) (M.e x) (M.e x')) : x' = ρ g x :=
  hM (hx.unique (h g x))

theorem IsTranslate.eq_g0Act {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r}
    {F F' : Bridge.Gf V → W} (h : IsTranslate V β L g₀ F F') (κ : (levEnv V β L).Q) (hκ : LiftsTo V β L κ g₀) :
    F' = Bridge.g0Act (levEnv V β L).ch κ F :=
  funext (h.2 κ hκ)

end Space

def Commutes {G E E' : Type} [Group G] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (f : E →ₗ[ℂ] E') : Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IsActX (t : T) (ρ : Representation ℂ G (R.HX t).H) : Prop :=
  IsTransRep D.sp.X' R.βX (R.datXt t) R.eG (R.HX t) ρ

def IsActV (i : Fin D.R.m) (t : T) (ρ : Representation ℂ G (R.HV i t).H) : Prop :=
  IsTransRep (Vc D i) (R.βV i) (R.datVt i t) R.eG (R.HV i t) ρ

def GEquiv : Prop :=
  (∀ t, ∃ ρ, IsActX R t ρ ∧ Commutes ρ R.gE (R.Th t)) ∧
    ∀ i t, ∃ ρ, IsActV R i t ρ ∧ Commutes ρ (R.gW i (sg0 D A)) (R.thG i t)

def GEquivAdj : Prop :=
  (∀ t, ∃ ρ, IsActX R t ρ ∧ Commutes R.gE ρ (LinearMap.adjoint (R.Th t))) ∧
    ∀ i t, ∃ ρ, IsActV R i t ρ ∧ Commutes (R.gW i (sg0 D A)) ρ (LinearMap.adjoint (R.thG i t))

theorem GEquiv.th_of_translate (h : GEquiv R) (t : T) (hinj : Function.Injective (R.HX t).e) (g : G) (x x' : (R.HX t).H)
    (hx : IsTranslate D.sp.X' R.βX (R.datXt t) (R.eG g) ((R.HX t).e x) ((R.HX t).e x')) :
    R.Th t x' = R.gE g (R.Th t x) := by
  unfold GEquiv at h
  refine (h.1 t).elim fun ρ hh => ?_
  have hρ := hh.1
  have hc := hh.2
  unfold IsActX at hρ
  have e : x' = ρ g x := IsTransRep.eq_of_translate (V := D.sp.X') (β := R.βX) (L := R.datXt t) (eG := R.eG) hinj hρ hx
  rw [e]
  exact hc g x

variable (D) in

def GEquivAll : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    R.Char F → GEquiv R ∧ GEquivAdj R

end GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilSignShift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NcGapGt (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h < |((x.1 - y.1 : ℚ) : ℝ)|

def NcGapGe (S : SPar) (h : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h ≤ |((x.1 - y.1 : ℚ) : ℝ)|

def minSig (S : SPar) : ℕ :=
  min (S.filter fun x => x.2 = true).card (S.filter fun x => x.2 = false).card

def shiftPar (c : ℚ) (S : SPar) : SPar := S.image fun x => (x.1 + c, x.2)

variable (D : D7)

def alV (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i - 1 / 2 else -(D.hc τ).e i

def alW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℚ :=
  if Odd ((i : ℕ) + 1) then -(D.hc τ).e i else -(D.hc τ).e i - 1 / 2

def lamS (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alW D i τ) (parA (Ptw D) i τ)

def lamT (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := shiftPar (-alV D i τ) (parA (Ptw D) ((i : ℕ) + 1) τ)

def StepGap (i : Fin D.R.m) : Prop :=
  ∀ τ, NcGapGt (lamS D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGt (lamT D i τ) ((D.R.rankY ((i : ℕ) + 1) : ℝ) ^ 3) ∧
    NcGapGe (lamS D i τ) (120 * (D.R.rankY i : ℝ) * (minSig (lamS D i τ) : ℝ) ^ ((3 : ℝ) / 2))

variable {D}

def StepWeil (ψ : AddChar (AF D.host.F) ℂ) (i : Fin D.R.m) (V W : HSp D)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) : Prop :=
  ∃ χV χW : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χV χW ω ∧
    ∀ τ, HasInfExp D χV τ (alV D i τ) ∧ HasInfExp D χW τ (alW D i τ)

def VacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f

def fockOf {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) : PolF D W.rank V.rank → (WO V W → ℂ) :=
  pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f

def ItPair (D : D7) : Prop :=
  ∀ (i : Fin D.R.m), StepGap D i →
    ∀ (θ : InfFam D), IsInfFam θ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar), S = parB (Ptw D) i → S' = parB (Ptw D) ((i : ℕ) + 1) →
    ∀ (M : DSModel V S) (M' : DSModel W S'),
      ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
        ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ),
          StepWeil ψ i V W ω → VacVec ψ θ M M' f → f ≠ 0 →
            IsItW θ M M' ω (fockOf ψ θ M M' f) It

end GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift

end
end

