import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

namespace GlobalTheory.HoweR

section Gl

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

def IsGl (F : ι → ι → Module.End ℂ M) : Prop :=
  ∀ a b c d, F a b * F c d - F c d * F a b = (if b = c then F a d else 0) - (if d = a then F c b else 0)

def negT (F : ι → ι → Module.End ℂ M) : ι → ι → Module.End ℂ M := fun a b => -F b a

def cas (s : ι → Bool) (F : ι → ι → Module.End ℂ M) : Module.End ℂ M :=
  ∑ a, ∑ b, if s a = s b then F a b * F b a else 0

def qop (F : ι → ι → Module.End ℂ M) (α β : ℂ) (a b : ι) : Module.End ℂ M :=
  ∑ c, F a c * F c b - α • F a b - if a = b then β • 1 else 0

def UnitOn (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) : Prop :=
  FiniteDimensional ℂ U ∧ (∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) ∧
    ∃ ip : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (∀ x ∈ U, ∀ y ∈ U, star (ip x y) = ip y x) ∧ (∀ x ∈ U, x ≠ 0 → 0 < (ip x x).re) ∧
      ∀ a b, s a = s b → ∀ x ∈ U, ∀ y ∈ U, ip (F a b x) y = ip x (F b a y)

def LocU (s : ι → Bool) (F : ι → ι → Module.End ℂ M) : Prop :=
  ∀ t : Finset M, ∃ U : Submodule ℂ M, (∀ x ∈ t, x ∈ U) ∧ UnitOn s F U

end Gl

section Act

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def units (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Ix p q → Ix p q → Module.End ℂ V := fun a b => act (Eab a b)

def Stab (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) : Prop := ∀ Z, ∀ y ∈ N, act Z y ∈ N

def Good (act : Mat p q →ₗ[ℂ] Module.End ℂ V) : Prop :=
  IsLieAct act ∧ (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) ∧ LocU (fun a : Ix p q => a.isLeft) (units act)

def QuadMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (α β α' β' : ℂ) (N N' : Submodule ℂ V) : Prop :=
  ∀ a b, ∀ v ∈ N', qop (units act) α β a b v ∈ N ∧ qop (negT (units act)) α' β' a b v ∈ N

def AdmMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  ∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) → hwSub act μ ≤ U ⊔ C

def CycMod (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  ∃ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ ∧ genSub act {v} ⊔ C = ⊤ ∧ hwSub act μ ≤ Submodule.span ℂ {v} ⊔ C

def Pack (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  Good act ∧ Stab act C ∧ (∃ α β α' β' : ℂ, QuadMod act α β α' β' C ⊤) ∧ AdmMod act C ∧ CycMod act C

end Act

def coinv (P Q R S : ℕ) (x : ℂ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Formalism.BasicNotions.TH.Pol P Q R S), g = fockAct1 P Q R S X f - (x * X.trace) • f}

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

def actAt {p q : ℕ} (w : T) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) : Mat p q →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  ((PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w) ∘ₗ a

theorem actAt_apply {p q : ℕ} (w : T) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (Z : Mat p q) :
    actAt w a Z = atPl w (a Z) := rfl

def tensAll (H : ∀ w, Submodule ℂ (V w)) : Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ {y | ∃ f : ∀ w, V w, (∀ w, f w ∈ H w) ∧ y = PiTensorProduct.tprod ℂ f}

def tensAny (C : ∀ w, Submodule ℂ (V w)) : Submodule ℂ (⨂[ℂ] i, V i) :=
  Submodule.span ℂ {y | ∃ f : ∀ w, V w, (∃ w, f w ∈ C w) ∧ y = PiTensorProduct.tprod ℂ f}

end Tensor

def HoweAlg {T : Type} {R S : T → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V) (C : Submodule ℂ V) : Prop :=
  (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ k, (∀ w, Stab (a w) (N k)) ∧ C ≤ N k) → m ≤ L) ∧
  ∀ N N' : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → N ≠ ⊤ → (∀ w, Stab (a w) N') → C ≤ N' → N' ≠ ⊤ → N ⊔ N' ≠ ⊤

example : IsGl (fun _ _ : Fin 2 => (0 : Module.End ℂ ℂ)) ∧ cas (fun _ : Fin 2 => true) (fun _ _ => (0 : Module.End ℂ ℂ)) = 0 := by
  refine ⟨fun a b c d => by simp, by simp [cas]⟩

end GlobalTheory.HoweR

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type}

def dblAct (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (w : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) :
    (κ' ⊕ κ' → AF F) × (κ' ⊕ κ' → AF F) :=
  (Sum.elim (s (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl)).1 (s (w.1 ∘ Sum.inr, -(w.2 ∘ Sum.inr))).1,
    Sum.elim (s (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl)).2 (-(s (w.1 ∘ Sum.inr, -(w.2 ∘ Sum.inr))).2))

variable [Fintype κ] [Fintype κ']

structure IsOp (ψ : AddChar (AF F) ℂ) (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ'
  pres' : ∀ φ ∈ schA F κ', S' φ ∈ schA F κ
  left : ∀ φ ∈ schA F κ, S' (S φ) = φ
  right : ∀ φ ∈ schA F κ', S (S' φ) = φ
  adm : ∀ l ∈ (adeleClass F).adm κ', l ∘ₗ S ∈ (adeleClass F).adm κ
  adm' : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S' ∈ (adeleClass F).adm κ'
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (s w) (S φ)
  theta : ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F κ, thetaSum F (S φ) = c * thetaSum F φ
  norm : ∀ (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

def IsOp2 (ψ : AddChar (AF F) ℂ) (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop :=
  IsOp ψ s S S' ∧ ∃ Sd Sd', IsOp ψ (dblAct s) Sd Sd' ∧
    ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, Sd (boxFun φ₁ φ₂) = boxFun (S φ₁) (star (S (star φ₂)))

end GlobalTheory.TowU

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows

namespace GlobalTheory.LowRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def AdelC (F : Face D A) : Prop :=
  GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (b : ℝ), Sizes D i b → ∀ t : T, PrimeToHost R t →
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s →
  ∀ P : LevelP R.Pg D.R.r ℂ, IsLocalLevel P →
  ∀ (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), IsConjChars R i t s cμ cη m →
  ∀ ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ),
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω →
  ∀ BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) →
  ∀ f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ,
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f →
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) →
  ∀ c : CoefA (Vc D i), c.Is →
  ∀ io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io →
  ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))),
    IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)) ν 𝓕 →
  ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf (Vc D i)),
    Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y →
  ∀ HV : HMod (Bridge.Gf (Vc D i) → c.W),
    HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y) →
    (∃ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th) ∧
    ∀ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th →
      ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ t P ev, th (adjLev P th x) = (l : ℂ) • x) ∧
          mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l

def LiftIsCuspC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f c io =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ φ ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)),
      ∃ U ∈ R.Wall i σ, ∀ (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)), U (fun ρ => v ρ) g =
        Lift.thetaPInt ν 𝓕 (fun g h f => Datum.thetaKO ω h g f) (ptAt R i σ BW f) io (c.ext φ) (PiTensorProduct.tprod ℂ v) g

open Datum in

def FiniteZetaC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P _ ω _ f _ _ =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
      ∃ x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ,
        (∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2)) ∧
        ∀ U₁ ∈ partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) ev,
        ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec,
          HasSum (fun y : FinCos (Wc D i) (levW R i) =>
              l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
            ((Nat.card P.H : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (eulerOff D (finS R t) x / (dOff D (finS R t) : ℂ)) *
              starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂)))

def FormalDegreeUpperC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i _ σ _ _ _ _ _ _ _ =>
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ (ρ : D.what₂.Tau) (mR : Measure (Upq (Wc D i) ρ)), Lev.IsMinf mR →
    ∀ e : lowT (R.MW i σ) ρ, ‖((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 →
      let k : Upq (Wc D i) ρ → ℝ := fun b => ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2
      Integrable k mR ∧ 0 < ∫ b, k b ∂mR ∧
        Real.log (∫ b, k b ∂mR)⁻¹ ≤
          2 + (D.R.r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (D.R.r : ℝ) ^ 2 * D.R.nV * ((degAt D i σ ρ : ℝ) + 2))

def GalOut (i : Fin D.R.m) (ph : ℂ) : Prop :=
    (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) ∧
    (∀ gramR c0R c0L,
      Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
        (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
      ∀ σ, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i)) ∧
    ∀ σ, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK ((starRingEnd ℂ).comp σ) ∧
      ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ =
        starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ

def StdV (D : D7) : Prop := ∀ i : Fin D.R.m, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)

end

def ConjRatLift5 : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ),
    GlobalTheory.Core5 R F → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R κ v₀, BarTie fw → IoExt R → R.LUnif → (∀ i, OMPins T R κ v₀ O i) →
    ∀ i : Fin D.R.m, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph →
     GalOut R i ph

theorem AdelC.full {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (h : AdelC R F) :
    AdelicLiftScalar R F := fun hc => h ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩

theorem ConjRatLift5.full (h : ConjRatLift5) : GlobalTheory.ConjScalar.ConjRatLift :=
  fun D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hc => h D G Pl0 T0 A T R F κ v₀ O ph (GlobalTheory.Core5.of_char hc)

end GlobalTheory.LowRow

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HoweD

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}

variable (F) in

abbrev TensD (P Q R S : InfinitePlace F → ℕ) : Type := ⨂[ℂ] w : InfinitePlace F, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)

def FramedD (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) : Prop :=
  a * b = Complex.I ∧ (∀ w, IsFrame (a • JA.map (piInf (τ w))) (A w)) ∧ ∀ w, IsFrame (b • JB.map (piInf (τ w))) (C w)

def IsFockMapD (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) : Prop :=
  Function.Injective Φ ∧ ∀ u : Matrix α β (AE F E), At (evI F) u →
    ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      ∀ T, SD (fun t => d.rho ψ (realAd F t • u)) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))

def IsGenD (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)}
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (γ : Multiplicative ℝ →* UG (cA σ) J) (Y : ∀ w : InfinitePlace F, Mat (R w) (S w)) : Prop :=
  ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
    C w * NormedSpace.exp (t • Y w)

def ActsByD (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {r s : InfinitePlace F → ℕ}
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (r w) (s w)) ℂ) (om : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ))
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (act : ∀ w, Mat (r w) (s w) →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (c : InfinitePlace F → ℂ) : Prop :=
  ∀ γ ∈ RLines σ J, ∀ Y, IsGenD τ C γ Y → ∀ T, SD (fun t => om (γ (Multiplicative.ofAdd t))) (Φ T)
    (Φ (sumPl (fun w => act w (Y w) + (c w * (Y w).trace) • 1) T))

end Adelic

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev DatFn (D : D7) (i : Fin D.R.m) : Type :=
  (∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) → ℂ

abbrev IsWeilTw (χ : (AE D)ˣ →* Circle) (ω : WeilRep D i) : Prop :=
  IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω

open Classical in

def VecOf (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) ∧
    ∃ e : AE D, IsIdemSum e (R.Pg ∪ Q) ∧
      IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i)
        (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
          Ω (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) φ

open Classical in

def PhiOf (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (N : Submodule (𝓞 D.host.E) La)
    (φ : (Fin (Vc D i).rank → La ⧸ N) → ℂ) : Prop :=
  ∃ e : AE D, IsIdemSum e (R.Pg ∪ Q) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)) ∧
    φ (fun b => Submodule.Quotient.mk (x b)) =
      Ω (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)))

def ReadsOnly {i : Fin D.R.m} (S : Finset (Pl D.host.E)) (Ω : DatFn D i) : Prop :=
  ∀ y y', (∀ PP ∈ S, y PP = y' PP) → Ω y = Ω y'

open Classical in

def omegaFree (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) : DatFn D i := fun y =>
  (if ∀ PP ∈ R.Pg, y PP = y₀ PP then 1 else 0) *
    if h : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det then ∏ PP ∈ Q.attach, (((ξR PP.1 (h PP.1 PP.2).unit)⁻¹ : ℂˣ) : ℂ) else 0

structure KerDat (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ) : Prop where
  chr : ChrEq χ ξ
  fin : ∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n
  triv : ξ.TrivOn D.host.F
  tame : ∀ v, ξ.TameAt v
  pl : IsTwistPlaces D.host.g Q
  off : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  ram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, IsConjPl PP' PP
  res : ∀ PP ∈ Q, IsRes ξ PP (ξR PP)
  weil : IsWeilTw R i χ ω
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg Q ξR (R.vacP i) φ

variable {R i}

theorem KerDat.isKernel {ξ χ ξR Q ω φ} (h : KerDat R i ξ χ ξR Q ω φ) : IsKernel R i ξ Q ω φ :=
  ⟨χ, ξR, h.chr, h.res, h.weil, h.vec⟩

theorem KerDat.vecOf {ξ χ ξR Q ω φ} (h : KerDat R i ξ χ ξR Q ω φ) :
    VecOf R i Q (fun y => omegaK R.Pg y * omegaQ Q (Wc D i).rank ξR (-1) y) φ := h.vec

theorem kerDat_tuple (hL : R.toLevCh.Is A.μ0) (hP : R.IsThP) (t : T0) :
    KerDat R i (R.xiH t) (R.xi t) (R.xiR t) (R.Q t) (R.ωP i t) (R.vP i t) :=
  ⟨hL.xi t, hL.xi_fin t, hL.xi_triv t, hL.xi_tame t, hL.Q_pl t, fun PP h => (hL.Q_off t PP h).1, hL.Q_ram t, hL.xiR t,
    hP.ωP i t, hP.vP i t⟩

end GlobalTheory.OnCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.UG Formalism.BasicNotions
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.PRep

namespace GlobalTheory.ResW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def rootPow (Λ : Fin N → ℝ) (r : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, if h : (i : ℕ) + 1 < N then (r i / r ⟨i + 1, h⟩) ^ Λ i else 1

def Bd (Λ : Fin N → ℝ) (f : GA E N → ℂ) : Prop :=
  ∀ Ω : Set (GL (Fin N) (Cinf E)), IsCompact Ω → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ (r : Fin N → ℝ) (d : GL (Fin N) (Cinf E)),
    (∀ i, 0 < r i) → (∀ i j : Fin N, (j : ℕ) = i + 1 → t * r j ≤ r i) →
    d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖f (infGL E N (d * c))‖ ≤ C * rootPow Λ r

def BdD (Λ : Fin N → ℝ) (φ : Sm E N) : Prop := ∀ l : List (Lie E N), Bd Λ ((l.map (lie E N)).prod φ).1

def locR (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin N) (w.adicCompletion E)) (Sm E N) :=
  (finRep E N).comp (locGL E N w)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

def LocMap (V : Submodule ℂ (Sm E N)) (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (y : Fin n → GlobalTheory.LocGL.IrrGL (w.adicCompletion E)) (hd : ∑ i, (y i).1 = N) : Prop :=
  ∃ b : Sm E N →ₗ[ℂ] GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.stdBlocks (fun i => (y i).1) hd) (GlobalTheory.SmGL.piTensor fun i => (y i).rep),
    (∃ φ ∈ V, b φ ≠ 0) ∧ ∀ φ ∈ V, ∀ g, b (locR N w g φ) = GlobalTheory.LocGL.prodIrr y hd g (b φ)

section CM

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

structure IsBCW (π : Submodule ℂ (UA L n → ℂ)) {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (V : ∀ i, Submodule ℂ (Sm L (N i)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 L)), SmIrr (GL (Fin (N i)) (w.adicCompletion L)))
    (m : Fin c → (L →+* ℂ) → Multiset ℂ) : Prop where
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  unram : ∀ w, IsUnramU π w → GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w n)
  inert : ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L)
    (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w (locProd h w (σ · w)) (GlobalTheory.LGrp.bcParam n α)
  split : ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))
  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, m i τ = infOfWeight lam

end CM

def BCSpehU : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L],
    (∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA L n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm L (N i)))
        (σ : ∀ i (w : HeightOneSpectrum (𝓞 L)), SmIrr (GL (Fin (N i)) (w.adicCompletion L)))
        (m : Fin c → (L →+* ℂ) → Multiset ℂ), IsBCW π h V σ m ∧
        ∀ i, ∃ (a d : ℕ) (P : CuspSub L a), SpehShape (V i) P d ∧ P.IsCsd

end GlobalTheory.ResW

end
end

