import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZero
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OActFinEt

variable {S : Scheme.{0}} {O : Type} [CommRing O] {A : Over S} [GrpObj A]

theorem act_zero (act : OAct O A) : act.act 0 = 1 :=
  mul_left_cancel (a := act.act 0) (by rw [_root_.mul_one, ← act.add, add_zero])

theorem act_natCast (act : OAct O A) : ∀ n : ℕ, act.act (n : O) = 𝟙 A ^ n
  | 0 => by rw [Nat.cast_zero, act_zero, pow_zero]
  | n + 1 => by rw [Nat.cast_succ, act.add, act_natCast act n, act.one, pow_succ]

theorem exists_natCast_dvd {E : Type} [Field E] [NumberField E] (b : 𝓞 E) (hb : b ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ b ∣ (n : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · exact Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)

theorem finite_etale_act (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k]
    [CharZero k] (A : Over (Sp k)) [GrpObj A] (act : OAct (𝓞 E) A) (g : ℕ) :
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ b : 𝓞 E, b ≠ 0 →
      IsFinite (act.act b).left ∧ Etale (act.act b).left ∧
        Finite {x : 𝟙_ (Over (Sp k)) ⟶ A // x ≫ act.act b = 1} := by
  intro hA hg b hb
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  obtain ⟨n, hn0, b', hb'⟩ := exists_natCast_dvd b hb
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    simpa using (Ne.isUnit hnk).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have h1 : act.act b ≫ act.act b' = 𝟙 A ^ n := by rw [← act.mul, ← hb', act_natCast]
  have h2 : act.act b' ≫ act.act b = 𝟙 A ^ n := by rw [← act.mul, mul_comm, ← hb', act_natCast]
  haveI := act.hom b
  haveI := act.hom b'
  haveI hF : IsFinite (𝟙 A ^ n).left := GrpTangent.isFinite_id_pow A hu
  haveI hE : Etale (𝟙 A ^ n).left := GrpTangent.etale_id_pow A hu
  haveI : IsSeparated A.hom := inferInstance
  have hsep : ∀ f : A ⟶ A, IsSeparated f.left := fun f => by
    have : IsSeparated (f.left ≫ A.hom) := by rw [Over.w f]; infer_instance
    exact IsSeparated.of_comp f.left A.hom
  haveI := hsep (act.act b')
  haveI : IsFinite ((act.act b).left ≫ (act.act b').left) := by rw [← Over.comp_left, h1]; exact hF
  haveI hfin : IsFinite (act.act b).left := IsFinite.of_comp _ (act.act b').left
  haveI : FormallyUnramified ((act.act b).left ≫ (act.act b').left) := by
    rw [← Over.comp_left, h1]; infer_instance
  haveI : FormallyUnramified (act.act b).left := FormallyUnramified.of_comp _ (act.act b').left
  haveI : Flat (act.act b).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A hA _ inferInstance
      hfin).1
  haveI : LocallyOfFinitePresentation ((act.act b).left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFinitePresentation (act.act b).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom
  refine ⟨hfin, Etale.of_formallyUnramified_of_flat _, ?_⟩
  have hfinN := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA hg hnk
  refine Finite.of_injective (β := {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ n = 1})
    (fun x => ⟨x.1, ?_⟩) ?_
  · have := congrArg (· ≫ act.act b') x.2
    simp only [Category.assoc, h1, one_comp] at this
    rwa [comp_pow, Category.comp_id] at this
  · intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h

end GlobalTheory.OActFinEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RoundEqn

open GlobalTheory.Cartier.CartierDiv

variable {X : Scheme.{0}} [IsIntegral X]

theorem eff_of_atlas {C : Type} {E : C → CartierDiv X} {n : ℕ} {ι : Type}
    (𝒜 : SncAtlas E n ι) (c : C) : (E c).Eff := by
  intro y
  have hy : y ∈ ⨆ i, 𝒜.U i := by rw [𝒜.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
  obtain ⟨e, -, -, heq⟩ := 𝒜.snc i
  refine ⟨_, heq c y hi, ?_⟩
  rw [one_mul]
  cases h : e c with
  | none => exact (unitAt_one y).regAt
  | some j => exact ((𝒜.chart i).chart y hi).mem j

theorem Eff.nsmul' {D : CartierDiv X} (h : D.Eff) (m : ℕ) : (m • D).Eff := by
  induction m with
  | zero => rw [zero_nsmul]; exact eff_zero
  | succ m ih => rw [succ_nsmul]; exact ih.add h

theorem isEqn_sum {C : Type} (s : Finset C) (D : C → CartierDiv X) (g : C → X.functionFieldˣ)
    (y : X) (h : ∀ c ∈ s, (D c).IsEqn y (g c)) : (∑ c ∈ s, D c).IsEqn y (∏ c ∈ s, g c) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun c hc => h c (Finset.mem_insert_of_mem hc))

theorem prod_elim_pow {C : Type} [Fintype C] {n : ℕ} {M : Type} [CommMonoid M] (x : Fin n → M)
    (J : Finset (Fin n)) (e : C → Option (Fin n)) (hJ : ∀ j, j ∈ J ↔ ∃ c, e c = some j)
    (r : C → ℕ) :
    ∏ c, ((e c).elim 1 x) ^ r c =
      ∏ j ∈ J, x j ^ (∑ c, if e c = some j then r c else 0) := by
  have step : ∀ c, ((e c).elim 1 x) ^ r c =
      ∏ j ∈ J, x j ^ (if e c = some j then r c else 0) := by
    intro c
    cases h : e c with
    | none => simp
    | some j₀ =>
      have hj₀ : j₀ ∈ J := (hJ j₀).2 ⟨c, h⟩
      rw [Finset.prod_eq_single j₀]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro hn; exact (hn hj₀).elim
  simp_rw [step]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_pow_eq_pow_sum _ _ _

end GlobalTheory.RoundEqn

open GlobalTheory.RoundEqn GlobalTheory.Cartier.CartierDiv in

theorem GlobalTheory.roundedTwist_isEqn :
  ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ((p • G + ∑ c, r c • E c) - p • G).Eff ∧ ∀ (i : ι), ∃ ρ : Fin n → ℕ, (∀ j, ρ j < p) ∧ ∀ y ∈ 𝒜.U i, ∀ t, G.IsEqn y t → (p • G + ∑ c, r c • E c).IsEqn y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j) := by
  intro p hp X _ _ C _ E n ι _ 𝒜 G r hr
  classical
  refine ⟨?_, fun i => ?_⟩
  · rw [add_sub_cancel_left]
    refine Finset.sum_induction _ (fun D : CartierDiv X => D.Eff) (fun _ _ h h' => h.add h') eff_zero ?_
    intro c _
    exact Eff.nsmul' (eff_of_atlas 𝒜 c) (r c)
  · obtain ⟨e, huniq, hJ, heq⟩ := 𝒜.snc i
    refine ⟨fun j => ∑ c, if e c = some j then r c else 0, fun j => ?_, fun y hy t ht => ?_⟩
    · show (∑ c, if e c = some j then r c else 0) < p
      by_cases h : ∃ c, e c = some j
      · obtain ⟨c₀, hc₀⟩ := h
        rw [Finset.sum_eq_single c₀]
        · rw [if_pos hc₀]; exact hr c₀
        · intro c _ hc; rw [if_neg]; exact fun h' => hc (huniq c c₀ j h' hc₀)
        · intro hn; exact (hn (Finset.mem_univ _)).elim
      · push_neg at h
        rw [Finset.sum_eq_zero fun c _ => if_neg (h c)]
        exact hp.out.pos
    · rw [← prod_elim_pow (𝒜.x i) (𝒜.J i) e hJ r]
      refine (ht.nsmul p).add (isEqn_sum _ _ _ y fun c _ => ?_)
      exact (heq c y hy).nsmul (r c)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondAtOfFirstAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open Formalism.L2.Host (HChar ordF atFin IsUnitAt)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.AdelicLiftCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

section Places

variable {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0)
include hL

end Places

section Generic

variable {G H W : Type} [Group G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : G →* H) (ρ : G →* Module.End ℂ W)

end Generic

section Forms

variable {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

include hc

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IsResidual (i : Fin D.R.m) (t : T) (s : ℂ →+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  (∀ PP ∈ R.Pg, m PP = (LiftFormsMainTerm.conjRes s (R.chi ((i : ℕ) + 1)) PP)⁻¹) ∧ ∀ PP ∈ R.Q t, m PP = LiftFormsMainTerm.conjRes s (R.xiR t) PP

variable {R}

section Residual

variable {i : Fin D.R.m} {t : T} {s : ℂ →+* ℂ} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (hm : IsResidual R i t s m)
  (P : LevelP R.Pg D.R.r ℂ)

include hm

end Residual

section Concl

variable {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ}

def FirstConcl (b : ℝ) (t : T) (P : LevelP R.Pg D.R.r ℂ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (pt : PolF D (Wc D i).rank (Vc D i).rank → (Datum.WO (Vc D i) (Wc D i) → ℂ)) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))) (HV : HMod (Bridge.Gf (Vc D i) → c.W)) : Prop :=
  (∃ th, TwistedLevelValues.IsLift R i σ ω pt c io ν 𝓕 HV th) ∧
    ∀ th, TwistedLevelValues.IsLift R i σ ω pt c io ν 𝓕 HV th →
      ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, TwistedLevelValues.typePart R i σ t P ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ TwistedLevelValues.typePart R i σ t P ev, th (TwistedLevelValues.adjLev P th x) = (l : ℂ) • x) ∧
          TwistedLevelValues.mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * TwistedLevelValues.Lp D b ≤ Real.log l

def SecondConcl (b : ℝ) (t : T) (s : ℂ →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) (X : LiftFormsMainTerm.LiftInput R i σ) : Prop :=
  (∃ th : X.src t s P →ₗ[ℂ] (R.HW i σ).H, X.IsLift th) ∧
    ∀ th : X.src t s P →ₗ[ℂ] (R.HW i σ).H, X.IsLift th →
      ∀ c, LiftFormsMainTerm.typePart R i σ t P c ≠ ⊥ →
        ∃ l : ℝ, X.ActsBy th (LiftFormsMainTerm.typePart R i σ t P c) l ∧ 0 < l ∧
          LiftFormsMainTerm.mainTerm i σ - 8 * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * LiftFormsMainTerm.Lpr D b) ≤ Real.log l

variable {t : T} {s : ℂ →+* ℂ} {P : LevelP R.Pg D.R.r ℂ} (X : LiftFormsMainTerm.LiftInput R i σ)
  (HV : HMod (Bridge.Gf (Vc D i) → X.coef.W)) (φ : HV.H ≃ₗ[ℂ] X.src t s P)
  (hφ : ∀ x, (φ x : GA D (Vc D i) → X.coef.W) = X.coef.ext (HV.e x))
  (hip : ∀ x y, IntegrableOn (fun h => ⟪X.coef.ext (HV.e x) h, X.coef.ext (HV.e y) h⟫_ℂ) X.fd X.ν ∧
    ∫ h in X.fd, ⟪X.coef.ext (HV.e x) h, X.coef.ext (HV.e y) h⟫_ℂ ∂X.ν = ⟪x, y⟫_ℂ)

end Concl

variable (R)

def FirstAt (i : Fin D.R.m) (b : ℝ) : Prop :=
  ∀ t : T, TwistedLevelValues.PrimeToHost R t →
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), TwistedLevelValues.IsEmbOverK D σ s →
  ∀ P : LevelP R.Pg D.R.r ℂ, TwistedLevelValues.IsLocalLevel P →
  ∀ (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), TwistedLevelValues.IsConjChars R i t s cμ cη m →
  ∀ ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ),
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω →
  ∀ BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (TwistedLevelValues.pW D i ρ)) →
  ∀ f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ,
    TwistedLevelValues.IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m
      f₀ f →
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (TwistedLevelValues.ptAt R i σ BW f) →
  ∀ c : CoefA (Vc D i), c.Is →
  ∀ io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
    IsIoW R.θ (R.MW i σ) c ω (TwistedLevelValues.ptAt R i σ BW f) (TwistedLevelValues.deltaAtEmb D i σ) io →
  ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))),
    IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m)) ν 𝓕 →
  ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf (Vc D i)),
    Bridge.IsReps (Bridge.ratF (Vc D i)) (TwistedLevelValues.grpOf (Vc D i) (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m)) y →
  ∀ HV : HMod (Bridge.Gf (Vc D i) → c.W),
    HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (TwistedLevelValues.grpOf (Vc D i) (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m))
        (TwistedLevelValues.chrOf (Vc D i) (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (TwistedLevelValues.grpOf (Vc D i) (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m)) y) →
    FirstConcl b t P ω (TwistedLevelValues.ptAt R i σ BW f) c io ν 𝓕 HV

def SecondAt (i : Fin D.R.m) (b : ℝ) : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (t : T), LiftFormsMainTerm.SameOnK σ → (s : ℂ →+* ℂ).comp D.what₂.embLL = σ →
    LiftFormsMainTerm.GoodPlaces R t → ∀ (P : LevelP R.Pg D.R.r ℂ) (X : LiftFormsMainTerm.LiftInput R i σ), X.Is t (s : ℂ →+* ℂ) P →
      TwistedLevelValues.IsLocalLevel P → X.BV = R.BV i → Lift.PtTheta R.ψ (Vc D i) (Wc D i) X.pt → SecondConcl b t (s : ℂ →+* ℂ) P X

variable {R} {F : Face D A}

end GlobalTheory.AdelicLiftCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInverseGramLocalBasisIntegral
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem selfDual_inv_gram_integral (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (w : HeightOneSpectrum (𝓞 E))
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x)))
    (X : Matrix (Fin n) (Fin n) E) (hX : IsUnit X.det) (hG : IsUnit (Xᵀ * J * X.map σ).det)
    (hval : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) (s : 𝓞 E) (hs : s ∉ w.asIdeal)
    (hsr : ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r)
    (e : E) (he : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) (i k : Fin n) :
    w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 := by
  set G := Xᵀ * J * X.map σ with hGdef
  set a : Fin n → E := fun j => e * G⁻¹ i j with ha
  have haG : a ᵥ* G = fun j => if j = i then e else 0 := by
    have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
    funext j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.mul_apply, Matrix.one_apply] at h2
    simp only [Matrix.vecMul, dotProduct, ha, mul_assoc, ← Finset.mul_sum, h2]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]
  have key : ∀ c : Fin n → E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (X *ᵥ a) (X *ᵥ c) = e * σ (c i) := by
    intro c
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form
    have h1 : (fun j => σ ((X *ᵥ c) j)) = X.map σ *ᵥ (fun j => σ (c j)) := by
      funext j
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec, haG]
    simp [dotProduct]
  have hXX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  have hXX' : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have hform_smul : ∀ (t : E) (u v : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (t • u) v = t * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J u v := by
    intro t u v
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form
    rw [smul_dotProduct, smul_eq_mul]
  set y : Fin n → E := (s : E) • (X *ᵥ a) with hy
  have hyL : y ∈ L := by
    refine (hL y).2 fun x hx o => ?_
    obtain ⟨r, hr⟩ := hsr x hx i
    have hx' : X *ᵥ (X⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hXX', Matrix.one_mulVec]
    have h3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x = e * (r : E) := by
      rw [hy, hform_smul, ← hx', key, ← hr]
      ring
    rw [h3]
    have h4 : (o : E) * (e * (r : E)) = ((o * r : 𝓞 E) : E) * e := by
      push_cast; ring
    rw [h4]
    exact he (o * r)
  have h5 := hval y hyL k
  have h6 : (X⁻¹ *ᵥ y) k = (s : E) * (e * G⁻¹ i k) := by
    rw [hy, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
    rfl
  rw [h6, map_mul] at h5
  have hsv : w.valuation E (s : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hs
  rw [hsv, one_mul] at h5
  exact h5

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess leviV)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace Weight

variable {A B : LB X}

theorem SemiPosReg.tens {ψ : Weight p σ A} {φ : Weight p σ B} (hψ : ψ.IsCInf) (hφ : φ.IsCInf)
    (hψ' : ψ.SemiPosReg D) (hφ' : φ.SemiPosReg D) : (ψ.tens φ).SemiPosReg D := fun i c y hy ξ => by
  have h1 := (mem_ptsIn_inf.1 hy.2).1
  have h2 := (mem_ptsIn_inf.1 hy.2).2
  have e := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add (hψ.contDiffAt c hy.1 h1)
    (hφ.contDiffAt c hy.1 h2) ξ
  have := add_nonneg (hψ' i.1 c y ⟨hy.1, h1⟩ ξ) (hφ' i.2 c y ⟨hy.1, h2⟩ ξ)
  rw [← Complex.add_re, ← e] at this
  exact this

theorem SemiPosReg.of_mul {E : LB X} (ψ : Weight p σ E) {φ : Weight p σ B} (hφ : φ.IsCInf)
    (hφ' : φ.SemiPosReg D) (c : ℝ) (hc : 0 ≤ c) (j : E.ι → B.ι)
    (hj : ∀ i y, y ∈ ptsIn p σ (E.U i) → y ∈ ptsIn p σ (B.U (j i)))
    (he : ∀ i y, ψ.φ i y = c * φ.φ (j i) y) : ψ.SemiPosReg D := fun i c' y hy ξ => by
  have h1 := hj i y hy.2
  have hf : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =
      fun v => ((c * φ.φ (j i) (c'.e.symm v) : ℝ) : ℂ) := funext fun v => by rw [he]
  rw [hf, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul c (hφ.contDiffAt c' hy.1 h1) ξ,
    Complex.re_ofReal_mul]
  exact mul_nonneg hc (hφ' (j i) c' y ⟨hy.1, h1⟩ ξ)

end Weight

namespace HermLB

variable {L M : HermLB p}

theorem SemiPos.tens (hL : L.SemiPos D) (hM : M.SemiPos D) : (L.tens M).SemiPos D := fun σ =>
  Weight.SemiPosReg.tens (L.cInf σ) (M.cInf σ) (hL σ) (hM σ)

theorem SemiPos.pow (hL : L.SemiPos D) (m : ℕ) : (L.pow m).SemiPos D := fun σ =>
  Weight.SemiPosReg.of_mul _ (L.cInf σ) (hL σ) ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit)
    (fun _ _ h => mem_pow_iff.1 h) fun j y => (L.φ σ).zpow_φ (m : ℤ) j y

theorem semiPos_dual_pow_zero (hL : L.SemiPos D) : ((L.pow 0).dual).SemiPos D := fun σ =>
  Weight.SemiPosReg.of_mul _ (L.cInf σ) (hL σ) 0 le_rfl (fun j => j PUnit.unit)
    (fun _ _ h => (mem_pow_iff (n := ((0 : ℕ) : ℤ))).1 h) fun j y =>
      (congrArg (fun t : ℝ => -t) ((L.φ σ).zpow_φ ((0 : ℕ) : ℤ) j y)).trans (by simp)

end HermLB

namespace ArInt

variable {ι : Type} [Fintype ι]

theorem semiPos_zp {L : HermLB p} (hL : L.SemiPos D) {n : ℤ} (hn : 0 ≤ n) : (zp L n).SemiPos D := by
  have h0 : (-n).toNat = 0 := Int.toNat_eq_zero.2 (by omega)
  unfold zp
  rw [h0]
  exact (hL.pow _).tens (HermLB.semiPos_dual_pow_zero hL)

theorem semiPos_comb (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (D : ℕ)
    (hL : ∀ i, (L i).SemiPos D) (hn : ∀ i, 0 ≤ n i) : (comb L n).SemiPos D := by
  unfold comb
  induction (Finset.univ : Finset ι).toList with
  | nil => exact (HermLB.isNef_triv p D).semiPos
  | cons i l ih => exact (semiPos_zp (hL i) (hn i)).tens ih

example : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (ι : Type) [Fintype ι]
    (L : ι → GlobalTheory.HermLB p) (n : ι → ℤ) (D : ℕ), (∀ i, (L i).SemiPos D) → (∀ i, 0 ≤ n i) →
    (GlobalTheory.ArInt.comb L n).SemiPos D := @semiPos_comb

end ArInt

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilMeasureOfCongruentForm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFinOver

theorem liesOver_comp_complexConj_of_not_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p)
    (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ →
      LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  intro p _ G ψ h x
  exact (GlobalTheory.HTGroupOver.liesOver_or_conj p G ψ).resolve_left h x

end GlobalTheory.StabFinOver

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ → LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) :=
  GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruentStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_gram_inv_congruent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), ∃ Z : GL (Fin G.n) ℂ, (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) = (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  first | exact @GlobalTheory.LKMid.Pair.gram_psi_inv_congr | exact GlobalTheory.LKMid.Pair.gram_psi_inv_congr | (intros; apply GlobalTheory.LKMid.Pair.gram_psi_inv_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOnStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one : GlobalTheory.EtC.C2 := by
  first | (exact @GlobalTheory.EtC.etC_c2) | (exact GlobalTheory.EtC.etC_c2) | (intros; apply GlobalTheory.EtC.etC_c2  <;> assumption)
end

