import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DrinfeldLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRankOneIdem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.DrinLev.HT

open GlobalTheory.UPel.HT GlobalTheory.IwLevel

variable {p : ℕ} [Fact p.Prime]

abbrev powO (D : Datum p) (w : Ideal (𝓞 D.F)) (m : ℕ) : Ideal D.O := (w ^ m).map (algebraMap (𝓞 D.F) D.O)

def IsRankOneIdem (D : Datum p) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) : Prop :=
  e * e - e ∈ powO D w m ∧ (∀ x : D.O, ∃ c : 𝓞 D.F, e * x * e - algebraMap (𝓞 D.F) D.O c * e ∈ powO D w m) ∧
    e ∉ powO D w 1

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S S' : Scheme.{0}}

def IsEpsTors {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) {T : Over S} (x : T ⟶ o.A) :
    Prop :=
  KilledBy (htAct o) (powO D w m) x ∧ x ≫ o.act.act e = x

structure SubRep (A : Over S) (P : ∀ {T : Over S}, (T ⟶ A) → Prop) where

  Z : Over S

  incl : Z ⟶ A
  mono : Mono incl
  pts : ∀ (T : Over S) (x : T ⟶ A), P x ↔ ∃ y, y ≫ incl = x

def SubRep.unit (A : Over S) [GrpObj A] : SubRep A (fun x => x = 1) where
  Z := 𝟙_ (Over S)
  incl := 1
  mono := ⟨fun g h _ => toUnit_unique g h⟩
  pts T x := ⟨fun h => ⟨toUnit T, by rw [MonObj.comp_one, h]⟩, fun ⟨y, hy⟩ => hy ▸ MonObj.comp_one y⟩

structure HTLevel {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) where

  α : (Fin D.n → 𝓞 D.F ⧸ w ^ m) → (𝟙_ (Over S) ⟶ o.A)
  map_add : ∀ x y, α (x + y) = α x * α y
  map_smul : ∀ (c : 𝓞 D.F) x, α (c • x) = α x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)
  full : ∃ (G : SubRep o.A (IsEpsTors o w m e)) (β : (Fin D.n → 𝓞 D.F ⧸ w ^ m) → (𝟙_ (Over S) ⟶ G.Z)),
    (∀ x, β x ≫ G.incl = α x) ∧ IsFullSet G.Z β

structure ObjLev (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) (s : S ⟶ Sp R) where

  obj : Obj b N s

  lev : HTLevel obj w m e

def ObjLevMap {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} (o' : ObjLev b N w m e s')
    (o : ObjLev b N w m e s) (f : S' ⟶ S) : Prop :=
  ∃ φ : ObjMap o'.obj o.obj f, ∀ x, (o'.lev.α x).left ≫ φ.φ = f ≫ (o.lev.α x).left

structure LevRep (b : Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) where

  X : Scheme.{0}

  s : X ⟶ Sp R

  univ : ObjLev b N w m e s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : ObjLev b N w m e s'),
    ∃! f : S ⟶ X, f ≫ s = s' ∧ ObjLevMap o univ f

namespace LevRep

variable {w : Ideal (𝓞 D.F)} {m : ℕ} {e : D.O}

def forget (M : LevRep b N w m e) (F₀ : RepFam b N) : M.X ⟶ F₀.X :=
  (F₀.rep M.X M.s M.univ.obj).exists.choose

def Proj (M : LevRep b N w m e) : Prop := IsProjOver M.s

def Regular (M : LevRep b N w m e) : Prop := ∀ x : M.X, IsRegularLocalRing (M.X.presheaf.stalk x)

def FinFlat (M : LevRep b N w m e) (F₀ : RepFam b N) : Prop :=
  IsFinite (M.forget F₀) ∧ Flat (M.forget F₀)

end LevRep

structure LevModel (M₀ : Model b N) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) extends LevRep b N w m e where
  proj : toLevRep.Proj
  regular : toLevRep.Regular
  finFlat : toLevRep.FinFlat M₀.toRepFam

section Basic₂

example (D : Datum p) (w : Ideal (𝓞 D.F)) (e : D.O) (he : e ∉ powO D w 1) : IsRankOneIdem D w 0 e := by
  have h : powO D w 0 = ⊤ := by
    rw [powO, pow_zero, Ideal.one_eq_top]
    exact (Ideal.eq_top_iff_one _).2 (by simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) (Submodule.mem_top (x := (1 : 𝓞 D.F))))
  refine ⟨?_, fun x => ⟨0, ?_⟩, he⟩ <;> simp [h]

example {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (m : ℕ) (e : D.O) :
    IsEpsTors o w m e (1 : 𝟙_ (Over S) ⟶ o.A) := by
  have := o.act.hom e
  refine ⟨fun a _ => ?_, ?_⟩
  · have := (htAct o).hom a
    exact MonObj.one_comp _
  · exact MonObj.one_comp _

end Basic₂

end GlobalTheory.DrinLev.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSumOfSelf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

structure Base : Prop where
  llc : GlobalTheory.Published.LocalLanglandsGL
  ex : GlobalTheory.Published.LocalLanglandsExists
  conv : GlobalTheory.Published.LocalConverseGL
  adm : GlobalTheory.Published.IrreducibleAdmissibleGL
  len : GlobalTheory.Published.StandardFunctorsFiniteLength
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  js : GlobalTheory.Published.JacquetShalikaRigidity
  gk : GlobalTheory.Published.GelfandKazhdanDual

theorem Base.uniq (H : Base) : GlobalTheory.TheRec.RecUnique :=
  GlobalTheory.TheRec.recUnique_of_localConverse H.ex H.conv H.exh H.adm H.len

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SatMatch (sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, sat w B ∧
    ∀ (_hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      IsWDOf ι r ((WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2))

theorem SatMatch.wdOf_eq {sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} (H : SatMatch sat ι r) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, sat w B ∧
      ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
        wdOf h hl ι r = (WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpTw ((1 - (a : ℝ)) / 2) :=
  H.mono fun _ ⟨B, hB, hw⟩ => ⟨B, hB, fun hl A h => (hw hl A h).wdOf_eq hl⟩

def IsSumOf {Γ k : Type} [Group Γ] [Field k] {a m : ℕ} {b : Fin m → ℕ} (r : Γ →* GL (Fin a) k)
    (ρ : ∀ i, Γ →* GL (Fin (b i)) k) : Prop :=
  ∀ g, (r g).val.trace = ∑ i, (ρ i g).val.trace

def GalPol [IsCMField E] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  ∃ (χ : HChar (maximalRealSubfield E)) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ),
    (∀ v : InfinitePlace (maximalRealSubfield E), χ.locInf v (-1) = (-1) ^ a) ∧ IsLAdicCharOf ι χ μ ∧
    ∀ c : Ω ≃+* Ω, IsCMConjOm E Ω c →
      IsConjDual c r (cycBar E Ω l ^ (1 - (a : ℤ)) * μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)))

example {Γ k : Type} [Group Γ] [Field k] {a : ℕ} {b : Fin 2 → ℕ} (r : Γ →* GL (Fin a) k)
    (ρ : ∀ i, Γ →* GL (Fin (b i)) k) (H : IsSumOf r ρ) (g : Γ) :
    (r g).val.trace = (ρ 0 g).val.trace + (ρ 1 g).val.trace := by
  have := H g; rwa [Fin.sum_univ_two] at this

example (H : Base) : GlobalTheory.TheRec.RecUnique := H.uniq

end GlobalTheory.AboveL

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RingHomFormallyEtaleOfBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open TopologicalSpace
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

section Etale

variable {X Y : Scheme.{0}}

def EtaleAtPt (f : X ⟶ Y) (x : X) : Prop := (f.stalkMap x).hom.FormallyEtale

theorem ringHom_formallyEtale_of_bijective {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : Function.Bijective g) : g.FormallyEtale := by
  letI := g.toAlgebra
  show Algebra.FormallyEtale A B
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hg)

theorem etaleAtPt_of_isIso (f : X ⟶ Y) [IsIso f] (x : X) : EtaleAtPt f x := by
  unfold EtaleAtPt
  exact ringHom_formallyEtale_of_bijective _ (ConcreteCategory.bijective_of_isIso (f.stalkMap x))

end Etale

section Strata

variable {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A] {ρ : RingAct A O}
  {𝔴 : Ideal O} {d n : ℕ} (C : Chain ρ 𝔴 d n)

def nonEtaleLocus (j : Fin n) : Set (C.B j.castSucc).left :=
  {x | ¬ EtaleAtPt (C.φ j).left x}

def stratSet (j : Fin n) : Set S :=
  closure ((C.B j.castSucc).hom.base '' nonEtaleLocus C j)

theorem isClosed_stratSet (j : Fin n) : IsClosed (stratSet C j) := isClosed_closure

def stratClosed (j : Fin n) : Closeds S := ⟨stratSet C j, isClosed_stratSet C j⟩

def stratIdeal (j : Fin n) : S.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (stratClosed C j)

@[simp] theorem coe_support_stratIdeal (j : Fin n) : ((stratIdeal C j).support : Set S) = stratSet C j :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

theorem stratSet_eq_empty_of_isIso (j : Fin n) [IsIso (C.φ j)] : stratSet C j = ∅ := by
  have : IsIso (C.φ j).left := inferInstanceAs (IsIso ((Over.forget S).map (C.φ j)))
  have h : nonEtaleLocus C j = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => hx (etaleAtPt_of_isIso _ x)
  rw [stratSet, h, Set.image_empty, closure_empty]

theorem stratIdeal_eq_top_of_isIso (j : Fin n) [IsIso (C.φ j)] : stratIdeal C j = ⊤ := by
  have : stratClosed C j = ⊥ := Closeds.ext (stratSet_eq_empty_of_isIso C j)
  rw [stratIdeal, this, Scheme.IdealSheafData.vanishingIdeal_bot]

def openStratum (T : Finset (Fin n)) : Set S := {s | ∀ j, s ∈ stratSet C j ↔ j ∈ T}

def openStratumOpens (T : Finset (Fin n)) : (GlobalTheory.Strata.Y (stratIdeal C) T).Opens :=
  ⟨(GlobalTheory.Strata.Yι (stratIdeal C) T).base ⁻¹' (⋂ j ∈ Tᶜ, (stratSet C j)ᶜ),
    (isOpen_biInter_finset fun j _ => (isClosed_stratSet C j).isOpen_compl).preimage
      (GlobalTheory.Strata.Yι (stratIdeal C) T).base.hom.continuous⟩

end Strata

section Rep

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {w : Ideal (𝓞 D.F)}

abbrev HTIwRep.strat (M : HTIwRep b N w) : Fin D.n → M.X.IdealSheafData := stratIdeal M.univC

abbrev HTIwRep.openStratum (M : HTIwRep b N w) (T : Finset (Fin D.n)) : Set M.X := IwLevel.openStratum M.univC T

end Rep

section Basic₂

variable {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A]

example (hA : IsAbelianScheme A) (ρ : RingAct A O) (h : IsIsogDeg (ρ.act 1) 1) (n : ℕ) (j : Fin n) :
    stratSet (powChain hA ρ 1 (fun _ => by simp) h n) j = ∅ := by
  haveI : IsIso ((powChain hA ρ 1 (fun _ => by simp) h n).φ j) := by
    show IsIso (ρ.act 1); rw [ρ.map_one]; infer_instance
  exact stratSet_eq_empty_of_isIso _ j

example (hA : IsAbelianScheme A) (ρ : RingAct A O) (h : IsIsogDeg (ρ.act 1) 1) (n : ℕ) (T : Finset (Fin n)) :
    openStratum (powChain hA ρ 1 (fun _ => by simp) h n) T = if T = ∅ then Set.univ else ∅ := by
  have e : ∀ j, stratSet (powChain hA ρ 1 (fun _ => by simp) h n) j = ∅ := fun j => by
    haveI : IsIso ((powChain hA ρ 1 (fun _ => by simp) h n).φ j) := by
      show IsIso (ρ.act 1); rw [ρ.map_one]; infer_instance
    exact stratSet_eq_empty_of_isIso _ j
  ext s
  simp only [openStratum, e, Set.mem_empty_iff_false, false_iff, Set.mem_setOf_eq]
  split_ifs with hT
  · simp [hT]
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hT
    simp only [Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    exact ⟨j, hj⟩

example (hA : IsAbelianScheme A) (ρ : RingAct A O) (h : IsIsogDeg (ρ.act 1) 1) :
    stratIdeal (powChain hA ρ 1 (fun _ => by simp) h 1) 0 = ⊤ := by
  haveI : IsIso ((powChain hA ρ 1 (fun _ => by simp) h 1).φ 0) := by
    show IsIso (ρ.act 1); rw [ρ.map_one]; infer_instance
  exact stratIdeal_eq_top_of_isIso _ 0

end Basic₂

end GlobalTheory.IwLevel
end
end

