import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OddOrSlightlyRegIffOfEven
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.TheRec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CBGal

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def SlightlyReg (π : CuspSub E a) : Prop :=
  ∃ (τ : E →+* ℂ) (z : Fin a → ℂ), (CG.mk π).infChar τ = Finset.univ.val.map z ∧ StrictAnti (fun i => (z i).re) ∧
    ∃ i j : Fin a, Even (i : ℕ) ∧ (j : ℕ) = i + 1 ∧ (z j).re + 1 < (z i).re

def OddOrSlightlyReg (π : CuspSub E a) : Prop := Odd a ∨ SlightlyReg π

theorem OddOrSlightlyReg.of_odd (π : CuspSub E a) (h : Odd a) : OddOrSlightlyReg π := Or.inl h

theorem OddOrSlightlyReg.of_slightlyReg {π : CuspSub E a} (h : SlightlyReg π) : OddOrSlightlyReg π := Or.inr h

theorem oddOrSlightlyReg_iff_of_even (π : CuspSub E a) (h : Even a) : OddOrSlightlyReg π ↔ SlightlyReg π :=
  ⟨fun h' => h'.resolve_left (Nat.not_odd_iff_even.2 h), Or.inr⟩

def SlightlyRegAll (π : CuspSub E a) : Prop :=
  ∃ (τ : E →+* ℂ) (z : Fin a → ℂ), (CG.mk π).infChar τ = Finset.univ.val.map z ∧ StrictAnti (fun i => (z i).re) ∧
    ∀ i j : Fin a, Even (i : ℕ) → (j : ℕ) = i + 1 → (z j).re + 1 < (z i).re

theorem SlightlyRegAll.slightlyReg {π : CuspSub E a} (ha : 2 ≤ a) (h : SlightlyRegAll π) : SlightlyReg π := by
  obtain ⟨τ, z, hz, hs, hg⟩ := h
  exact ⟨τ, z, hz, hs, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, rfl⟩, rfl, hg _ _ ⟨0, rfl⟩ rfl⟩

theorem slightlyReg_of_weight (π : CuspSub E a) (τ : E →+* ℂ) (w : Fin a → ℤ) (hw : Antitone w)
    (h : (CG.mk π).infChar τ = Finset.univ.val.map fun k : Fin a => (w k : ℂ) + (((a : ℂ) - 1) / 2 - (k : ℕ)))
    (k l : Fin a) (hk : Even (k : ℕ)) (hl : (l : ℕ) = k + 1) (hg : w l < w k) : SlightlyReg π := by
  refine ⟨τ, _, h, ?_, k, l, hk, hl, ?_⟩
  · intro x y hxy
    have h1 : w y ≤ w x := hw hxy.le
    have h2 : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := by exact_mod_cast hxy
    have h3 : ((w y : ℤ) : ℝ) ≤ ((w x : ℤ) : ℝ) := by exact_mod_cast h1
    simp; linarith
  · have h1 : ((w l : ℤ) : ℝ) + 1 ≤ ((w k : ℤ) : ℝ) := by exact_mod_cast hg
    have h2 : ((l : ℕ) : ℝ) = ((k : ℕ) : ℝ) + 1 := by exact_mod_cast hl
    simp; linarith

example (π : CuspSub E 3) : OddOrSlightlyReg π := OddOrSlightlyReg.of_odd π ⟨1, rfl⟩

example (π : CuspSub E 4) (h : SlightlyRegAll π) : OddOrSlightlyReg π := .of_slightlyReg (h.slightlyReg (by norm_num))

example (π : CuspSub E 4) (τ : E →+* ℂ)
    (h : (CG.mk π).infChar τ = Finset.univ.val.map fun k : Fin 4 => ((![3, 2, 1, 1] k : ℤ) : ℂ) + (((4 : ℂ) - 1) / 2 - (k : ℕ))) :
    SlightlyReg π :=
  slightlyReg_of_weight π τ ![3, 2, 1, 1] (by intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all <;> omega)
    (by simpa using h) 0 1 ⟨0, rfl⟩ rfl (by decide)

end GlobalTheory.CBGal

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow2
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

namespace WDRep

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def ineEig (a : WDRep h V) (χ : Ine (F := E) A → ℂ) : Submodule ℂ V :=
  ⨅ σ : Ine (F := E) A, Module.End.eigenspace (a.ρ (ineIncl h σ)) (χ σ)

theorem mem_ineEig {a : WDRep h V} {χ : Ine (F := E) A → ℂ} {v : V} :
    v ∈ a.ineEig χ ↔ ∀ σ : Ine (F := E) A, a.ρ (ineIncl h σ) v = χ σ • v := by
  simp [ineEig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

def Mono0Ine (a : WDRep h V) (χ : Ine (F := E) A → ℂ) : Prop :=
  ∀ v ∈ a.ineEig χ, a.N v = 0

theorem Mono0.mono0Ine {a : WDRep h V} (ha : a.Mono0) (χ : Ine (F := E) A → ℂ) : a.Mono0Ine χ :=
  fun v _ => by rw [show a.N = 0 from ha]; rfl

theorem Iso.mono0Ine {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) {χ : Ine (F := E) A → ℂ}
    (ha : a.Mono0Ine χ) : b.Mono0Ine χ := by
  obtain ⟨e, h1, h2⟩ := hab
  intro u hu
  have hv : e.symm u ∈ a.ineEig χ := mem_ineEig.2 fun σ => e.injective (by
    rw [h1, LinearEquiv.apply_symm_apply, map_smul, LinearEquiv.apply_symm_apply]
    exact mem_ineEig.1 hu σ)
  rw [← LinearEquiv.apply_symm_apply e u, ← h2, ha _ hv, map_zero]

theorem mono0Ine_tw {a : WDRep h V} {χ : Ine (F := E) A → ℂ} (s : ℝ) :
    (a.tw s).Mono0Ine χ ↔ a.Mono0Ine χ := by
  have e : (a.tw s).ineEig χ = a.ineEig χ := by
    ext v; simp only [mem_ineEig, tw_ρ, deg_ineIncl, zpow_zero, one_smul]
  simp only [Mono0Ine, e, tw_N]

end WDRep

namespace WD

def mono0Ine (x : WD h) (χ : Ine (F := E) A → ℂ) : Prop :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.Mono0Ine χ)
    (fun _ _ hab => propext ⟨fun ha => WDRep.Iso.mono0Ine hab ha, fun hb => WDRep.Iso.mono0Ine hab.symm hb⟩) x

@[simp] theorem mono0Ine_mk {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (χ : Ine (F := E) A → ℂ) : mono0Ine (mk a) χ ↔ a.Mono0Ine χ :=
  ⟨WDRep.Iso.mono0Ine (iso_std a).symm, WDRep.Iso.mono0Ine (iso_std a)⟩

theorem mono0Ine_of_mono0 {x : WD h} (hx : mono0 x) (χ : Ine (F := E) A → ℂ) : mono0Ine x χ := by
  induction x using ind with
  | hP n a => exact (mono0Ine_mk a χ).2 (WDRep.Mono0.mono0Ine ((monodromyZero_ofWeilDeligneRepClass_iff a).1 hx) χ)

@[simp] theorem mono0Ine_lpTw (x : WD h) (s : ℝ) (χ : Ine (F := E) A → ℂ) :
    mono0Ine (lpTw x s) χ ↔ mono0Ine x χ := by
  induction x using ind with
  | hP n a => rw [lpTw_mk, mono0Ine_mk, mono0Ine_mk, WDRep.mono0Ine_tw]

example : ¬ (lpSp h 2).mono0Ine (fun _ => 1) := by
  rw [lpSp, mono0Ine_mk]
  intro H
  have hv : (Pi.single 0 1 : Fin 2 → ℂ) ∈ (WDRep.sp h 2).ineEig (fun _ => 1) := by
    refine WDRep.mem_ineEig.2 fun σ => ?_
    ext i
    simp [WDRep.sp_ρ, deg_ineIncl]
  have := congrFun (H _ hv) 1
  simp [WDRep.sp_N, shiftEnd_apply] at this

example (x : WD h) (hx : x.mono0) (χ : Ine (F := E) A → ℂ) : x.mono0Ine χ := mono0Ine_of_mono0 hx χ

example : ¬ deg (1 : Weil h) ≠ 0 := by simp

end WD

end GlobalTheory.WeilDeligne

namespace GlobalTheory.GalNarrow2

open GlobalTheory.TheRec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

def SqIntSomewhere (π : CuspSub E a) : Prop :=
  ∃ (x : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (x.adicCompletion E))), π.IsLocComp x σ ∧
    UnitaryDual.IsSquareIntegrable (IrrGL.of σ.ρ σ.smooth σ.irred)

def IsWeightOf (π : CuspSub E a) (wt : ℤ) : Prop :=
  ∀ τ : E →+* ℂ, (CG.mk π).infChar (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) =
    ((CG.mk π).infChar τ).map fun z => (a : ℂ) - 1 - (wt : ℂ) - z

structure AboveN (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where

  deRham : IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)

  jumps : ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  iwahori : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ rc, IsTheRec h rc →
      (∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
      ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).mono0)

  sizeAbove : ∀ (wt : ℤ) (g : Weil h), deg g ≠ 0 → ∀ z ∈ ((wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).lpTw ((wt : ℝ) / 2)).eig g,
    IsWeightOf π wt → ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧
      ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure PropsN (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  cont : Continuous r

  ss : IsSSRep r

  pol : ∀ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ → ∀ c : Ω ≃+* Ω, IsCMConjOm E Ω c →
    IsConjDual c r (cycBar E Ω l ^ (1 - (a : ℤ)) * μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)))

  awaySS : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ →
      ∀ g : Weil h, (wdOf h hl ι r).charPol g = (rc (algNorm σ)).charPol g

  awayFromResidueChar : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
      wdOf h hl ι r = rc (algNorm σ)

  awayIne : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ → ∀ χ : Ine (F := E) A → ℂ,
      (rc (algNorm σ)).mono0Ine χ → (wdOf h hl ι r).mono0Ine χ

  sizeAway : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (g : Weil h), deg g ≠ 0 → ∀ z ∈ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).eig g,
      ((normV w : ℕ) : ℝ) ^ (-(|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2) < ‖z‖ ∧
        ‖z‖ < ((normV w : ℕ) : ℝ) ^ ((|(deg g : ℤ)| : ℝ) * (a : ℝ) / 2)

  pureUnr : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    (∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ) → ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered

  sqInt : SqIntSomewhere π → ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω)
    (h : IsPlaceOver A w), (∀ (rc : IrrGL (w.adicCompletion E) → WD h), IsTheRec h rc → ∀ σ, π.IsLocComp w σ →
      wdOf h hl ι r = rc (algNorm σ)) ∧ ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered

  weights : ∀ (τ : E →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (ι.toRingHom.comp τ) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveN π ι r HT P h Bw hj

end GlobalTheory.GalNarrow2

namespace GlobalTheory.Published

def PolarizedGaloisRepNarrow2 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
        GalNarrow2.PropsN π χ ι r wt HT

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

def resTo {K Ω : Type} (L : Type) [Field K] [Field L] [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
    {M : Type} [Monoid M] (r : G K Ω →* M) : G L Ω →* M :=
  r.comp (AlgEquiv.restrictScalarsHom K)

def Restricts {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (x : WD h) (x' : WD h') : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h' (Fin n → ℂ)), WD.mk a = x ∧ WD.mk b = x' ∧ b.N = a.N ∧
    ∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → b.ρ σ' = a.ρ σ

def Irr {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (r : Γ →* GL (Fin a) k) : Prop :=
  1 ≤ a ∧ ∀ W : Submodule k (Fin a → k), (∀ g, ∀ v ∈ W, (r g).val.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

def IneTriv {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x : WD h) : Prop :=
  ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = (Polynomial.X - 1) ^ x.lpDim

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

def RegPol (π : CuspSub E a) : Prop :=
  (CG.mk π).IsRegAlg ∧ ∃ χ : HChar (maximalRealSubfield E), GlobalTheory.ContraPair.PolarizedPair π χ

def RepOf (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  (CG.mk π).IsRegAlg ∧ ∃ (χ : HChar (maximalRealSubfield E)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
    GlobalTheory.ContraPair.PolarizedPair π χ ∧ GalHyps.Props π χ ι r wt HT

def IsAut (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop := ∃ π : CuspSub E a, RepOf π ι r

end GlobalTheory.AboveL

end
end

