import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DegreesPos
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DiscSpec.ResidualModel

theorem of_discreteSpectrumGL (H : GlobalTheory.Published.DiscreteSpectrumGL) : GlobalTheory.Published.DiscreteSpectrumResidual := by
  intro E _ _ _ N hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := H E N hN
  exact ⟨h1, h2, h3, h4, fun V hV a d π hn e w => ⟨(h5 V hV a d π hn e).exLoc w, (h5 V hV a d π hn e).loc w⟩⟩

theorem discreteSpectrumGL_iff : GlobalTheory.Published.DiscreteSpectrumGL ↔ GlobalTheory.Published.DiscreteSpectrumResidual ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
      ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a), IsNormalised π → IsSpehOf V π d →
        ∀ τ, ∃ m, π.HasInfChar τ m ∧ HasInfCharGL V τ (GlobalTheory.SphGal.spehInf d m) := by
  refine ⟨fun H => ⟨of_discreteSpectrumGL H, fun E _ _ _ N hN V hV a d π hn e =>
    ((H E N hN).2.2.2.2 V hV a d π hn e).inf⟩, fun ⟨H, H'⟩ E _ _ _ N hN => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H E N hN
  exact ⟨h1, h2, h3, h4, fun V hV a d π hn e => ⟨fun w => (h5 V hV a d π hn e w).1, fun w => (h5 V hV a d π hn e w).2,
    H' E N hN V hV a d π hn e⟩⟩

theorem residual_one (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] :
    (∀ V : Submodule ℂ (Sm E 1), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = 1 → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E 1), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E 1), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E 1), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E 1), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → ∀ w, (∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ') ∧
        ∀ σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
          GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.DiscSpec.Model.discreteSpectrum_one (E := E)
  exact ⟨h1, h2, h3, h4, fun V hV a d π hn e w => ⟨(h5 V hV a d π hn e).exLoc w, (h5 V hV a d π hn e).loc w⟩⟩

theorem degrees_pos {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N a d : ℕ} (hN : 1 ≤ N)
    {V : Submodule ℂ (Sm E N)} {π : CuspSub E a} (h : IsSpehOf V π d) : 1 ≤ a ∧ 1 ≤ d := by
  have := h.mul_eq
  constructor
  · rcases a with _ | a
    · simp at this; omega
    · omega
  · rcases d with _ | d
    · simp at this; omega
    · omega

theorem isDiscrete_of_isNormalised (H : GlobalTheory.Published.DiscreteSpectrumResidual) {E : Type} [Field E] [NumberField E]
    [IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a) (π : CuspSub E a) (hn : IsNormalised π) :
    ∃ V : Submodule ℂ (Sm E a), IsDiscrete V ∧ IsSpehOf V π 1 :=
  ((H E a ha).2.1 a 1 π (one_mul a) hn).exists

end GlobalTheory.DiscSpec.ResidualModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def DepthZeroWild : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))), (cls σ).IsCusp →
    (∃ v : σ.V, v ≠ 0 ∧ ∀ κ : GL (Fin n) (w.adicCompletion E),
      (∀ a b, Valued.v (((κ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) a b) < 1) → σ.ρ κ v = v) →
    ∀ t ∈ Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (t y / y - 1) < 1) →
    (rc (cls σ)).inePol t = (X - 1) ^ n

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def algNorm {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (w.adicCompletion E) :=
  (IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)

omit [NumberField E] in

def IsSstAt (P : LocPrime l) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (r : ↥Gw →* GL (Fin a) (Om l)) : Prop :=
  ∃ LL' r', IsModel Bw r LL' r' ∧ IsSst P (Bw.repE LL' r')

variable [IsAlgClosure E Ω] [IsCMField E]

def IsLAdicCharOf (ι : Qbar l ≃+* ℂ) (χ : HChar (maximalRealSubfield E))
    (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ) : Prop :=
  Continuous μ ∧ ∃ (art : Ideles (maximalRealSubfield E) →* Gab (maximalRealSubfield E) Ω)
    (n : (maximalRealSubfield E →+* ℂ) → ℤ), IsGlobalArtin art ∧ IsAlgPos χ n ∧ IsLAdicOf art ι χ n μ

structure IsAttachedAbove (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where

  deRham : IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)

  jumps : ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  iwahori : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      ∀ rc, IsRec h rc → wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure IsGalRepOf (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  cont : Continuous r

  ss : IsSSRep r

  pol : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ ∧ ∀ c : Ω ≃+* Ω, IsCMConjOm E Ω c →
    IsConjDual c r (cycBar E Ω l ^ (1 - (a : ℤ)) * μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)))

  away : ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι r (rc (algNorm σ))

  pure : ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    ∃ x : WD h, IsWDOf ι r x ∧ (x.lpTw ((wt : ℝ) / 2)).tempered

  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), IsAttachedAbove π ι r HT P h Bw hj

end GlobalTheory.GalOfCusp

namespace GlobalTheory.Published

open GlobalTheory.GalOfCusp

def GaloisRepOfPolarizedCuspidal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → IsPolarized π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalRepOf π χ ι r wt HT

theorem GaloisRepOfPolarizedCuspidal.of_isCsd (H : GaloisRepOfPolarizedCuspidal) {E : Type} (Ω : Type) [Field E]
    [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} (hr : (CG.mk π).IsRegAlg) (hc : π.IsCsd) :
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT :=
  H E Ω l ι a ha π _ hr (isPolarized_of_isCsd hc)

end GlobalTheory.Published

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem rec_algNorm {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    rc (algNorm σ) = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2) := by
  obtain ⟨_, _, _, -, H⟩ := H
  exact H.nu_eq _ _

variable [IsCMField E] {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}

theorem IsGalRepOf.wdOf_eq (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) :
    wdOf h hl ι r = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2) :=
  ((H.away w hl A h rc hrc σ hσ).wdOf_eq hl).trans (rec_algNorm hrc σ)

theorem IsGalRepOf.tempered_wdOf (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) :
    ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered := by
  obtain ⟨x, h1, h2⟩ := H.pure w hl A h
  rwa [h1.wdOf_eq hl]

end GlobalTheory.GalOfCusp
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.Published

def GenericUnlinkedGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsGeneric π →
    ∃ (h : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧ (∀ i, IsLSeg (Δ i) (x i).rep) ∧ Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.UnitaryDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSquareIntegrable (δ : IrrGL k) : Prop :=
  0 < δ.1 ∧ IsUnitarisable δ.rep ∧
    letI : MeasurableSpace (GL (Fin δ.1) k ⧸ Subgroup.center (GL (Fin δ.1) k)) := borel _
    ∃ μ : Measure (GL (Fin δ.1) k ⧸ Subgroup.center (GL (Fin δ.1) k)), μ.IsHaarMeasure ∧
      ∀ v, ∀ ℓ ∈ smoothPart δ.rep.dual, ∫⁻ q, ‖ℓ (δ.rep q.out v)‖ₑ ^ 2 ∂μ < ⊤

def IsUnitarySpeh (x : IrrGL k) : Prop := ∃ (δ : IrrGL k) (m : ℕ), IsSquareIntegrable δ ∧ 1 ≤ m ∧ IsSpeh δ m x.rep

end GlobalTheory.UnitaryDual

namespace GlobalTheory.Published

open GlobalTheory.UnitaryDual

def UnitaryDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π →
    ∃ (u : List (IrrGL k)) (τ : List (IrrGL k × ℝ)), (∀ x ∈ u, IsUnitarySpeh x) ∧
      (∀ p ∈ τ, IsUnitarySpeh p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
      ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), List.ofFn x = GenericUnitary.factors u τ ∧
        Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.Published

def LanglandsMultisegments : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    (∀ (𝔪 𝔫 : Multiset (Segment k)) (x : IrrGL k), IsL 𝔪 x.rep → IsL 𝔫 x.rep → 𝔪 = 𝔫) ∧
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsComplementaryProductAbsPow
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem IsUnitaryLSeg.deg_pos {x : IrrGL k} (h : IsUnitaryLSeg x) : 0 < x.1 := by
  obtain ⟨⟨Δ, hΔ⟩, -⟩ := h
  rw [← hΔ.deg_eq]
  exact Nat.mul_pos Δ.len_pos Δ.d_pos

theorem IsComplementaryProduct.isUnitarisable_one {π : Representation ℂ (GL (Fin 1) k) V}
    (H : IsComplementaryProduct π) : IsUnitarisable π := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, ⟨φ⟩⟩ := H
  have hpos : ∀ a, 1 ≤ (x a).1 := fun a => by
    obtain ⟨y, s, hy, -, e⟩ := exists_of_mem_factors hδ hτ (y := x a) (hx ▸ List.mem_ofFn.2 ⟨a, rfl⟩)
    rw [e]; exact hy.deg_pos
  have h1 : h ≤ 1 := by
    have := Finset.sum_le_sum (s := Finset.univ) fun a _ => hpos a
    simpa [hd] using this
  have h0 : h ≠ 0 := by rintro rfl; simp at hd
  obtain rfl : h = 1 := by omega
  have hl := congrArg List.length hx
  cases τ with
  | cons p τ => simp [factors] at hl; omega
  | nil =>
    have hm : x 0 ∈ δ := by
      have : List.ofFn x = δ := by simpa [factors] using hx
      rw [← this]; exact List.mem_ofFn.2 ⟨0, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y, x = fun _ => y := ⟨x 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
    obtain ⟨n, c⟩ := y
    obtain rfl : n = 1 := by simpa using hd
    obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨1, c⟩ : IrrGL k) hd
    exact isUnitarisable_of_equiv (ψ.trans φ.symm) (hδ _ hm).2

theorem not_isComplementaryProduct_absPow {s : ℝ} (hs : s ≠ 0) :
    ¬ IsComplementaryProduct (detRep (Fin 1) (absPow k s)) := fun H => by
  have hu := (isUnitarisable_ofChar_iff _).1 H.isUnitarisable_one
  refine hs ((absPow_ofReal_eq_one (k := k)).1 (MonoidHom.ext fun z => Units.ext ?_) : s = 0)
  have h := hu (Matrix.GeneralLinearGroup.scalar (Fin 1) z)
  have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [detChar_apply, h2, val_absPow_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k z).le _)] at h
  rw [val_absPow_ofReal, h]; simp

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem isCuspidal_of_isSmooth_one {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) : IsCuspidal π := by
  refine ⟨hs, fun s d e he => absurd ?_ he⟩
  rw [eq_bot_iff]
  intro u hu
  have := det_eq_one_of_mem_unipRad k hu
  rw [Subgroup.mem_bot]
  ext i j
  have h := congrArg Units.val this
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using h

theorem isComplementaryProduct_one_iff {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) : IsComplementaryProduct π ↔ IsUnitarisable π :=
  ⟨IsComplementaryProduct.isUnitarisable_one,
    isComplementaryProduct_of_isCuspidal one_pos hi (isCuspidal_of_isSmooth_one hs)⟩

theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((Representation.trivial ℂ (GL (Fin 0) k) ℂ).Equiv (prodIrr x hd)) := by
  let L := (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm
  have h1 : ∀ g : GL (Fin 0) k, g = 1 := fun g => Subsingleton.elim _ _
  let f : (Representation.trivial ℂ (GL (Fin 0) k) ℂ).IntertwiningMap (prodIrr x hd) :=
    { toFun := fun v => ⟨⟨fun _ => L v, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (h1 _)
          simp⟩, mem_smoothPart_of_nhds (Filter.univ_mem' fun g => by rw [h1 g]; simp)⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun _ => L.map_smul c v))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun _ => rfl)) }
  refine ⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩⟩⟩
  · exact L.injective (congrArg (fun φ => φ.1.1 1) h)
  · rw [h1 g]; exact L.apply_symm_apply _

theorem isComplementaryProduct_zero {π : Representation ℂ (GL (Fin 0) k) V} (hi : π.IsIrreducible) :
    IsComplementaryProduct π := by
  have h1 : ∀ g : GL (Fin 0) k, π g = 1 := fun g => by rw [Subsingleton.elim g 1, map_one]
  let e : Subrepresentation π ≃o Submodule ℂ V :=
    { toFun := fun S => S.toSubmodule
      invFun := fun S => ⟨S, fun g v hv => by rw [h1]; exact hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hsimp : IsSimpleModule ℂ V := (isSimpleModule_iff ℂ V).2 (e.isSimpleOrder_iff.1 hi)
  have hr : Module.finrank ℂ V = 1 := isSimpleModule_iff_finrank_eq_one.1 hsimp
  have : Module.Finite ℂ V := Module.finite_of_finrank_eq_succ hr
  let a : V ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simp [hr])
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl
  exact ⟨[], [], by simp, by simp, 0, Fin.elim0, rfl, rfl,
    ⟨(Representation.Equiv.mk a fun g => by rw [h1]; ext; simp).trans ψ⟩⟩

end GlobalTheory.GenericUnitary
end
end

