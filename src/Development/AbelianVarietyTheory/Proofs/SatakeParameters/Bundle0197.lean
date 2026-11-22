import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittTheoremModUniformizerPowStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralWittTheorem_mod_uniformizerPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (z z' : ι → Fin n' → L), (∀ i, 1 ≤ a i) →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j)) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a i) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  first | exact @GlobalTheory.Hk3.IntWittMod.witt_mod_pow | exact GlobalTheory.Hk3.IntWittMod.witt_mod_pow | (intros; apply GlobalTheory.Hk3.IntWittMod.witt_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleGl1IsoDet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLOneChar

open GlobalTheory.SmGL

theorem equiv_detRep_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  intro k _ _ _ _ d V _ _ σ ω hd hirr hω
  have hact : ∀ (g : GL (Fin d) k) (v : V), σ g v = (ω (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro g v
    conv_lhs => rw [GlobalTheory.ProdSupport.eq_scalar_det hd g]
    exact hω _ v
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : (⊥ : Subrepresentation σ) = ⊤ :=
      Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g w hw => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [hact, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩
  have hS : S = ⊤ := by
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact hv this
    · exact h
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℂ V v) := by
    intro w
    have hw : w ∈ S.toSubmodule := by rw [hS]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨c, rfl⟩
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℂ V v) := by
    intro a b hab
    simp only [LinearMap.toSpanSingleton_apply] at hab
    exact smul_left_injective ℂ hv hab
  let e : ℂ ≃ₗ[ℂ] V := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨(Representation.Equiv.mk e fun g => ?_).symm⟩
  ext c
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, detRep, ofChar_apply,
    detChar_apply, hact, smul_smul, smul_eq_mul]
  rw [mul_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one]

end GlobalTheory.GLOneChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientEigenvector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.VecSubquot

theorem exists_irreducible_subquotient_of_ne_zero : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (x : V), x ≠ 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      τ.IsIrreducible ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
        ∀ (g : G) (c : ℂ), ρ g x = c • x → τ g y = c • y := by
  intro G V _ _ _ ρ x hx

  let s : Set (Submodule ℂ V) := {N | (∀ (g : G), ∀ v ∈ N, ρ g v ∈ N) ∧ x ∉ N}
  have hbot : (⊥ : Submodule ℂ V) ∈ s := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], by simpa using hx⟩
  obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun hx' => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨M, hM, hvM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hv
      exact le_sSup hM ((hcs hM).1 g v hvM)
    · obtain ⟨M, hM, hxM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hx'
      exact (hcs hM).2 hxM) ⊥ hbot
  obtain ⟨hNst, hxN⟩ := hmax.prop

  let O : Submodule ℂ V := Submodule.span ℂ (Set.range fun g : G => ρ g x)
  have hOst : ∀ (g : G), ∀ v ∈ O, ρ g v ∈ O := by
    intro g v hv
    have : O.map (ρ g) ≤ O := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩
    exact this ⟨v, hv, rfl⟩
  have hxO : x ∈ O := Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩
  let T : Subrepresentation ρ := ⟨N, fun g v hv => hNst g v hv⟩
  let S : Subrepresentation ρ := ⟨N ⊔ O, fun g v hv => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (hNst g a ha) (hOst g b hb)⟩
  have hxS : x ∈ S.toSubmodule := Submodule.mem_sup_right hxO
  have hcov : T ⋖ S := by
    refine ⟨lt_of_le_of_ne (fun v hv => Submodule.mem_sup_left hv) fun h => hxN ?_, ?_⟩
    · have : x ∈ (S : Set V) := hxS
      rw [← h] at this
      exact this
    · intro T' h1 h2
      have hle : N ≤ T'.toSubmodule := h1.le
      have hxT' : x ∈ T'.toSubmodule := by
        by_contra hn
        have hmem : T'.toSubmodule ∈ s := ⟨fun g v hv => T'.apply_mem_toSubmodule g hv, hn⟩
        have heq : T'.toSubmodule = N := le_antisymm (hmax.2 hmem hle) hle
        exact h1.ne (Subrepresentation.toSubmodule_injective heq.symm)
      have hST' : S.toSubmodule ≤ T'.toSubmodule := by
        refine sup_le hle ?_
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        exact T'.apply_mem_toSubmodule g hxT'
      exact h2.not_ge hST'
  refine ⟨_, inferInstance, inferInstance, GlobalTheory.SmGL.subQuot S T,
    Submodule.Quotient.mk (⟨x, hxS⟩ : S.toSubmodule), GlobalTheory.SmGL.isIrreducible_subQuot hcov,
    ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩, ?_, ?_⟩
  · intro h0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact hxN h0
  · intro g c hgc
    show Submodule.Quotient.mk (S.toRepresentation g ⟨x, hxS⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext hgc

end GlobalTheory.VecSubquot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartForm
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

open GlobalTheory.DefU

namespace GlobalTheory.Cong

theorem ofType_of_finPart_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n)
    (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) →
    OfType (fun τ => W.at τ) K π.V := by
  intro E _ _ _ n π W K f hf hf0 hK
  refine ⟨π.isAut, fun τ => ?_, ?_⟩
  · have h : (AU.mk π).HasWt (InfinitePlace.mk τ).embedding (W (InfinitePlace.mk τ)) :=
      hasWeightAt_of_finPart π W hf hf0 (InfinitePlace.mk τ)
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · have h' := h
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), e] at h'
      exact h'
    · have h2 := h.conjugate
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ] at h2
      exact h2
  · have hne : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (LinearMap.ext hc)
    refine ⟨f.1 v, AutSub.mem_finPart.1 hf v, hv, fun x hx => ?_⟩
    funext g
    rw [RU_apply]
    exact hK x hx v g

example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n) (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) → OfType (fun τ => W.at τ) K π.V := ofType_of_finPart_fixed

end GlobalTheory.Cong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwistParamAbove

theorem isFrobSS_wdRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    IsFrobSS (wdRho P ι Bw h hj ρ) (wdN P ι ρ) (wdRep P ι Bw h hj ρ) := by
  obtain ⟨u, hN, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  have := isFrobSS_of_unipotent u hu hc hρ
  rwa [hN] at this

theorem isModel_twist {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω Gw O} {a : ℕ} {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)} {s : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1} (h₁ : IsModel Bw r L s) (h₂ : IsModel Bw c L m) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) := by
  refine ⟨h₁.1, ?_⟩
  rw [← h₁.2, ← h₂.2]
  ext g i j
  simp [mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
  simp [Matrix.map_apply]

end GlobalTheory.TwistParamAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.EmptyFirstBlock

section Reindex

variable {R : Type} [CommRing R] {t : ℕ} {c : Bool → ℕ}

def trueEquiv (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) : Fin (c true) ≃ Fin t :=
  Equiv.ofBijective (fun i => f ⟨true, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact absurd i.2 (by omega)
    | true => exact ⟨i, rfl⟩⟩

@[simp] theorem trueEquiv_apply (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) (i : Fin (c true)) :
    trueEquiv f hc i = f ⟨true, i⟩ := rfl

def reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    GL m R →* GL n R :=
  Units.map (Matrix.reindexAlgEquiv R R e).toRingEquiv.toMonoidHom

theorem val_reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m R) (i j : n) :
    (reindexGL e g : Matrix n n R) i j = (g : Matrix m m R) (e.symm i) (e.symm j) := rfl

theorem det_reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m R) : Matrix.GeneralLinearGroup.det (reindexGL e g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  have : (reindexGL e g : Matrix n n R) = (g : Matrix m m R).submatrix e.symm e.symm := by
    ext i j; rfl
  rw [this, Matrix.det_submatrix_equiv_self]

def liftT (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) (h : GL (Fin t) R) :
    SmGL.Levi R (fun j => Fin (c j)) :=
  Pi.mulSingle (M := fun j => GL (Fin (c j)) R) true (reindexGL (trueEquiv f hc).symm h)

theorem leviEmb_liftT (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) (h : GL (Fin t) R) :
    SmGL.leviEmb R f (liftT f hc h) = h := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | false => exact absurd i.2 (by omega)
  | true =>
    cases b with
    | false => exact absurd j.2 (by omega)
    | true =>
      rw [SmGL.leviEmb_apply_same]
      simp [liftT, val_reindexGL]

theorem eq_one_of_mem_unipRad (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) {g : GL (Fin t) R}
    (hg : g ∈ SmGL.unipRad R f) : g = 1 := by
  obtain ⟨-, h2⟩ := SmGL.mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | false => exact absurd i.2 (by omega)
  | true =>
    cases b with
    | false => exact absurd j.2 (by omega)
    | true =>
      rw [h2 true i j]
      simp [Matrix.one_apply]

end Reindex

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {t : ℕ} {c : Bool → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem twKer_eq_bot (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    (π : Representation ℂ (GL (Fin t) k) W) : twKer π (SmGL.unipRad k f) 1 = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro _ ⟨n, v, rfl⟩
  have : (n : GL (Fin t) k) = 1 := eq_one_of_mem_unipRad f hc n.2
  simp [this]

theorem deltaHalf_eq_one (hc : c false = 0) (g : SmGL.Levi k (fun j => Fin (c j))) :
    SmGL.deltaHalf k (fun j => Fin (c j)) g = 1 := by
  haveI : IsEmpty (Fin (c false)) := by rw [hc]; infer_instance
  rw [SmGL.deltaHalf_apply, Fintype.prod_bool]
  have h1 : SmGL.modExp (fun j => Fin (c j)) true = 0 := by
    simp only [SmGL.modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g false) = 1 := by
    ext; simp [Matrix.det_isEmpty]
  have h0 : SmGL.absPow k 0 = 1 := by
    ext x; simp [SmGL.val_absPow]
  rw [h1, h2]
  simp [h0]

theorem jac_liftT_mk (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    (π : Representation ℂ (GL (Fin t) k) W) (h : GL (Fin t) k) (w : W) :
    SmGL.jac f π (liftT f hc h) (Submodule.Quotient.mk w) = Submodule.Quotient.mk (π h w) := by
  rw [SmGL.jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, leviEmb_liftT]

theorem subrep_dichotomy (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    {π : Representation ℂ (GL (Fin t) k) W} (hπ : π.IsIrreducible)
    (S : Subrepresentation (SmGL.jac f π)) : S = ⊥ ∨ S = ⊤ := by
  let T : Subrepresentation π := ⟨S.toSubmodule.comap (twKer π (SmGL.unipRad k f) 1).mkQ,
    fun h w hw => by
      show Submodule.Quotient.mk (π h w) ∈ S.toSubmodule
      rw [← jac_liftT_mk f hc]
      exact S.apply_mem_toSubmodule _ hw⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun u hu => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : w ∈ T.toSubmodule := hu
    rw [h] at this
    have hw : w = 0 := (Submodule.mem_bot ℂ).1 this
    rw [hw]
    exact Submodule.zero_mem _
  · right
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun u _ => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : w ∈ T.toSubmodule := by rw [h]; trivial
    exact this

end Main

end GlobalTheory.EmptyFirstBlock

namespace GlobalTheory.EmptyFirstBlock

section Tensor

theorem tprod_ne_zero {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (x : ∀ i, X i) (hx : ∀ i, x i ≠ 0) : PiTensorProduct.tprod ℂ x ≠ 0 := by
  have : ∀ i, ∃ φ : Module.Dual ℂ (X i), φ (x i) ≠ 0 := fun i => by
    by_contra h
    push_neg at h
    exact hx i ((Module.forall_dual_apply_eq_zero_iff ℂ (x i)).1 h)
  choose φ hφ using this
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) h0
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at this
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hφ i) this

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reindexGL_mem_KO {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {h : GL m k} (hh : h ∈ KO k m) : reindexGL e h ∈ KO k n := by
  obtain ⟨h0, rfl⟩ := hh
  exact ⟨reindexGL e h0, Units.ext (Matrix.ext fun i j => rfl)⟩

theorem isSpherical_twist_of_empty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin t) k) W) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin t) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (χ : kˣ →* ℂˣ) (z : (s true).V), IsSmooth π → π.IsIrreducible → c false = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (jac f π) → z ≠ 0 → (∀ g ∈ KO k (Fin (c true)), (s true).ρ g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z) → IsSpherical (twist π (detChar (Fin t) χ⁻¹)) := by
  intro k _ _ _ _ t W _ _ π c f s χ z _ hπ hc hsub hz0 hz
  haveI := nontrivial_of_irreducible (s false).irr
  obtain ⟨w0, hw0⟩ := exists_ne (0 : (s false).V)
  let x : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) w0 z j
  have hx : ∀ j, x j ≠ 0 := by
    intro j
    cases j
    · exact hw0
    · exact hz0
  have hX : PiTensorProduct.tprod ℂ x ≠ 0 := tprod_ne_zero x hx
  obtain ⟨S, F, hF⟩ := hsub
  rcases subrep_dichotomy f hc hπ S with rfl | rfl
  · exfalso
    obtain ⟨u, hu⟩ := hF (PiTensorProduct.tprod ℂ x)
    exact hX (by rw [← hu, show u = 0 from Subtype.ext u.2, map_zero])
  let j : (SmGL.jac f π).IntertwiningMap (⊤ : Subrepresentation (SmGL.jac f π)).toRepresentation :=
    ⟨LinearMap.codRestrict _ LinearMap.id (fun _ => trivial), fun _ => rfl⟩
  let G := F.comp j
  have hG : Function.Surjective G := fun w => by
    obtain ⟨u, rfl⟩ := hF w
    exact ⟨u.1, rfl⟩
  have hGi : Function.Injective G := by
    refine (injective_iff_map_eq_zero G).2 fun y hy => ?_
    rcases subrep_dichotomy f hc hπ G.ker with h | h
    · have : y ∈ G.ker := hy
      rw [h] at this
      exact this
    · exfalso
      obtain ⟨u, hu⟩ := hG (PiTensorProduct.tprod ℂ x)
      have : u ∈ G.ker := by rw [h]; trivial
      exact hX (hu ▸ this)
  obtain ⟨u, hu⟩ := hG (PiTensorProduct.tprod ℂ x)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hX
    rw [← hu, Submodule.Quotient.mk_zero, map_zero]
  have key : ∀ h ∈ KO k (Fin t), π h v = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • v := by
    intro h hh
    have hg' : reindexGL (trueEquiv f hc).symm h ∈ KO k (Fin (c true)) := reindexGL_mem_KO _ hh
    have hdet := det_reindexGL (R := k) (trueEquiv f hc).symm h
    have htens : (piTensor fun j => (s j).ρ) (liftT f hc h) (PiTensorProduct.tprod ℂ x) =
        (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • PiTensorProduct.tprod ℂ x := by
      rw [piTensor_tprod]
      have hfun : (fun a => (s a).ρ (liftT f hc h a) (x a)) =
          Function.update x true ((χ (Matrix.GeneralLinearGroup.det h) : ℂ) • x true) := by
        funext a
        cases a
        · simp [liftT, x]
        · simp [liftT, x, hz _ hg', hdet]
      rw [hfun, MultilinearMap.map_update_smul, Function.update_eq_self]
    have h1 : G (SmGL.jac f π (liftT f hc h) (Submodule.Quotient.mk v)) =
        G ((χ (Matrix.GeneralLinearGroup.det h) : ℂ) • Submodule.Quotient.mk v) := by
      rw [G.isIntertwining, hu, map_smul, hu, htens]
    have h2 := hGi h1
    rw [jac_liftT_mk f hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, twKer_eq_bot f hc,
      Submodule.mem_bot, sub_eq_zero] at h2
    exact h2
  show fixed (twist π (detChar (Fin t) χ⁻¹)) (KO k (Fin t)) ≠ ⊥
  intro hbot
  have hmem : v ∈ fixed (twist π (detChar (Fin t) χ⁻¹)) (KO k (Fin t)) := by
    intro h
    show twist π (detChar (Fin t) χ⁻¹) (h : GL (Fin t) k) v = (((1 : _ →* ℂˣ) h : ℂˣ) : ℂ) • v
    rw [twist_apply, key h h.2, smul_smul]
    simp
  rw [hbot] at hmem
  exact hv0 ((Submodule.mem_bot ℂ).1 hmem)

end GlobalTheory.EmptyFirstBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatakeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  first | exact @GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | exact GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | (intros; apply GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake <;> assumption)
end

