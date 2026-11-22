import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinear
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistence
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp.Adapt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ext_frac {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [Module.Finite A B] (f : FractionRing A →+* ℂ) :
    ∃ g : FractionRing B →+* ℂ, ∀ a : A, g (algebraMap B _ (algebraMap A B a)) = f (algebraMap A _ a) := by
  letI : Algebra A ℂ := (f.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B (FractionRing B)
  have hA : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj
  have hC : Function.Injective (algebraMap A ℂ) :=
    f.injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : Module.IsTorsionFree A (FractionRing B) := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hA (h.trans (map_zero _).symm)) id
  haveI : Module.IsTorsionFree A ℂ := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hC (h.trans (map_zero _).symm)) id
  let g := IsAlgClosed.lift (M := ℂ) (R := A) (S := FractionRing B)
  refine ⟨g.toRingHom, fun a => ?_⟩
  have h := g.commutes a
  rw [IsScalarTower.algebraMap_apply A B (FractionRing B)] at h
  exact h

variable {D : D7}

theorem charOf_congr {Ω : Type} [Field Ω] [Algebra D.host.E Ω] (a : Recip D Ω) {R : Type} [CommRing R]
    (f f' : R →+* ℂ) (ψ : G D.host.E Ω →* Rˣ) (h : ∀ σ, f (ψ σ : Rˣ) = f' (ψ σ : Rˣ)) :
    GlobalTheory.SeriesTie.charOf a f ψ = GlobalTheory.SeriesTie.charOf a f' ψ := by
  have hv : ∀ x, ∃ σ, a.pull ψ x = ψ σ := by
    intro x
    unfold Recip.pull GlobalTheory.SeriesTie.descend
    split_ifs with hc
    · obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective _ (a.sym x)
      refine ⟨σ, ?_⟩
      rw [MonoidHom.comp_apply, ← hσ]
      rfl
    · exact ⟨1, by simp⟩
  refine MonoidHom.ext fun x => ?_
  obtain ⟨σ, hσ⟩ := hv x
  simp only [GlobalTheory.SeriesTie.charOf, MonoidHom.comp_apply, hσ]
  rw [show Units.map f.toMonoidHom (ψ σ) = Units.map f'.toMonoidHom (ψ σ) from Units.ext (h σ)]

open Classical in

def withTau (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : Setup D.ntw :=
  { ρ with
    e := fun i b => if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b
    ek := fun i b k => if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k }

open Classical in

theorem withTau_e (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) :
    (withTau ρ t s τ).e i b = if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b := rfl

open Classical in

theorem withTau_ek (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) (k : ℕ) :
    (withTau ρ t s τ).ek i b k = if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k := rfl

theorem withTau_good {ρ : Setup D.ntw} (hρ : ρ.Good) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ)
    (hfix : ∀ y, τ (embLL0 D y) = embLL0 D y)
    (hδ : ∀ σ, τ (ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) =
      ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) :
    (withTau ρ t s τ).Good := by
  refine ⟨hρ.rc, hρ.ch, hρ.bad_ne, hρ.goodSetup_bad_mem_badPlaces, hρ.goodSetup_badPlaces_conj, hρ.goodSetup_placesOverTwo_subset, hρ.goodSetup_count_eq_zero_off_badPlaces, ?_, ?_, hρ.base, hρ.latS, hρ.latT, hρ.Pg,
    ?_, hρ.weil, hρ.classes⟩
  · intro i b x
    rw [withTau_e]
    split_ifs with h
    · show τ (ρ.e i b _) = _
      rw [hρ.e_LL0]
      exact hfix x
    · exact hρ.e_LL0 i b x
  · intro i b k x
    show (withTau ρ t s τ).ek i b k _ = (withTau ρ t s τ).e i b _
    rw [withTau_e, withTau_ek]
    split_ifs with h
    · exact congrArg τ (hρ.ek_e i b k x)
    · exact hρ.ek_e i b k x
  · intro i j b
    show (ρ.B i j b).de = twistOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (ρ.ch i)
      (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
    rw [hρ.delta i j b]
    unfold twistOf
    have : GlobalTheory.SeriesTie.charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) =
        GlobalTheory.SeriesTie.charOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
          (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
      refine charOf_congr _ _ _ _ fun σ => ?_
      show ρ.e i b _ = (withTau ρ t s τ).e i b _
      rw [withTau_e]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact (hδ σ).symm
      · rfl
    rw [this]

theorem ext_onSmallField {c : NChoice D} (hc : NChTie D c) (w : D.what₂.places.Pl) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (g : FractionRing (c.Oe w) →+* ℂ)
    (hg : ∀ a : D.ntw.Ok (c.twI w) (c.k' w), g (algebraMap (c.Oe w) _ (algebraMap _ (c.Oe w) a)) =
      ρ.ek (c.twI w) (c.sd w) (c.k' w) (algebraMap _ _ a))
    (y : D.LL0) : g (c.embW w (y : D.what₂.LL)) = embLL0 D y := by
  obtain ⟨⟨y', z⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors (D.ntw.O0 (c.twI w)))
    ((if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) y)
  have hz0 : (z : D.ntw.O0 (c.twI w)) ≠ 0 := nonZeroDivisors.coe_ne_zero z
  have e1 : ∀ x : D.ntw.O (c.twI w), ρ.ek (c.twI w) (c.sd w) (c.k' w)
      (algebraMap _ (FractionRing _) (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) x)) =
      ρ.e (c.twI w) (c.sd w) (algebraMap _ _ x) := hρ.ek_e (c.twI w) (c.sd w) (c.k' w)
  have h1 := congrArg g (hc.embedding_baseField_condition w y y' z hz0 hz)
  rw [map_mul, hg, hg, e1, e1] at h1
  have h2 : sideEmb D.ntw (c.twI w) (c.sd w) y * algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) =
      algebraMap _ _ (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y') := by
    have := congrArg (IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w))
      (K := FractionRing (D.ntw.O0 (c.twI w))) (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) hz
    simp only [map_mul, IsFractionRing.map, IsLocalization.map_eq] at this
    exact this
  have h3 := congrArg (ρ.e (c.twI w) (c.sd w)) h2
  rw [map_mul, hρ.e_LL0] at h3
  have hne : ρ.e (c.twI w) (c.sd w) (algebraMap _ (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z)) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      ((map_ne_zero_iff _ (D.ntw.O_inj (c.twI w))).2 hz0))
  exact mul_right_cancel₀ hne (h1.trans h3.symm)

section Point

theorem realPin_withTau {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ)
    (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : RealPin Rl cG (withTau ρ t s τ) :=
  { psi := h.psi, inf := h.inf, cartT := h.cartT, onbS := h.onbS, onbT := h.onbT, latS := h.latS, latT := h.latT,
    frS := h.frS, frT := h.frT, vac := h.vac, Pg := h.Pg, grp := h.grp, mu0 := h.mu0, eta := h.eta, delta := h.delta,
    deltaPl := h.deltaPl, ap := h.ap, am := h.am }

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem adapt_at (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m) (hm : More p) (ρ : Setup D.ntw) (hρ : ρ.Good)
    (hpin : RealPin p.R p.cG ρ) : ∃ ρ' : Setup D.ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ' := by
  haveI : Module.Finite (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w) := ex.nch.Oe_fin w
  obtain ⟨g, hg⟩ := exists_ext_frac (ex.nch.Oe_inj w) (ρ.ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w))
  haveI : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL (g.comp (ex.nch.embW w)) D.what₂.embLL
  have hfix : ∀ y : D.LL0, τ (embLL0 D y) = embLL0 D y := fun y => by
    have h := ext_onSmallField ex.nch_tie w hρ g hg y
    have h2 : τ (g (ex.nch.embW w (y : D.what₂.LL))) = D.what₂.embLL y := hτ _
    rw [h] at h2
    exact h2
  have hχ : (p.R.C.delAt (D.ntw.l (ex.nch.twI w))).ValuesIn 0 (embLL0 D) := by
    have hv := hm.2.2.small.val
    unfold CharFrame.delAt
    split_ifs
    exacts [hv.del', hv.del]
  have hδ := GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values ρ hρ (ex.nch.twI w) j (ex.nch.sd w) _ (hpin.delta _ j _) hχ τ hfix
  refine ⟨withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ, withTau_good hρ _ _ τ hfix hδ, ⟨rfl, rfl, rfl, rfl, rfl⟩, realPin_withTau hpin _ _ τ,
    τ.toRingHom.comp g, fun x => hτ x, fun a => ?_⟩
  show τ (g _) = (withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ).ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) _
  rw [withTau_ek, if_pos ⟨rfl, rfl⟩]
  exact congrArg τ (hg a)

end Point

end GlobalTheory.BigOn.Exp.Adapt

open GlobalTheory.BigOn.Exp.Adapt in

theorem GlobalTheory.BigOn.Exp.adaptEx : AdaptEx := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm CH _ _ => ⟨0, fun x hx _ i p _ hm w _ j => adapt_at p w j hm⟩⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinearStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_homogeneous_operator_linear : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ψ : AddChar K ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ (n m : ℕ) (A : (Matrix (Fin n) (Fin m) K → ℂ) → Matrix (Fin n) (Fin m) K → ℂ),
    (∀ f ∈ SB (Matrix (Fin n) (Fin m) K), ∀ f' ∈ SB (Matrix (Fin n) (Fin m) K), A (f + f') = A f + A f') →
    (∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A (c • f) = c • A f) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z)) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * f Y) = fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * A f Y) →
    ∃ c : ℂ, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A f = c • f := by
  first | exact @GlobalTheory.SchurLin.schur_linear_model | exact GlobalTheory.SchurLin.schur_linear_model | (intros; apply GlobalTheory.SchurLin.schur_linear_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesEvalZeroFormMemAdmissible
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.MixUniq

open scoped Classical

abbrev ev0 {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0

theorem adelicCoordinatesEvalZeroForm_mem_admissible {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [ev0, LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem rho_zero_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (z : Matrix (Fin n) (Fin d₁) (AE F E))
    (hz : (M₁.co.e z).1 = 0) (Ψ : Fn F n d₁) : M₁.co.rho ψ z Ψ 0 = Ψ 0 := by
  simp [Darboux.rho, schr, hz]

theorem rho_first (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (y : Fin n × Fin d₁ → AF F) (Ψ : Fn F n d₁) :
    M₁.co.rho ψ (M₁.co.e.symm (y, 0)) Ψ 0 = Ψ y := by
  simp [Darboux.rho, schr]

end GlobalTheory.MixUniq

namespace GlobalTheory.MixUniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

theorem apply_eq_evaluation_zero (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (ι' : Matrix (Fin d) (Fin d₁) E)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι')ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ)) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) (y : Fin n × Fin d₁ → AF F) :
    S Φ y = ev0 (Fin n × Fin d₁) (S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (y, 0) * (incM F ι')ᵀ) Φ)) := by
  rw [hS _ Φ hΦ]
  simp only [ev0, LinearMap.proj_apply]
  rw [rho_first]

theorem evAt_zero_comp_eq_of_exp_phase_mul (M : Model σ X W) (M₁ : Model σ X W₁) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (H' : Plane E d d₁)
    (S : Fn F n d →ₗ[ℂ] Fn F n d₁)
    (hS : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
      M₁.co.rho ψ z (S Φ))
    (hI : ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho ψ u Φ) = S Φ)
    (w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (hw : ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr ψ w φ = M.co.rho ψ u (M.co.rho ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ))
    (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    (ev0 (Fin n × Fin d₁) ∘ₗ S) (schr ψ w Φ) = (ev0 (Fin n × Fin d₁) ∘ₗ S) Φ := by
  obtain ⟨u, hu, z, hz, he⟩ := hw
  have h1 := GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ hΦ
  simp only [LinearMap.comp_apply, ev0, LinearMap.proj_apply]
  rw [he, hI u hu _ h1, hS z Φ hΦ, rho_zero_first M₁ ψ z hz]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ T : Fn F n d →ₗ[ℂ] Fn F n d₁, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d₁)) →
        (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (T Φ)) →
        (∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ u Φ) = T Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁), l ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), T Φ = c • e Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he T hTm hTh hTi hTa
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨L, hiso, hrk, hL⟩ := GlobalTheory.T.skew_adapted_pair_restriction_theta F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
  have hadmT : ev0 (Fin n × Fin d₁) ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d) := hTa _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  have hadmE : ev0 (Fin n × Fin d₁) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) :=
    GlobalTheory.T.eigen_intertwiner_composition F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he _ (adelicCoordinatesEvalZeroForm_mem_admissible _)
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.eigen_intertwiner_transitive F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hψ (Fin n × Fin d) L hiso hrk _ hadmT _ hadmE
    (fun t w hw Φ hΦ => evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H' T hTh hTi _ (hL t w hw) Φ hΦ)
    (fun t w hw Φ hΦ => evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H' e he.Heisenberg₂ he.inv _ (hL t w hw) Φ hΦ)
    ⟨_, GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ₀ hΦ₀, by
      rw [LinearMap.comp_apply, ← apply_eq_evaluation_zero M M₁ B.ψ H'.ι e he.Heisenberg₂ Φ₀ hΦ₀ y]; exact hy⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  rw [apply_eq_evaluation_zero M M₁ B.ψ H'.ι T hTh Φ hΦ y, Pi.smul_apply, apply_eq_evaluation_zero M M₁ B.ψ H'.ι e he.Heisenberg₂ Φ hΦ y, smul_eq_mul]
  exact hc _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ Φ hΦ)

end GlobalTheory.MixUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariantStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (κ : Type) [Fintype κ], Fintype.card κ = a * b → ∀ (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ), (∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)), IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd → ∀ (χ : Chr F E), IsHecke F E χ → ∀ (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)), IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd → ∀ (q : UG (cA σ) (dbl (incM F JB))) (q₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) = incM F q₀ → ∀ (s : GL (Fin b) (AE F E)), ((q : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) = Matrix.fromRows (1 : Matrix (Fin b) (Fin b) (AE F E)) (-1) * (s : Matrix (Fin b) (Fin b) (AE F E)) → ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd q φ) = thetaSum F φ := by
  first | exact @GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | exact GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag | (intros; apply GlobalTheory.ThetaOppParab.thetaSum_omd_antidiag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGapsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchoredWeight_indefiniteLift_gaps : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
    (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m), (i : ℕ) + 1 < D.R.m →
    (dat p i).p + (dat p i).q = D.R.r ∧ GlobalTheory.FlagTan.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 ∧
    ∀ (τ : Psi p.T.Q.H) (k : ℕ), k + 1 < (dat p i).p + (dat p i).q →
      (k + 1 ≠ (dat p i).p → min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) - 2 ≤ (gap (uW p i τ) k : ℝ)) ∧
      (k + 1 = (dat p i).p → LevelStarExponents.h0 L + D.R.r - 3 ≤ (gap (uW p i τ) k : ℝ)) := by
  first | exact @GlobalTheory.RecGaps.gaps | exact GlobalTheory.RecGaps.gaps | (intros; apply GlobalTheory.RecGaps.gaps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie

def parOf {D : D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) : Par where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  f := D.R.f
  n := D.R.n
  Nr := (Vc D j).rank
  L := L.sc.L
  x := L.sc.x
  b' := L.sc.b'
  η := L.etaSz
  S := L.Sc

theorem atPts_and {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : AtPts Q) (h' : AtPts Q') : AtPts fun Fm x hx i p => Q Fm x hx i p ∧ Q' Fm x hx i p :=
  Closed.imp (h.and h') fun Fm _ _ H => by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := H
    exact ⟨max a b, fun x hx hle i p hp hm =>
      ⟨ha x hx ((le_max_left _ _).trans hle) i p hp hm, hb x hx ((le_max_right _ _).trans hle) i p hp hm⟩⟩

theorem atPts_imp {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (h : AtPts Q) (H : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i),
      Q Fm x hx i p → Q' Fm x hx i p) : AtPts Q' :=
  Closed.imp h fun Fm _ _ ⟨a, ha⟩ => ⟨a, fun x hx hle i p hp hm => H Fm x hx i p (ha x hx hle i p hp hm)⟩

end GlobalTheory.ExpTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTupleThetaSpanHasTypeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseTupleThetaSpan_hasType : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), R.LUnif → FormsDetermined R i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → (∀ u : F.P0, (R.FW i).chi u = 1) → ∀ x ∈ thetaBase R i F.P0 F.ψ0⁻¹ 1 v (ownAt D v), ∀ u : F.P0, (R.FW i).ρ u x = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • x := by
  first | exact @GlobalTheory.BaseKernelType.thetaBase_hasType | exact GlobalTheory.BaseKernelType.thetaBase_hasType | (intros; apply GlobalTheory.BaseKernelType.thetaBase_hasType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfBottomPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotTransfer

theorem bottom_const_transfer : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
      NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D)
      (Y : Tri T B B' WW₁) (c : T → ℂ), IsBottomTri W i j X → IsBottomTri W i j Y → Y.IsConst W.ψ W.θ c →
      ∃ u : T → D.what₂.LLˣ, X.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S hψ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨X₁, hX₁, hX₁c⟩ := GlobalTheory.T.definiteBottomTriple_transport_same_ranks_constants W i j A A' WW X B B' WW₁ Y hX hY
  obtain ⟨Y₁, hY₁, e1, e2, e3, hY₁c⟩ := GlobalTheory.T.exists_definiteBottomTriple_transferred_frames W S hψ μ₀ hL hN i j B B' WW₁ X₁ Y hX₁ hY
  obtain ⟨u, hu⟩ := hY₁c c hc
  exact ⟨u, hX₁c _ (GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices W i j B B' WW₁ X₁ Y₁ hX₁ hY₁ e1.symm e2.symm e3.symm _ hu)⟩

end GlobalTheory.BotTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClosedPointIsCentreOfPlaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_closedPoint_isCentreOfPlace : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  first | exact @GlobalTheory.Nef.centre_place | exact GlobalTheory.Nef.centre_place | (intros; apply GlobalTheory.Nef.centre_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingsIndependentSpanningAllEmbeddingsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormReadings_independent_spanning_all_embeddings : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  first | exact @GlobalTheory.UnifAll.unif_all | exact GlobalTheory.UnifAll.unif_all | (intros; apply GlobalTheory.UnifAll.unif_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupIdempotentCoefficientsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_idempotent_coefficients : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.CovTop.RecTied D L →
    (∀ k : p.P.Gp, ∑ g, (idemOf p.P.A3.A.X).coeff g * (idemOf p.P.A3.A.X).coeff (g⁻¹ * k) = (idemOf p.P.A3.A.X).coeff k) ∧
    (∀ g h : p.P.Gp, (idemOf p.P.A3.A.X).coeff (h * g * h⁻¹) = (idemOf p.P.A3.A.X).coeff g) ∧
    (∀ g : p.P.Gp, IsIntegral ℤ ((Fintype.card p.P.Gp : D.what₂.LL) * (idemOf p.P.A3.A.X).coeff g)) ∧
    ∀ (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp), σ ((idemOf p.P.A3.A.X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf p.P.A3.A.X).coeff g)) := by
  first | exact @GlobalTheory.TieIdem.tied_good_idem | exact GlobalTheory.TieIdem.tied_good_idem | (intros; apply GlobalTheory.TieIdem.tied_good_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaLowGivesFirstIdentityStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_low_gives_first_identity : GlobalTheory.BigTop.LamLow → IPb := by
  first | exact @GlobalTheory.BigTop.Fun.ipb_of_lamLow | exact GlobalTheory.BigTop.Fun.ipb_of_lamLow | (intros; apply GlobalTheory.BigTop.Fun.ipb_of_lamLow <;> assumption)
end

