import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalSpectrumFinitenessOfDecayHarishChandra
section
noncomputable section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpecFinite

open GlobalTheory.CuspMult GlobalTheory.PRep

section Abstract

variable {H X : Type} [Group H] [TopologicalSpace H] [AddCommGroup X] [Module ℂ X]

theorem simple_asSubmodule {ρ : Representation ℂ H X} (U : Subrepresentation ρ) (hU : U.toRepresentation.IsIrreducible) :
    IsSimpleModule (MonoidAlgebra ℂ H) U.asSubmodule := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) U.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).1 hU
  exact IsSimpleModule.congr (GlobalTheory.RepCount.subEquiv U).symm

theorem exists_sub_equiv {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (h1 : σ.IsIrreducible) {f : W →ₗ[ℂ] X} (hf : ∀ g s, f (σ g s) = ρ g (f s)) (h0 : f ≠ 0) :
    ∃ U : Subrepresentation ρ, U.toSubmodule = LinearMap.range f ∧ Function.Injective f ∧
      ∃ e : W ≃ₗ[ℂ] U.toSubmodule, (∀ s, (e s : X) = f s) ∧ ∀ g s, e (σ g s) = U.toRepresentation g (e s) := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf
  have hi : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | hz
    · exact hi
    · exact absurd (LinearMap.ext fun s => DFunLike.congr_fun hz s) h0
  exact ⟨F.range, rfl, hi, LinearEquiv.ofInjective f hi, fun s => rfl, fun g s => Subtype.ext (hf g s)⟩

theorem rank_homInto_lt {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X) (K : Subgroup H) (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) (h1 : σ.IsIrreducible)
    {x : W} (hx0 : x ≠ 0) (hx : ∀ k ∈ K, σ k x = x) : Module.rank ℂ (homInto σ ρ C) < Cardinal.aleph0 := by
  let ev : homInto σ ρ C →ₗ[ℂ] ↥(C ⊓ fixed ρ K) :=
    { toFun := fun f => ⟨(f : W →ₗ[ℂ] X) x, f.2.1 x, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← f.2.2, hx k hk]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun f hf => ?_
    by_contra hne
    obtain ⟨U, -, hi, -⟩ := exists_sub_equiv h1 f.2.2 (fun h => hne (Subtype.ext h))
    have h0 : (f : W →ₗ[ℂ] X) x = (f : W →ₗ[ℂ] X) 0 := by
      rw [map_zero]
      exact congrArg Subtype.val hf
    exact hx0 (hi h0)
  haveI := FiniteDimensional.of_injective ev hinj
  exact Module.rank_lt_aleph0 ℂ _

theorem finite_classes (ρ : Representation ℂ H X) (C : Submodule ℂ X) (K : Subgroup H)
    (hA : FiniteDimensional ℂ ↥(C ⊓ fixed ρ K)) :
    ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
      (σs : ∀ i, Representation ℂ H (Ws i)),
      ((∀ i, (σs i).IsIrreducible) ∧ (∀ i, IsAdmissible (σs i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σs i).Equiv (σs j))) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → IsAdmissible σ →
        homInto σ ρ C ≠ ⊥ → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i)) := by
  classical
  let S : Set (Subrepresentation ρ) := {U | U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    IsAdmissible U.toRepresentation ∧ U.toSubmodule ⊓ fixed ρ K ≠ ⊥}
  let comp : Subrepresentation ρ → Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    fun U => isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule U.asSubmodule
  let T : Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) := comp '' S
  have hT : sSupIndep T := (sSupIndep_isotypicComponents (MonoidAlgebra ℂ H) ρ.asModule).mono (by
    rintro _ ⟨U, hU, rfl⟩
    exact ⟨U.asSubmodule, simple_asSubmodule U hU.2.1, rfl⟩)
  have hy : ∀ c : T, ∃ y : ↥(C ⊓ fixed ρ K), y ≠ 0 ∧
      ρ.asModuleEquiv.symm (y : X) ∈ (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := by
    rintro ⟨_, U, hU, rfl⟩
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hU.2.2.2
    exact ⟨⟨y, hU.1 hy.1, hy.2⟩, fun h => hy0 (congrArg Subtype.val h), U.asSubmodule.le_isotypicComponent hy.1⟩
  choose y hy0 hyc using hy
  have hsm : ∀ (c : T) (a : ℂ), ρ.asModuleEquiv.symm ((a • y c : ↥(C ⊓ fixed ρ K)) : X) ∈
      (c : Submodule (MonoidAlgebra ℂ H) ρ.asModule) := fun c a => by
    rw [Submodule.coe_smul, map_smul]
    exact Submodule.smul_of_tower_mem _ a (hyc c)
  have hli : LinearIndependent ℂ y := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have hx : ρ.asModuleEquiv.symm ((g i • y i : ↥(C ⊓ fixed ρ K)) : X) ∈
        (i : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ⊓ sSup (T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)}) := by
      refine ⟨hsm i (g i), ?_⟩
      have he : (g i • y i : ↥(C ⊓ fixed ρ K)) = - ∑ j ∈ s.erase i, g j • y j := by
        rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase s (fun j => g j • y j) hi, hs]
      rw [he, Submodule.coe_neg, Submodule.coe_sum, map_neg, map_sum]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
      refine (le_sSup (show (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ∈ T \ {(i : Submodule (MonoidAlgebra ℂ H) ρ.asModule)} from
          ⟨j.2, fun h => Finset.ne_of_mem_erase hj (Subtype.ext h)⟩) :
        (j : Submodule (MonoidAlgebra ℂ H) ρ.asModule) ≤ _) (hsm j (g j))
    rw [(hT i.2).eq_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff, Submodule.coe_eq_zero, smul_eq_zero] at hx
    exact hx.resolve_right (hy0 i)
  haveI : Finite T := hli.finite
  haveI := Fintype.ofFinite T
  let e := Fintype.equivFin T
  have hrep : ∀ c : T, ∃ U ∈ S, comp U = c := fun c => c.2
  choose U hUS hUc using hrep
  refine ⟨Fintype.card T, fun i => ↥(U (e.symm i)).toSubmodule, fun i => inferInstance, fun i => inferInstance,
    fun i => (U (e.symm i)).toRepresentation, ⟨fun i => (hUS _).2.1, fun i => (hUS _).2.2.1, fun i j hij => ⟨fun φ => hij ?_⟩⟩, ?_⟩
  · obtain ⟨ψ⟩ := (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).1 ⟨φ⟩
    have h3 := ((GlobalTheory.RepCount.subEquiv _).symm.trans (ψ.trans (GlobalTheory.RepCount.subEquiv _))).isotypicComponent_eq
      (M := ρ.asModule)
    exact e.symm.injective (Subtype.ext ((hUc _).symm.trans (h3.trans (hUc _))))
  · rintro W _ _ σ h1 h2 hne ⟨x, hx0, hx⟩
    obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨V, hV, hi, ev, hev, heq⟩ := exists_sub_equiv h1 hf.2 hf0
    haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).1 h1
    let ψ : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule :=
      LinearEquiv.ofBijective (GlobalTheory.RepCount.modMap ev.toLinearMap heq) ev.bijective
    have hVirr : V.toRepresentation.IsIrreducible :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).2 (IsSimpleModule.congr ψ.symm)
    have hVS : V ∈ S := by
      refine ⟨?_, hVirr, GlobalTheory.RepCount.isAdmissible_of_injective ev.symm.toLinearMap (fun g s => ?_) ev.symm.injective h2, ?_⟩
      · rw [hV]
        rintro _ ⟨s, rfl⟩
        exact hf.1 s
      · rw [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_eq, heq, LinearEquiv.apply_symm_apply]
      · rw [Submodule.ne_bot_iff]
        refine ⟨f x, ⟨hV ▸ ⟨x, rfl⟩, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => by rw [← hf.2, hx k hk]⟩, fun h => hx0 (hi ?_)⟩
        rw [h, map_zero]
    refine ⟨e ⟨comp V, V, hVS, rfl⟩, ?_⟩
    show Nonempty (σ.Equiv (U (e.symm (e ⟨comp V, V, hVS, rfl⟩))).toRepresentation)
    generalize hc : e.symm (e ⟨comp V, V, hVS, rfl⟩) = c
    rw [Equiv.symm_apply_apply] at hc
    haveI := simple_asSubmodule V hVirr
    haveI := simple_asSubmodule (U c) (hUS c).2.1
    have hle : (U c).asSubmodule ≤ comp V :=
      ((U c).asSubmodule.le_isotypicComponent).trans_eq ((hUc c).trans (congrArg Subtype.val hc).symm)
    obtain ⟨χ⟩ := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule V.asSubmodule) _ hle
    exact (GlobalTheory.CuspFactor.nonempty_equiv_iff _ _).2
      ⟨(ψ.trans (GlobalTheory.RepCount.subEquiv V)).trans (χ.symm.trans (GlobalTheory.RepCount.subEquiv _).symm)⟩

end Abstract

theorem specFin : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation →
    SpecFin := by
  intro hQ hP hDM D V S M μ _ _
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hm : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ →
      mCuspDS μ σ M = Module.rank ℂ (homInto σ (finRep M) (allMaps θ M)) := fun W _ _ σ h =>
    (GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hQ hP hDM D θ hθ V S M μ W σ h.1).symm
  refine ⟨fun W _ _ σ h1 h2 => ?_, fun K hK => ?_⟩
  · haveI := GlobalTheory.CuspFactor.nontrivial_of_irr σ h1
    obtain ⟨x, hx0⟩ := exists_ne (0 : W)
    let St : Subgroup (GfC V) :=
      { carrier := {g | σ g x = x}
        mul_mem' := fun {a b} ha hb => by
          show σ (a * b) x = x
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          show σ a⁻¹ x = x
          conv_lhs => rw [← ha]
          simp }
    rw [hm W σ h2]
    exact rank_homInto_lt σ (finRep M) (allMaps θ M) St (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ St (h2.1 x)) h1 hx0
      (fun k hk => hk)
  · obtain ⟨n, Ws, i1, i2, σs, hs, hcov⟩ :=
      finite_classes (finRep M) (allMaps θ M) K (GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ K hK)
    refine ⟨n, Ws, i1, i2, σs, hs, fun W _ _ σ h1 h2 hm0 hx => hcov W σ h1 h2 (fun h => hm0 ?_) hx⟩
    rw [hm W σ h2, h, rank_bot]

end GlobalTheory.SpecFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
section
noncomputable section

namespace GlobalTheory.FockKFin

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) : Submodule ℂ (SInf F κ) :=
  Submodule.span ℂ {h | ∃ a b : κ → mixedEmbedding.mixedSpace F, ∃ f ∈ P, h = dOp a b f}

theorem dOp_mem_dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) (a b : κ → mixedEmbedding.mixedSpace F)
    {f : SInf F κ} (hf : f ∈ P) : dOp a b f ∈ dStep P :=
  Submodule.subset_span ⟨a, b, f, hf, rfl⟩

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {g | GaussD M τ g}

def polLe (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (vacSp M τ) (fun _ P => P ⊔ dStep P) m

theorem polLe_zero (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : polLe M τ 0 = vacSp M τ := rfl

theorem polLe_succ (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    polLe M τ (m + 1) = polLe M τ m ⊔ dStep (polLe M τ m) := rfl

theorem polLe_mono (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Monotone (polLe M τ) :=
  monotone_nat_of_le_succ fun m => by rw [polLe_succ]; exact le_sup_left

def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pureL_apply {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (f : SInf F κ) :
    pureL φ f = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := rfl

end GlobalTheory.FockKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxChangeRealisedCompAndReindex
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F]

theorem isOp_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp ψ s S S') (ht : IsOp ψ t T T') : IsOp ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') where
  pres φ h := ht.pres _ (hs.pres φ h)
  pres' φ h := hs.pres' _ (ht.pres' φ h)
  left φ h := by simp only [LinearMap.comp_apply]; rw [ht.left _ (hs.pres φ h), hs.left φ h]
  right φ h := by simp only [LinearMap.comp_apply]; rw [hs.right _ (ht.pres' φ h), ht.right φ h]
  adm l hl := by rw [← LinearMap.comp_assoc]; exact hs.adm _ (ht.adm l hl)
  adm' l hl := by rw [← LinearMap.comp_assoc]; exact ht.adm' _ (hs.adm' l hl)
  Heisenberg₂ w φ h := by
    simp only [LinearMap.comp_apply, Function.comp_apply]
    rw [hs.Heisenberg₂ w φ h, ht.Heisenberg₂ _ _ (hs.pres φ h)]
  theta := by
    obtain ⟨c₁, hc₁, e₁⟩ := hs.theta
    obtain ⟨c₂, hc₂, e₂⟩ := ht.theta
    exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, fun φ h => by
      simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩
  norm μ μ'' hμ hμ'' := by
    letI : MeasurableSpace (κ' → AF F) := borel _
    haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
    haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
    obtain ⟨c₁, h1, h1', e₁⟩ := hs.norm μ Measure.addHaar hμ inferInstance
    obtain ⟨c₂, h2, h2', e₂⟩ := ht.norm Measure.addHaar μ'' inferInstance hμ''
    exact ⟨c₂ * c₁, mul_ne_zero h2 h1, ENNReal.mul_ne_top h2' h1', fun φ h => by
      simp only [LinearMap.comp_apply]; rw [e₂ _ (hs.pres φ h), e₁ φ h, mul_assoc]⟩

theorem dblAct_comp {κ κ' κ'' : Type} (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) :
    dblAct (t ∘ s) = dblAct t ∘ dblAct s := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem isOp2_comp {ψ : AddChar (AF F) ℂ} {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
    {t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)}
    {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}
    {T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)} {T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hs : IsOp2 ψ s S S') (ht : IsOp2 ψ t T T') : IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T') := by
  obtain ⟨hs1, Sd, Sd', hsd, hsb⟩ := hs
  obtain ⟨ht1, Td, Td', htd, htb⟩ := ht
  have hc : ∀ {ι : Type} [Fintype ι], ∀ φ ∈ schA F ι, star φ ∈ schA F ι := fun φ h => GlobalTheory.ConjSch.conj_mem_schA φ h
  refine ⟨isOp_comp hs1 ht1, Td ∘ₗ Sd, Sd' ∘ₗ Td', ?_, fun φ₁ h₁ φ₂ h₂ => ?_⟩
  · rw [dblAct_comp]; exact isOp_comp hsd htd
  · simp only [LinearMap.comp_apply]
    rw [hsb φ₁ h₁ φ₂ h₂, htb _ (hs1.pres _ h₁) _ (hc _ (hs1.pres _ (hc _ h₂))), star_star]

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

def addRe {X : Type} [TopologicalSpace X] [AddCommGroup X] (e : κ' ≃ κ) : (κ' → X) ≃ₜ+ (κ → X) where
  toFun x := x ∘ e.symm
  invFun y := y ∘ e
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

def reix {R : Type} (e : κ' ≃ κ) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : κ' → R => x ∘ e.symm)

theorem reix_apply {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e.symm) := rfl

theorem reix_symm_reix {R : Type} (e : κ' ≃ κ) (φ : (κ → R) → ℂ) : reix e.symm (reix e φ) = φ := by
  funext x; simp only [reix_apply, Equiv.symm_symm]; congr 1; funext i; simp

def linRe (e : κ' ≃ κ) : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) e.symm).toContinuousLinearEquiv

theorem sb_reix (e : κ' ≃ κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun y : κ' → FiniteAdeleRing (𝓞 F) F => g (y ∘ e.symm)) ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) :=
  ⟨hg.1.comp_continuous (addRe e).continuous, hg.2.comp_homeomorph (addRe e).toHomeomorph⟩

theorem reix_pureA (e : κ' ≃ κ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    reix e (pureA F f g) = pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e) f)
      (fun y => g (y ∘ e.symm)) := by
  funext x
  rfl

theorem reix_mem_schA (e : κ' ≃ κ) {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have hle : schA F κ ≤ (schA F κ').comap (reix e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    exact Submodule.subset_span ⟨_, _, sb_reix e hg, reix_pureA e f g⟩
  exact hle h

theorem reix_adm (e : κ' ≃ κ) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ reix e ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl _ (sb_reix e hg)
  exact ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (linRe e)), fun f => by
    rw [LinearMap.comp_apply, reix_pureA]; exact hT _⟩

theorem reix_theta (e : κ' ≃ κ) (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AF F) (ξ i)))

theorem reix_heis (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    reix e (schr ψ w φ) = schr ψ (w.1 ∘ e, w.2 ∘ e) (reix e φ) := by
  have hd : ∀ u v : κ → AF F, (u ∘ e) ⬝ᵥ (v ∘ e) = u ⬝ᵥ v := fun u v => by
    simp only [dotProduct, Function.comp_apply]; exact Equiv.sum_comp e (fun i => u i * v i)
  funext x
  simp only [reix_apply, schr]
  have h1 : (x ∘ e.symm) ⬝ᵥ w.2 = x ⬝ᵥ (w.2 ∘ e) := by
    rw [← hd]; congr 1; funext i; simp
  have h2 : x ∘ e.symm + w.1 = (x + w.1 ∘ e) ∘ e.symm := by funext i; simp
  rw [h1, h2, hd]

theorem reix_norm (e : κ' ≃ κ) (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (hμ' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : (κ → AF F) → ℂ,
      ∫⁻ x, ‖reix e φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  letI : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  haveI := hμ'
  let L : (κ' → AF F) ≃ₜ+ (κ → AF F) := addRe e
  haveI : (μ'.map L).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ' L
  have heq := Measure.isAddLeftInvariant_eq_smul (μ'.map L) μ
  refine ⟨(Measure.addHaarScalarFactor (μ'.map L) μ : ℝ≥0∞),
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top,
    fun φ => ?_⟩
  have hm := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) L.toHomeomorph.toMeasurableEquiv (μ := μ')
  have hL : (⇑L.toHomeomorph.toMeasurableEquiv : (κ' → AF F) → (κ → AF F)) = ⇑L := rfl
  rw [hL, heq, lintegral_smul_measure] at hm
  rw [ENNReal.smul_def, smul_eq_mul] at hm
  exact hm.symm

end GlobalTheory.TowU.RealComp

namespace GlobalTheory.TowU.RealComp

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem isOp_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) where
  pres _ h := reix_mem_schA e h
  pres' _ h := reix_mem_schA e.symm h
  left φ _ := reix_symm_reix e φ
  right φ _ := by simpa using reix_symm_reix e.symm φ
  adm _ hl := reix_adm e hl
  adm' _ hl := reix_adm e.symm hl
  Heisenberg₂ w φ _ := reix_heis ψ e w φ
  theta := ⟨1, one_ne_zero, fun φ _ => by rw [reix_theta, one_mul]⟩
  norm μ μ' hμ hμ' := by
    obtain ⟨c, h0, h1, h⟩ := reix_norm e μ μ' hμ hμ'
    exact ⟨c, h0, h1, fun φ _ => h φ⟩

theorem dblAct_reix (e : κ' ≃ κ) :
    dblAct (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) =
      fun w => (w.1 ∘ Equiv.sumCongr e e, w.2 ∘ Equiv.sumCongr e e) := by
  funext w
  refine Prod.ext ?_ ?_ <;> funext a <;> rcases a with a | a <;> simp [dblAct]

theorem isOp2_reix (ψ : AddChar (AF F) ℂ) (e : κ' ≃ κ) :
    IsOp2 ψ (fun w : (κ → AF F) × (κ → AF F) => (w.1 ∘ e, w.2 ∘ e)) (reix e) (reix e.symm) := by
  refine ⟨isOp_reix ψ e, reix (Equiv.sumCongr e e), reix (Equiv.sumCongr e e).symm, ?_, fun φ₁ _ φ₂ _ => ?_⟩
  · rw [dblAct_reix]; exact isOp_reix ψ _
  · funext x
    simp only [reix_apply, boxFun, Pi.star_apply, star_star]
    congr 2 <;> funext i <;> simp

theorem realised_comp_reix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ (κ κ' κ'' : Type) [Fintype κ] [Fintype κ'] [Fintype κ''] (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (t : (κ' → AF F) × (κ' → AF F) → (κ'' → AF F) × (κ'' → AF F)) (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (T : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)) (T' : ((κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsOp2 ψ s S S' → IsOp2 ψ t T T' → IsOp2 ψ (t ∘ s) (T ∘ₗ S) (S' ∘ₗ T')) ∧ ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (e : κ' ≃ κ), ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => (w.1 ∘ e, w.2 ∘ e)) S S' :=
  fun _ _ _ ψ _ => ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hs ht => isOp2_comp hs ht, fun _ _ _ _ e => ⟨_, _, isOp2_reix ψ e⟩⟩

end GlobalTheory.TowU.RealComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenLatticeImageLeSpanAfterBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenLattice_image_le_span_after_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G))
    (f' : Fin n → (A'.t.G ⟶ B'.t.G)) (g' : Fin n → (B'.t.G ⟶ A'.t.G)),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) → (∀ i, Serre.IsLinearHom A'.t.act B'.t.act (f' i)) →
    (∀ i, Serre.IsLinearHom B'.t.act A'.t.act (g' i)) → (∀ i, (f' i).left ≫ mB.φ = mA.φ ≫ (f i).left) →
    ∏ i, (g' i ≫ f' i) = 𝟙 B'.t.G →
    ∀ (FA : GenFib A.pol) (FB : GenFib B.pol) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
    (∀ i, FA.IsDiffOf FB (f i) (M i)) → ∀ (τ : 𝓞 E →+* 𝓞 K), ∀ w ∈ FB.eigLat B.t.act τ,
    (fun k => j (w k)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin FB.P₀.g → K) k => j (c k)) ''
      {v | ∃ i, ∃ e ∈ FA.eigLat A.t.act τ, v = M i e}) := by
  first | exact @GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff | exact GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff | (intros; apply GlobalTheory.CM.LieSpanBaseChange.eigLat_image_le_span_diff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_residue_holomorphic_region : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k₀ : ℕ) (U₀ : Set ℂ) (H₀ : ℂ → GAd σ J → ℂ), U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) →
      (∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g) →
      (∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s)) →
      (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) →
      ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∀ s ∈ V, ∀ k ∈ levelAll σ J L a, ∀ g, H₀ s (g * k) = H₀ s g := by
  first | exact @GlobalTheory.EisRes.levelAll_inv_near_rho | exact GlobalTheory.EisRes.levelAll_inv_near_rho | (intros; apply GlobalTheory.EisRes.levelAll_inv_near_rho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeffStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → P.coeff 0 ≠ 0 ∧ ∀ k ≤ n, P.coeff 0 * IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) := by
  first | exact @GlobalTheory.ConjSelfRecip.ell_coeff_conj | exact GlobalTheory.ConjSelfRecip.ell_coeff_conj | (intros; apply GlobalTheory.ConjSelfRecip.ell_coeff_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSumPowOfCommuteStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_smul_pow_of_commute_of_separable : ∀ {K : Type} [Field K] {n : ℕ} (g t : Matrix (Fin n) (Fin n) K), g.charpoly.Separable →
    t * g = g * t → ∃ c : Fin n → K, t = ∑ i, c i • g ^ (i : ℕ) := by
  first | exact @GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute | exact GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute | (intros; apply GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute <;> assumption)
end

