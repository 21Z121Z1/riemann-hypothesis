import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0079
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0344
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.AlgCountDim

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

theorem eventually_evFin_integral (x : AF F) :
    ∀ᶠ v in Filter.cofinite, GlobalTheory.AdelicU.evFin F v x ∈ v.adicCompletionIntegers F := x.2.2

theorem eventually_vac_eq_one (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (x : Fin n × Fin d → AF F) :
    ∀ᶠ v in Filter.cofinite, M.vac v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) = 1 := by
  have hint : ∀ᶠ v in Filter.cofinite, ∀ i, GlobalTheory.AdelicU.evFin F v (x i) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => eventually_evFin_integral (x i)
  filter_upwards [hM.std, hint] with v hv hi
  rw [hv]
  simp [Set.indicator, hi]

open Classical in

theorem pure_update_eq (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ) (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : Fin n × Fin d → AF F)
    (hx : {v | v ≠ a ∧ φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 1}.Finite) :
    ∃ c : ℂ, ∀ ζ : (Fin n × Fin d → Fv F a) → ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ a ζ) x =
        f (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) * (ζ (fun i => GlobalTheory.AdelicU.evFin F a (x i)) * c) := by
  classical
  set s := hx.toFinset with hs
  have ha : a ∉ s := by simp [hs]
  refine ⟨∏ v ∈ s, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)), fun ζ => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset (s := insert a s)]
  · rw [Finset.prod_insert ha, Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    have : v ≠ a := fun h => ha (h ▸ hv)
    rw [Function.update_of_ne this]
  · intro v hv
    simp only [Function.mem_mulSupport] at hv
    by_cases h : v = a
    · simp [h]
    · rw [Function.update_of_ne h] at hv
      simp [hs, h, hv]

section Main

variable (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)

open Classical in

def gens : Set ((Fin n × Fin d → AF F) → ℂ) :=
  Set.range fun p : Σ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb) ×
      (∀ v : S, Module.Basis.ofVectorSpaceIndex ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v.1))) =>
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) p.2.1 : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (fun v => if h : v ∈ p.1 then
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (p.2.2 ⟨v, h⟩) :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v)

open Classical in

theorem pure_mem_span_gens (hM : M.IsGood ψ) (i : Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb)) :
    ∀ (S T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ v, v ∉ S → v ∉ T → φ v = M.vac v) →
      (∀ v ∈ T, ∃ j, φ v = ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ ∈
        Submodule.span ℂ (gens M ψ emb) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro T φ _ hoff hT
    choose j hj using hT
    have hfun : (fun v => if h : v ∈ T then
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (j v h) :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v) = φ := by
      funext v
      by_cases h : v ∈ T
      · rw [dif_pos h]
        exact (hj v h).symm
      · rw [dif_neg h]
        exact (hoff v (Finset.notMem_empty v) h).symm
    exact Submodule.subset_span ⟨⟨T, i, fun v => j v.1 v.2⟩, congrArg (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
      ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) hfun⟩
  | insert a S ha ih =>
    intro T φ hSB hoff hT
    set g := ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    have hfin : ∀ x : Fin n × Fin d → AF F,
        {v | v ≠ a ∧ φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 1}.Finite := by
      intro x
      have h2 := Filter.eventually_cofinite.1 (eventually_vac_eq_one M ψ hM x)
      refine ((insert a S ∪ T : Finset _).finite_toSet.union h2).subset ?_
      rintro v ⟨_, hv⟩
      by_cases h : v ∈ insert a S ∪ T
      · exact Or.inl h
      · right
        simp only [Finset.mem_union, not_or] at h
        rw [hoff v h.1 h.2] at hv
        exact hv
    have key : ∀ ζ ∈ Submodule.span ℂ (Set.range fun j =>
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) : (Fin n × Fin d → Fv F a) → ℂ)),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ) ∈ Submodule.span ℂ (gens M ψ emb) := by
      intro ζ hζ
      induction hζ using Submodule.span_induction with
      | mem ζ hζ =>
        obtain ⟨j, rfl⟩ := hζ
        apply ih (insert a T)
        · intro v
          by_cases h : v = a
          · subst h
            rw [Function.update_self]
            exact (Module.Basis.ofVectorSpace ℂ _ j).2
          · rw [Function.update_of_ne h]
            exact hSB v
        · intro v hvS hvT
          have hva : v ≠ a := fun h => hvT (h ▸ Finset.mem_insert_self _ _)
          rw [Function.update_of_ne hva]
          exact hoff v (by simp [hva, hvS]) (fun h => hvT (Finset.mem_insert_of_mem h))
        · intro v hv
          by_cases h : v = a
          · subst h
            exact ⟨j, by rw [Function.update_self]⟩
          · rw [Function.update_of_ne h]
            exact hT v ((Finset.mem_insert.1 hv).resolve_left h)
      | zero =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a 0) = 0 := funext fun x => by
          obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
          rw [hc]
          simp
        rw [this]
        exact zero_mem _
      | add ζ₁ ζ₂ _ _ h₁ h₂ =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a (ζ₁ + ζ₂)) =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ₁) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ₂) :=
          funext fun x => by
            obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
            simp only [Pi.add_apply, hc]
            ring
        rw [this]
        exact add_mem h₁ h₂
      | smul r ζ _ h =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a (r • ζ)) = r • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ) :=
          funext fun x => by
            obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
            simp only [Pi.smul_apply, smul_eq_mul, hc]
            ring
        rw [this]
        exact Submodule.smul_mem _ r h
    have hmem : φ a ∈ Submodule.span ℂ (Set.range fun j =>
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) : (Fin n × Fin d → Fv F a) → ℂ)) := by
      have h1 : (⟨φ a, hSB a⟩ : GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) ∈
          Submodule.span ℂ (Set.range (Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)))) := by
        rw [Module.Basis.span_eq]
        trivial
      have := Submodule.apply_mem_span_image_of_mem_span (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)).subtype h1
      rw [← Set.range_comp] at this
      exact this
    simpa using key _ hmem

end Main

theorem rank_algD_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    Module.rank ℂ (M.Pol ψ emb) ≤ Cardinal.aleph0 →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Module.rank ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ≤ Cardinal.aleph0) →
    Module.rank ℂ (GlobalTheory.SquareAgree.algD M ψ emb) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ n d X W M ψ emb hM hPol hSB
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : Countable (Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb)) := by
    rw [← Cardinal.mk_le_aleph0_iff, (Module.Basis.ofVectorSpace ℂ _).mk_eq_rank'']
    exact hPol
  haveI : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
      Countable (Module.Basis.ofVectorSpaceIndex ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v))) := fun v => by
    rw [← Cardinal.mk_le_aleph0_iff, (Module.Basis.ofVectorSpace ℂ _).mk_eq_rank'']
    exact hSB v
  have hle : GlobalTheory.SquareAgree.algD M ψ emb ≤ Submodule.span ℂ (gens M ψ emb) := by
    rw [GlobalTheory.SquareAgree.algD, Submodule.span_le]
    rintro _ ⟨f, φ, hf, hφ, hcof, rfl⟩
    have hfin := Filter.eventually_cofinite.1 hcof
    have key : ∀ g ∈ Submodule.span ℂ (Set.range (Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb))),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ ∈ Submodule.span ℂ (gens M ψ emb) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨i, rfl⟩ := hg
        exact pure_mem_span_gens M ψ emb hM i hfin.toFinset ∅ φ hφ (fun v hv _ => by simpa using hv) (by simp)
      | zero =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((0 : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ = 0 :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
        rw [this]
        exact zero_mem _
      | add g₁ g₂ _ _ h₁ h₂ =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((g₁ + g₂ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g₁ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ +
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g₂ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
        rw [this]
        exact add_mem h₁ h₂
      | smul r g _ h =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((r • g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ =
            r • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
        rw [this]
        exact Submodule.smul_mem _ r h
    exact key ⟨f, hf⟩ (by rw [Module.Basis.span_eq]; trivial)
  calc Module.rank ℂ (GlobalTheory.SquareAgree.algD M ψ emb) ≤ Module.rank ℂ (Submodule.span ℂ (gens M ψ emb)) :=
        Submodule.rank_mono hle
    _ ≤ Cardinal.mk (gens M ψ emb) := rank_span_le _
    _ ≤ Cardinal.aleph0 := by
        rw [Cardinal.mk_le_aleph0_iff]
        exact (Set.countable_range _).to_subtype

end GlobalTheory.AlgCountDim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.SBCount

open TopologicalSpace Cardinal

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {K : Set X | IsCompact K ∧ IsOpen K}.Countable := by
  classical
  have hB := isBasis_countableBasis X
  haveI : Countable (countableBasis X) := (countable_countableBasis X).to_subtype
  refine (Set.countable_range fun t : Finset (countableBasis X) => ⋃ b ∈ t, (b : Set X)).mono ?_
  rintro K ⟨hKc, hKo⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun b : {b : countableBasis X // (b : Set X) ⊆ K} => (b.1 : Set X))
    (fun b => hB.isOpen b.1.2) (fun x hx => by
      obtain ⟨b, hbB, hxb, hbK⟩ := hB.exists_subset_of_mem_open hx hKo
      exact Set.mem_iUnion.2 ⟨⟨⟨b, hbB⟩, hbK⟩, hxb⟩)
  refine ⟨t.image (fun c => c.1), ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨b, hb, hxb⟩ := hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hb
    exact c.2 hxb
  · intro x hx
    have := ht hx
    rw [Set.mem_iUnion₂] at this
    obtain ⟨c, hc, hxc⟩ := this
    rw [Set.mem_iUnion₂]
    exact ⟨c.1, Finset.mem_image.2 ⟨c, hc, rfl⟩, hxc⟩

theorem finite_range_of_sb {X : Type} [TopologicalSpace X] {f : X → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : (Set.range f).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun w => f ⁻¹' {w}) (fun w => hf _)
    fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩
  refine (t.finite_toSet.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : f x = 0
  · exact Or.inl hx
  · simpa using Or.inr (by simpa using ht (subset_tsupport f hx))

theorem sb_le_span (X : Type) [TopologicalSpace X] :
    GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun K : Set X => K.indicator (1 : X → ℂ)) '' {K : Set X | IsCompact K ∧ IsOpen K}) := by
  classical
  rintro f ⟨hf, hcs⟩
  have hfin := finite_range_of_sb hf hcs
  have hsum : f = ∑ c ∈ hfin.toFinset.erase 0, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : f x = 0
    · rw [hx]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
      have : x ∉ f ⁻¹' {c} := by simp [hx, Ne.symm hc0]
      simp [Set.indicator_of_notMem this]
    · rw [Finset.sum_eq_single (f x)]
      · simp
      · intro c _ hcx
        have : x ∉ f ⁻¹' {c} := by simp [Ne.symm hcx]
        simp [Set.indicator_of_notMem this]
      · intro h
        exact absurd (Finset.mem_erase.2 ⟨hx, by simp⟩) h
  rw [hsum]
  refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ⁻¹' {c}, ⟨?_, hf _⟩, rfl⟩)
  have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
  refine hcs.isCompact.of_isClosed_subset (hf.isClosed_fiber c) fun x hx => subset_tsupport f ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  simp [Function.mem_support, hx, hc0]

theorem rank_sb_le_aleph0 (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  refine (Submodule.rank_mono (sb_le_span X)).trans ((rank_span_le _).trans ?_)
  exact Cardinal.mk_le_aleph0_iff.2 ((countable_compactOpen X).image _).to_subtype

theorem rank_sb_localField_le : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (κ : Type) [Fintype κ],
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  intro F _ _ v κ _
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI := GlobalTheory.LocAtTopology.secondCountable_localField (Fv F v)
  exact rank_sb_le_aleph0 _

end GlobalTheory.SBCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompactStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_centralizer_noncompact : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, (μa w).IsHaarMeasure) → IsTestArchG M μa fa → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ γ : GF V, IsRegSS γ.1.1 → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w)) → ∀ b : GA D V → ℂ, Continuous b → LeftInv (cent (rat V γ)) b → (∀ g x, b (embArch D.sp.cm.sig V.gram w g * x) = b x) → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], HasQuotInt (cent (rat V γ)) dt μ (fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x) 0 := by
  first | exact @GlobalTheory.ArchVanish.hasQuotInt_weighted_eq_zero | exact GlobalTheory.ArchVanish.hasQuotInt_weighted_eq_zero | (intros; apply GlobalTheory.ArchVanish.hasQuotInt_weighted_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationTransportTopGroupEquivStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_transport_topGroupEquiv : ∀ (G G' : Type) [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (Φ : G ≃ₜ* G') (ν : Measure G) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), (σ.IsIrreducible → Representation.IsIrreducible (σ.comp Φ.symm.toMulEquiv.toMonoidHom)) ∧ (IsAdmissible σ → IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W)) ∧ ∀ (f : G → ℂ) (f' : G' → ℂ), (∀ g, f' (Φ g) = f g) → ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W) f' A ↔ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ f A := by
  first | exact @GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport | exact GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport | (intros; apply GlobalTheory.TransportIso.irreducible_admissible_integralOp_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightRegularOperatorRepresentedContinuousStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightRegularOperator_represented_continuous : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, ∀ F : DividedPowerChartLift V μ, (∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ) ∧ Continuous (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ LeftInv (GQ V) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ lift (GQ V) (RopG V μ f F) =ᵐ[μ] fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ := by
  first | exact @GlobalTheory.RopRep.rop_rep | exact GlobalTheory.RopRep.rop_rep | (intros; apply GlobalTheory.RopRep.rop_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RkSubSuccLe
section
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.ThetaGLSub

namespace GlobalTheory.ThetaGLRank

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

variable (k n m) in

def rkSub (ρ : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) where
  carrier := {Φ | Φ ∈ SB (Matrix (Fin n) (Fin m) k) ∧ ∀ x : Matrix (Fin n) (Fin m) k, x.rank < ρ → Φ x = 0}
  add_mem' := by
    rintro Φ Ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨Submodule.add_mem _ h1 h3, fun x hx => by simp [h2 x hx, h4 x hx]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c Φ ⟨h1, h2⟩
    exact ⟨Submodule.smul_mem _ c h1, fun x hx => by simp [h2 x hx]⟩

theorem rkSub_le_SB (ρ : ℕ) : rkSub k n m ρ ≤ SB (Matrix (Fin n) (Fin m) k) := fun _ h => h.1

theorem rkSub_zero : rkSub k n m 0 = SB (Matrix (Fin n) (Fin m) k) :=
  le_antisymm (rkSub_le_SB 0) fun _ h => ⟨h, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩

theorem rkSub_succ_n : rkSub k n m (n + 1) = ⊥ := by
  refine eq_bot_iff.2 fun Φ h => ?_
  refine funext fun x => h.2 x ?_
  have : x.rank ≤ n := by simpa using Matrix.rank_le_height x
  omega

theorem rkSub_succ_le (ρ : ℕ) : rkSub k n m (ρ + 1) ≤ rkSub k n m ρ :=
  fun _ h => ⟨h.1, fun x hx => h.2 x (Nat.lt_succ_of_lt hx)⟩

theorem om_mem_rkSub (ρ : ℕ) (g : GL (Fin m) k) {Φ : Matrix (Fin n) (Fin m) k → ℂ}
    (h : Φ ∈ rkSub k n m ρ) : om 1 g (1 : GL (Fin n) k) Φ ∈ rkSub k n m ρ := by
  refine ⟨Model.om_mem_SB 1 g 1 h.1, fun x hx => ?_⟩
  have hr : ((1 : GL (Fin n) k)⁻¹.val * x * g.val).rank = x.rank := by
    simp only [inv_one, Units.val_one, Matrix.one_mul]
    exact Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units g)
  simp only [om]
  rw [h.2 _ (hr ▸ hx), mul_zero]

theorem isSub_aug_sup (χ : GL (Fin n) k →* ℂˣ) (ρ : ℕ) : IsSub χ (aug m χ ⊔ rkSub k n m ρ) := by
  refine ⟨le_sup_left, sup_le (aug_le_SB χ) (rkSub_le_SB ρ), fun g Φ hΦ => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
  rw [om_add]
  exact Submodule.add_mem_sup ((isSub_aug χ).2.2 g y hy) (om_mem_rkSub ρ g hz)

theorem IsSub.inf {χ : GL (Fin n) k →* ℂˣ} {N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (h : IsSub χ N)
    (h' : IsSub χ N') : IsSub χ (N ⊓ N') :=
  ⟨le_inf h.1 h'.1, inf_le_left.trans h.2.1, fun g Φ hΦ => ⟨h.2.2 g Φ hΦ.1, h'.2.2 g Φ hΦ.2⟩⟩

end GlobalTheory.ThetaGLRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.SchurAdm

theorem schur_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id :=
  _root_.GlobalTheory.SchurAdmissibility.schur_admissible

end GlobalTheory.SchurAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeriesStatement
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ℓ w = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  first | exact @GlobalTheory.KFiniteDense.eq_zero_of_kFin | exact GlobalTheory.KFiniteDense.eq_zero_of_kFin | (intros; apply GlobalTheory.KFiniteDense.eq_zero_of_kFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → (∀ f, IsThetaFunO ψ V W f → (∀ x, IntegrableOn (fun y => f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧ IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 f) ∧ (∀ x, res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x) f) = heisO ψ V' W x (res V V' W C B μ 𝓨 f)) ∧ ∀ y, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C y) f) = res V V' W C B μ 𝓨 f) ∧ ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  first | exact @GlobalTheory.TowerRestrict.res_theta | exact GlobalTheory.TowerRestrict.res_theta | (intros; apply GlobalTheory.TowerRestrict.res_theta <;> assumption)
end

