import Mathlib
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
import GroundTheory.GlobalFields.SplittingFromInequality.Galois
import GroundTheory.GlobalFields.KummerTheory.Splitting
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0823
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0396
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingIntegralIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0720
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0621
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0716
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0620
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0816
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SplitAway

open GroundTheory.Global Filter

theorem splitsCompletely_of_tower {K E M : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
    {u : HeightOneSpectrum (𝓞 K)} (h : SplitsCompletely M u) : SplitsCompletely E u := by
  intro w hw
  obtain ⟨W⟩ := GroundTheory.Global.nonempty_placesOver M w
  have h1 : W.1.asIdeal.LiesOver w.asIdeal := W.2
  have h2 : W.1.asIdeal.LiesOver u.asIdeal := Ideal.LiesOver.trans W.1.asIdeal w.asIdeal u.asIdeal
  obtain ⟨he, hf⟩ := h W.1 h2
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal W.1.asIdeal] at he
  rw [Ideal.inertiaDeg_tower (R := 𝓞 K) w.asIdeal W.1.asIdeal] at hf
  exact ⟨(mul_eq_one.1 he).1, (mul_eq_one.1 hf).1⟩

theorem infinite_setOf_splitsCompletely (E : Type) [Field E] [NumberField E] :
    {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely E u}.Infinite := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure E) := Algebra.IsAlgebraic.trans ℚ E (AlgebraicClosure E)
  haveI : IsAlgClosure ℚ (AlgebraicClosure E) := ⟨inferInstance, inferInstance⟩
  let M := IntermediateField.normalClosure ℚ E (AlgebraicClosure E)
  haveI : IsGalois ℚ (AlgebraicClosure E) := IsAlgClosure.isGalois ℚ _
  haveI : IsGalois ℚ M := IsGalois.normalClosure ℚ E (AlgebraicClosure E)
  haveI : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely ℚ M
  have hsub : {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely M u} ⊆
      {u : HeightOneSpectrum (𝓞 ℚ) | SplitsCompletely E u} := fun u hu => splitsCompletely_of_tower (M := M) hu
  intro hfin
  have h0 := GroundTheory.Global.hasDirichletDensity_zero_of_finite (hfin.subset hsub)
  have e := tendsto_nhds_unique hd h0
  have hpos : (0 : ℝ) < 1 / (Module.finrank ℚ M : ℝ) := by
    have := Module.finrank_pos (R := ℚ) (M := M)
    positivity
  exact hpos.ne' e

theorem primesOver_rat_eq (E : Type) [Field E] [NumberField E] (u : HeightOneSpectrum (𝓞 ℚ)) :
    u.asIdeal.primesOver (𝓞 E) = (u.asIdeal.under ℤ).primesOver (𝓞 E) := by
  have hs : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := fun x =>
    ⟨Rat.ringOfIntegersEquiv x, by
      rw [eq_intCast, ← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  ext Q
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    refine ⟨?_⟩
    rw [h.over, Ideal.under_under]
  · intro h
    refine ⟨Ideal.comap_injective_of_surjective _ hs ?_⟩
    change Ideal.under ℤ u.asIdeal = Ideal.under ℤ (Q.under (𝓞 ℚ))
    rw [Ideal.under_under, ← h.over]

end GlobalTheory.SplitAway

open GlobalTheory.SplitAway GroundTheory.Global in
theorem GlobalTheory.SplitAway.exists_splitsFully_notMem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Finset (HeightOneSpectrum (𝓞 F))),
    ∃ v ∉ P, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ P
  classical
  obtain ⟨u, huS, huT⟩ := ((infinite_setOf_splitsCompletely E).diff
    (P.finite_toSet.image fun v : HeightOneSpectrum (𝓞 F) => v.under (𝓞 ℚ))).nonempty
  have hu : SplitsCompletely E u := huS
  obtain ⟨⟨v, hv⟩⟩ := GroundTheory.Global.nonempty_placesOver F u
  refine ⟨v, fun hP => huT ⟨v, hP, HeightOneSpectrum.ext hv.over.symm⟩, ?_, ?_⟩
  · show ((v.asIdeal.under ℤ).primesOver (𝓞 E)).ncard = Module.finrank ℚ E
    have e1 : v.asIdeal.under ℤ = u.asIdeal.under ℤ := by
      rw [hv.over, Ideal.under_under]
    rw [e1, ← primesOver_rat_eq]
    exact (splitsCompletely_iff_ncard_primesOver E u).1 hu
  · have hF : SplitsCompletely E v := hu.of_liesOver v
    haveI := (splitsCompletely_iff_isFiniteSplit (L := E) v).1 hF
    obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun (v.adicCompletion F)
      (v.adicCompletion F ⊗[F] E)
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exfalso
        haveI : Subsingleton (v.adicCompletion F ⊗[F] E) := e.toEquiv.subsingleton
        have h1 : Module.finrank (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) = Module.finrank F E :=
          Module.finrank_baseChange
        rw [Module.finrank_zero_of_subsingleton] at h1
        exact (Module.finrank_pos (R := F) (M := E)).ne h1
      · exact h
    exact ⟨(((Pi.evalAlgHom (v.adicCompletion F) (fun _ : Fin n => v.adicCompletion F) ⟨0, hn⟩).comp
      e.toAlgHom).restrictScalars F).comp Algebra.TensorProduct.includeRight⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingIntegralIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_doubling_integral_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
      (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
      (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
      (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
      (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, Xc.Good v → ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁ ∧ k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) ∧
        GlobalTheory.FunObj.zdeg z ≠ 0 ∧ ∀ i, ∃ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) ∧
          Φ₀D ∈ Γ.M'.So Bs.ψ t := by
  first | exact @GlobalTheory.RegSo.exists_comb_mem_So | exact GlobalTheory.RegSo.exists_comb_mem_So | (intros; apply GlobalTheory.RegSo.exists_comb_mem_So <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilFactorization
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DarbImage

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_add {κ : Type} [Fintype κ] (f g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul {κ : Type} [Fintype κ] (c : ℂ) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_zero {κ : Type} [Fintype κ] (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) φ = 0 := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]

theorem map_eq {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (Th : ((Fin n × Fin d → AF F) → ℂ) → Q)
    (T : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] Q) (Alg : Submodule ℂ Q)
    (hsub : GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d))
    (hT : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ = Th Φ)
    (hvac : ∀ (f₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      M.IsGauss ψ τ f₀ → (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∈ Alg)
    (hder : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ)
      (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      f ∈ M.Pol ψ τ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) f f₁ →
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ Alg → Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) ∈ Alg)
    (hrev : Alg ≤ (GlobalTheory.TripleAssembly.darbAlg M ψ τ).map T) :
    (GlobalTheory.TripleAssembly.darbAlg M ψ τ).map T = Alg := by
  refine le_antisymm ?_ hrev
  have hmem : ∀ f ∈ M.Pol ψ τ, ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = Th (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := fun f hf φ h1 h2 =>
    hT _ (hsub (Submodule.subset_span ⟨f, φ, hf, h1, h2, rfl⟩))
  have hG : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hC : ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → ∀ f ∈ M.Pol ψ τ,
      ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ :=
    fun u hu f hf f₁ hA => Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ hA
  let N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) :=
    { carrier := {f | f ∈ M.Pol ψ τ ∧ ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ Alg}
      add_mem' := fun {f g} hf hg => ⟨(M.Pol ψ τ).add_mem hf.1 hg.1, fun φ h1 h2 => by
        rw [pure_add, map_add]; exact Alg.add_mem (hf.2 φ h1 h2) (hg.2 φ h1 h2)⟩
      zero_mem' := ⟨(M.Pol ψ τ).zero_mem, fun φ _ _ => by rw [pure_zero, map_zero]; exact Alg.zero_mem⟩
      smul_mem' := fun c f hf => ⟨(M.Pol ψ τ).smul_mem c hf.1, fun φ h1 h2 => by
        rw [pure_smul, map_smul]; exact Alg.smul_mem c (hf.2 φ h1 h2)⟩ }
  have hPN : M.Pol ψ τ ≤ N := sInf_le ⟨fun f₀ h => ⟨hG f₀ h, fun φ h1 h2 => by
      rw [hmem f₀ (hG f₀ h) φ h1 h2]; exact hvac f₀ φ h h1 h2⟩,
    fun u hu f hf f₁ hA => ⟨hC u hu f hf.1 f₁ hA, fun φ h1 h2 => by
      rw [hmem f₁ (hC u hu f hf.1 f₁ hA) φ h1 h2]
      exact hder f φ u f₁ hf.1 hu hA h1 h2 (by rw [← hmem f hf.1 φ h1 h2]; exact hf.2 φ h1 h2)⟩⟩
  rw [Submodule.map_le_iff_le_comap]
  unfold GlobalTheory.TripleAssembly.darbAlg
  rw [Submodule.span_le]
  rintro Φ ⟨f, φ, hf, h1, h2, rfl⟩
  exact (hPN hf).2 φ h1 h2

end Generic

end GlobalTheory.DarbImage

namespace GlobalTheory.DarbImage

theorem thetaImage : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ T : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb).map T = algF ψ θ true A B) ∧
        ∀ T : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) →ₗ[ℂ] (WO W₁ X → ℂ),
          (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)),
            T Φ = GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Φ) →
          (GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb).map T = algF ψ θ false A₁ B := by
  intro hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have hG : Γ.M.IsGood Bs.ψ := hM.triple.geo.hM
  have hG' : Γ.M'.IsGood Bs.ψ := hM.triple.geo.hM'
  have hs := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb hG
  have hs' := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb hG'
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · refine map_eq Γ.M Bs.ψ Bs.emb _ T _ hs hT
      (GlobalTheory.T.seesaw_weil_doubling_factor hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM)
      (fun f φ u f₁ hf hu hA h1 h2 hin => ?_) ?_
    · obtain ⟨L, hLc, hLf, hL⟩ := GlobalTheory.T.seesaw_weil_zeta_unramified hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM f φ u f₁ hf hu hA h1 h2
      rw [hL]
      exact GlobalTheory.T.fockAlgebraicThetaVectors_stable_lineDerivative D ψ θ hψ hθ true W X A B _ hin L hLc hLf
    · rw [algF, Submodule.span_le]
      rintro q ⟨g, P, hg, rfl⟩
      obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.seesaw_weil_zeta_global hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM g P hg
      exact ⟨Φ, hΦ, by rw [hT Φ (hs hΦ), hΦe]⟩
  · refine map_eq Γ.M' Bs.ψ Bs.emb _ T _ hs' hT
      (GlobalTheory.T.seesaw_weil_zeta_nonvanishing hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB R Rf hM)
      (fun f φ u f₁ hf hu hA h1 h2 hin => ?_) ?_
    · obtain ⟨L, hLc, hLf, hL⟩ := GlobalTheory.T.seesaw_weil_zeta_continuation hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM f φ u f₁ hf hu hA h1 h2
      rw [hL]
      exact GlobalTheory.T.fockAlgebraicThetaVectors_stable_lineDerivative D ψ θ hψ hθ false W₁ X A₁ B _ hin L hLc hLf
    · rw [algF, Submodule.span_le]
      rintro q ⟨g, P, hg, rfl⟩
      obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.exists_darbAlg_thO_eq_fockF' hHD hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hTr ωA ωB hWA hWB e Bs Γ Xc om om' h hTA hTB
        R Rf hM g P hg
      exact ⟨Φ, hΦ, by rw [hT Φ (hs' hΦ), hΦe]⟩

end GlobalTheory.DarbImage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguez
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareAgree

theorem I_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (s : ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J) :
    M.I om (s • Φ) h = s * M.I om Φ h := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_smul, GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul,
    tsum_mul_left, integral_const_mul]

theorem thetaIntegralsAgree : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SquareSt.ThetaIntegralsAgree := by
  intro hMi hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨-, ⟨c, hc, -⟩, hc0⟩, hCo⟩ := hK' R Rf hR
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.doubling_integral_factorisation hP.howeDualityUnitary hP.howeDualityReal hMi hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTD R Rf hR
    Pi rf rl p p' hM
  refine ⟨c * s, mul_ne_zero (hc0 c hc) hs0, fun Φ' hΦ' => ?_⟩
  obtain ⟨Φ₀, hΦ₀, hrel, Φ₀D, hD₀, hSo⟩ :=
    GlobalTheory.SquareAgree.CoinvPass.coinv_passage D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hTD R Rf hR hCo Φ' hΦ'
  obtain ⟨hbd, hconv, -⟩ := hDec.2 Φ₀D hSo
  refine ⟨Φ₀, hΦ₀, hrel, GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hO hν₁ hTD Φ₀ Φ₀D hD₀
    hconv ?_, fun Φ hΦ hp => ?_⟩
  · obtain ⟨C, k, hC⟩ := hbd 0
    exact ⟨C, k, fun g h => by simpa using hC g h⟩
  · obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
    have hm := hs Φ hΦ Φ₀ hΦ₀ ΦD Φ₀D hD hD₀ hSo hp
    funext h
    rw [GlobalTheory.SquareAgree.thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h,
      _root_.Pi.smul_apply,
      GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (kapX X e hO.JX) Φ₀D Φ₀ hO.measW₁ hO.domW₁ (hO.theta_eq_B hD₀) h,
      hc ΦD (s • Φ₀D) hm (kapX X e hO.JX h), I_smul, smul_eq_mul, mul_assoc]

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepCommuteAtGoodPlacesAlgebraicVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.GoodComm

theorem exists_open_fix_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W₁ X : HSp D}
    {A₁ : Fr W₁} {B : Fr X} {χS χT : (AE D)ˣ →* Circle} {ωB : WRep W₁ X} (hW : IsWeilDatumO ψ W₁ X χS χT ωB)
    {Ψ : WO W₁ X → ℂ} (hΨ : Ψ ∈ algF ψ θ false A₁ B) :
    ∃ U : Subgroup (GA D W₁), IsOpen (U : Set (GA D W₁)) ∧ ∀ k ∈ U, k ∈ GfC W₁ → ωB (k, 1) Ψ = Ψ := by
  induction hΨ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, P, hf, rfl⟩ := hΦ
    obtain ⟨U, U', hU, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std W₁ X ωB
      (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f hf.1
    refine ⟨U, hU, fun k hk hkf => ?_⟩
    have e := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ W₁ X χS χT ωB hW θ hθ k hkf 1 (one_mem _)
      (frSgn false A₁).cart B.cart A₁.onb B.onb f P hf.1
    show ωB (k, 1) (fockF ψ θ false A₁ B f P) = fockF ψ θ false A₁ B f P
    unfold fockF
    exact e.trans (by rw [hfix k hk hkf 1 (one_mem _) (one_mem _)]; rfl)
  | zero => exact ⟨⊤, by simp, fun k _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨U', hU', h'⟩ := hy
    refine ⟨U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU', fun k hk hkf => ?_⟩
    rw [map_add, h k (Subgroup.mem_inf.1 hk).1 hkf, h' k (Subgroup.mem_inf.1 hk).2 hkf]
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf => by rw [map_smul, h k hk hkf]⟩

theorem comm_at_good_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W₁ X : HSp D) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ωB : WRep W₁ X), IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (n : ℕ) (Ψ : Fin n → WO W₁ X → ℂ) (u : Fin n → GA D W₁), (∀ i, Ψ i ∈ algF ψ θ false A₁ B) → (∀ i, u i ∈ GfC W₁) →
    ∃ P : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ P, ∀ z : GA D W₁ →₀ ℂ,
      (∀ k ∈ z.support, k ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v)) → ∀ i, ∃ u' ∈ GfC W₁,
        (z.sum fun k c => c • ωB (k, 1)) (ωB (u i, 1) (Ψ i)) = ωB (u', 1) ((z.sum fun k c => c • ωB (k, 1)) (Ψ i)) := by
  classical
  intro D ψ θ hθ W₁ X A₁ B α β ωB hB n Ψ u hΨ hu
  have hW : IsWeilDatumO ψ W₁ X α (α / β) ωB := hB
  choose U hU hfix using fun i => exists_open_fix_algF (A₁ := A₁) (B := B) hθ hW (hΨ i)
  have hfin : ∀ i, {v : HeightOneSpectrum (𝓞 D.host.F) | ¬ (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ U i ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ GfC W₁)}.Finite := fun i =>
    ((GlobalTheory.PlaceGen.gen_by_local D W₁ (U i) (hU i)).1 (u i)).preimage Sum.inl_injective.injOn
  refine ⟨Finset.univ.biUnion fun i => (hfin i).toFinset, fun v hv z hz i => ?_⟩
  have hvi : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ U i ∧ GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.gAt W₁ (Sum.inl v) (u i) ∈ GfC W₁ := by
    by_contra hc
    exact hv (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hfin i).mem_toFinset.2 hc⟩)
  set uv := GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig W₁.gram v (u i)) with huv
  have hfixv : ωB (uv, 1) (Ψ i) = Ψ i := hfix i uv hvi.1 hvi.2
  refine ⟨u i * uv⁻¹, mul_mem (hu i) (inv_mem hvi.2), ?_⟩
  have hp : GlobalTheory.AdelicU.proj D.sp.cm.sig W₁.gram v (u i * uv⁻¹) = 1 := by
    rw [map_mul, map_inv, huv, GlobalTheory.AdelicU.proj_emb_self, mul_inv_cancel]
  have m : ∀ (a b : GA D W₁) (f : WO W₁ X → ℂ), ωB (a * b, 1) f = ωB (a, 1) (ωB (b, 1) f) := fun a b f => by
    rw [show ((a * b, (1 : GA D X)) : GA D W₁ × GA D X) = (a, 1) * (b, 1) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ k ∈ z.support, ωB (k, 1) (ωB (u i, 1) (Ψ i)) = ωB (u i * uv⁻¹, 1) (ωB (k, 1) (Ψ i)) := by
    intro k hk
    obtain ⟨x, rfl⟩ := hz k hk
    have hc := GlobalTheory.AdelicU.commute_emb D.sp.cm.sig W₁.gram x hp
    have e1 : GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x * u i =
        (u i * uv⁻¹) * (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x * uv) := by
      rw [← mul_assoc, ← hc.eq]; group
    rw [← m, e1, m (u i * uv⁻¹), m (GlobalTheory.AdelicU.emb D.sp.cm.sig W₁.gram v x) uv, hfixv]
  simp only [Finsupp.sum]
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, key k hk]

end GlobalTheory.GoodComm
end

