import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0692
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceResidueMapEqReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory

theorem adicIntegers_red_eq_zero_iff {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (g : ℕ) (hg : g.Prime)
    (red : v.adicCompletionIntegers K →+* ZMod g) (y : v.adicCompletionIntegers K) :
    red y = 0 ↔ Valued.v (y : v.adicCompletion K) < 1 := by
  have : Fact g.Prime := ⟨hg⟩
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective red (ZMod.ringHom_surjective red))
  rw [← RingHom.mem_ker, hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact ⟨fun h => lt_of_le_of_ne y.2 h, ne_of_lt⟩

theorem exists_ringHom_adicIntegers {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {R : Type} [CommRing R] (f : R →+* v.adicCompletion K)
    (hf : ∀ a, Valued.v (f a) ≤ 1) :
    ∃ j : R →+* v.adicCompletionIntegers K, ∀ a, (j a : v.adicCompletion K) = f a :=
  ⟨f.codRestrict (v.adicCompletionIntegers K) hf, fun _ => rfl⟩

theorem zmod_iso_comp_eq_mk {R : Type} [CommRing R] (I : Ideal R) (g : ℕ) (φ : R →+* ZMod g)
    (hφ : ∀ a ∈ I, φ a = 0) (iso : ZMod g ≃+* R ⧸ I) (u : R) :
    iso (φ u) = Ideal.Quotient.mk I u := by

  have hid : (Ideal.Quotient.lift I φ hφ).comp (iso : ZMod g →+* R ⧸ I) = RingHom.id (ZMod g) :=
    Subsingleton.elim _ _
  have h : φ u = iso.symm (Ideal.Quotient.mk I u) := by
    simpa using congrArg (fun F : ZMod g →+* ZMod g => F (iso.symm (Ideal.Quotient.mk I u))) hid
  rw [h, RingEquiv.apply_symm_apply]

theorem adicIntegers_red_eq_iff {K : Type} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (g : ℕ) (hg : g.Prime)
    (red : v.adicCompletionIntegers K →+* ZMod g) (y x : v.adicCompletionIntegers K) :
    Valued.v ((y : v.adicCompletion K) - (x : v.adicCompletion K)) < 1 ↔ red x = red y := by
  have h := adicIntegers_red_eq_zero_iff v g hg red (y - x)
  rw [map_sub, sub_eq_zero] at h
  exact h.symm.trans eq_comm

theorem splitPlace_red_eq_reduction : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ∀ (red : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod g) (iso : ZMod g ≃+* kP s.w) (x : s.v.adicCompletionIntegers (maximalRealSubfield L)) (u : 𝓞 L), Valued.v (s.i (u : L) - (x : s.v.adicCompletion (maximalRealSubfield L))) < 1 ↔ iso (red x) = Ideal.Quotient.mk s.w.asIdeal u := by
  intro L _ _ _ s g hg red iso x u

  obtain ⟨j, hj⟩ := exists_ringHom_adicIntegers s.v
    ((s.i : L →+* s.v.adicCompletion (maximalRealSubfield L)).comp (algebraMap (𝓞 L) L))
    (fun a => s.split_le_one a)
  have hj' : ∀ a : 𝓞 L, (j a : s.v.adicCompletion (maximalRealSubfield L)) = s.i (a : L) :=
    fun a => hj a

  have hφ : ∀ a ∈ s.w.asIdeal, (red.comp j) a = 0 := by
    intro a ha
    have hlt : Valued.v (s.i (a : L)) < 1 := (s.split_mem_ideal a).1 ha
    exact (adicIntegers_red_eq_zero_iff s.v g hg red (j a)).2 (by rw [hj' a]; exact hlt)
  have key := zmod_iso_comp_eq_mk s.w.asIdeal g (red.comp j) hφ iso u
  have h4 := adicIntegers_red_eq_iff s.v g hg red (j u) x
  rw [hj' u] at h4
  rw [← key, iso.injective.eq_iff]
  exact h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqSmulMulVecMemHat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HatIntSmul

theorem mem_stdLat_coord {E : Type} [Field E] [NumberField E] {n : ℕ} {s : Fin n → E}
    (hs : s ∈ Formalism.L2.Pj.stdLat E n) (j : Fin n) : ∃ o : 𝓞 E, s j = (o : E) := by
  have := (Submodule.mem_pi.mp hs) j (Set.mem_univ _)
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp this
  exact ⟨o, ho.symm⟩

theorem single_mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (i : Fin n) (o : 𝓞 E) :
    Pi.single i (o : E) ∈ Formalism.L2.Pj.stdLat E n := by
  refine Submodule.mem_pi.mpr fun j _ => ?_
  rw [Submodule.mem_one]
  by_cases h : j = i
  · subst h; exact ⟨o, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem nsmul_tmul {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
    (a : ℕ) (β : Af F) (x : E) : a • (β ⊗ₜ[F] x) = β ⊗ₜ[F] (((a : 𝓞 E) : E) * x) := by
  have h := map_nsmul (TensorProduct.mk F (Af F) E β) a x
  simp only [TensorProduct.mk_apply] at h
  rw [← h, nsmul_eq_mul]
  simp

set_option maxHeartbeats 2000000 in

theorem sq_smul_mulVec_mem_hat : ∀ (D : D7) (n : ℕ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (a : ℕ), (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E n, (a : 𝓞 D.host.E) • x ∈ Λ) → (∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E n) → ∀ (M : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)), (∀ i j, M i j ∈ intAE D) → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)), (a ^ 2) • (M *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  intro D n Λ a h1 h2 M hM y hy
  have mulMem : ∀ {x y : Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
    intro x y hx hy
    refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
    · intro x _; rw [zero_mul]; exact zero_mem _
    · intro x _; rw [mul_zero]; exact zero_mem _
    · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
    · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
    · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
    · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

  have stepA : ∀ w : Fin n → Af D.host.F ⊗[D.host.F] D.host.E, (∀ i, w i ∈ intAE D) →
      a • w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
    intro w hw
    have hw' : a • w = ∑ i, a • Pi.single i (w i) := by
      rw [← Finset.smul_sum, Finset.univ_sum_single]
    rw [hw']
    refine sum_mem fun i _ => ?_
    have key : ∀ z ∈ intAE D, a • Pi.single i z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβ, o, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨β, fun v => hβ v, (a : 𝓞 D.host.E) • Pi.single i (o : D.host.E), h1 _ (single_mem_stdLat i o), ?_⟩
        funext k
        by_cases hk : k = i
        · subst hk
          rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, nsmul_tmul, Algebra.smul_def]
        · simp [Pi.single_apply, hk]
      | zero => simp
      | add x y _ _ hx hy => rw [Pi.single_add, smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [Pi.single_neg, smul_neg]; exact neg_mem hx
    exact key _ (hw i)
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    obtain ⟨o, ho⟩ := Classical.axiomOfChoice (mem_stdLat_coord (h2 x hx))
    have e : (a ^ 2) • (M *ᵥ fun i => α ⊗ₜ[D.host.F] x i) =
        a • (M *ᵥ fun j => α ⊗ₜ[D.host.F] ((o j : 𝓞 D.host.E) : D.host.E)) := by
      rw [pow_two, mul_smul, ← Matrix.mulVec_smul]
      congr 2
      funext j
      rw [Pi.smul_apply, nsmul_tmul, ← ho j]
      simp [Algebra.smul_def]
    rw [e]
    refine stepA _ fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    refine sum_mem fun j _ => mulMem (hM i j) (AddSubgroup.subset_closure ⟨α, fun v => hα v, o j, rfl⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg, smul_neg]; exact neg_mem hy

end GlobalTheory.HatIntSmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishingPreservedByRealLieDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenReal

set_option maxHeartbeats 2000000 in

theorem downInt_lie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (τ : D.what₂.Tau)
    (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ →
    ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank),
    (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) →
    ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ), (∀ g, downInt R i t y (R.ptP i t P) l g = 0) →
    ∀ g, downInt R i t y (R.ptP i t P') l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y τ Y hY P P' hder l hvan g
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hom := (hP i t).datum
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ptP i t P) := hG.core.thP.pt_theta i t P
  obtain ⟨ht, hd⟩ := GlobalTheory.Chain.LiftReg.tame_dOmT hθ hom hY
  have hf' := ht.theta hf

  have hid : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT R.θ (R.ωP i t) τ Y (R.ptP i t P) = R.ptP i t P' := by
    funext z
    have h1 := hd _ hf 1 z
    simp only [one_mul, map_one, Module.End.one_apply] at h1
    exact h1.unique (hder z)
  rw [← hid]
  set f := R.ptP i t P with hfdef
  set f' := GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT R.θ (R.ωP i t) τ Y f with hf'def

  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have hrat : ∀ γ ∈ GQ (Vc D i), ∀ (c : GA D (Vc D i)) (g' : GA D (Wc D i)),
      thetaKO (R.ωP i t) (γ * c) g' f' = thetaKO (R.ωP i t) c g' f' := by
    intro γ hγ c g'
    unfold thetaKO
    have e : ((γ * c, g') : GA D (Vc D i) × GA D (Wc D i)) = ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (c, g') := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf')
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩

  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact (Vc D i) hpos
  have hΨ : Continuous fun p : GA D (Vc D i) × ℝ =>
      thetaKO (R.ωP i t) p.1 (g * oneP R.θ (Wc D i) τ Y p.2) f' * l (R.extV i t y p.1) := by
    refine Continuous.mul ?_ (hcont.comp continuous_fst)
    exact (hom.om_cont f' hf' 0).comp (continuous_fst.prodMk
      (continuous_const.mul ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_snd)))
  obtain ⟨B, hB⟩ := (hC.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn hΨ.continuousOn
  have hbd : ∀ (h : GA D (Vc D i)) (x : ℝ), x ∈ Metric.ball (0 : ℝ) 1 →
      ‖thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f' * l (R.extV i t y h)‖ ≤ B := by
    intro h x hxb
    obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    subst e
    rw [hrat γ hγ c, hinv γ hγ c]
    exact hB (c, x) (Set.mk_mem_prod hc (Metric.ball_subset_closedBall hxb))

  have hfin : R.νV i t (R.fdV i t) < ⊤ := by
    haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D (Vc D i)) :=
      inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
    have h1 := GlobalTheory.integrableOn_fundamentalDomain_of_cocompact (GA D (Vc D i)) (GQ (Vc D i)) C hC
      (fun h => by
        obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
        exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩)
      (R.νV i t) (hm.νV i t).1.1 (R.fdV i t) (hm.νV i t).2 (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    rcases (integrableOn_const_iff (C := (1 : ℂ))).1 h1 with h2 | h2
    · simp at h2
    · exact h2

  have hmeas : ∀ (φ : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ x : ℝ,
      AEStronglyMeasurable (fun h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) φ * l (R.extV i t y h))
        ((R.νV i t).restrict (R.fdV i t)) := fun φ hφ x =>
    (((hom.om_cont φ hφ 0).comp (continuous_id.prodMk continuous_const)).mul hcont).measurable.aestronglyMeasurable
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (R.νV i t).restrict (R.fdV i t))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (F := fun x h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f * l (R.extV i t y h))
    (F' := fun x h => thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f' * l (R.extV i t y h))
    (bound := fun _ => B) (Metric.ball_mem_nhds 0 one_pos) (.of_forall fun x => hmeas f hf x)
    (GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand D G Pl0 T A Ks R F hG hP i t y f l _ hf)
    (hmeas f' hf' 0) (.of_forall fun h x hxb => hbd h x hxb) (integrableOn_const hfin.ne)
    (.of_forall fun h x _ => ?_)).2
  · have e : (fun x : ℝ => ∫ h in R.fdV i t, thetaKO (R.ωP i t) h (g * oneP R.θ (Wc D i) τ Y x) f *
        l (R.extV i t y h) ∂(R.νV i t)) = fun _ => 0 := funext fun x => hvan _
    rw [e] at key
    have h0 := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at h0
    exact h0
  · refine (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hY (φ := fun g' => thetaKO (R.ωP i t) h g' f)
      (φ' := fun g' => thetaKO (R.ωP i t) h g' f') (fun g' => ?_) g x).mul_const _
    simpa only [thetaKO, Prod.mk_mul_mk, mul_one] using hd f hf (h, g') 0

end GlobalTheory.DownLift.GenReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterEqGaloisOfLadicUnitaryHecke
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar

noncomputable section

namespace GlobalTheory.HeckeRead

theorem read_of_isGal_side : ∀ {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}, IsGlobalArtin art → ∀ {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → ∀ (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i)), (∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x → embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y)) → ∀ (χ : HChar D.host.E), χ.IsUnitary → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ)) → ∀ (H : Formalism.L2.NC.HC D.host.E), (∀ x, H.χ x = χ.1 x) → ∀ {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (T.O0 i)ˣ}, IsGal art κ (sideIso ι b) χ n r → Formalism.L2.NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i))) embO (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) H 0 := by
  intro D N T art ha i κ ι hι b embO hO χ hχu S hS H hH n r hr
  classical
  have hfin := Formalism.L2.NC.finite_placesOver (E := D.host.E) (T.l i)
  refine ⟨hfin.toFinset ∪ S, fun P hP => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hu, y, hy⟩ := hS P hP.2
  have hAt := (GlobalTheory.HeckeUnifVal.at_val_and_unr_iff χ H (MonoidHom.ext hH) P).1 hu
  have hyC : D.what₂.embLL ((y : D.LL0) : D.what₂.LL) = ((χ.val P : ℂˣ) : ℂ) := hy
  have hyi : D.what₂.embLL ((y⁻¹ : D.LL0) : D.what₂.LL) = ((χ.val P : ℂˣ) : ℂ)⁻¹ := by
    rw [IntermediateField.coe_inv, map_inv₀, hyC]
  refine ⟨_, hAt, y⁻¹, ?_, fun σ hσ => ?_⟩
  · rw [zpow_zero, mul_one]
    exact hyi
  · have hl : ((T.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hP.1
    have hf := hr.frob ha (Or.inl hl) hu (N.plOm.2 P) hσ
    have inj : Function.Injective (fun z : FractionRing (T.O0 i) => ι (κ z)) := ι.injective.comp κ.injective
    have hkey : algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i) =
        (if b then T.emb0 i else T.emb0b i) y⁻¹ := by
      cases b
      · have hf' : ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i))) =
            ((χ.val P : ℂˣ) : ℂ) := by
          have e1 : starRingEnd ℂ (ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i)))) =
              ((χ.val P : ℂˣ) : ℂ)⁻¹ := hf
          have hn : ‖((χ.val P : ℂˣ) : ℂ)‖ = 1 := hχu _
          rw [Complex.inv_eq_conj hn] at e1
          have := congrArg (starRingEnd ℂ) e1
          simpa only [Complex.conj_conj] using this
        have hst : ((y : D.LL0) : D.what₂.LL) = star ((y⁻¹ : D.LL0) : D.what₂.LL) := by
          apply D.what₂.embLL.injective
          rw [D.starLL_cx, hyi, hyC]
          have hn : ‖((χ.val P : ℂˣ) : ℂ)‖ = 1 := hχu _
          rw [Complex.inv_eq_conj hn, Complex.conj_conj]
        show _ = T.emb0b i y⁻¹
        rw [T.restX_coefficientEmbedding_conj i y⁻¹ y hst]
        apply inj
        show ι (κ _) = ι (κ _)
        rw [hf', hι, hyC]
      · have hf' : ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i))) =
            ((χ.val P : ℂˣ) : ℂ)⁻¹ := hf
        show _ = T.emb0 i y⁻¹
        apply inj
        show ι (κ _) = ι (κ _)
        rw [hf', hι, hyi]
    rw [hO y⁻¹ _ hkey]
    rfl

end GlobalTheory.HeckeRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterIsLadicOfFiniteOrderHecke
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar

noncomputable section

namespace GlobalTheory.DeltaGal

theorem continuous_comp_of_isOpen_ker {Gp M Y : Type*} [Group Gp] [TopologicalSpace Gp] [IsTopologicalGroup Gp]
    [Group M] [TopologicalSpace Y] (f : Gp →* M) (h : IsOpen (f.ker : Set Gp)) (u : M → Y) :
    Continuous (fun g => u (f g)) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : (fun x => g⁻¹ * x) ⁻¹' (f.ker : Set Gp) ∈ nhds g :=
    ((continuous_const.mul continuous_id).isOpen_preimage _ h).mem_nhds (by simp)
  refine (continuousAt_const (y := u (f g))).congr ?_
  filter_upwards [hm] with x hx
  simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv] at hx
  rw [inv_mul_eq_one.1 hx]

theorem delta_isGal : GlobalTheory.Published.ChebotarevDegreeOne → ∀ {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}, IsGlobalArtin art → ∀ (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := by
  intro _ D cf b0 b1 Sx T Sp art hart i κ ι hι
  set χ := cf.delAt (T.l i) with hχ
  have hfin : ∃ n, 0 < n ∧ χ.OrderDvd n := by
    rw [hχ]; unfold CharFrame.delAt; split_ifs
    exacts [cf.isDel'.fin, cf.isDel.fin]
  obtain ⟨n, hn, hord⟩ := hfin
  have hpos : IsAlgPos χ 0 := fun k _ => by
    rw [HChar.inf_eq_one_of_order hn hord k]; simp
  refine ⟨hpos, continuous_comp_of_isOpen_ker (T.delta i) (T.delta_open i) (fun u => (u : T.O0 i)), ?_⟩
  obtain ⟨r', hr'c, hr'⟩ := hart.exists_isLAdicOf ι hpos
  suffices h : inQ κ (T.delta i) = r' by rw [h]; exact hr'
  have hc : Continuous (inQ κ (T.delta i)) :=
    continuous_comp_of_isOpen_ker (T.delta i) (T.delta_open i) (Units.map (toQ κ : T.O0 i →* Qbar (T.l i)))
  have h0 : Ideal.span {((T.l i : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (T.lPrime i).out.ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 D.host.E) in Filter.cofinite, ((T.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hS := Filter.eventually_cofinite.1 (hl.and (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1)
  refine mul_inv_eq_one.1 (GlobalTheory.FrobDense.eq_one_of_frob _ _ art hart _ (inQ κ (T.delta i) * r'⁻¹)
    (hc.mul hr'c.inv) hS.toFinset fun v hv A hA σ hσ => ?_)
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  apply Units.ext
  rw [hr'.frob_unr hart (Or.inr rfl) hv.2 hA hσ]
  obtain ⟨x, hx1, hx2⟩ := Sp.deltaRead i v hv.1 hv.2 A σ hA hσ
  show κ (algebraMap _ _ ((T.delta i σ : T.O0 i))) = _
  rw [hx2]
  apply ι.injective
  rw [hι, hx1, map_inv₀, RingEquiv.apply_symm_apply, Units.val_inv_eq_inv_val]

end GlobalTheory.DeltaGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistSecondStepKeptWithLocalisations
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.FitTw

noncomputable section

namespace GlobalTheory.TwInputs.SideBLoc

set_option maxHeartbeats 8000000 in

theorem exists_sideB_withLoc : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ (L : LocAll (lay0 D)) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E), (∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) → ∃ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR ∧ ∃ Bs' : SideB (withLoc L) (cfL L cf) Rw' low Pq ({ S with } : RatDat (withLoc L).ntw) hL eig θ, HEq Bs'.rowS Bs.rowS := by
  intro D cf Rw low Pq S hL eig θ Bs L ψ hψ
  refine ⟨⟨Rw.locR, Rw.satR, Rw.lab_eq⟩, HEq.rfl, ?_⟩
  exact ⟨{ Bs with
    twF := twFL L Bs.twF
    tw := twTiedL L Bs.tw
    chiD := chiDL L Bs.chiD ψ
    chi := chiL L Bs.chi ψ hψ
    deltaRead := deltaReadL L Bs.deltaRead
    exp := expL L Bs.exp }, HEq.rfl⟩

end GlobalTheory.TwInputs.SideBLoc

end
end

