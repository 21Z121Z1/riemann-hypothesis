import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0022
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0830
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0818
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.RationalHermitianCountable.CountableRatHerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0781
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0790
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0784
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0778
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0777
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0834
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingByUnit
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.Haar

theorem nnnorm_eq_distribHaarChar (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : (Fv F v)ˣ) :
    ‖(n : Fv F v)‖₊ = distribHaarChar (Fv F v) n := by
  have hn : (n : Fv F v) ≠ 0 := n.ne_zero
  have hva : Valued.v (n : Fv F v) ≠ 0 := (Valuation.ne_zero_iff _).2 hn
  have h := PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v (n : Fv F v) hn
  rw [PI.NglqJacSplitW.modF, dif_neg hn] at h
  have hu : Units.mk0 (n : Fv F v) hn = n := by ext; rfl
  rw [hu] at h
  have habs : PI.LocJacTyp.absV v (n : Fv F v) = ‖(n : Fv F v)‖ := by
    unfold PI.LocJacTyp.absV
    rw [dif_neg hva, NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hva]
    push_cast
    rfl
  rw [habs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal] at h
  exact (ENNReal.coe_injective h).symm

theorem map_mul_left (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hl : lam.IsAddHaarMeasure) (n : (Fv F v)ˣ) :
    lam.map (fun t => (n : Fv F v) * t) = (‖(n : Fv F v)‖₊)⁻¹ • lam := by
  have : SecondCountableTopology (Fv F v) := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  have : lam.Regular := inferInstance
  have hc : Continuous fun t : Fv F v => (n : Fv F v) * t := continuous_const.mul continuous_id
  ext S hS
  rw [Measure.map_apply hc.measurable hS, nnnorm_eq_distribHaarChar, ← map_inv]
  have hset : (fun t : Fv F v => (n : Fv F v) * t) ⁻¹' S = n⁻¹ • S := by
    ext y
    rw [Set.mem_inv_smul_set_iff]
    rfl
  rw [hset, ← distribHaarChar_mul lam n⁻¹ S]
  rfl

end GlobalTheory.CompanionTheory.Haar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingTensorUnits
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale

open GlobalTheory.CompanionTheory.SW.WBox (cK eW)

theorem map_eq_of_conj {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m s : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0) (hs : ∀ x, s (s x) = x)
    (h : ν.map (fun x => s (m (s (m x)))) = (c * c) • ν) : ν.map m = c • ν :=
  _root_.UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj m s ν c hs h

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem cK_tmul_mul' (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

end Coord

theorem pi_map_mul {R ι : Type} [Fintype ι] [CommRing R] [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam]
    (f : R → R) (hf : Measurable f) (c : ℝ≥0) (h : lam.map f = c • lam) :
    (Measure.pi fun _ : ι => lam).map (fun t i => f (t i)) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam := by
  haveI : SigmaFinite (lam.map f) := by rw [h]; infer_instance
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  refine Measure.pi_eq fun s hs => ?_
  simp only [h, Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul r e => simp [sigR, hσ]

theorem conj_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2]
  simp

def mulT {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (u : Sˣ) :
    (Fin 1 → Fin 1 → S) ≃ₜ+ (Fin 1 → Fin 1 → S) where
  toFun X a i := (u : S) * X a i
  invFun X a i := ((u⁻¹ : Sˣ) : S) * X a i
  left_inv X := by
    funext a i
    exact Units.inv_mul_cancel_left u _
  right_inv X := by
    funext a i
    exact Units.mul_inv_cancel_left u _
  map_add' X Y := by
    funext a i
    exact mul_add _ _ _
  continuous_toFun := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul (continuous_apply_apply a i)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    continuous_const.mul (continuous_apply_apply a i)

def sigT {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (f : S →+* S) (hf : Continuous f)
    (hff : ∀ x, f (f x) = x) : (Fin 1 → Fin 1 → S) ≃ₜ+ (Fin 1 → Fin 1 → S) where
  toFun X a i := f (X a i)
  invFun X a i := f (X a i)
  left_inv X := by
    funext a i
    exact hff _
  right_inv X := by
    funext a i
    exact hff _
  map_add' X Y := by
    funext a i
    exact map_add f _ _
  continuous_toFun := continuous_pi fun a => continuous_pi fun i =>
    hf.comp (continuous_apply_apply a i)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    hf.comp (continuous_apply_apply a i)

theorem map_coordW_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ (y : (R ⊗[F] E)ˣ) (n : Rˣ) (c : ℝ≥0), (n : R) ⊗ₜ[F] (1 : E) = sigR R σ y * y → lam.map (fun t => (n : R) * t) = c • lam → (coordW R b lam 1 1).map (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => (y : R ⊗[F] E) * X a i) = c • coordW R b lam 1 1 := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR d b lam hlam y n c hn hc
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨iTR, iLC, iSC, iT2, hsc, -, hK', hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  haveI := hB 1 1
  haveI := hlam
  have hK : IsHomeomorph (cK (F := F) (E := E) R b) := hK' 2 b
  haveI hν : (coordW R b lam 1 1).IsAddHaarMeasure :=
    (GlobalTheory.T.coordinate_haar_measure F E σ hcm R 2 b lam hlam).2.1 1 1
  have hinv := sigR_sigR R σ (conj_conj σ hcm)
  set π : Measure (Fin 1 × Fin 1 × Fin 2 → R) := Measure.pi fun _ => lam with hπ
  have hmp := GlobalTheory.CompanionTheory.SW.WBox.map_coordW R hK lam 1 1
  have hf : Measurable (fun t : R => (n : R) * t) := (continuous_const.mul continuous_id).measurable
  have hTm : Measurable (fun (t : Fin 1 × Fin 1 × Fin 2 → R) i => (n : R) * t i) :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  have hT : π.map (fun t i => (n : R) * t i) = (c * c) • π := by
    have h1 := pi_map_mul (ι := Fin 1 × Fin 1 × Fin 2) lam _ hf c hc
    have e : c ^ Fintype.card (Fin 1 × Fin 1 × Fin 2) = c * c := by
      simp [pow_two]
    rw [e] at h1
    exact h1
  have hνπ : coordW R b lam 1 1 = π.map (eW R hK 1 1).symm := by
    rw [hπ, ← hmp.map_eq, Measure.map_map (eW R hK 1 1).symm.measurable (eW R hK 1 1).measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id]
  have hNc : Continuous (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) :=
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  have hNm := hNc.measurable
  have hcomm : (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) ∘ (eW R hK 1 1).symm =
      (eW R hK 1 1).symm ∘ (fun t i => (n : R) * t i) := by
    funext t
    apply (eW R hK 1 1).injective
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    funext p
    have h1 := congrFun ((eW R hK 1 1).apply_symm_apply t) p
    rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply] at h1
    rw [GlobalTheory.CompanionTheory.SW.WBox.eW_apply, cK_tmul_mul', h1]
  have hN : (coordW R b lam 1 1).map
      (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) =
      (c * c) • coordW R b lam 1 1 := by
    calc _ = (π.map (eW R hK 1 1).symm).map
            (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) := by rw [← hνπ]
      _ = π.map ((eW R hK 1 1).symm ∘ (fun t i => (n : R) * t i)) := by
          rw [Measure.map_map hNm (eW R hK 1 1).symm.measurable, hcomm]
      _ = (π.map (fun t i => (n : R) * t i)).map (eW R hK 1 1).symm := by
          rw [Measure.map_map (eW R hK 1 1).symm.measurable hTm]
      _ = _ := by rw [hT, Measure.map_smul, ← hνπ]
  refine map_eq_of_conj (mulT y) (sigT (sigR R σ) hsc hinv) _ c (fun X => ?_) ?_
  · funext a i
    exact hinv _
  · have e : (fun X => sigT (sigR R σ) hsc hinv (mulT y (sigT (sigR R σ) hsc hinv (mulT y X)))) =
        (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => ((n : R) ⊗ₜ[F] (1 : E)) * X a i) := by
      funext X a i
      change sigR R σ ((y : R ⊗[F] E) * sigR R σ ((y : R ⊗[F] E) * X a i)) = _
      rw [map_mul, hinv, hn, mul_assoc]
    rw [e, hN]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingMonomial
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.CompanionTheory.SwUnf GlobalTheory.CompanionTheory.HermPoisson GlobalTheory.CompanionTheory.SiegelUnip
variable {D : D7} {n : ℕ}

theorem integral_pull (D : D7) (n : ℕ) (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure)
    (a : GL (Fin n) (AE D)) (F : hermA D n → ℂ) :
    ∫ b, F b ∂lam = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(n : ℂ)) * ∫ b, F (pull a b) ∂lam := by
  have key := GlobalTheory.CompanionTheory.CgMod.integral_cg D n lam hl a (fun c => F (pull a c))
  have e : ∀ c : hermA D n, pull a (cg a c) = c := fun c => Subtype.ext (by
    show (a⁻¹).1 * (a.1 * c.1 * adj a.1) * adj (a⁻¹).1 = c.1
    have h1 : (a⁻¹).1 * a.1 = 1 := by simp
    calc (a⁻¹).1 * (a.1 * c.1 * adj a.1) * adj (a⁻¹).1
        = ((a⁻¹).1 * a.1) * c.1 * (adj a.1 * adj (a⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = c.1 := by rw [h1, adj_mul_adj_inv, Matrix.one_mul, Matrix.mul_one])
  simp only [e] at key
  exact key

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem matchMono : PositivityTheory.PfSWUS.MatchMono := by
  intro D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hCD w hw β hβ a k hk φ hφ
  obtain ⟨hpl, hne⟩ := GlobalTheory.CompanionTheory.MM.isPlaces_of_hasRealPar D ψ θ l hS.hψ hS.hθ hS.hl
  obtain ⟨ε, fr, hfr, hfr1⟩ := GlobalTheory.CompanionTheory.CartFrames.exists_frames D V θ s hS.hθ hS.hs
  obtain ⟨hfock, hsch⟩ := mono_mem D n V θ l s φ hS.hθ hpl.ne hS.hs hφ
  obtain ⟨lamG, hlamG⟩ := GlobalTheory.CompanionTheory.LocHaar.exists_addHaar_tens D n
  obtain ⟨𝓕, hμ⟩ := hS.hμ
  obtain ⟨e, c, g, d, bs, gv, hpure, hφe⟩ := hφ
  obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.PfSWUS.MonoSplit.main D n V l s fr e c hne hfr1
  have hcm := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  have hT : ∀ x y, D.sp.cm.sig (β.1 y x) = β.1 x y := fun x y => by
    have := congrFun (congrFun β.2 x) y
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  obtain ⟨hnb, hlam⟩ := hCD
  haveI : lam.IsAddHaarMeasure := hlam.1
  refine ⟨d, bs, θ, l, ε, fr, gAt θ a, P, lamG, latAt a.1, latAt (adj (a⁻¹).1),
    fun X => φ (HMul.hMul (tupOf X) a.1), fun Y => g fun i j => ∑ k, Y k i * finPart D (a.1 k j),
    fun v Y => gv v (fun j i => ∑ k, Y k i * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 k j),
    μ.map tupInv, lam.map hermTo, ψ, ?_, npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n), ⟨(n : ℝ) / 2, ?_⟩, ?_⟩
  · refine
      { cm := hcm, herm := hJ, lt := hR.1, hT := hT, det := hβ, chr := hS.hψ, places := hpl, frames := hfr, haar := hlamG,
        co := fun v => ⟨GlobalTheory.CompanionTheory.MM.latAt_isCO D n a v, ?_⟩, std := ?_, pure := GlobalTheory.CompanionTheory.PureTwist.isPureFin_twist D n V.rank d bs g gv a hpure, prod := ?_,
        sdW := sdW_map V hS.hψ hμ, sdH := sdHerm_map hS.hψ hlam }
    · exact GlobalTheory.CompanionTheory.MM.latAt_isCO D n (astar a) v
    · filter_upwards [GlobalTheory.CompanionTheory.MM.LatStd.latAt_eq_latO D n a d bs, GlobalTheory.CompanionTheory.MM.LatStd.latAt_eq_latO D n (astar a) d bs] with v h1 h2
      exact ⟨h1, h2⟩
    · intro X
      have hcomp : ∀ τ, compAt θ τ (HMul.hMul (tupOf X) a.1 : Mx D V.rank n) =
          Matrix.of (fun i j => θ τ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X j i)) * (gAt θ a τ).1 := by
        intro τ
        ext i j
        simp only [compAt, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
        rfl
      have hfin : (fun i j => finPart D ((HMul.hMul (tupOf X) a.1 : Mx D V.rank n) i j)) =
          fun i j => ∑ k, HeckeCharacterZeroLocus.SiegelWeilU.projFin X k i * finPart D (a.1 k j) := by
        funext i j
        simp only [Matrix.mul_apply, map_sum, map_mul]
        rfl
      show φ (HMul.hMul (tupOf X) a.1) = PositivityTheory.SiegelWeilFormula.Gen.phiInf θ l fr (gAt θ a) P (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
        (g fun i j => ∑ k, HeckeCharacterZeroLocus.SiegelWeilU.projFin X k i * finPart D (a.1 k j))
      rw [hφe]
      simp only []
      rw [hP, hfin]
      congr 1
      unfold PositivityTheory.SiegelWeilFormula.Gen.phiInf PositivityTheory.SiegelWeilFormula.Gen.crd
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hcomp τ, Matrix.mul_assoc]
  · intro z hz
    obtain ⟨i1, -, i3, -, -, -⟩ := lattice_Mx D n n
    haveI : IsTopologicalAddGroup (Mx D n n) := i1
    haveI : SecondCountableTopology (Mx D n n) := i3
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : IsTopologicalAddGroup (Matrix (Fin n) (Fin n) (AE D)) := i1
    haveI : BorelSpace (HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    set r := absA D (Matrix.GeneralLinearGroup.det a) with hr
    have hr0 : r ≠ 0 := ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
    have hS' : Std D n V ψ χ θ μ ω H l s ν (⟨φ, hsch⟩ : schwartzA θ V.rank n) := { hS with hΦ := hfock }
    have hF0 : Integrable (fun b : hermA D n => sect ω H (⟨φ, hsch⟩ : schwartzA θ V.rank n) z (w * nb b * 1)) lam :=
      (PositivityTheory.PfSWUS.HUnfold.unfold D n V ψ χ θ μ ω H l s ν _ hS' hR nb lam 𝓖 ⟨hnb, hlam⟩ w hw β hβ z hz 1).1
    have hF : Integrable (fun b : hermA D n => npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ φ b) lam :=
      hF0.congr (Filter.Eventually.of_forall fun b => sect_w D n V ψ χ θ μ ω H hS.hω nb hnb w hw ⟨φ, hsch⟩ z b)
    have hFp := integrable_pull D n lam hlam.1 a _ hF
    have hch : Continuous fun b : hermA D n =>
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) := by
      have h := continuous_chi hS.hψ (-(β.1.map (incA D)))
      exact h.congr fun b => chi_neg_left ψ _ b
    have hcn : ∀ b : hermA D n, ‖ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 :=
      fun b => hS.hψ.2.1 _
    have hrm : npow r (V.rank : ℂ) ≠ 0 := by
      unfold npow
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => hr0 (by exact_mod_cast h.1)

    have hR1 : Integrable (fun b : hermA D n => npow (H (w * nb (pull a b))) (z - s0 V n) *
        Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) lam := by
      have h1 : Integrable (fun b : hermA D n => (npow r (V.rank : ℂ))⁻¹ *
          (npow (H (w * nb (pull a b))) (z - s0 V n) * Jt ψ V μ φ (pull a b))) lam := hFp.const_mul _
      have h2 : Integrable (fun b : hermA D n => npow (H (w * nb (pull a b))) (z - s0 V n) *
          Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b) lam := by
        refine h1.congr (Filter.Eventually.of_forall fun b => ?_)
        show (npow r (V.rank : ℂ))⁻¹ * (npow (H (w * nb (pull a b))) (z - s0 V n) * Jt ψ V μ φ (pull a b)) = _
        rw [jt_pull D n V ψ μ 𝓕 hμ φ a b, ← hr, mul_left_comm (npow (H (w * nb (pull a b))) (z - s0 V n)),
          inv_mul_cancel_left₀ hrm]
      refine h2.mono (h2.aestronglyMeasurable.mul hch.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun b => ?_)
      rw [norm_mul, hcn, mul_one]
    have hwhI : ∀ b : hermA D n,
        PositivityTheory.SiegelWeilFormula.Gen.whI (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
          (fun X => φ (HMul.hMul (tupOf X) a.1))
          (PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)))
          (β.1.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F))) z (hermTo b) =
        npow (H (w * nb (pull a b))) (z - s0 V n) *
          Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
          ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) := by
      intro b
      unfold PositivityTheory.SiegelWeilFormula.Gen.whI
      have e1 := GlobalTheory.T.local_haar_lattice_unipotent_integral D n θ hS.hθ H hS.hH nb hnb w hw a lamG hlamG b
      have e2 := jtR_hermTo V ψ μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b
      have e3 : (z - ((V.rank : ℂ) - n) / 2) = z - s0 V n := by
        unfold s0
        ring
      show ((PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)) b.1 : ℝ) : ℂ) ^
          (-(z - ((V.rank : ℂ) - n) / 2)) * _ * _ = _
      rw [e1, e3, npow_inv, e2]
      rfl
    let Mh : hermA D n ≃ₜ HermR (AF D.host.F) D.sp.cm.sig n :=
      { toEquiv := ⟨hermTo, hermFrom, hermFrom_hermTo, hermTo_hermFrom⟩
        continuous_toFun := continuous_hermTo
        continuous_invFun := continuous_hermFrom }
    have hemb : MeasurableEmbedding (hermTo (D := D) (r := n)) := Mh.measurableEmbedding
    constructor
    · exact hemb.integrable_map_iff.2 (hR1.congr (Filter.Eventually.of_forall fun b => (hwhI b).symm))
    · refine Eq.trans ?_ (congrArg (fun t => npow r ((V.rank : ℂ) - n) * t)
        (integral_map_of (hermTo (D := D) (r := n)) hermFrom hermFrom_hermTo hermTo_hermFrom hermTo_add continuous_hermTo
        continuous_hermFrom lam _)).symm
      beta_reduce
      rw [integral_congr_ae (Filter.Eventually.of_forall fun b => hwhI b)]
      show ∫ b, npow (H (w * nb b * k)) (z - s0 V n) * Jt ψ V μ φ b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) b.1 : Mx D n n))) ∂lam = _
      rw [integral_pull D n lam hlam.1 a]
      have hcong : ∀ b : hermA D n, npow (H (w * nb (pull a b) * k)) (z - s0 V n) * Jt ψ V μ φ (pull a b) *
          ψ (-halfTr (Matrix.trace (HMul.hMul (adj a.1 * β.1.map (incA D) * a.1) (pull a b).1 : Mx D n n))) =
          npow r (V.rank : ℂ) * (npow (H (w * nb (pull a b))) (z - s0 V n) *
            Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b *
            ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) := by
        intro b
        rw [GlobalTheory.CompanionTheory.PfSWUS.height_mul_K hS.hH _ hk, jt_pull D n V ψ μ 𝓕 hμ φ a b, trace_pull, ← hr]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hcong), integral_const_mul, ← mul_assoc]
      congr 1
      rw [sub_eq_add_neg, npow_add_of r hr0, mul_comm]
  · intro μH 𝓕H hμH hF
    exact congrArg (fun t => npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) * t)
      (ifrB_eq_meanC D n V ν hS.hν _ μH 𝓕H hμH hF β hβ)
end GlobalTheory.CompanionTheory.MM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCentreCharacterCellStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_centre_character_cell : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ), b₀.1.det ≠ 0 →
    ∀ (W : Submodule D.host.E (Fin ρ → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D ρ, chz ψ b₀ ν ≠ 1 ∧
    ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → zKer hn x = W →
      mat u = blk4 1 (bl hn ν.1 0 0 0) 0 1 →
      ∃ q ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat q) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = q * γ := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.SmallZ.small | exact GlobalTheory.CompanionTheory.ZUnf.SmallZ.small | (intros; apply GlobalTheory.CompanionTheory.ZUnf.SmallZ.small <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFactorizationRowsStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_factorization_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ A B Dd : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 A B 0 Dd) → blk4 a b c d = blk4 A B 0 Dd * blk4 a₂ b₂ c₂ d₂ →
    ∀ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K), cT σ ζ = ζ →
    ∃ (ζ₂ : Matrix (Fin ρ) (Fin ρ) K) (η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      cT σ ζ₂ = ζ₂ ∧ rowC hn η a c = T * rowC hn η₂ a₂ c₂ ∧ rowD hn σ ζ η b d = T * rowD hn σ ζ₂ η₂ b₂ d₂ := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep | exact GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep | (intros; apply GlobalTheory.CompanionTheory.ZUnf.ClassRep.exists_change_rep <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormula
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

theorem rv_zero_apply (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    rv v 0 s = if s ≠ 0 ∧ s ∈ v.adicCompletionIntegers F then 1 else 0 := by
  unfold rv
  rw [tsum_eq_single 0]
  · have h : (s ∈ v.adicCompletionIntegers F) ↔ Valued.v s ≤ 1 :=
      HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v
    simp [h]
  · intro i hi
    simp [hi]

theorem rv_zero_of_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v} (h0 : s ≠ 0)
    (hs : s ∈ v.adicCompletionIntegers F) : rv v 0 s = 1 := by
  rw [rv_zero_apply, if_pos ⟨h0, hs⟩]

theorem rv_zero_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v}
    (hs : s ∉ v.adicCompletionIntegers F) : rv v 0 s = 0 := by
  rw [rv_zero_apply, if_neg fun h => hs h.2]

theorem pure_rv_zero_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ) :
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), (a : AF F).2 v ≠ 0 := fun v =>
    IdeleGroup.finite_ne_zero a v
  unfold PositivityTheory.Rg.Base1.pure
  split_ifs with h
  · rw [finprod_eq_one_of_forall_eq_one (fun v : {v // v ∉ S} => rv_zero_of_mem v.1 (hne v.1) (h v.1 v.2)),
      mul_one]
  · push_neg at h
    obtain ⟨v, hvS, hv⟩ := h
    have hfin : (Function.mulSupport fun v : {v // v ∉ S} => rv v.1 0 ((a : AF F).2 v.1)).Finite := by
      have hco : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
          (a : AF F).2 v ∈ v.adicCompletionIntegers F := (a : AF F).2.2
      refine Set.Finite.subset (Set.Finite.preimage Subtype.val_injective.injOn hco) ?_
      intro w hw
      by_contra hmem
      exact hw (rv_zero_of_mem w.1 (hne w.1) (not_not.1 hmem))
    rw [finprod_eq_zero _ (⟨v, hvS⟩ : {v // v ∉ S}) (rv_zero_of_not_mem v hv) hfin, mul_zero,
      ENNReal.ofReal_zero]

end GlobalTheory.CompanionTheory.BasePsi

end
end

