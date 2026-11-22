import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0972
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0842
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0971
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0853
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0973
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialLieDerivativeEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.LieEquivFock

theorem lie_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (ψ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) → (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ' ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ' w'))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t τ Y hY ψ ψ' hψ hψ'
  obtain ⟨a, hL⟩ := GlobalTheory.T.hasDerivAt_fockVector_targetLieOneParam D G Pl0 T A Ks R F hG hF i t τ Y hY
  have hinj : Function.Injective (R.ptP i t) := (GlobalTheory.CoefActIo.thetaVector_laws (i := i) hG.core t).2.2
  have hlin : ∀ (c : ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t (c • P) = c • R.ptP i t P := by
    intro c P
    unfold RealDat.ptP
    exact map_smul _ c P
  set Y' := (R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹
  set Lop : PolF D (Wc D i).rank (Vc D i).rank → PolF D (Wc D i).rank (Vc D i).rank :=
    fun P => fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ)) Y' P + a • P
    with hLop
  have hder : ∀ w, ψ' w = Lop (ψ w) := by
    intro w
    apply hinj
    funext z
    exact (hψ' w z).unique (hL (ψ w) z)
  intro u hu w'
  obtain ⟨c, g, hg⟩ := GlobalTheory.T.realPoints_act_fock_scalar_linear_substitution D G Pl0 T A Ks R F hG i t u hu
  have h1 : ψ ((R.cV i).ρ u w') = c • fockSubst (pS D i) g (ψ w') := by
    apply hinj
    rw [hψ u hu w', hg, hlin]
  have hcomm : ∀ Q, Lop (fockSubst (pS D i) g Q) = fockSubst (pS D i) g (Lop Q) := by
    intro Q
    simp only [hLop, map_add, map_smul]
    rw [GlobalTheory.T.fockPolynomialSubstitution_commute_targetGlAction]
  have hsm : ∀ x, Lop (c • x) = c • Lop x := by
    intro x
    simp only [hLop, map_smul, smul_add]
    rw [smul_comm a c]
  rw [hder, h1, hder, hg, ← hlin, hsm, hcomm]

end GlobalTheory.LieEquivFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanLe
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CuspDescent

theorem exists_indep_comb {K R V : Type} [Field K] [AddCommGroup R] [Module K R] [AddCommGroup V] [Module ℂ V]
    (σ : K →+* ℂ) (ρ : R →ₛₗ[σ] V) (S : Submodule K R) {P : V} (hP : P ∈ Submodule.span ℂ (ρ '' (S : Set R))) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (f : Fin m → R), (∀ i, f i ∈ S) ∧
      (∀ c : Fin m → K, ∑ i, σ (c i) * e i = 0 → c = 0) ∧ P = ∑ i, e i • ρ (f i) := by
  obtain ⟨n, z, v, hv⟩ := Submodule.mem_span_set'.1 hP
  choose g hg hgv using fun k => (v k).2
  letI : Algebra K ℂ := σ.toAlgebra
  have hsm : ∀ (a : K) (x : ℂ), a • x = σ a * x := fun a x => by rw [Algebra.smul_def]; rfl
  let W : Submodule K ℂ := Submodule.span K (Set.range z)
  have hzW : ∀ k, z k ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  haveI : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range z)
  let ζ := Module.finBasis K W
  let β : Fin n → Fin (Module.finrank K W) → K := fun k m => ζ.repr ⟨z k, hzW k⟩ m
  have hzexp : ∀ k, z k = ∑ m, σ (β k m) * (ζ m : ℂ) := by
    intro k
    have h2 := congrArg Subtype.val (ζ.sum_repr ⟨z k, hzW k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hsm] at h2
    exact h2.symm
  have hlin : LinearIndependent K (fun m => (ζ m : ℂ)) :=
    ζ.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
  refine ⟨_, fun m => (ζ m : ℂ), fun m => ∑ k, β k m • g k,
    fun m => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k), fun c hc => ?_, ?_⟩
  · funext m
    exact (Fintype.linearIndependent_iff.1 hlin) c (by simpa only [hsm] using hc) m
  · rw [← hv]
    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul, hgv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, hzexp k]
    congr 1
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

section Geometric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem rd_prod {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (N : ℕ) (f : Fin (N + 1) → Rul Xo c) :
    rdU U (∏ t, f t) = ∏ t, rdU U (f t) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Fin.prod_univ_castSucc, GlobalTheory.CuspAllEmb.rd_mul, ih, ← Fin.prod_univ_castSucc fun t => rdU U (f t)]

theorem prod_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (N : ℕ) (f : Fin (N + 1) → Rul Xo c)
    (hf : ∀ t, f t ∈ sec Xo c a n) : ∏ t, f t ∈ sec Xo c ((N + 1) • a) ((N + 1) * n) := by
  induction N with
  | zero => simpa using hf 0
  | succ N ih =>
    rw [succ_nsmul, add_mul _ 1, one_mul, Fin.prod_univ_castSucc]
    exact sec_mul Xo c _ _ _ _ (ih _ fun t => hf _) (hf _)

theorem pow_comb {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (N : ℕ) {ι : Type} [Fintype ι] (e : ι → ℂ) (f : ι → Rul Xo c) :
    (∑ i, e i • rdU U (f i)) ^ (N + 1) =
      ∑ p : Fin (N + 1) → ι, (∏ t, e (p t)) • rdU U (∏ t, f (p t)) := by
  classical
  rw [Fintype.sum_pow]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [rd_prod, Finset.prod_smul]

theorem isSec_comb (X : Data E r) (la : Wt X.Ψ r) {ι : Type} [Fintype ι] (e : ι → ℂ) (Q : ι → Frame X.Ψ r → ℂ)
    (hQ : ∀ i, X.IsSec la (Q i)) : X.IsSec la (∑ i, e i • Q i) := by
  refine ⟨DifferentiableOn.sum fun i _ => (hQ i).1.const_smul (e i), fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).2.1 x hx b hb]; ring
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).2.2 γ hγ x hx]; ring

theorem descent (hf : 1 < Module.finrank ℚ E / 2) {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hU : IsUnf U)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) (N : ℕ)
    (hI : ∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c ((N + 1) • a) ((N + 1) * n)) →
      LinearIndependent c.F b → LinearIndependent ℂ fun i => rdU U (b i))
    (hspan : holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) ≤ Submodule.span ℂ (rdU U ''
      {g | g ∈ sec Xo c ((N + 1) • a) ((N + 1) * n) ∧ rdU U g ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n))})) :
    holSub0 U.X (laU U a n) ⊓ Submodule.span ℂ (rdU U '' (sec Xo c a n : Set (Rul Xo c))) ≤
      Submodule.span ℂ (rdU U '' {f | f ∈ sec Xo c a n ∧ rdU U f ∈ holSub0 U.X (laU U a n)}) := by
  classical
  rintro P ⟨hP, hPs⟩
  obtain ⟨m, e, f, hfs, he, rfl⟩ := exists_indep_comb σ (rdU U) _ hPs
  have hoff : ∀ e' : Fin m → ℂ, ∑ i, e' i • rdU U (f i) ∈ offZero U.X := fun e' =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (rdU_mem_offZero _ _)
  have hpow : (∑ i, e i • rdU U (f i)) ^ (N + 1) ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) := by
    refine ⟨(GlobalTheory.CuspAllEmb.mem_holSub _ _ _).2 fun k => ?_, ?_⟩
    · have h1 := (GlobalTheory.CuspAllEmb.mem_holSub _ _ _).1 hP.1 k
      rw [GlobalTheory.CuspAllEmb.la_smul _ _ hd.2]
      rcases N with _ | N
      · simpa using h1
      · have h2 := GlobalTheory.CuspAllEmb.ss_mul _ hf h1 (GlobalTheory.CuspAllEmb.isSec_pow _ h1.1.1 N)
        rw [← pow_succ', ← succ_nsmul'] at h2
        exact h2
    · rw [pow_comb]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (rdU_mem_offZero _ _)
  obtain ⟨q, z, v, hv⟩ := Submodule.mem_span_set'.1 (hspan hpow)
  choose g hg hgv using fun k => (v k).2
  have conj : ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) →
      ∑ i, φ (e i) • rdU U (f i) ∈ holSub0 U.X (laU U a n) := by
    intro φ hφ
    have tr := GlobalTheory.CuspAllEmb.transfer (φ : ℂ →+* ℂ) hφ (rdU U) (rdU U) _ hI
      (fun p : Fin (N + 1) → Fin m => ∏ t, f (p t)) g (fun p => prod_mem_sec N _ fun t => hfs _) (fun k => (hg k).1)
      (fun p => ∏ t, e (p t)) z (by rw [← pow_comb, ← hv]; simp only [hgv])
    simp only [map_prod, RingHom.coe_coe] at tr
    rw [← pow_comb U N (fun i => φ (e i)) f] at tr
    have hm : (∑ i, φ (e i) • rdU U (f i)) ^ (N + 1) ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) := by
      rw [tr]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k).2
    refine ⟨(GlobalTheory.CuspAllEmb.mem_holSub _ _ _).2 fun k => ?_, hoff _⟩
    have h1 := (GlobalTheory.CuspAllEmb.mem_holSub _ _ _).1 hm.1 k
    rw [GlobalTheory.CuspAllEmb.la_smul _ _ hd.2] at h1
    refine GlobalTheory.CuspAllEmb.ss_of_pow _ hf ?_ N h1
    have := isSec_comb (U.X k) (laU U a n k) (fun i => φ (e i)) (fun i => rdU U (f i) k)
      (fun i => hU.2.2.2.2.1 a n hd _ (hfs i) k)
    simpa only [Finset.sum_apply, Pi.smul_apply] using this
  haveI := c.fin
  haveI : NumberField c.F := {}
  have htop := GlobalTheory.T.span_automorphismConjugates_of_numberField_independent_eq_top c.F σ (Fin m) e he
  let L : (Fin m → ℂ) →ₗ[ℂ] FDSec U.X := Fintype.linearCombination ℂ fun i => rdU U (f i)
  have hle : (⊤ : Submodule ℂ (Fin m → ℂ)) ≤ (holSub0 U.X (laU U a n)).comap L := by
    rw [← htop, Submodule.span_le]
    rintro _ ⟨φ, hφ, rfl⟩
    exact conj φ hφ
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f i, ⟨hfs i, ?_⟩, rfl⟩)
  have := hle (Submodule.mem_top (x := Pi.single i 1))
  simpa [L] using this

end Geometric

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in

theorem cusp_descends : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ⊓ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (wtA w) w.n : Set (Rul (T.Q.Xo j) T.Q.c))) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  intro D T h j hj σ hσ w hw hn
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := Formalism.L2.Pj.hostSize_finrank D
  have h8 := D.eight_le_f
  set N := 8 * D.R.f * D.R.r + 3 with hN
  have hA : wtA (WeightAlgebra.wsmul (N + 1) w) = (N + 1) • wtA w := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold wtA
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [WeightAlgebra.wsmul, ext0]
    split_ifs <;> ring
  have hd : Dom ((N + 1) • wtA w) ((N + 1) * w.n) := hA ▸ dom_wtA (WeightAlgebra.wsmul (N + 1) w)
  refine descent (by omega) (T.U j σ) (h.unf j hj σ hσ) (dom_wtA w) N
    (GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj σ hσ _ _ hd) ?_
  have key := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj (WeightAlgebra.wsmul (N + 1) w)
    (fun τ i hi => Nat.mul_pos (Nat.succ_pos N) (hw τ i hi)) (Nat.le_mul_of_pos_right _ hn) σ hσ
  rw [hA] at key
  refine key.trans (Submodule.span_mono (Set.image_mono fun g hg => ?_))
  exact ⟨cusp_le_sec _ _ _ _ _ hg, ((mem_cusp _ _ _ _ _ _).1 hg).2 σ hσ, rdU_mem_offZero _ _⟩

end GlobalTheory.CuspDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairRealPlacesIrreducible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HoweIrrCompact

section FockLin
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

theorem fockT_zero : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (0 : Matrix (Fin b) (Fin b) ℂ) = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT]

theorem fockT_add (Y Y' : Matrix (Fin b) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (Y + Y') = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y + GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y' := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem fockT_smul (c : ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (c • Y) = c • GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

end FockLin

theorem howe_irr : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ ψ ∈ M, (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w')))) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → ψ' ∈ M) → M ≠ ⊥ → ∀ φ : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → φ ∈ M := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t M hMeq hMlie hM0 φ hφ
  classical
  have hC := hG.core
  obtain ⟨-, -, hinj⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  obtain ⟨w, BS, r, hact, hU, hsurj, hε⟩ := GlobalTheory.T.realPoints_act_fock_by_realComponents_basis D G Pl0 T A Ks R F hG hFull i t
  set ρ' : ↥(GinfC (Vc D i)) →* Module.End ℂ (R.cV i).W := (R.cV i).ρ.comp (GinfC (Vc D i)).subtype with hρ'
  have eqv : ∀ ψ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
      (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) →
      ∀ (k : ↥(GinfC (Vc D i))) (w' : (R.cV i).W), ψ (ρ' k w') = GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r k) (ψ w') := by
    intro ψ hψ k w'
    apply hinj
    rw [← hact k (ψ w')]
    exact hψ k k.2 w'
  have hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ k, U.map (ρ' k) ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hUk
    refine (hC.models.cV i).2.2.2.2 U fun h => ?_
    have e := GlobalTheory.AutMult.toInf_mul_toFin (V := Vc D i) h
    have h1 : (R.cV i).ρ h = ρ' (GlobalTheory.AutMult.toInf (Vc D i) h) := by
      calc (R.cV i).ρ h = (R.cV i).ρ ((GlobalTheory.AutMult.toInf (Vc D i) h : GA D (Vc D i)) * GlobalTheory.AutMult.toFin (Vc D i) h) := by rw [e]
        _ = ρ' (GlobalTheory.AutMult.toInf (Vc D i) h) := by
          rw [map_mul, (hC.models.cV i).1 _ (GlobalTheory.AutMult.toFin (Vc D i) h).2, mul_one]
          rfl
    rw [h1]
    exact hUk _
  have hlie : ∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M := by
    intro ψ hψ τ
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.hasDerivAt_fockVectors_targetLie_realPlace D G Pl0 T A Ks R F hG hFull i t τ
    have hε' : (R.MW i (sg0 D A)).ε τ = fun j : Fin (Wc D i).rank => decide ((j : ℕ) < w.p τ) := funext (hε τ)
    set fr := (R.MW i (sg0 D A)).fr τ with hfr
    have base : ∀ Y ∈ lieAt (Wc D i) τ,
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) (fr * Y * fr⁻¹) ∘ₗ ψ ∈ M := by
      intro Y hY
      have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) (fr * Y * fr⁻¹) + κ Y • (1 : Module.End ℂ (PolF D (Wc D i).rank (Vc D i).rank))) ∘ₗ ψ ∈ M :=
        hMlie ψ hψ τ Y hY _ fun w' z => by
          simpa using hκ Y hY (ψ w') z
      have h2 : κ Y • ψ ∈ M := M.smul_mem _ hψ
      have h3 := M.sub_mem h1 h2
      convert h3 using 1
      ext x
      simp
    have hsp := GlobalTheory.T.span_conj_unitaryLieAlgebra_realPlace_eq_top D (Wc D i) τ fr ((R.MW i (sg0 D A)).fr_unit τ)
    intro Z
    have hZ : Z ∈ Submodule.span ℂ {Z : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ | ∃ Y ∈ lieAt (Wc D i) τ, Z = fr * Y * fr⁻¹} := by
      rw [hsp]; exact Submodule.mem_top
    rw [← hε']
    induction hZ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, hY, rfl⟩ := hx
      exact base Y hY
    | zero =>
      rw [fockT_zero, LinearMap.zero_comp]; exact M.zero_mem
    | add x y _ _ hx hy =>
      rw [fockT_add, LinearMap.add_comp]; exact M.add_mem hx hy
    | smul c x _ hx =>
      rw [fockT_smul, LinearMap.smul_comp]; exact M.smul_mem c hx
  exact GlobalTheory.T.howeDuality_compactPair_polynomialFock_allRealPlaces D (Vc D i).rank (Wc D i).rank w BS ↥(GinfC (Vc D i)) r hU hsurj (R.cV i).W ρ' hirr M
    (fun ψ hψ => eqv ψ (hMeq ψ hψ)) hlie hM0 φ (eqv φ hφ)

end GlobalTheory.HoweIrrCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsScalarMove
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ} (kap : ℝ) (lam : type_of% Rl.lam3)
  {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem pin_move {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) : RealPin (fullHeckeRealDatMovedReadings Rl w kap lam) cG ρ :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15, h.16, h.17, h.18⟩

theorem isNorm_move {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) :
    IsNorm (fullHeckeRealDatMovedReadings Rl w kap lam) v₀ B ν ↔ IsNorm Rl v₀ B ν := Iff.rfl

theorem vec_move {j : Fin D.R.m} (h : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) :
    FWT.IsChosenExtremalVector (fullHeckeRealDatMovedReadings Rl w kap lam).toRealDat j (sg0 D A3.A) (v₀ j _) := h

theorem isScalar_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ}
    (h : IsScalar YS v₀ hρ i j b ν) : IsScalar (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ hρ i j b ν :=
  ⟨h.ne, fun h' => (isNorm_move kap lam _ _).2 (h.norm (h'.imp fun _ => (isNorm_move kap lam _ _).1)), fun h' =>
    (congrArg (Rat hρ) (realRd_move kap lam YS hw hst v₀ hρ i j b ν)).mpr
      (h.rat ((ratRow_move kap lam YS hw hst v₀ hρ i j b).1 h'))⟩

def moveZ (Z : ExportTie YS v₀) : ExportTie (Rl := fullHeckeRealDatMovedReadings Rl w kap lam) (cG := cG) (S := moveS w YS) (moveYS kap lam YS hw hst) v₀ where
  ρ := Z.ρ
  good := Z.good
  pin := pin_move kap lam Z.pin
  vec := fun j => vec_move kap lam (Z.vec j)
  ν := Z.ν
  scalar := fun i j b => isScalar_move kap lam hw hst Z.good i j b (Z.scalar i j b)
  tie := cast (congrArg (Comparison₂ Z.good (Y := D.nexp)) (rd_move kap lam hw hst Z).symm) Z.tie
  hecke := fun i j b => (congrArg HeckeTie (realRd_move kap lam YS hw hst v₀ Z.good i j b _)).mpr (Z.hecke i j b)
  univ := Z.univ

theorem rd_moveZ (Z : ExportTie YS v₀) : (moveZ kap lam hw hst Z).rd = Z.rd := rd_move kap lam hw hst Z

end GlobalTheory.Unframe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslatesStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_of_mem_span_vacuumTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (e : AE D) (M : ℕ) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, IsThetaFunO ψ V W f := by
  first | exact @GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp | exact GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp | (intros; apply GlobalTheory.LevelSeries.isThetaFunO_of_mem_trSp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanksStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_all_ranks : ∀ r, UnitMatch r := by
  first | exact @GlobalTheory.JR.unitMatch_all | exact GlobalTheory.JR.unitMatch_all | (intros; apply GlobalTheory.JR.unitMatch_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReadingStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  first | exact @GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 | exact GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 | (intros; apply GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleLiftsEquivariantRootOfUnityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_lifts_equivariant_rootOfUnity : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∀ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) → (∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f)) → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (y y' : (R.HV i A.μ0).H), (∀ h : GA D (Vc D i), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i A.μ0).e y (fin _ h) = M.c0' x ∧ (R.HV i A.μ0).e y' (fin _ h) = M.c0' x') → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  first | exact @GlobalTheory.ConjRefLift.conjFun_lifts_root | exact GlobalTheory.ConjRefLift.conjFun_lifts_root | (intros; apply GlobalTheory.ConjRefLift.conjFun_lifts_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlacesStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_integral_of_small_at_other_places : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  first | exact @GlobalTheory.TraceSmall.trace_le_one | exact GlobalTheory.TraceSmall.trace_le_one | (intros; apply GlobalTheory.TraceSmall.trace_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProductStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
                       (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ ∧
          GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x =
            ((H x * (GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) := by
  first | (exact @GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD) | (exact GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD) | (intros; apply GlobalTheory.RSEulerId.thetaZ_eq_mul_eulD  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedLevelCoverExistsConstantsDominantWeigStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ cc₂ : C.U₂.Comp → ℂ, ∀ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n → ({ C with cc₂ := cc₂ } : Cover T j σ).IsPinned a n := by
  first | exact @GlobalTheory.CoverRead.Cover.exists_pinned_dom | exact GlobalTheory.CoverRead.Cover.exists_pinned_dom | (intros; apply GlobalTheory.CoverRead.Cover.exists_pinned_dom <;> assumption)
end

