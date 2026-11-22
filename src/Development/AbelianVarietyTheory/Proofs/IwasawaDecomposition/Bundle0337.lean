import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBesselPeriodSesquilinear
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCompAlgebraMap
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TwistTop

theorem exists_homeomorph : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : Model Y) (σ : F →+* ℂ), ∃ Φ : CxPts Y.str σ ≃ₜ CxPts M.p (σ.comp (algebraMap (𝓞 F) F)), ∀ z, (Φ z).1 = z.1 ≫ M.j := fun F _ _ Y M σ => by
  have e : spMap σ ≫ spMap (algebraMap (𝓞 F) F) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [← Spec.map_comp]; rfl
  have h₁ (z : CxPts Y.str σ) : (z.1 ≫ M.j) ≫ M.p = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, M.pb.w, ← Category.assoc, z.2, e]
  have h₂ : Continuous fun y : CxPts M.p (σ.comp (algebraMap (𝓞 F) F)) =>
      M.pb.lift y.1 (spMap σ) (y.2.trans e.symm) := by
    rw [(Points.isEmbedding_of_isPullback M.pb).continuous_iff]
    refine (continuous_subtype_val.prodMk (continuous_const (y := spMap σ))).congr fun y => ?_
    exact (Prod.ext (M.pb.lift_fst _ _ _) (M.pb.lift_snd _ _ _)).symm
  exact ⟨{ toFun := fun z => ⟨z.1 ≫ M.j, h₁ z⟩
           invFun := fun y => ⟨M.pb.lift y.1 (spMap σ) (y.2.trans e.symm), M.pb.lift_snd _ _ _⟩
           left_inv := fun z => Subtype.ext (M.pb.hom_ext (M.pb.lift_fst _ _ _)
             ((M.pb.lift_snd _ _ _).trans z.2.symm))
           right_inv := fun y => Subtype.ext (M.pb.lift_fst _ _ _)
           continuous_toFun := ((Points.continuous_comp M.j).comp continuous_subtype_val).subtype_mk h₁
           continuous_invFun := h₂.subtype_mk fun y => M.pb.lift_snd _ _ _ }, fun _ => rfl⟩

theorem bijective_comp_algebraMap (F : Type) [Field F] [NumberField F] :
    Function.Bijective fun σ : F →+* ℂ => σ.comp (algebraMap (𝓞 F) F) := by
  refine ⟨fun σ τ h => IsLocalization.ringHom_ext (S := F) (nonZeroDivisors (𝓞 F)) (j := σ) (k := τ) h, fun τ => ?_⟩
  have hi : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
    have : (n : ℂ) = 0 := (map_intCast τ n).symm.trans hn
    exact Int.cast_eq_zero.1 this
  exact ⟨IsFractionRing.lift (K := F) hi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) hi a⟩

theorem chernInt_model (hd : GlobalTheory.Published.ChernDegree) {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)
    (L : HermLB M.p) {Δ : Y.Dv} {r : (L.B.pull M.j).ι → Y.Fnˣ} (h : Presents Δ (L.B.pull M.j) r) (σ : F →+* ℂ) :
    (L.φ (σ.comp (algebraMap (𝓞 F) F))).chernInt Y.dim Set.univ (fun _ => 1) = (Y.inter (fun _ => Δ) : ℝ) := by
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph F Y M σ
  have := CxPts.secondCountableTopology_of_isProjOver (σ.comp (algebraMap (𝓞 F) F)) M.ar.isProjOver
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.analytic_weight_linear_comb _ _ _ _ M.p Y.str _ σ Y.dim M.j Φ hΦ (GlobalTheory.T.generically_smooth_model F Y M _) inferInstance _ _ (L.cInf _)
  exact h₂.symm.trans (hd F Y σ Δ _ r h _ h₁).2

theorem sum_emb {F : Type} [Field F] [NumberField F] (c : InfinitePlace F → ℝ) :
    ∑ σ : F →+* ℂ, c (InfinitePlace.mk σ) = ∑ v : InfinitePlace F, (v.mult : ℝ) * c v := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => congrArg c (Finset.mem_filter.1 hσ).2, Finset.sum_const,
    InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem isArTop_twist : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (t : ℝ) (ci : InfinitePlace F → ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support cf).Finite → A.IsArTop t → (A.twist ci cf).IsArTop (t + ((Y.dim : ℝ) + 1) * A.deg * ((∑ v : InfinitePlace F, (v.mult : ℝ) * ci v) + ∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ)) := by
  intro hc hd F _ _ C Y A t ci cf hcf ⟨M, L, k, cf₀, a, ⟨hf, r, hr, hi, hv⟩, ha, ht⟩
  have := M.ar.isIntegral
  let E := Equiv.ofBijective _ (bijective_comp_algebraMap F)
  have hE (σ : F →+* ℂ) : E.symm (σ.comp (algebraMap (𝓞 F) F)) = σ := E.symm_apply_apply σ
  let s (τ : 𝓞 F →+* ℂ) : ℝ := (k : ℕ) * (A.n : ℕ) * ci (InfinitePlace.mk (E.symm τ))
  have hs (τ : 𝓞 F →+* ℂ) : s ((starRingEnd ℂ).comp τ) = s τ := by
    obtain ⟨σ, rfl⟩ := E.surjective τ
    have e : (starRingEnd ℂ).comp (E σ) = E (ComplexEmbedding.conjugate σ) := rfl
    simp only [s, e, Equiv.symm_apply_apply, InfinitePlace.mk_conjugate_eq]
  refine ⟨M, L.shift s hs, k, cf₀ + cf, _, ⟨(hf.union hcf).subset (Function.support_add _ _), r, hr,
    fun σ y y' i f h₁ h₂ h₃ => ?_, fun v e y yt i h₁ h₂ => ?_⟩, isSelfInter_shift hc.1 hc.2.1 _ _ _ _ M.ar L a s hs ha, ?_⟩
  · have e := hi σ y y' i f h₁ h₂ h₃
    change Real.exp (-(2 * (k : ℕ) * (A.n : ℕ) * (A.ci (InfinitePlace.mk σ) + ci (InfinitePlace.mk σ)))) *
      C.pn Y σ _ (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y =
      ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-((L.φ _).φ (i PUnit.unit) y' + 2 * s _))
    rw [neg_add, Real.exp_add, ← mul_assoc, ← e, mul_add, neg_add, Real.exp_add, mul_right_comm]
    simp only [s, hE, mul_assoc]
  · have e := hv v e y yt i h₁ h₂
    change ((k : ℕ) : ℝ) * (A.lg v _ y - (A.n : ℕ) * cf v) = Real.log (Ext.w _ (valAt y.1
      (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn))) - (k : ℕ) * (A.n : ℕ) * (cf₀ v + cf v)
    linear_combination e
  · have e₁ : ∑ᶠ τ, s τ * (L.φ τ).chernInt Y.dim Set.univ (fun _ => 1) =
        (k : ℕ) * (A.n : ℕ) * (((k : ℕ) : ℝ) ^ Y.dim * (Y.inter (fun _ => A.D) : ℝ)) *
          ∑ v : InfinitePlace F, (v.mult : ℝ) * ci v := by
      rw [← finsum_comp_equiv E, finsum_eq_sum_of_fintype, ← sum_emb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      have e := chernInt_model hd.2 M L hr σ
      rw [Var.inter_const_nsmul] at e
      push_cast at e
      rw [show (L.φ (E σ)).chernInt Y.dim Set.univ (fun _ => 1) = _ from e]
      simp only [s, Equiv.symm_apply_apply]
      ring
    have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
    have e₂ : ∑ᶠ v, (cf₀ + cf) v = ∑ᶠ v, cf₀ v + ∑ᶠ v, cf v := finsum_add_distrib hf hcf
    rw [e₁, e₂, ht, deg_twist, ← add_div]
    congr 1
    simp only [Adl.deg, Adl.twist]
    field_simp
    ring

end GlobalTheory.TwistTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointAlgebraic
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ClosedAlg

theorem isAlgPt_of_isClosed : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → ArInt.IsAlgPt (M.j x) := by
  intro F _ _ Y M x hx
  let ι : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra F (AlgebraicClosure ℚ) := ι.toRingHom.toAlgebra
  obtain ⟨⟨⟨y, hy⟩, hyx⟩⟩ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure ℚ) Y.str x hx).1
  have h : (y ≫ M.j) ≫ M.p = spMap ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, M.pb.w, ← Category.assoc, hy]
    exact (Spec.map_comp _ _).symm
  have h2 := GlobalTheory.Mean4O.GeomPt.isAlgPt M.ar
    (⟨y ≫ M.j, h⟩ : GlobalTheory.Mean4O.GeomPt M.p ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)))
  subst hyx
  exact h2

end GlobalTheory.TrueGeo.ClosedAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpan
section
set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trace_pow_mul_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι)
    (j w : ℕ) (hj : 1 ≤ j) (f : Mat m S → S) (hf : f ∈ TrSpan m w S) :
    (fun A : Mat m S => ((A τ) ^ j).trace * f A) ∈ TrSpan m (j + w) S := by
  unfold TrSpan at hf
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨l, hl, hw, rfl⟩ := h
    refine Submodule.subset_span ⟨(τ, j) :: l, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hj
      · exact hl x hx
    · simp [hw]
    · funext A
      simp [trProd]
  | zero =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (0 : Mat m S → S) A) = 0 := by
      funext A; simp
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (f + g) A) =
        (fun A : Mat m S => ((A τ) ^ j).trace * f A) + (fun A : Mat m S => ((A τ) ^ j).trace * g A) := by
      funext A; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (c • f) A) =
        c • (fun A : Mat m S => ((A τ) ^ j).trace * f A) := by
      funext A; simp
    rw [this]; exact Submodule.smul_mem _ c hf

theorem coeff_charpolyRev_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (τ : ι) (k : ℕ) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine Submodule.subset_span ⟨[], by simp, by simp, ?_⟩
      funext A
      simp [trProd, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have key : (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) =
          (-(k : ℝ)⁻¹) • ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ (i + 1)) •
            (fun A : Mat m S => ((A τ) ^ (i + 1)).trace *
              (Matrix.charpolyRev (-(A τ))).coeff (k - 1 - i)) := by
        funext A
        have h := GlobalTheory.natCast_mul_coeff_charpolyRev (-(A τ)) k
        have e : ∀ i : ℕ, ((-(A τ)) ^ (i + 1)).trace = ((-1 : ℝ) ^ (i + 1)) • ((A τ) ^ (i + 1)).trace := by
          intro i
          rw [← neg_one_smul ℝ (A τ), smul_pow, Matrix.trace_smul]
        simp only [e, smul_mul_assoc] at h
        simp only [Pi.smul_apply, Finset.sum_apply]
        rw [neg_smul, ← smul_neg, ← h, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          inv_mul_cancel₀ hk', one_smul]
      rw [key]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
      have hi' := Finset.mem_range.1 hi
      have h := trace_pow_mul_mem_trSpan m S τ (i + 1) (k - 1 - i) (by omega) _ (ih (k - 1 - i) (by omega))
      rwa [show i + 1 + (k - 1 - i) = k by omega] at h

end GlobalTheory.GoodMetric.ChernSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBesselPeriodSesquilinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBesselPeriod_sesquilinear : ∀ D : D7, PosLin D := by
  first | exact @GlobalTheory.RootExch.PosLinear.posLin | exact GlobalTheory.RootExch.PosLinear.posLin | (intros; apply GlobalTheory.RootExch.PosLinear.posLin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseFrobSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.OSplitBig

def sysPol (D : D7) (c : PlE D.host → ℕ → ℂ) (w : PlE D.host) : ℂ[X] :=
  X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
    C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c w k) * X ^ (D.R.nV - k)

def frobSet (D : D7) (F : Finset (PlE D.host)) : Set (G D.host.E D.nd.Om) :=
  {σ | ∃ w : PlE D.host, w ∉ F ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem dense_frobSet (D : D7) (h : GlobalTheory.RowTie.ChebSplit D.nd) (F : Finset (PlE D.host)) :
    Dense (frobSet D F) := h F

theorem heckePol_map (D : D7) (L : LocAll (lay0 D)) (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i) (v : PlE D.host)
    (hv : SplitOut (withLoc L).nd i v) :
    (heckePol (withLoc L).nd i x v).map (iotaOC (withLoc L) i) =
      sysPol D (GlobalTheory.CoefDuty.ptSys (withLoc L) i x) v := by
  have hS := hv
  obtain ⟨hsp, hl, hSi, hQ⟩ := hv
  have hgen : ∀ k ∈ Finset.Icc 1 D.R.nV,
      GenAt (withLoc L) ((withLoc L).nd.l i) ((withLoc L).nd.Q i) v k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    refine ⟨hsp, hl, ?_, hQ, hk1, hk2⟩
    intro hmem
    exact hSi (((withLoc L).nd.S_def i v).2 hmem)
  simp only [heckePol, sysPol, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [GlobalTheory.CoefDuty.ptSys, if_pos (hgen k hk), map_mul, map_pow, map_neg, map_one, map_natCast]
  rfl

end GlobalTheory.OSplitBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlagStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_bear_common_fullFlag : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p p' : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → p' ≫ f₁ = q ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p q → CoBear Eb S₁ φ₁ S₂ φ₂ (p' ≫ f₁) p' q → p = p' := by
  first | exact @GlobalTheory.FlagBundle.eq_of_coBear | exact GlobalTheory.FlagBundle.eq_of_coBear | (intros; apply GlobalTheory.FlagBundle.eq_of_coBear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_weilMatrixCoeff_finitePoint_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w, ∫ x in 𝓕, heisO ψ S T (actO S T p.1 p.2 w) f x * star (f x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ := by
  first | exact @GlobalTheory.Mem.CoefInv.eventually_coef_actO | exact GlobalTheory.Mem.CoefInv.eventually_coef_actO | (intros; apply GlobalTheory.Mem.CoefInv.eventually_coef_actO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.LocAdm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_finGL : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin n) (Fin n) (Af E) => 1 - matN n (sFin E) 1 + x.map (sFin E))

theorem t2Space_finiteAdeleRing_cmField : T2Space (FiniteAdeleRing (𝓞 E) E) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))

theorem t2Space_adeleRing_cmField : T2Space (Ad E) :=
  haveI := t2Space_finiteAdeleRing_cmField (E := E)
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))

theorem t2Space_adelicGL_cmField : T2Space (GA E n) :=
  haveI := t2Space_adeleRing_cmField (E := E)
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_UA : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := t2Space_adeleRing_cmField (E := E)
  show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 * (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
  exact isClosed_eq (((Units.continuous_val.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose.matrix_mul
    continuous_const).matrix_mul Units.continuous_val) continuous_const

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU n w ≤ finU E n := inf_le_left

theorem continuous_inclusion_locU (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (Subgroup.inclusion (locU_le_finU (n := n) w)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem isClosed_of_retract (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) : IsClosed ((locU n w : Subgroup (UA E n)) : Set (UA E n)) := by
  haveI := t2Space_adelicGL_cmField (E := E) (n := n)
  have e : ((locU n w : Subgroup (UA E n)) : Set (UA E n)) = {x | ((r x : locU n w) : UA E n) = x} := by
    ext x
    constructor
    · intro h
      exact congrArg Subtype.val (hx ⟨x, h⟩)
    · intro h
      change x ∈ locU n w
      rw [← show ((r x : locU n w) : UA E n) = x from h]
      exact (r x).2

  rw [e]
  exact isClosed_eq (continuous_subtype_val.comp hr) continuous_id

theorem isSmooth_loc (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) :
    IsSmooth (π.rep.comp (locU n w).subtype) := fun v => by
  have h := (π.isAut.aut v.1 v.2).level
  convert h.preimage (continuous_inclusion_locU (n := n) w) using 1
  ext k
  exact Subtype.ext_iff

theorem exists_compact_open (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) (L : Subgroup (finU E n)) (hL : IsOpen (L : Set (finU E n))) :
    ∃ K : Subgroup (locU n w), IsOpen (K : Set (locU n w)) ∧ IsCompact (K : Set (locU n w)) ∧
      K ≤ L.comap (Subgroup.inclusion (locU_le_finU w)) := by
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : locU n w →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (locU n w).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (locU n w) := U0.comap p ⊓ L.comap (Subgroup.inclusion (locU_le_finU w))
  have hKo : IsOpen (K : Set (locU n w)) :=
    (hU0o.preimage hp).inter (hL.preimage (continuous_inclusion_locU w))
  have hι : Topology.IsClosedEmbedding (fun x : locU n w => ((x : UA E n) : GA E n)) :=
    isClosed_UA.isClosedEmbedding_subtypeVal.comp (isClosed_of_retract w r hr hx).isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, (Subgroup.mem_inf.1 hx).1, ?_⟩, inf_le_right⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := (Subgroup.mem_inf.1 x.2).1
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_admissible_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n)
    (w : HeightOneSpectrum (𝓞 E)), ∃ σ : SmIrr (locU n w), IsAdmissible σ.ρ ∧
      IsCompAlong π.V (locU n w) (MonoidHom.id _) σ.ρ := by
  intro E _ _ _ n π w
  obtain ⟨r, hr, hrx, hrc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hadm := (GlobalTheory.T.definiteUnitary_admissible_finiteMultiplicity E n π).1
  let ρ : Representation ℂ (locU n w) π.V := π.rep.comp (locU n w).subtype
  let ρf : Representation ℂ (finU E n) π.V := π.rep.comp (finU E n).subtype
  have hρ : IsSmooth ρ := isSmooth_loc π w
  have hle := locU_le_finU (n := n) w
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.isAut.ne_bot
  let v0 : π.V := ⟨φ, hφ⟩
  have hv0 : v0 ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let L : Subgroup (finU E n) := LocEx.stab ρf v0
  have hLo : IsOpen (L : Set (finU E n)) := by
    convert (π.isAut.aut φ hφ).level using 1
    ext k
    exact Subtype.ext_iff
  have hLl : IsOpen ((L.comap (Subgroup.inclusion hle) : Subgroup (locU n w)) : Set (locU n w)) :=
    hLo.preimage (continuous_inclusion_locU w)
  obtain ⟨K, hKo, hKc, hKL⟩ := exists_compact_open w r hr hrx L hLo

  have hT : ∀ x : UA E n, ∀ (g : locU n w) (y : π.V),
      π.rep ((r x : UA E n)⁻¹ * x) (ρ g y) = ρ g (π.rep ((r x : UA E n)⁻¹ * x) y) := fun x g y => by
    change π.rep _ (π.rep (g : UA E n) y) = π.rep (g : UA E n) (π.rep _ y)
    rw [← Module.End.mul_apply, ← map_mul, (hrc x g).eq, map_mul, Module.End.mul_apply]
  have hst : ∀ x, ∀ y ∈ LocEx.nullPart ρ K, π.rep x y ∈ LocEx.nullPart ρ K := fun x y hy => by
    have h1 := LocEx.nullPart_act ρ K (r x) (LocEx.nullPart_comm ρ K (π.rep ((r x : UA E n)⁻¹ * x)) (hT x) hy)
    have e : π.rep x y = ρ (r x) (π.rep ((r x : UA E n)⁻¹ * x) y) := by
      change _ = π.rep (r x : UA E n) _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [e]
    exact h1
  have hφK : v0 ∈ fixed ρ K := LocEx.mem_fix.2 fun k hk => hKL hk
  have h2 : ∀ W : Submodule ℂ π.V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W ⊓ fixed ρ K = ⊥ → W = ⊥ := by
    intro W hW h
    rcases ((CuspRep.isIrreducible_iff _).1 π.isIrreducible_rep).2 (LocEx.nullPart ρ K) hst with h1 | h1
    · exact le_bot_iff.1 (h1 ▸ LocEx.le_nullPart hρ hKc W hW h)
    · exact absurd (LocEx.eq_zero_of_mem_nullPart hρ hKc hφK (h1 ▸ Submodule.mem_top)) hv0

  let M : Subgroup (UA E n) := L.map (finU E n).subtype ⊓ r.ker
  have hcomm : ∀ k ∈ M, ∀ g : locU n w, Commute k (g : UA E n) := fun k hk g => by
    have h := hrc k g
    rwa [MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hk).2, OneMemClass.coe_one, inv_one, one_mul] at h
  have hU : ∀ g, ∀ v ∈ fixed π.rep M, ρ g v ∈ fixed π.rep M := fun g v hv => LocEx.mem_fix.2 fun k hk => by
    change π.rep k (π.rep (g : UA E n) v) = π.rep (g : UA E n) v
    rw [← Module.End.mul_apply, ← map_mul, (hcomm k hk g).eq, map_mul, Module.End.mul_apply,
      LocEx.mem_fix.1 hv k hk]
  have hU0 : fixed π.rep M ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v0, LocEx.mem_fix.2 fun k hk => by
    obtain ⟨k', hk', rfl⟩ := (Subgroup.mem_inf.1 hk).1
    exact hk', hv0⟩
  have hfin : ∀ K' : Subgroup (locU n w), IsOpen (K' : Set (locU n w)) →
      FiniteDimensional ℂ ↥(fixed π.rep M ⊓ fixed ρ K') := fun K' hK' => by
    let r' : finU E n →* locU n w := r.comp (finU E n).subtype
    let H : Subgroup (finU E n) := L ⊓ (K' ⊓ L.comap (Subgroup.inclusion hle)).comap r'
    have hHo : IsOpen (H : Set (finU E n)) := hLo.inter ((hK'.inter hLl).preimage (hr.comp continuous_subtype_val))
    haveI := hadm H hHo
    refine Submodule.finiteDimensional_of_le (S₂ := fixed ρf H) fun v hv => LocEx.mem_fix.2 fun k hk => ?_
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨hkL, hkK, hkL'⟩ := And.intro (Subgroup.mem_inf.1 hk).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).2)
    have hcM : (r k : UA E n)⁻¹ * k ∈ M := by
      refine Subgroup.mem_inf.2 ⟨⟨(Subgroup.inclusion hle (r' k))⁻¹ * k, L.mul_mem (L.inv_mem hkL') hkL, rfl⟩, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrx (r k), inv_mul_cancel]
    have e1 := LocEx.mem_fix.1 hv1 _ hcM
    have e2 : π.rep (r k : UA E n) v = v := LocEx.mem_fix.1 hv2 _ hkK
    change π.rep (k : UA E n) v = v
    rw [← mul_inv_cancel_left (r k : UA E n) (k : UA E n), map_mul, Module.End.mul_apply, e1, e2]
  obtain ⟨σ, ⟨f, hf0, hf⟩, hσ⟩ := LocEx.exists_irred hρ hKo h2 (fixed π.rep M) hU hU0 hfin
  refine ⟨σ, hσ, σ.irred, π.V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun x v => ?_⟩
  · exact LinearMap.congr_fun e v
  · change (f (σ.ρ x v)).1 = _
    rw [hf]
    rfl

end GlobalTheory.DefU.LocAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ccr_operators_thetaFunctions : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  first | exact @GlobalTheory.Mem.Lift.exists_isCCR_theta | exact GlobalTheory.Mem.Lift.exists_isCCR_theta | (intros; apply GlobalTheory.Mem.Lift.exists_isCCR_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteMeasureReductionDomainInfinityStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_measure_reduction_domain_infinity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)), Submodule.IsLattice E Λ → ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure], ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E, (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧ ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  first | exact @GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | exact GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | (intros; apply GlobalTheory.GLInfReduction.exists_cover_of_finite_measure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreimagePositiveResidueDegreeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preimage_positive_residue_degree : ∀ (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g] [LocallyOfFiniteType g] (z : Z), z ∈ Set.range g → ∃ w, g w = z ∧ 0 < g.residueDegree w := by
  first | exact @GlobalTheory.exists_residueDegree_pos_of_mem_range | exact GlobalTheory.exists_residueDegree_pos_of_mem_range | (intros; apply GlobalTheory.exists_residueDegree_pos_of_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalLevelFormOfFaceLevelMultiplicityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalLevelForm_of_faceLevelMultiplicity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Tm : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)), Tm ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) → ∃ Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ, (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) ∧ R.cX.toMap R.prX Fn = Tm := by
  first | exact @GlobalTheory.MultLevelP.exists_form_of_mult | exact GlobalTheory.MultLevelP.exists_form_of_mult | (intros; apply GlobalTheory.MultLevelP.exists_form_of_mult <;> assumption)
end

