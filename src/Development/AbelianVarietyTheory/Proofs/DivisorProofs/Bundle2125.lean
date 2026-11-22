import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsBigSmallFactorBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleSeriesEqPhaseThetaKO
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
noncomputable section

namespace GlobalTheory.AdTh.VecSeries
open GlobalTheory.AdTh GlobalTheory.AdTh.PhaseMap

set_option maxHeartbeats 2000000 in

theorem singleSeries_eq_phase_thetaKO : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → IoExt R → ∀ (χ : (AE D)ˣ →* Circle) (ω : WeilRep D i), IsWeilTw R i χ ω → ∀ (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q Ω φ' → ∀ (ka : ℂ), GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → ∀ (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g' : ℕ) (Dc : GlobalTheory.Dict.Dic (T.Q.Dw ((i : ℕ) + 1)) T.Q.c (O i).s0 X g' (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (vr : GlobalTheory.Harm.Var X.Ψ (T.Q.Dw ((i : ℕ) + 1)).p X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.AdTh.IsVarOf (Vc D i) (Wc D i) X (T.Q.Dw ((i : ℕ) + 1)).p vr → ∀ (h : GA D (Vc D i)) (w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ (g γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → singleSeries R i ω φ' h ((O i).c0' y) w g = ka * thetaKO ω h (γ * g) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) φ' (MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hR i hOP hE χ ω hω Q Ω φ' hφ ka hka P y hy X g' Dc vr hM hp hv h w hw g γ hγ
  have hθ : IsInfFam R.θ := hR.models.inf
  have hstd := hOP.2.lift.std
  have hPr := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hR i A.μ0 hstd).1
  have hψ := hPr.weil.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A _ R F hR i A.μ0 hstd
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [gramAt_one hPr.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hPr.std], by simp⟩

  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' := by
    obtain ⟨⟨hψ', h0⟩, e, -, hth⟩ := hφ
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ' hθ hth h0.theta

  have hsub : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ P',
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f P' =
        pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f
          (MvPolynomial.aeval (fun k => ∑ b, MvPolynomial.C
              (if (k.2.1 : ℕ) < ((Wc D i).sig (tauE D k.1)).1 then (R.BV i k.1)⁻¹ k.2.2 b
                else (starRingEnd ℂ) ((R.BV i k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b)) P') := by
    intro f hf P'
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) (R.BV i) _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hBV τ)) f hf P'
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i A.μ0)) :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hPr.sigV hPr.sigW _ f1 f2
      (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A _ R F hR i hstd)

  have hlt : ∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, (vr (Dc.eL ℓ)).2.2 = ℓ.2.2 ∧
      ((ℓ.1 = tauE D (vr (Dc.eL ℓ)).1 ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = ℓ.2.1) ∨
        (ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (vr (Dc.eL ℓ)).1) ∧
          ((vr (Dc.eL ℓ)).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1)) := by
    intro ℓ
    have hP := hT.j.pins
    have hm : ∀ τ, τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0 := fun τ hτ => by
      unfold Datum.mult
      rw [if_neg fun h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 => hτ ((hM.psi τ).2
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ h)), hp]
    obtain ⟨h1, h2⟩ := GlobalTheory.AdTh.Dic.letter Dc (fun τ => RingHom.ext fun _ => rfl) hm ℓ
    obtain ⟨g1, g2, g3⟩ := hv (Dc.eL ℓ)
    refine ⟨g2.trans h1, ?_⟩
    rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩
    · rw [e1, Sum.elim_inl] at g3
      exact Or.inl ⟨e2.trans g1, g3.trans e3⟩
    · rw [e1, Sum.elim_inr] at g3
      exact Or.inr ⟨by rw [← g1]; exact e2, by rw [g3, e3]⟩

  have hio := hka (fun ℓ => vr (Dc.eL ℓ)) hlt w hw A.μ0 y
  have hpol : MvPolynomial.rename (fun ℓ => vr (Dc.eL ℓ)) (MvPolynomial.map (inC (O i).c') ((O i).io y)) =
      MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) := by
    rw [hy, MvPolynomial.rename_rename]
    exact congrArg (MvPolynomial.rename _) (MvPolynomial.map_map _ _ _)

  have hS : (MvPolynomial.aeval (fun k => ∑ b, MvPolynomial.C
              (if (k.2.1 : ℕ) < ((Wc D i).sig (tauE D k.1)).1 then (R.BV i k.1)⁻¹ k.2.2 b
                else (starRingEnd ℂ) ((R.BV i k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b))) (R.ioP i (PiTensorProduct.tprod ℂ w) ((O i).c0' y)) =
      ka • MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) := by
    apply hinj
    rw [map_smul, ← hsub _ f1, ← hpol]
    exact hio

  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) φ' (MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)))) :=
    GlobalTheory.FockTheta.ptStable D R.ψ R.θ hψ hθ _ _ _ _ _ _ φ' _ hthφ
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → thetaKO ω h g f = thetaKO ω h (γ * g) f := fun f hf => by
    have e1 : ((h, γ * g) : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g) := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  have hsm : ∀ k f, thetaKO ω h k (ka • f) = ka * thetaKO ω h k f := fun k f => by
    rw [thetaKO, thetaKO, map_smul]
    rfl
  show thetaKO ω h g (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) φ' (R.ioP i (PiTensorProduct.tprod ℂ w) ((O i).c0' y))) = _
  rw [hsub _ hthφ, hS, map_smul, hsm, hmove _ hth]

end GlobalTheory.AdTh.VecSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvZeroUniq

open scoped Classical

theorem proj_zero_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AF F) i).1) = 0 := by
    funext i
    exact map_zero _
  have h2 : (fun i => ((0 : κ → AF F) i).2) = 0 := rfl
  show pureA F f g 0 = _
  rw [pureA, h1, h2]
  simp [mul_comm]

theorem schr_mem_schA {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have h2 := GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace ψ hψ w.2 _ (GlobalTheory.SchwartzTranslate.main F κ w.1 Φ hΦ)
  have : schr ψ w Φ = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) • (fun x => ψ (x ⬝ᵥ w.2) * Φ (x + w.1)) := by
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul, AddChar.map_add_eq_mul]
    ring
  rw [this]
  exact Submodule.smul_mem _ _ h2

theorem apply_eq_rho {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (f : (κ → AF F) → ℂ)
    (x : κ → AF F) : f x = dc.rho ψ (dc.e.symm (x, 0)) f 0 := by
  simp [Darboux.rho, schr]

theorem rho_apply_zero {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (f : (κ → AF F) → ℂ)
    (z : W) (hz : (dc.e z).1 = 0) : dc.rho ψ z f 0 = f 0 := by
  simp [Darboux.rho, schr, hz]

theorem uniqB : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ l l' : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) → l' ∈ (adeleClass F).adm (Fin n × Fin d) →
      (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ ∧ l' (M.co.rho B.ψ u Φ) = l' Φ) →
      (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l Φ ∧
        l' (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l' Φ) →
      (∃ Φ ∈ schA F (Fin n × Fin d), l' Φ ≠ 0) → ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l Φ = c * l' Φ := GlobalTheory.T.skew_adapted_pair_restriction_eigen

theorem evNe : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := GlobalTheory.T.eigen_intertwiner_extension

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ S : Fn F n d →ₗ[ℂ] Fn F n d₁, (∀ Φ ∈ schA F (Fin n × Fin d), S Φ ∈ schA F (Fin n × Fin d₁)) →
        (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (S Φ)) →
        (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ u Φ) = S Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁), l ∘ₗ S ∈ (adeleClass F).adm (Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), S Φ = c • e Φ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ e he S _ hSheis hSinv hSadm
  have hstd : IsStd B.ψ := hP.base.std
  let δ : Fn F n d₁ →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδ : δ ∈ (adeleClass F).adm (Fin n × Fin d₁) := proj_zero_mem_adm F _
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => schr_mem_schA _ hstd _ hΦ
  have hδe : ∀ (f : Fn F n d₁) x, f x = δ (M₁.co.rho B.ψ (M₁.co.e.symm (x, 0)) f) := fun f x => apply_eq_rho _ _ f x
  have hfix : ∀ z, (M₁.co.e z).1 = 0 → ∀ f : Fn F n d₁, δ (M₁.co.rho B.ψ z f) = δ f :=
    fun z hz f => rho_apply_zero _ _ f z hz
  obtain ⟨Φ₀, hΦ₀, hne⟩ := evNe F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  obtain ⟨x₀, hx₀⟩ : ∃ x, e Φ₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨c, hc⟩ := uniqB hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁
    (δ ∘ₗ S) (δ ∘ₗ e) (hSadm δ hδ) (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he δ hδ)
    (fun u hu Φ hΦ => ⟨by simp only [LinearMap.comp_apply]; rw [hSinv u hu Φ hΦ],
      by simp only [LinearMap.comp_apply]; rw [he.inv u hu Φ hΦ]⟩)
    (fun z hz Φ hΦ => ⟨by simp only [LinearMap.comp_apply]; rw [hSheis z Φ hΦ, hfix z hz],
      by simp only [LinearMap.comp_apply]; rw [he.Heisenberg₂ z Φ hΦ, hfix z hz]⟩)
    ⟨_, hρ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (x₀, 0) * (incM F H'.ι)ᵀ) Φ₀ hΦ₀, by
      simp only [LinearMap.comp_apply]
      rw [he.Heisenberg₂ _ Φ₀ hΦ₀, ← hδe]
      exact hx₀⟩
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (x, 0) * (incM F H'.ι)ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hSheis _ Φ hΦ, he.Heisenberg₂ _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

end GlobalTheory.EvZeroUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockBound
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameAut

theorem norm_val_of_orderDvd {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n)
    (v : HeightOneSpectrum (𝓞 E)) : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : (χ.val v) ^ n = 1 := by
    have h2 := congrArg (fun ψ : Formalism.L2.Host.HChar E => ψ.val v) h
    simpa [Formalism.L2.Host.HChar.val, Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc] using h2
  have h3 : ((χ.val v : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h3 hn.ne'

theorem norm_sq_valTw_half {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (h : χ.IsUnitary)
    (v : HeightOneSpectrum (𝓞 E)) : ‖χ.valTw (1 / 2) v‖ ^ 2 = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have h1 : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := h _
  have hq : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have hq' : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast hq
  rw [Formalism.L2.Host.HChar.valTw, norm_mul, h1, one_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re, Complex.ofReal_re,
    ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, ← Real.rpow_neg_one]
  norm_num

theorem norm_sq_firstValA {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    (j : Fin D.R.m) (t : T) (P : Pl0) (hP : P ∈ A.ok t) :
    ‖D.what₂.embLL (Formalism.L2.Col.firstValA (A.muVal j t) A.etaVal A.q A.r P)‖ ^ 2 = (A.q P : ℝ) ^ A.r := by
  obtain ⟨hQ, -, -, h4⟩ := GlobalTheory.GoodPrimes.good_primes R F hL
  have hq := (h4 hF t P hP).2.2
  obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
  have hP0 : P ∈ A.ok A.μ0 := by
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    refine (hT.ok _ P).2 ?_
    rw [hQ, Finset.coe_empty, Set.union_empty]
    exact ⟨h1, fun h => h2 (Or.inl h), fun Q h => h3 Q (Or.inl h)⟩
  have hmu : ‖D.what₂.embLL (A.muVal j t P : D.what₂.LL)‖ = 1 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    rw [hF.muVal j t P hP, Formalism.L2.Host.HChar.val_mul, Units.val_mul, norm_mul, norm_val_of_orderDvd _ hn ho, mul_one]
    exact (R.C.isMu0 j).unitary _
  have heta : ‖D.what₂.embLL (A.etaVal P : D.what₂.LL)‖ ^ 2 = (A.q P : ℝ)⁻¹ := by
    rw [hF.etaVal P hP0, hq]
    exact norm_sq_valTw_half _ R.C.isEta.unitary _
  have hq0 : (A.q P : ℝ) ≠ 0 := by
    rw [hq]
    exact_mod_cast fun e => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  obtain ⟨s, hs⟩ : Odd A.r := hT.ranks.2.1 ▸ Formalism.L2.NTheta.odd_r D.R
  have hd : (A.r + 1) / 2 = s + 1 := by omega
  unfold Formalism.L2.Col.firstValA
  rw [hd, hs]
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Units.val_inv_eq_inv_val, map_inv₀, norm_inv, hmu, inv_one, one_mul,
    mul_pow, heta, Complex.norm_natCast]
  field_simp
  ring

theorem norm_sq_blockValue : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ ν hν Q
  have h := norm_sq_firstValA p.R.toRealDat p.F.lv2 p.charW.base.lev p.charW.base.fam j (p.R.mu w) Q.1 Q.2
  obtain rfl : ν = fun Q => Formalism.L2.Col.firstValA (p.P.A3.A.muVal j (p.R.mu w)) p.P.A3.A.etaVal p.P.A3.A.q p.P.A3.A.r Q.1 :=
    List.mem_singleton.1 hν
  have e : (blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t = p.P.A3.A.r := Nat.add_sub_cancel ..
  rw [e]
  exact h

end GlobalTheory.FrameAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockDecomposition
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameLab

variable {D : D7}

theorem cO_cO (x : 𝓞 D.host.E) : Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E x) = x :=
  RingOfIntegers.ext (star_star (x : D.host.E))

theorem mem_conjPl_of_fixed (P : HeightOneSpectrum (𝓞 D.host.E)) {x : 𝓞 D.host.E} (hx : Formalism.DivisionValues.cO D.host.E x = x) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x ∈ P.asIdeal := by
  change x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := by rw [← cO_cO y, e, hx]
    rwa [← this]
  · exact fun h => ⟨x, h, hx⟩

theorem under_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl P).under (𝓞 (maximalRealSubfield D.host.E)) = P.under (𝓞 (maximalRealSubfield D.host.E)) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  exact mem_conjPl_of_fixed P (x := algebraMap _ (𝓞 D.host.E) x)
    (RingOfIntegers.ext (IsCMField.complexConj_apply_eq_self D.host.E (x : maximalRealSubfield D.host.E)))

theorem absNorm_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal _ (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem labels_ok : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ Q
  obtain ⟨-, h2, h3⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam (p.R.mu w) Q.1 Q.2
  refine ⟨⟨plOf p j (p.R.mu w) Q, fun e => h2 e.symm, (under_conjPl _).symm⟩, under_conjPl _,
    (absNorm_conjPl _).trans h3.symm, mem_conjPl_of_fixed _ (map_natCast _ _)⟩

end GlobalTheory.FrameLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceFiniteSet
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameAutCof

theorem sub_mem_of_prime_norm {K : Type} [Field K] [NumberField K] (σ : 𝓞 K →+* 𝓞 K) (I : Ideal (𝓞 K))
    (hp : (Ideal.absNorm I).Prime) (hI : I.map σ ≤ I) (x : 𝓞 K) : σ x - x ∈ I := by
  have hc : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Fact (Ideal.absNorm I).Prime := ⟨hp⟩
  have : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  have := Fintype.ofFinite (𝓞 K ⧸ I)
  let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ I) hp (by rw [← Nat.card_eq_fintype_card, hc])
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (e.symm (Ideal.Quotient.mk I x))
  have h1 : x - (n : 𝓞 K) ∈ I := by
    rw [← Ideal.Quotient.eq, map_intCast]
    apply e.symm.injective
    rw [map_intCast, hn]
  have h2 : σ x - (n : 𝓞 K) ∈ I := by
    have := hI (Ideal.mem_map_of_mem σ h1)
    rwa [map_sub, map_intCast] at this
  have := I.sub_mem h2 h1
  rwa [sub_sub_sub_cancel_right] at this

theorem finite_fixed {K : Type} [Field K] [NumberField K] [StarRing K] (h : ∃ x : K, star x ≠ x) :
    {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal).Prime ∧ Formalism.DivisionValues.conjPl v = v}.Finite := by
  have hx : ∃ x : 𝓞 K, Formalism.DivisionValues.cO K x - x ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨y, hy⟩ := h
    apply hy
    have h0 : ∀ a : 𝓞 K, star (a : K) = a := fun a => congrArg (fun z : 𝓞 K => (z : K)) (sub_eq_zero.1 (hn a))
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
    rw [star_div₀]
    exact congrArg₂ (· / ·) (h0 a) (h0 b)
  obtain ⟨x, hx⟩ := hx
  refine (Ideal.finite_factors (I := Ideal.span {Formalism.DivisionValues.cO K x - x}) (by simpa using hx)).subset ?_
  rintro v ⟨hp, hv⟩
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact sub_mem_of_prime_norm (Formalism.DivisionValues.cO K : 𝓞 K →+* 𝓞 K) v.asIdeal hp
    (le_of_eq (congrArg HeightOneSpectrum.asIdeal hv)) x

theorem exists_star_ne (D : D7) : ∃ x : D.host.E, star x ≠ x := by
  by_contra hn
  push Not at hn
  apply IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  exact hn x

theorem cofinite_labels {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (GlobalTheory.ExpTie.blk p j t).Pl, ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t Q).asIdeal ∧ labOf p j t Q = v}.Finite := by
  obtain ⟨gR, c0R, c0L, hTie⟩ := p.charW.base.fam.tie
  have honto := p.charW.base.fam.pl_onto
  have hcc : ∀ v : HeightOneSpectrum (𝓞 D.host.E), Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl v) = v := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl
  have hinj : Function.Injective (Formalism.DivisionValues.conjPl (K := D.host.E)) := Function.Involutive.injective hcc
  set S : Set (HeightOneSpectrum (𝓞 D.host.E)) := (p.R.Sb : Set (Pl D.host.E)) ∪ (p.R.Q t : Set (Pl D.host.E)) with hS
  have hSf : S.Finite := hTie.S_fin.union (Finset.finite_toSet _)
  have hlf : {v : HeightOneSpectrum (𝓞 D.host.E) | v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa using hl)
  refine (((finite_fixed (exists_star_ne D)).union hSf).union ((hSf.union hlf).preimage hinj.injOn)).subset ?_
  rintro v ⟨hp, hv⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, not_or, not_and, Ideal.dvd_span_singleton] at hn
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hn
  have hci : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (Formalism.DivisionValues.conjPl v).asIdeal = v.asIdeal := by
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hcc]
  have hoff : Bridge.SplitOff (D := D) (Formalism.DivisionValues.conjPl v) S := by
    refine ⟨?_, h3, fun Q hQ he => h2 ?_⟩
    · rw [hci]
      exact fun he => h1 hp (HeightOneSpectrum.ext he).symm
    · rw [hci] at he
      exact HeightOneSpectrum.ext he ▸ hQ
  obtain ⟨P, hP⟩ := honto (Formalism.DivisionValues.conjPl v) ⟨hoff.1, fun h => hoff.2.1 (Or.inl h), fun Q hQ => hoff.2.2 Q (Or.inl hQ)⟩
  have hok := (hTie.ok t P).2 (hP ▸ hoff)
  have e1 : plOf p j t ⟨P, hok⟩ = Formalism.DivisionValues.conjPl v := hP
  refine hv ⟨⟨P, hok⟩, ?_, ?_⟩
  · rw [e1]; exact h4
  · show Formalism.DivisionValues.conjPl (plOf p j t ⟨P, hok⟩) = v
    rw [e1, hcc]

theorem cofinite_labels_at : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite :=
  fun p _ _ j _ _ _ _ w _ _ hs => cofinite_labels p j (p.R.mu w) hs.1.ne_zero

end GlobalTheory.FrameAutCof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsBigSmallFactorBoundsStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExponents_bigSmallFactorBounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), ∀ (F k m n B : ℕ) (Sg : ℝ) (u : GlobalTheory.AllWt.Weight Dw), Shape Dw F k m → k ≤ Dw.p + 1 → WtBd Dw k n u B Sg → ExpBd Dw k (gap Dw (thA Dw u n)) (B + 1) (F * (Sg + 2 * Dw.q * B)) (2 * B + 1) := by
  first | exact @GlobalTheory.RefSum.ThetaExp.expBd_thA | exact GlobalTheory.RefSum.ThetaExp.expBd_thA | (intros; apply GlobalTheory.RefSum.ThetaExp.expBd_thA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtFiniteSetStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_trivial_at_finite_set : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat g - 1) = 0) →
    (∀ u : AF F, (∀ w ∈ S, evFin F w u = 0) → u • (mat h - 1) = 0) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ φ₂ : ∀ w : Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ w, φ₂ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ w, w ∉ S → φ₂ w = φ w) ∧ om' (g, h) (pure f φ) = pure f φ₂ := by
  first | exact @GlobalTheory.PureStabFin.pure_stab_fin | exact GlobalTheory.PureStabFin.pure_stab_fin | (intros; apply GlobalTheory.PureStabFin.pure_stab_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackPolynomialRightActionOfCocycleStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPullbackPolynomial_rightAction_of_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (a : U → C → ℂˣ), (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) → tw M (fun c => (a 1 c : ℂ)) 1 = AlgHom.id ℂ _ ∧ ∀ u v : U, (tw M (fun c => (a v c : ℂ)) v).comp (tw M (fun c => (a u c : ℂ)) u) = tw M (fun c => (a (u * v) c : ℂ)) (u * v) := by
  first | exact @GlobalTheory.CuspEmb.tw_law | exact GlobalTheory.CuspEmb.tw_law | (intros; apply GlobalTheory.CuspEmb.tw_law <;> assumption)
end

