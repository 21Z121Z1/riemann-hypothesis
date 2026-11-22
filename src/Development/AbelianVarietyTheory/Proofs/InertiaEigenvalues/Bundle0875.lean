import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0873
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmVecEqPhaseLetters
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SerLetters

theorem coord_mem_fieldRange {ι K J : Type} [Field K] [Fintype J] (σ : K →+* ℂ) (e : J → MvPolynomial ι K)
    (hli : LinearIndependent ℂ fun j => MvPolynomial.map σ (e j)) (a : J → ℂ)
    (hx : ∀ m, MvPolynomial.coeff m (∑ j, a j • MvPolynomial.map σ (e j)) ∈ σ.fieldRange) (j : J) :
    a j ∈ σ.fieldRange := by
  classical
  by_contra hj
  letI : Algebra K ℂ := σ.toAlgebra
  let p : Submodule K ℂ := LinearMap.range (Algebra.linearMap K ℂ)
  have hp : ∀ z ∈ σ.fieldRange, z ∈ p := fun z hz => by
    obtain ⟨y, rfl⟩ := RingHom.mem_fieldRange.1 hz
    exact ⟨y, rfl⟩
  have hnot : a j ∉ p := fun h => hj (by obtain ⟨y, hy⟩ := h; exact RingHom.mem_fieldRange.2 ⟨y, hy⟩)
  obtain ⟨π, hπ, hπp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hπ0 : ∀ z ∈ p, π z = 0 := fun z hz => by
    have : π z ∈ p.map π := Submodule.mem_map_of_mem hz
    rwa [hπp, Submodule.mem_bot] at this
  have hsum : ∑ k, π (a k) • e k = 0 := by
    ext m
    have h1 := hπ0 _ (hp _ (hx m))
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, map_sum] at h1
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : a k * σ (MvPolynomial.coeff m (e k)) = MvPolynomial.coeff m (e k) • a k := by
      rw [Algebra.smul_def]; exact mul_comm _ _
    rw [e1, map_smul, smul_eq_mul, mul_comm]
  have h2 : ∑ k, σ (π (a k)) • MvPolynomial.map σ (e k) = 0 := by
    have := congrArg (MvPolynomial.map σ) hsum
    simpa [map_sum, MvPolynomial.smul_eq_C_mul, MvPolynomial.map_C] using this
  have h3 := Fintype.linearIndependent_iff.1 hli _ h2 j
  exact hπ ((map_eq_zero σ).1 h3)

end GlobalTheory.SerLetters

section Letters1
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerLetters
open GlobalTheory.AdTh.PhaseMap GlobalTheory.AdTh.PhaseMapFree

set_option maxHeartbeats 1600000 in

theorem io_eq_phase_smul_letters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ i : Fin D.R.m, VStd D i → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, GlobalTheory.AdTh.PhaseMap.IsLt lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ io : VsV D i T.Q.c.F →ₗ[T.Q.c.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F, (∀ v, io v ∈ Submodule.span T.Q.c.F (HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank T.Q.c.F ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j)))) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v : VsV D i T.Q.c.F, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v))) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f (GlobalTheory.AdTh.PhaseMap.toF T.Q.c lt (io v)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hFam hM hP hT i hstd u hu c0 hc lt hl
  have hθ : IsInfFam R.θ := hM.inf
  have hcV : (R.cV i).Is := hM.cV i
  have hPr := isPair_of_clauses D G Pl0 T0 A _ R hL hM hP i A.μ0 hstd
  have hψ := hPr.weil.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := vec_fock_of_clauses D G Pl0 T0 A _ R hM hP i A.μ0 hstd
  obtain ⟨io, hw, hio⟩ := GlobalTheory.CoefMapRecord.exists_io_record D T.Q hT.laws.pins κ hT.kap i T.Q.c
  obtain ⟨hwok, cga, i1, i2, irng, i3, -, -, i4, -⟩ := hio
  obtain ⟨n1, n2, n3, n4, hc0⟩ := GlobalTheory.T.complexCoefficientMap_coreField_properties D G Pl0 T0 A T R κ v₀ hT i hstd c0 hc hw hwok
  obtain ⟨r1, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hM.vpos i) hPr.sigV hcV
  obtain ⟨-, -, w1, w2, w3⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hty : IsTyp D T.Q.H := ⟨w1, w2⟩
  obtain ⟨d1, d2, -⟩ := hT.laws.pins.2.2.2 _ (inR i)
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨u₀, w₀, hu₀, hw₀, hΔ⟩ : ExtremalVectorPairsToDelta R i (v₀ i (sg0 D A)) :=
    (hT.hv₀ i (sg0 D A)).2 rfl (GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hL hFam hM hP i)
  obtain rfl : u = u₀ := funext fun ρ => Subtype.ext ((hu ρ).trans (hu₀ ρ).symm)
  clear hu₀
  have hioP := (hP.ioP i A.μ0).1
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hM.BV i τ
    rw [gramAt_one hPr.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hPr.std], by simp⟩
  let PTf := fun f => pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1)
    (onb (R.MW i (sg0 D A))) f
  let PT := PTf (R.vP i A.μ0)
  have hsub : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ),
      (∀ τ, (U τ)ᴴ * U τ = 1) → ∀ P,
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) U (onb (R.MW i (sg0 D A))) f P =
        PTf f (GlobalTheory.AdTh.PhaseMap.sub (fun τ => ((Wc D i).sig (tauE D τ)).1) U P) := fun f hf U hU P => by
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) U _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hU τ)) f hf P
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective PT :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hPr.sigV hPr.sigW _ f1 f2
      (thetaVector_ne_zero_of_clauses D G Pl0 T0 A _ R hL hP i)
  obtain ⟨g, hg, hgB⟩ : ∃ g ∈ GinfC (Vc D i), ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) g) = R.BV i τ :=
    (GlobalTheory.SmoothForms.RealPts.glue R.θ hθ (Vc D i)).2 (R.BV i) fun τ => by
      show (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = gramAt D (Vc D i) τ
      rw [gramAt_one hPr.std, Matrix.mul_one, hBV]
  obtain ⟨χ, hχ, hχg⟩ := om_real hPr f4 f3 f5 f1 f2 hg
  rw [funext hgB] at hχg
  let A₀ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i A.μ0) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)
  have hA₀ : ∀ a ∈ GinfC (Vc D i), ∀ w, A₀ ((R.cV i).ρ a w) = R.ωP i A.μ0 (a, 1) (A₀ w) :=
    fun a ha w => (hioP a ha _ w).symm
  have hw₁ : A₀ ((R.cV i).ρ g⁻¹ (χ • w₀)) = PT (RealDat.Delta i) := by
    have h1 : A₀ (χ • w₀) = R.ωP i A.μ0 (g, 1) (PT (RealDat.Delta i)) := by
      rw [map_smul, hχg, ← hΔ]
      rfl
    rw [hA₀ _ (inv_mem hg), h1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
    exact congrArg (fun T : Module.End ℂ _ => T _) (map_one (R.ωP i A.μ0))
  have hn₁ : ‖(R.cV i).ρ g⁻¹ (χ • w₀)‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hcV.2.1, ← norm_eq_sqrt_re_inner, norm_smul, hχ, hw₀, mul_one]
  haveI := hcV.2.2.2.1
  haveI : FiniteDimensional T.Q.c.F (VsV D i T.Q.c.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i))
  let c0' : VsV D i T.Q.c.F →ₛₗ[inC T.Q.c] (R.cV i).W :=
    { toFun := fun v => c0 (GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) v)
      map_add' := fun v w => by
        rw [← map_add]
        congr 1
        exact Subtype.ext (map_add (MvPolynomial.map (inC T.Q.c)) _ _)
      map_smul' := fun a v => by
        rw [← map_smul]
        congr 1
        apply Subtype.ext
        show MvPolynomial.map (inC T.Q.c) (a • (v : Pol T.Q.c.F D.what₂.Tau (Vc D i).rank)) =
          (inC T.Q.c a) • MvPolynomial.map (inC T.Q.c) (v : Pol T.Q.c.F D.what₂.Tau (Vc D i).rank)
        rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C] }
  have n1' : ‖c0' hw‖ = 1 := n1
  have n2' : ∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v,
      c0' (rhoM T.Q.c (fun τ => embF T.Q.c (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (c0' v) := n2
  have n3' : Submodule.span ℂ (Set.range c0') = ⊤ := n3
  have hsm : ∀ (a : T.Q.c.F) P, toF T.Q.c lt (a • P) = (a : ℂ) • toF T.Q.c lt P := fun a P => by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, toF_C, MvPolynomial.smul_eq_C_mul]
  obtain ⟨B₀, hB₀⟩ := exists_ext c0' n4
    { toFun := fun v => toF T.Q.c lt (io v)
      map_add' := fun v w => by rw [map_add, map_add]
      map_smul' := fun a v => by rw [map_smul, hsm]; rfl }
  replace hB₀ : ∀ v, B₀ (c0' v) = toF T.Q.c lt (io v) := hB₀
  have hpG : toF T.Q.c lt (io hw) = RealDat.Delta i := by
    rw [i4]
    refine toF_pG T.Q.c hl hty i1 _ _ _ _ _ (fun τ => by rw [hsig, d1]) (fun τ => by rw [hsig, d2]) (fun τ k hk => ?_)
      fun τ k hk => ?_
    · rw [d1] at hk
      exact (w3 τ k).1.trans ((dif_pos hk).trans ((hT.kap i τ).1 ⟨k, hk⟩))
    · rw [d2] at hk
      exact (w3 τ k).2.trans ((dif_pos hk).trans ((hT.kap i τ).2.1 ⟨k, hk⟩))
  have hne : PT (B₀ (c0' hw)) ≠ 0 := fun h => by
    rw [hB₀, map_eq_zero_iff _ hinj, map_eq_zero_iff _ (toF_injective T.Q.c hl hty), map_eq_zero_iff _ i2] at h
    rw [h, map_zero, norm_zero] at n1'
    exact zero_ne_one n1'
  have hwz : A₀ ((R.cV i).ρ g⁻¹ (χ • w₀)) = (PT ∘ₗ B₀) (c0' hw) := by rw [hw₁, LinearMap.comp_apply, hB₀, hpG]
  have hAeq : ∀ γ : GQ (Vc D i), ∃ s : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ),
      ∀ w, A₀ ((R.cV i).ρ γ w) = s (A₀ w) := fun γ => by
    obtain ⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩ := rat_parts hθ hPr.std γ
    have h7 : (R.cV i).ρ γ = (R.cV i).ρ a := by rw [h4, map_mul, hcV.1 k h3, mul_one]
    exact ⟨R.ωP i A.μ0 (a, 1), fun w => by rw [h7, hA₀ a h2]⟩
  have hAi : Function.Injective A₀ := by
    rw [← LinearMap.ker_eq_bot]
    refine (r2 _ fun γ => ?_).resolve_right fun h => hne ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, hs⟩ := hAeq γ
      have hx' : A₀ x = 0 := hx
      show A₀ ((R.cV i).ρ γ x) = 0
      rw [hs, hx', map_zero]
    · rw [← LinearMap.comp_apply, ← hwz]
      exact (h ▸ Submodule.mem_top : (R.cV i).ρ g⁻¹ (χ • w₀) ∈ LinearMap.ker A₀)
  obtain ⟨a, ha, ha'⟩ := proportional ((R.cV i).ρ.comp (GQ (Vc D i)).subtype) _ r1 (fun γ hγ => hγ) r2 A₀ (PT ∘ₗ B₀)
    (fun γ => by
      obtain ⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩ := rat_parts hθ hPr.std γ
      obtain ⟨x, hx, hxa⟩ := om_real hPr f4 f3 f5 f1 f2 h2
      have hx0 : x ≠ 0 := fun h => by simp [h] at hx
      have h7 : (R.cV i).ρ γ = (R.cV i).ρ a := by rw [h4, map_mul, hcV.1 k h3, mul_one]
      refine ⟨R.ωP i A.μ0 (a, 1), (cga γE.val : ℂ) * x⁻¹, fun w => ?_, fun w => ?_⟩
      · show A₀ ((R.cV i).ρ γ w) = _
        rw [h7, hA₀ a h2]
      · have h8 : (PT ∘ₗ B₀) ∘ₗ (R.cV i).ρ γ =
            ((cga γE.val : ℂ) * x⁻¹) • (R.ωP i A.μ0 (a, 1) ∘ₗ (PT ∘ₗ B₀)) := by
          refine LinearMap.ext_on_range n3' fun v => ?_
          simp only [LinearMap.comp_apply, LinearMap.smul_apply]
          rw [← n2' γ γE h1, hB₀, hB₀, i3 _ h5, hsm, hxa, hsub _ f1 _ (compAt_unitary hθ hPr.std a), smul_smul,
            inv_mul_cancel_right₀ hx0, map_smul,
            toF_gaStar T.Q.c hl hty (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => by rw [hsig, d1]) _ _ h6]
        exact LinearMap.congr_fun h8 w)
    ((R.cV i).ρ g⁻¹ (χ • w₀)) (c0' hw) hwz hne
  have h9 : ∀ x, GlobalTheory.AdTh.PhaseMap.sub (fun τ => ((Wc D i).sig (tauE D τ)).1) (R.BV i) (R.ioP i (PiTensorProduct.tprod ℂ u) x) =
      a • B₀ x := fun x => hinj (by rw [← hsub _ f1 _ hBV, map_smul]; exact ha x)
  have hB₀i : Function.Injective B₀ := fun x y hxy => hAi (by rw [ha, ha, LinearMap.comp_apply, LinearMap.comp_apply, hxy])
  refine ⟨a, ?_, io, fun v => irng ▸ LinearMap.mem_range_self io v, fun f hf v => ?_⟩
  · rw [← n1', ← ha', norm_smul, hn₁, mul_one]
  · rw [hsub f hf _ hBV, h9, map_smul, ← hB₀ v]
    rfl

end GlobalTheory.SerLetters
end Letters1

section Letters2
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerLetters

theorem map_mem_HHa {T0 : Type} {r : T0 → ℕ} {n : ℕ} {k K : Type} [Field k] [CharZero k] [Field K] (φ : k →+* K)
    {cc : T0 → T0} {isX : T0 → Prop} {a : T0 → ℕ → ℕ} {P : MvPolynomial (Letter T0 r n) k} (h : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map φ P ∈ HHa r n K cc isX a := by
  haveI : Infinite k := Infinite.of_injective (fun m : ℕ => (m : k)) Nat.cast_injective
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map φ h.1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rowInv_map φ h.2.1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rowDeg_map φ h.2.2⟩

end GlobalTheory.SerLetters
end Letters2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
section
open NumberField IsDedekindDomain GlobalTheory.JSW
open scoped ENNReal

noncomputable section
namespace GlobalTheory.RSPole.EulerPole

open Filter Topology GlobalTheory.RSPole

theorem schurAt_const_zero {n : ℕ} (a : Fin n → ℂ) : GlobalTheory.JSW.schurAt (fun _ => 0) a = 1 := by
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem one_le_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) : 1 ≤ schurDir q a x := by
  unfold schurDir
  refine le_trans ?_ (ENNReal.le_tsum ⟨fun _ => 0, antitone_const⟩)
  simp [schurAt_const_zero]

theorem hasProd_of_one_le {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) :
    HasProd f (⨆ s : Finset I, ∏ i ∈ s, f i) :=
  tendsto_atTop_iSup fun _ _ hst => Finset.prod_le_prod_of_subset_of_one_le' hst fun i _ _ => hf i

theorem finset_prod_le_tprod {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (s : Finset I) :
    ∏ i ∈ s, f i ≤ ∏' i, f i := by
  rw [(hasProd_of_one_le f hf).tprod_eq]; exact le_iSup (fun s : Finset I => ∏ i ∈ s, f i) s

theorem le_tprod_of_one_le {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (i : I) : f i ≤ ∏' i, f i := by
  simpa using finset_prod_le_tprod f hf {i}

theorem hasProd_toReal {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfin : ∏' i, f i ≠ ⊤) :
    HasProd (fun i => (f i).toReal) (∏' i, f i).toReal := by
  have h := hasProd_of_one_le f hf
  rw [← h.tprod_eq] at h
  have := (ENNReal.tendsto_toReal hfin).comp h
  simpa [HasProd, Function.comp_def, ENNReal.toReal_prod] using this

theorem schurAt_conj {n : ℕ} (l : Fin n → ℕ) (a : Fin n → ℂ) :
    GlobalTheory.JSW.schurAt l (fun i => starRingEnd ℂ (a i)) = starRingEnd ℂ (GlobalTheory.JSW.schurAt l a) := by
  rw [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schurAt, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Filter Topology GlobalTheory.RSPole

def schurTerm (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) : ℝ :=
  ‖GlobalTheory.JSW.schurAt l.1 a‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x))

theorem schurTerm_nonneg (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (l) : 0 ≤ schurTerm q a x l := by
  unfold schurTerm; positivity

theorem schurDir_eq (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) :
    schurDir q a x = ∑' l, ENNReal.ofReal (schurTerm q a x l) := rfl

theorem summable_schurTerm (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (hfin : schurDir q a x ≠ ⊤) :
    Summable (schurTerm q a x) := by
  rw [schurDir_eq] at hfin
  exact (ENNReal.summable_toReal hfin).congr fun l => ENNReal.toReal_ofReal (schurTerm_nonneg q a x l)

theorem toReal_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) :
    (schurDir q a x).toReal = ∑' l, schurTerm q a x l := by
  rw [schurDir_eq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun l => ENNReal.toReal_ofReal (schurTerm_nonneg q a x l)

theorem term_eq (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo le_rfl l.1) (fun i => (α i : ℂ)) *
      GlobalTheory.JSW.schurAt l.1 (fun j => (((Units.map (starRingEnd ℂ).toMonoidHom ∘ α) j : ℂˣ) : ℂ)) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) = ((schurTerm q (fun i => (α i : ℂ)) x l : ℝ) : ℂ) := by
  rw [GlobalTheory.JSW.padTo_self]
  have h1 : (fun j => (((Units.map (starRingEnd ℂ).toMonoidHom ∘ α) j : ℂˣ) : ℂ)) =
      fun j => starRingEnd ℂ (α j : ℂ) := by
    funext j; simp
  rw [h1, schurAt_conj, Complex.mul_conj']
  have h2 : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]; push_cast; rfl
  have h3 : (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)) = ((q : ℝ) ^ (-x)) ^ (∑ i, l.1 i) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]; ring_nf
  rw [h2, schurTerm, h3]
  push_cast
  ring

theorem locL_eq (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) (x : ℝ) (hfin : schurDir q (fun i => (α i : ℂ)) x ≠ ⊤) :
    locL q (Finset.univ.val.map α) ((Finset.univ.val.map α).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) =
      (((schurDir q (fun i => (α i : ℂ)) x).toReal : ℝ) : ℂ) := by
  have hs := summable_schurTerm q _ x hfin
  rw [Multiset.map_map]
  have key := cauchy_locL le_rfl α (Units.map (starRingEnd ℂ).toMonoidHom ∘ α) q (x : ℂ) (hs.congr fun l => by
    rw [← norm_pow, ← norm_mul, term_eq, Complex.norm_real, Real.norm_of_nonneg (schurTerm_nonneg _ _ _ _)])
  have h2 : HasSum (fun l => ((schurTerm q (fun i => (α i : ℂ)) x l : ℝ) : ℂ))
      (((schurDir q (fun i => (α i : ℂ)) x).toReal : ℝ) : ℂ) := by
    rw [toReal_schurDir]; exact Complex.hasSum_ofReal.mpr hs.hasSum
  simp only [term_eq] at key
  exact key.unique h2

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Filter Topology GlobalTheory.RSPole Set

theorem schurTerm_anti (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) {x y : ℝ} (hxy : x ≤ y) (l) :
    schurTerm q a y l ≤ schurTerm q a x l := by
  unfold schurTerm
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) ?_) (by positivity)
  have : (0 : ℝ) ≤ ((∑ i, l.1 i : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem schurDir_anti (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) {x y : ℝ} (hxy : x ≤ y) :
    schurDir q a y ≤ schurDir q a x := by
  rw [schurDir_eq, schurDir_eq]
  exact ENNReal.tsum_le_tsum fun l => ENNReal.ofReal_le_ofReal (schurTerm_anti q hq a hxy l)

theorem continuousOn_toReal_schurDir (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) (x₀ : ℝ)
    (hfin : schurDir q a x₀ ≠ ⊤) : ContinuousOn (fun x => (schurDir q a x).toReal) (Ici x₀) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : ContinuousOn (fun x => ∑' l, schurTerm q a x l) (Ici x₀) := by
    refine continuousOn_tsum (u := schurTerm q a x₀) (fun l => ?_) (summable_schurTerm q a x₀ hfin) ?_
    · unfold schurTerm
      exact (continuous_const.mul (continuous_const.rpow (by fun_prop) fun _ => Or.inl hqpos.ne')).continuousOn
    · intro l x hx
      rw [Real.norm_of_nonneg (schurTerm_nonneg _ _ _ _)]
      exact schurTerm_anti q hq a hx l
  exact hc.congr fun x _ => toReal_schurDir q a x

theorem one_le_toReal_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (hfin : schurDir q a x ≠ ⊤) :
    1 ≤ (schurDir q a x).toReal := by
  have := ENNReal.toReal_mono hfin (one_le_schurDir q a x)
  simpa using this

section
variable {I : Type} (q : I → ℕ) {n : ℕ} (a : I → Fin n → ℂ)

theorem schurDir_ne_top (x : ℝ) (h : eulD q a x ≠ ⊤) (w : I) : schurDir (q w) (a w) x ≠ ⊤ :=
  ne_top_of_le_ne_top h (le_tprod_of_one_le (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) w)

theorem hasProd_eulD (x : ℝ) (h : eulD q a x ≠ ⊤) :
    HasProd (fun w => (schurDir (q w) (a w) x).toReal) (eulD q a x).toReal :=
  hasProd_toReal (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) h

theorem summable_log (x : ℝ) (h : eulD q a x ≠ ⊤) :
    Summable fun w => Real.log (schurDir (q w) (a w) x).toReal := by
  have h1 : ∀ w, 1 ≤ (schurDir (q w) (a w) x).toReal :=
    fun w => one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x h w)
  refine summable_of_sum_le (c := Real.log (eulD q a x).toReal) (fun w => Real.log_nonneg (h1 w)) fun s => ?_
  rw [← Real.log_prod (fun w _ => (zero_lt_one.trans_le (h1 w)).ne')]
  refine Real.log_le_log (Finset.prod_pos fun w _ => zero_lt_one.trans_le (h1 w)) ?_
  rw [← ENNReal.toReal_prod]
  exact ENNReal.toReal_mono h (finset_prod_le_tprod (fun w => schurDir (q w) (a w) x)
    (fun w => one_le_schurDir _ _ _) s)

theorem toReal_eulD_eq_exp (x : ℝ) (h : eulD q a x ≠ ⊤) :
    (eulD q a x).toReal = Real.exp (∑' w, Real.log (schurDir (q w) (a w) x).toReal) := by
  have h1 : ∀ w, 0 < (schurDir (q w) (a w) x).toReal :=
    fun w => zero_lt_one.trans_le (one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x h w))
  exact (hasProd_eulD q a x h).unique (Real.hasProd_of_hasSum_log h1 (summable_log q a x h).hasSum)

theorem continuousOn_toReal_eulD (hq : ∀ w, 1 ≤ q w) (x₀ : ℝ) (hall : ∀ x, x₀ ≤ x → eulD q a x ≠ ⊤) :
    ContinuousOn (fun x => (eulD q a x).toReal) (Ici x₀) := by
  have hx₀ := hall x₀ le_rfl
  have hF : ∀ w x, x₀ ≤ x → 1 ≤ (schurDir (q w) (a w) x).toReal :=
    fun w x hx => one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x (hall x hx) w)
  have hc : ContinuousOn (fun x => ∑' w, Real.log (schurDir (q w) (a w) x).toReal) (Ici x₀) := by
    refine continuousOn_tsum (u := fun w => Real.log (schurDir (q w) (a w) x₀).toReal) (fun w => ?_)
      (summable_log q a x₀ hx₀) ?_
    · exact (continuousOn_toReal_schurDir (q w) (hq w) (a w) x₀ (schurDir_ne_top q a x₀ hx₀ w)).log
        fun x hx => (zero_lt_one.trans_le (hF w x hx)).ne'
    · intro w x hx
      rw [Real.norm_of_nonneg (Real.log_nonneg (hF w x hx))]
      refine Real.log_le_log (zero_lt_one.trans_le (hF w x hx)) ?_
      exact ENNReal.toReal_mono (schurDir_ne_top q a x₀ hx₀ w) (schurDir_anti (q w) (hq w) (a w) hx)
  exact (Real.continuous_exp.comp_continuousOn hc).congr fun x hx => toReal_eulD_eq_exp q a x (hall x hx)
end

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Set

theorem eulD_hasProd_locL : ∀ (I : Type) (q : I → ℕ) (n : ℕ) (α : I → Fin n → ℂˣ), (∀ w, 2 ≤ q w) →
    (∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤) →
    (∀ x : ℝ, 1 < x →
      HasProd (fun w => locL (q w) (Finset.univ.val.map (α w))
          ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
        (((GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) ∧
      1 ≤ (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) ∧
    ContinuousOn (fun x => (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) (Set.Ioi 1) := by
  intro I q n α hq hfin
  set a : I → Fin n → ℂ := fun w i => ((α w i : ℂˣ) : ℂ) with ha
  have hq1 : ∀ w, 1 ≤ q w := fun w => le_trans (by norm_num) (hq w)
  refine ⟨fun x hx => ⟨?_, ?_⟩, ?_⟩
  · have h := (hasProd_eulD q a x (hfin x hx)).map Complex.ofRealHom Complex.continuous_ofReal
    have he : (fun w => locL (q w) (Finset.univ.val.map (α w))
        ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) =
        Complex.ofRealHom ∘ fun w => (schurDir (q w) (a w) x).toReal := by
      funext w
      exact locL_eq (q w) (α w) x (schurDir_ne_top q a x (hfin x hx) w)
    rw [he]; exact h
  · have h1 : (1 : ℝ≥0∞) ≤ eulD q a x := by
      simpa [eulD] using finset_prod_le_tprod (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) ∅
    simpa using ENNReal.toReal_mono (hfin x hx) h1
  · intro x hx
    have hx' : (1 + x) / 2 < x := by simp only [mem_Ioi] at hx; linarith
    have h := continuousOn_toReal_eulD q a hq1 ((1 + x) / 2) fun y hy => hfin y (by simp only [mem_Ioi] at hx; linarith)
    exact (h.continuousAt (Ici_mem_nhds hx')).continuousWithinAt

end GlobalTheory.RSPole.EulerPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeSmoothOfChartDifferentiableLieDerivStableStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_smooth_of_chartDifferentiable_lieDerivStable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Submodule ℂ (GA E a → ℂ)), (∀ F ∈ S, ∀ g : GA E a, DifferentiableOn ℝ (chart F g) (invSet E a)) → (∀ F ∈ S, ∀ X : Lie E a, lieD X F ∈ S) → S ≤ Sm E a := by
  first | exact @GlobalTheory.SmoothClosure.le_Sm | exact GlobalTheory.SmoothClosure.le_Sm | (intros; apply GlobalTheory.SmoothClosure.le_Sm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOneStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellin_integral_rapidDecay_entire_of_le_one : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (δ : X → ℝ) (F : X → ℂ), Measurable δ → (∀ᵐ x ∂ν, 0 < δ x ∧ δ x ≤ 1) → Integrable δ ν → AEStronglyMeasurable F ν → (∀ K : ℕ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ ≤ C * δ x ^ K) → (∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν) ∧ Differentiable ℂ fun s : ℂ => ∫ x, F x * (δ x : ℂ) ^ s ∂ν := by
  first | exact @GlobalTheory.integral_mul_cpow_of_rapid_decay_entire | exact GlobalTheory.integral_mul_cpow_of_rapid_decay_entire | (intros; apply GlobalTheory.integral_mul_cpow_of_rapid_decay_entire <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralUnfoldMirabolicStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelbergThetaIntegral_unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ →
    ∀ φ φ' : GA E (m + 1) → ℂ, Measurable φ → Measurable φ' → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ γ g, φ' (ratGL E (m + 1) γ * g) = φ' g) → ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), Continuous Φ → ∀ x : ℝ,
    ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ →
    Zint μ 𝓕 φ φ' Φ N x = ∫ g in 𝓕P, Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) ∂μ := by
  first | exact @GlobalTheory.ZUnfTheta.zint_eq_mirabolic | exact GlobalTheory.ZUnfTheta.zint_eq_mirabolic | (intros; apply GlobalTheory.ZUnfTheta.zint_eq_mirabolic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentRepresentation
section
namespace GlobalTheory

theorem segmentRepresentation' : GlobalTheory.Published.SegmentRepresentation :=
  CompanionTheory.RgGu.segmentRepresentation

end GlobalTheory
end

