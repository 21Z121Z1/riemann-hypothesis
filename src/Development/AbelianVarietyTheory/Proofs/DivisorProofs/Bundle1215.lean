import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReproducingPolynomialValueAtOneMaxCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTranscendenceBasisOverConstEqOfAlgEquiv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem GlobalTheory.trBasis_card_eq_of_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (e : K ≃ₐ[ℂ] κ)
  (n k : ℕ) (x : Fin n → K) (z : Fin k → κ),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ) z → n = k := by
  intro K κ _ _ _ _ e n k x z hx hz
  have eK : (algebraMap ℂ K).toAlgebra = (inferInstance : Algebra ℂ K) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have eκ : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis at hx hz
  rw [eK] at hx
  rw [eκ] at hz
  have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hz
  rw [Cardinal.mk_fin, e.trdeg_eq] at h1
  rw [Cardinal.mk_fin, ← h1] at h2
  exact_mod_cast h2.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirSectionSumIdentityStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_section_sum_identity : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B → ∀ Ψ : (Fin k → NC R S) → W,
    ∑ i, ∑ g, ((formT 1 B (section1 Ψ i g) (GlobalTheory.BlockReps.casK (tAct 1 actW) (section1 Ψ i g))).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B (section1 Ψ i g) (section1 Ψ i g)).re -
        (formT 1 B (section1 Ψ i g) (fun h => GlobalTheory.BlockReps.casK actW (section1 Ψ i g h))).re) ≤
      (Fintype.card (NC R S) : ℝ) * ((formT k B Ψ (GlobalTheory.BlockReps.casK (tAct k actW) Ψ)).re -
        (formT k B Ψ (fun g => GlobalTheory.BlockReps.casK actW (Ψ g))).re) := by
  first | exact @GlobalTheory.SteepMult.CasDom.casDom | exact GlobalTheory.SteepMult.CasDom.casDom | (intros; apply GlobalTheory.SteepMult.CasDom.casDom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftPhaseConjReadingsFiveClausesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ) := by
  first | exact @GlobalTheory.CoreFive.shift_phase_conj | exact GlobalTheory.CoreFive.shift_phase_conj | (intros; apply GlobalTheory.CoreFive.shift_phase_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterExpansionWeightCompat
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.ToHol

theorem det_ne_of_frame {n : ℕ} (q : ℕ) (G x : Matrix (Fin n) (Fin n) ℂ)
    (h : xᴴ * G * x = diagonal fun c : Fin n => if (c : ℕ) < q then (-1 : ℂ) else 1) : x.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [det_mul, h0, mul_zero, det_diagonal] at this
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) this.symm
  split_ifs <;> norm_num

theorem unitary_of_frames {n : ℕ} (G x x₀ : Matrix (Fin n) (Fin n) ℂ) (hx : x.det ≠ 0)
    (h : x₀ᴴ * G * x₀ = xᴴ * G * x) : (x₀ * x⁻¹)ᴴ * G * (x₀ * x⁻¹) = G := by
  have hu : IsUnit x.det := hx.isUnit
  have h1 : x * x⁻¹ = 1 := mul_nonsing_inv x hu
  calc (x₀ * x⁻¹)ᴴ * G * (x₀ * x⁻¹) = x⁻¹ᴴ * (x₀ᴴ * G * x₀) * x⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (x * x⁻¹)ᴴ * G * (x * x⁻¹) := by
        rw [h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h1]; simp

theorem differentiable_det {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) :
    Differentiable ℂ fun y : Frame Ψ r => (mat y τ).det := by
  simp only [det_apply', mat, of_apply]
  fun_prop

theorem bchar_shift {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r) (e : Ψ → ℤ)
    (b : Frame Ψ r) (hb : b ∈ Bor Ψ r) :
    bchar la b = bchar (fun τ i => la τ i - e τ) b * ∏ τ, (mat b τ).det ^ e τ := by
  unfold bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : (mat b τ).det = ∏ i, b τ i i :=
    det_of_upperTriangular (M := mat b τ) fun a c h => (hb τ).2 a c h
  have hne : ∀ i, b τ i i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.1 (fun h => (hb τ).1 (hd.trans h)) i (Finset.mem_univ _)
  rw [hd, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_add₀ (hne i), sub_add_cancel]

theorem archM_mul' {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  unfold archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem exists_holCusp : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V)) (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (q : ℕ) (w : D.what₂.Tau → Fin V.rank → ℤ) (e : D.what₂.Tau → ℤ) (mu : GA D V → ℂ), IsInfFam θ → BaseDict θ V hr X dict Kf x₀ → Kf ≤ GfC V → (∀ k, (X k).p0 = q) → NegFirst V q x → (∀ g g', mu (g * g') = mu g * mu g') → (∀ g, ‖mu g‖ = 1) → (∀ γ ∈ GQ V, mu γ = 1) → (∀ k ∈ Kf, mu k = 1) → (∀ u ∈ GinfC V, mu u = ∏ ρ, (archM V (θ ρ) u).det ^ (-(e ρ))) → (∀ k (ρ : D.what₂.Tau) (τ : (X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la k τ (Fin.cast hr c) = w ρ c + e ρ) → (∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) → (∀ k (τ : (X k).Ψ) (a b : Fin r), (a : ℕ) < q → q ≤ (b : ℕ) → la k τ a < la k τ b) → ∃ a : GA D V, ∀ φ : GA D V → ℂ, IsHolFor θ V x w φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∀ k ∈ Kf, ∀ g, φ (g * k) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ P : FDSec X, IsHolCusp X la P ∧ ∀ g, φ (g * a) = mu g * P (dict g).1 (dict g).2 := by
  intro D θ V r hr Comp X dict Kf x₀ la x q w e mu hθ hB hKf hq hx hmul hnorm hQ hK hinf hla hχ hsep
  have hx₀ : NegFirst V q x₀ := hq (dict 1).1 ▸ (hB.1 (dict 1).1).2.1
  have hdx : ∀ ρ, (x ρ).det ≠ 0 := fun ρ => det_ne_of_frame q _ _ (hx ρ)
  have hdx₀ : ∀ ρ, (x₀ ρ).det ≠ 0 := fun ρ => det_ne_of_frame q _ _ (hx₀ ρ)
  obtain ⟨a, ha, haM⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 (fun ρ => x₀ ρ * (x ρ)⁻¹)
    (fun ρ => unitary_of_frames _ _ _ (hdx ρ) ((hx₀ ρ).trans (hx ρ).symm))
  have haM' : ∀ ρ, archM V (θ ρ) a * x ρ = x₀ ρ := fun ρ => by
    have : archM V (θ ρ) a = x₀ ρ * (x ρ)⁻¹ := haM ρ
    rw [this, Matrix.mul_assoc, nonsing_inv_mul _ (hdx ρ).isUnit, Matrix.mul_one]
  have hcomm := (GlobalTheory.UnitarySplit.real_finite_split D V).2.1
  have hmu0 : ∀ g, mu g ≠ 0 := fun g h => by simpa [h] using hnorm g
  refine ⟨a, fun φ hφ hl hk ⟨C, hC⟩ => ?_⟩
  obtain ⟨P, hP, hPe, hPb⟩ := GlobalTheory.T.automorphic_expansion_in_dictionary D θ V r hr Comp X dict Kf x₀ la (fun g => φ (g * a) / mu g) hθ hB hχ
    (fun γ hγ g => by simp only [mul_assoc, hl γ hγ, hmul, hQ γ hγ, one_mul])
    (fun k hk' g => by
      simp only [hmul, hK k hk', mul_one]
      rw [mul_assoc, ← hcomm a ha k (hKf hk'), ← mul_assoc, hk k hk'])
    (fun k g => by
      have hM := (hB.1 k).1
      choose s hs using fun τ : (X k).Ψ => (hM.1 τ.1).1 τ.2
      have hsρ : ∀ (ρ : D.what₂.Tau) (τ : (X k).Ψ), τ.1 = tauE D ρ → s τ = ρ := fun ρ τ h =>
        GlobalTheory.SmoothForms.RealPts.tauE_injective D ((hs τ).symm.trans h)
      have hsb : Function.Bijective s := by
        refine ⟨fun τ τ' h => Subtype.ext (by rw [hs τ, hs τ', h]), fun ρ => ?_⟩
        exact ⟨⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩, hsρ ρ _ rfl⟩
      obtain ⟨Q, hQd, hQb, hQe⟩ := GlobalTheory.T.holomorphic_form_frame_expansion D θ V r hr (X k) x w (fun τ i => la k τ i - e (s τ)) φ hθ hM
        ((hq k).symm ▸ hx) (fun ρ τ h c => by simp only [hla k ρ τ h c, hsρ ρ τ h, add_sub_cancel_right]) hφ g
      refine ⟨fun y => Q y * (∏ τ, (mat y τ).det ^ e (s τ)) * ((mu g)⁻¹ * ∏ τ, (x₀ (s τ)).det ^ (-e (s τ))), ?_, ?_, ?_⟩
      · refine DifferentiableOn.mul_const (hQd.mul ?_) _
        intro y hy
        refine DifferentiableAt.differentiableWithinAt ?_
        exact (HasFDerivAt.finset_prod (u := Finset.univ) (g := fun τ (y : Frame (X k).Ψ r) => (mat y τ).det ^ e (s τ))
          fun τ _ => (((differentiable_det τ) y).zpow (Or.inl (hy τ).1)).hasFDerivAt).differentiableAt
      · intro y hy b hb
        have hm : ∀ τ, mat (rmul y b) τ = mat y τ * mat b τ := fun τ => rfl
        simp only [hQb y hy b hb, hm, det_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [bchar_shift (la k) (fun τ => e (s τ)) b hb]
        ring
      · intro u hu y hy
        have hy' : FrIs θ V hr (X k) x (u * a) y := fun ρ τ h => by
          rw [hy ρ τ h, archM_mul', Matrix.mul_assoc, haM']
        have hd : ∀ τ, (mat y τ).det = (archM V (θ (s τ)) u).det * (x₀ (s τ)).det := fun τ => by
          rw [hy (s τ) τ (hs τ), det_reindex_self, det_mul]
        have hu' : mu u = ∏ τ, (archM V (θ (s τ)) u).det ^ (-(e (s τ))) := by
          rw [hinf u hu]
          exact (hsb.prod_comp fun ρ => (archM V (θ ρ) u).det ^ (-(e ρ))).symm
        have h1 : (∏ τ, (x₀ (s τ)).det ^ e (s τ)) * ∏ τ, (x₀ (s τ)).det ^ (-e (s τ)) = 1 := by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_eq_one fun τ _ => by rw [← zpow_add₀ (hdx₀ _), add_neg_cancel, zpow_zero]
        have h2 : (∏ τ, (archM V (θ (s τ)) u).det ^ e (s τ)) = (mu u)⁻¹ := by
          rw [hu', ← Finset.prod_inv_distrib]
          exact Finset.prod_congr rfl fun τ _ => by rw [_root_.zpow_neg, inv_inv]
        simp only [hQe (u * a) (mul_mem hu ha) y hy', hd, mul_zpow, Finset.prod_mul_distrib, h2, hmul, mul_assoc g u a]
        rw [div_eq_mul_inv, mul_inv]
        linear_combination (φ (g * (u * a)) * (mu u)⁻¹ * (mu g)⁻¹) * h1)
  refine ⟨P, fun k => ?_, fun g => ?_⟩
  · refine GlobalTheory.T.bounded_section_in_span_of_gap _ r (X k) (la k) (P k) ⟨hP k, C, hPb C (fun g => ?_) k⟩ ?_
    · simpa only [norm_div, hnorm, div_one] using hC _
    · intro τ a b h1 h2
      rw [hq k] at h1 h2
      exact hsep k τ a b h1 h2
  · rw [← hPe g]
    field_simp [hmu0 g]

end GlobalTheory.HolRead.ToHol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffsValuedBoundedOnCompactGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharpolyBound

theorem continuous_coeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  refine (MvPolynomial.continuous_eval _).comp ?_
  exact continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_vle (w : Pl E) (m : ℤ) : IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound {X : Type} [TopologicalSpace X] (w : Pl E) {f : X → w.adicCompletion E} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) : ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v (f x) ≤ B := by
  have hcov : C ⊆ ⋃ m : ℤ, f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
    rcases eq_or_ne (Valued.v (f x)) 0 with h | h
    · exact ⟨0, by rw [h]; exact zero_le'⟩
    · exact ⟨WithZero.log (Valued.v (f x)), (WithZero.exp_log h).ge⟩
  have hmono : Monotone fun m : ℤ => f ⁻¹' {y | Valued.v y ≤ WithZero.exp m} := by
    intro a b hab x hx
    exact le_trans hx (WithZero.exp_le_exp.2 hab)
  obtain ⟨m, hm⟩ := hC.elim_directed_cover _ (fun m => (isOpen_vle w m).preimage hf) hcov hmono.directed_le
  exact ⟨WithZero.exp m, fun x hx => hm hx⟩

end GlobalTheory.CharpolyBound

open GlobalTheory.CharpolyBound in
theorem GlobalTheory.CharpolyBound.bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ B) ∧ Valued.v ((g.val.charpoly.coeff 0)⁻¹) ≤ B := by
  intro E _ _ _ n w C hC
  have hval : Continuous fun g : GLw n w => g.val := Units.continuous_val
  have hinv : Continuous fun g : GLw n w => ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_coe_inv
  have hk : ∀ k : ℕ, ∃ B : WithZero (Multiplicative ℤ), ∀ g ∈ C, Valued.v (g.val.charpoly.coeff k) ≤ B :=
    fun k => exists_bound w ((continuous_coeff n k).comp hval) hC
  choose Bk hBk using hk
  obtain ⟨Bi, hBi⟩ := exists_bound w (hinv.matrix_det) hC
  refine ⟨(Finset.range (n + 1)).sup Bk ⊔ Bi, fun g hg => ⟨fun k => ?_, ?_⟩⟩
  · by_cases hkn : k ≤ n
    · exact le_sup_of_le_left ((hBk k g hg).trans (Finset.le_sup (f := Bk) (Finset.mem_range.2 (by omega))))
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega), map_zero]
      exact zero_le'
  · have h0 : g.val.charpoly.coeff 0 = (-1) ^ n * g.val.det := by
      rw [det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    have hdet : g.val.det * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
      rw [← det_mul, Units.mul_inv, det_one]
    have hc : (g.val.charpoly.coeff 0)⁻¹ =
        (-1) ^ n * ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det := by
      rw [h0, mul_inv, inv_eq_of_mul_eq_one_right hdet, ← inv_pow, inv_neg_one]
    rw [hc, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    exact le_sup_of_le_right (hBi g hg)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfHermitianMultiplicationModel
section
noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem charpoly_mulLeft_eq_of_gen {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (Q : F[X]) (hQ : Q.Monic) (hadj : Algebra.adjoin F {u} = ⊤) (hr : aeval u Q = 0)
    (hd : Module.finrank F A = Q.natDegree) : (LinearMap.mulLeft F u).charpoly = Q := by
  set P := (LinearMap.mulLeft F u).charpoly with hPdef
  have hP : P.Monic := LinearMap.charpoly_monic _
  have hPd : P.natDegree = Q.natDegree := by rw [hPdef, LinearMap.charpoly_natDegree, hd]
  by_cases hQ1 : Q = 1
  · subst hQ1
    rw [natDegree_one] at hPd
    exact Polynomial.eq_one_of_monic_natDegree_zero hP hPd
  set d := Q.natDegree with hddef
  let v : Fin d → A := fun i => u ^ (i : ℕ)
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro a _
    have ha : a ∈ Algebra.adjoin F {u} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨p, rfl⟩ := ha
    show aeval u p ∈ _
    rw [← Polynomial.aeval_modByMonic_eq_self_of_root hr,
      Polynomial.aeval_eq_sum_range' (Polynomial.natDegree_modByMonic_lt p hQ hQ1)]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩)
  have hli : LinearIndependent F v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hsp (by simp [hd, hddef])
  have hPu : aeval u P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F u)
    have h2 : (Algebra.lmul F A) u = LinearMap.mulLeft F u := by ext; simp
    rw [← hPdef, ← h2, Polynomial.aeval_algHom_apply] at h1
    have h3 := congrArg (fun f : Module.End F A => f 1) h1
    simpa using h3
  by_contra hne
  have hR : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (P - Q).degree < d := by
    have := Polynomial.degree_sub_lt (p := P) (q := Q) (by rw [Polynomial.degree_eq_natDegree hP.ne_zero,
      Polynomial.degree_eq_natDegree hQ.ne_zero, hPd]) hP.ne_zero (by rw [hP.leadingCoeff, hQ.leadingCoeff])
    rwa [Polynomial.degree_eq_natDegree hP.ne_zero, hPd] at this
  have hRd : (P - Q).natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hR).2 hdeg
  have hz : aeval u (P - Q) = 0 := by simp [hPu, hr]
  rw [Polynomial.aeval_eq_sum_range' hRd, Finset.sum_range (fun i => (P - Q).coeff i • u ^ i)] at hz
  have hc := (Fintype.linearIndependent_iff.1 hli) (fun i => (P - Q).coeff i) hz ⟨_, hRd⟩
  exact hR (Polynomial.leadingCoeff_eq_zero.1 hc)

theorem charpoly_of_semilinear {F L A : Type} [Field F] [Field L] [CommRing A] [Algebra F A] [Module.Finite F A]
    (e : F ≃+* L) {n : ℕ} (u : A) (g : Matrix (Fin n) (Fin n) L) (ψ : A ≃+ (Fin n → L))
    (hψ : ∀ (c : F) (y : A), ψ (c • y) = e c • ψ y) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) :
    g.charpoly = (LinearMap.mulLeft F u).charpoly.map (e : F →+* L) := by
  let b := Module.finBasis F A
  set d := Module.finrank F A
  let v : Fin d → (Fin n → L) := fun i => ψ (b i)
  have hsum : ∀ c : Fin d → L, ∑ i, c i • v i = ψ (∑ i, e.symm (c i) • b i) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ, e.apply_symm_apply]
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [hsum, map_eq_zero_iff ψ ψ.injective] at hc
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ hc i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, rfl⟩ := ψ.surjective x
    rw [← b.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin d) L (Fin n → L) := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = v i := fun i => Module.Basis.mk_apply hli hsp i
  let M := LinearMap.toMatrix b b (LinearMap.mulLeft F u)
  have key : LinearMap.toMatrix b' b' (Matrix.toLin' g) = M.map (e : F →+* L) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, hb', Matrix.toLin'_apply]
    have h1 : g *ᵥ v j = ∑ k, e (b.repr (u * b j) k) • b' k := by
      show g *ᵥ ψ (b j) = _
      rw [← hu]
      conv_lhs => rw [← b.sum_repr (u * b j)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hψ, hb']
    rw [h1, b'.repr_sum_self]
    simp [M, LinearMap.toMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul]
  calc g.charpoly = (Matrix.toLin' g).charpoly := by
        rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' g) (Pi.basisFun L (Fin n)),
          LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    _ = (M.map (e : F →+* L)).charpoly := by rw [← key, LinearMap.charpoly_toMatrix]
    _ = _ := by rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) (γ : GLw n w), Q.Monic → Fits w e B Q u → IsModel w e B u x γ → γ.val.charpoly = Q := by
  intro E _ _ _ w K e n Q B u x γ hQ hfit hmod
  obtain ⟨hadj, hr, hd, -⟩ := hfit
  obtain ⟨ψ, hψ, hu, -⟩ := hmod
  rw [charpoly_of_semilinear e u γ.val ψ hψ hu,
    charpoly_mulLeft_eq_of_gen u (Q.map e.symm.toRingHom) (hQ.map _) hadj hr (by rw [hd, natDegree_map]),
    Polynomial.map_map]
  ext i
  simp [Polynomial.coeff_map]

end GlobalTheory.KapLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompact
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharpolyInt

theorem charpoly_coeff_det_int {E : Type} [Field E] [NumberField E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) :
    (∀ k, A.charpoly.coeff k ∈ w.adicCompletionIntegers E) ∧ A.det ∈ w.adicCompletionIntegers E := by
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hMA : M.map (w.adicCompletionIntegers E).subtype = A := by ext i j; rfl
  refine ⟨fun k => ?_, ?_⟩
  · rw [← hMA, Matrix.charpoly_map, Polynomial.coeff_map]
    exact (M.charpoly.coeff k).2
  · have hdet : A.det = ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) := by
      rw [← hMA]; exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M).symm
    rw [hdet]; exact M.det.2

theorem entries_int_of_mem_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) (hg : g ∈ GlobalTheory.LFun.KGL w n) :
    (∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (g⁻¹).1 i j ∈ w.adicCompletionIntegers E := by
  simp only [GlobalTheory.LFun.KGL] at hg
  unfold GLint at hg
  obtain ⟨h, rfl⟩ := hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (bc (Ov E w).subtype h).1 i j = ((h.1 i j : Ov E w) : w.adicCompletion E) := rfl
    rw [this]; exact (h.1 i j).2
  · have : ((bc (Ov E w).subtype h)⁻¹).1 i j = (((h⁻¹).1 i j : Ov E w) : w.adicCompletion E) := by
      rw [← map_inv]; rfl
    rw [this]; exact ((h⁻¹).1 i j).2

theorem kint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    g ∈ GlobalTheory.LFun.KGL w n →
    (∀ k, Valued.v (g.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (g.val.charpoly.coeff 0) = 1 := by
  intro E _ _ _ n w g hg
  obtain ⟨h1, h2⟩ := entries_int_of_mem_KGL w n g hg
  obtain ⟨hc, hd⟩ := charpoly_coeff_det_int w g.val h1
  obtain ⟨-, hd'⟩ := charpoly_coeff_det_int w (g⁻¹).val h2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd hd'
  refine ⟨fun k => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc k), ?_⟩
  have hprod : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hv : Valued.v g.val.det * Valued.v (g⁻¹).val.det = 1 := by rw [← map_mul, hprod, map_one]
  have hdet : Valued.v g.val.det = 1 := by
    refine le_antisymm hd ?_
    calc (1 : _) = Valued.v g.val.det * Valued.v (g⁻¹).val.det := hv.symm
      _ ≤ Valued.v g.val.det * 1 := mul_le_mul' le_rfl hd'
      _ = Valued.v g.val.det := mul_one _
  have h0 : g.val.charpoly.coeff 0 = (-1) ^ Fintype.card (Fin n) * g.val.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h0, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, hdet]

end GlobalTheory.CharpolyInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMulLeftGeneratorEqMapSymm
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory

theorem charpoly_mulLeft_eq_of_adjoin_eq_top {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (u : A) (P : F[X]) (hP : P.Monic) (hadj : Algebra.adjoin F {u} = ⊤)
    (hu : aeval u P = 0) (hdim : Module.finrank F A = P.natDegree) :
    (LinearMap.mulLeft F u).charpoly = P := by
  have hint : IsIntegral F u := ⟨P, hP, hu⟩
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = u := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hmin : minpoly F u = P := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hP (minpoly.dvd F u hu) ?_).symm
    rw [← hdim, pb.finrank, PowerBasis.ofAdjoinEqTop_dim]
  have h1 := charpoly_leftMulMatrix pb
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, hgen, hmin] at h1
  exact h1

theorem charpoly_mulLeft_eq_map_symm : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (R : Type) [Field R] (e : K.E ≃+* R) (u : B.A) (Q : R[X]), Q.Monic → Algebra.adjoin K.E {u} = ⊤ → aeval u (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom := by
  intro K B R _ e u Q hQ hadj hu hdim
  exact charpoly_mulLeft_eq_of_adjoin_eq_top u _ (hQ.map _) hadj hu (by rw [hdim, hQ.natDegree_map])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceEqAddStarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTrace_eq_add_star : ∀ {D : D7} (x : D.host.E), ((Algebra.trace D.host.F D.host.E x : D.host.F) : D.host.E) = x + star x := by
  first | exact @GlobalTheory.TraceAddStar.trace_eq_add_star | exact GlobalTheory.TraceAddStar.trace_eq_add_star | (intros; apply GlobalTheory.TraceAddStar.trace_eq_add_star <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDimStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.codim_one_integral_subscheme_dim : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z], Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  first | exact @GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one | exact GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one | (intros; apply GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicActionRealCoordinatesStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_adelicAction_realCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  first | exact @GlobalTheory.RealWeilF.MCont.continuous_mMF | exact GlobalTheory.RealWeilF.MCont.continuous_mMF | (intros; apply GlobalTheory.RealWeilF.MCont.continuous_mMF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReproducingPolynomialValueAtOneMaxCompactStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reproducingPolynomial_valueAtOne_maxCompact : GlobalTheory.PsCo.Pc3.Repro := by
  first | exact @GlobalTheory.PsCo.Pc3.fock_reproducing_formula | exact GlobalTheory.PsCo.Pc3.fock_reproducing_formula | (intros; apply GlobalTheory.PsCo.Pc3.fock_reproducing_formula <;> assumption)
end

