import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteSourcePairCentredBlockParameters
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumFockVectorsIsVacuumOffLevel
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVacua

open GlobalTheory.IdemSupport

variable {D : D7}

theorem cP_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

theorem delta_orth {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
    {P Q : HeightOneSpectrum (𝓞 D.host.E)} {a b : AE D} (ha : IsDelta Φ P a) (hb : IsDelta Φ Q b) (h : P ≠ Q) :
    a * b = 0 := by
  refine hΦ.ext' (by rw [RingHom.map_mul, ha.1, zero_mul, RingHom.map_zero]) fun Q' => ?_
  rw [ev_mul, ev_zero]
  by_cases hQ : Q' = P
  · rw [hb.2.2 Q' (hQ ▸ h), mul_zero]
  · rw [ha.2.2 Q' hQ, zero_mul]

theorem half_orth {m n : ℕ} {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) {u : Matrix (Fin m) (Fin n) (AE D)}
    (hu : IsHalf e u ∨ IsHalf (cA D e) u) :
    u.map (infPart D) = 0 ∧ ∀ (S : Finset (Pl D.host.E)) (e' : AE D), IsIdemSum e' S →
      (∀ PP ∈ S, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ i j, e' * u i j = 0 ∧ cA D e' * u i j = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := (of_isPrimeIdem hΦ h).1
  obtain ⟨Q, a, hQ, ha, hu⟩ : ∃ Q a, (Q = P ∨ Q = cP P) ∧ IsDelta Φ Q a ∧ ∀ i j, a * u i j = u i j := by
    rcases hu with hu | hu
    exacts [⟨P, e, Or.inl rfl, hd, hu⟩, ⟨cP P, cA D e, Or.inr rfl, delta_conj hΦ hd, hu⟩]
  refine ⟨Matrix.ext fun i j => ?_, ?_⟩
  · rw [Matrix.map_apply, ← hu, RingHom.map_mul, ha.1, zero_mul, Matrix.zero_apply]
  · rintro S e' ⟨⟨es, hes, rfl⟩, -⟩ hS i j
    have key : ∀ PP ∈ S, PP ≠ Q ∧ cP PP ≠ Q := fun PP hPP => by
      obtain ⟨h1, h2⟩ := hS PP hPP
      rw [isConjPl_iff] at h2
      rcases hQ with rfl | rfl
      · exact ⟨h1, Ne.symm h2⟩
      · exact ⟨fun e => h2 (by rw [e, cP_cP]), fun e => h1 (by rw [← cP_cP PP, e, cP_cP])⟩
    have k1 : (∑ PP ∈ S, es PP) * a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun PP hPP => delta_orth hΦ (delta_of_isIdemAt hΦ (hes PP hPP)) ha (key PP hPP).1
    have k2 : cA D (∑ PP ∈ S, es PP) * a = 0 := by
      rw [map_sum, Finset.sum_mul]
      exact Finset.sum_eq_zero fun PP hPP =>
        delta_orth hΦ (delta_conj hΦ (delta_of_isIdemAt hΦ (hes PP hPP))) ha (key PP hPP).2
    rw [← hu, ← mul_assoc, ← mul_assoc, k1, k2, zero_mul]
    exact ⟨rfl, rfl⟩

theorem isVacAt_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) f₀ f B, GlobalTheory.GalLift.VecData R i σ f₀ f B → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ φ, GlobalTheory.Hk3.IsVacAt R.ψ _ _ P (GlobalTheory.GalLift.ptAt R i σ B f φ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hθ i σ f₀ f B hV P hP φ
  obtain ⟨⟨-, hvac⟩, e, he, hth⟩ := hV.vec
  obtain ⟨c, hc⟩ := hL.βV i
  obtain ⟨c', hc'⟩ := hL.βW i
  rw [one_pow] at hc hc'
  have h0 : GlobalTheory.Hk3.IsVacAt R.ψ _ _ P f₀ :=
    GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level R.ψ _ _ (R.βV i) (R.βW i) (R.ΛV i) (R.ΛW i) 1 1 hc hc' P
      (by rw [mul_one, Nat.cast_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)) f₀ hvac.theta hvac.lat
  refine ⟨hV.theta φ, fun e' f' h' u hu hh => ?_⟩
  obtain ⟨h1, h2⟩ := half_orth h' hh
  refine GlobalTheory.T.heisenbergOriented_finite_fixes_fockPolynomialVectors R.ψ R.θ _ _ hθ _ _ _ _ f hV.theta u h1 ?_ φ
  refine GlobalTheory.T.heisenbergOperator_fix_thetaDatum_away_splitPlaces R.ψ _ _ _ _ _ f₀ _ f hth u (fun a b => ?_) (h0.2 e' f' h' u hu hh)
  have := h2 _ e he (fun PP hPP => hP PP (Or.inl (by simpa using hPP))) a b
  rw [cA_cA]
  exact this.symm

end GlobalTheory.ConjVacua
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ConjHol
variable {D : D7} {S T : HSp D}

theorem gram_conj_emb (C : Ctx S T) (hH : ∀ τ, (gramAt D T τ)ᴴ = gramAt D T τ) (ρ : D.what₂.Tau)
    (M : Matrix (Fin T.rank) (Fin T.rank) ℂ) :
    FD.gram (C.m.e ρ).1 C.X.Gm (M.map (starRingEnd ℂ)) = Mᴴ * gramAt D T ρ * M := by
  ext a b
  have hh : ∀ i k, conj (gramAt D T ρ k i) = gramAt D T ρ i k := fun i k => by
    have := congrFun (congrFun (hH ρ) i) k
    rwa [Matrix.conjTranspose_apply] at this
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.map_apply, C.m.e_emb, C.m.gT, Matrix.transpose_apply,
    NumberField.ComplexEmbedding.conjugate_coe_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [gramAt, Matrix.map_apply] at hh ⊢
  simp only [Complex.conj_conj, hh, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

theorem unitFr_conj_moved : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → (∀ a, GlobalTheory.HolRead.IsUnitFr C.X (C.xB (C.mvB a B))) ∧ (∀ y, GlobalTheory.HolRead.IsUnitFr C.X y → ∃ a ∈ GinfC T, C.xB (C.mvB a B) = y) ∧ (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, C.xB (C.mvB a B) = C.xB (C.mvB a' B) → a = a') := by
  intro D S T C B hB
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hT := GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C
  have hH : ∀ τ, (gramAt D T τ)ᴴ = gramAt D T τ := fun τ => (R.1 τ).1
  refine ⟨fun a => ?_, fun y hy => ?_, fun a ha a' ha' h => ?_⟩
  · exact (hT.2 _ ((hT.2 B hB).2.2.2.2.2 a).1).1
  · let Y : C.Bas := fun ρ => (FD.mat y (C.m.e ρ)).map (starRingEnd ℂ)
    have hY : ∀ ρ, (Y ρ)ᴴ * gramAt D T ρ * Y ρ = sgnM C.X := by
      intro ρ
      rw [← gram_conj_emb C hH ρ]
      have e : (Y ρ).map (starRingEnd ℂ) = FD.mat y (C.m.e ρ) := by
        ext i j; simp [Y]
      rw [e]
      exact hy (C.m.e ρ)
    have hu : ∀ ρ, Y ρ * (B ρ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
      intro ρ
      have hd := isUnit_det_B C hB ρ
      have hd' : IsUnit (B ρ)ᴴ.det := by rw [det_conjTranspose]; exact hd.star
      show (Y ρ * (B ρ)⁻¹)ᴴ * gramAt D T ρ * (Y ρ * (B ρ)⁻¹) = gramAt D T ρ
      have e1 : (Y ρ * (B ρ)⁻¹)ᴴ * gramAt D T ρ * (Y ρ * (B ρ)⁻¹) =
          ((B ρ)⁻¹)ᴴ * ((Y ρ)ᴴ * gramAt D T ρ * Y ρ) * (B ρ)⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [e1, hY, ← hB ρ, conjTranspose_nonsing_inv]
      simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hd', Matrix.one_mul]
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
    obtain ⟨a, ha, hau⟩ := R.2.1 (fun ρ => Y ρ * (B ρ)⁻¹) hu
    refine ⟨a, ha, ?_⟩
    have hm : ∀ ρ, C.mvB a B ρ = Y ρ := by
      intro ρ
      simp only [Ctx.mvB]
      rw [show compAt C.θ ρ (mt T a) = Y ρ * (B ρ)⁻¹ from hau ρ, Matrix.mul_assoc,
        nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]
    funext σ i j
    obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
    simp only [Ctx.xB, Equiv.symm_apply_apply, hm, Y, Matrix.map_apply, Complex.conj_conj, FD.mat, Matrix.of_apply]
  · have hm : ∀ ρ, C.mvB a B ρ = C.mvB a' B ρ := by
      intro ρ
      ext i j
      have := congrFun (congrFun (congrFun h (C.m.e ρ)) i) j
      simp only [Ctx.xB, Equiv.symm_apply_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    refine R.2.2.1 a ha a' ha' fun ρ => ?_
    have e := congrArg (· * (B ρ)⁻¹) (hm ρ)
    simp only [Ctx.mvB, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_B C hB ρ), Matrix.mul_one] at e
    exact e

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlaceBoundedMatrixFromConjugateHalfHomL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjHalfOnto

open GlobalTheory.SplitHecke GlobalTheory.SplitHomLattice Formalism.L2.NTheta GlobalTheory.LatticeStable GlobalTheory.SplitScalar

variable {D : D7}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := GlobalTheory.SplitDualLat.cA_cA z

theorem cA_algebraMap (y : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) y) = algebraMap (AF D.host.F) (AE D) y := by
  change y ⊗ₜ[D.host.F] star (1 : D.host.E) = y ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [star_one]

theorem chart_conj {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hπ : Chart e v π) : Chart (cA D e) v (π.comp (cA D)) := by
  refine ⟨fun x => ?_, fun a => ?_, fun y => ?_, fun a => ?_⟩
  · obtain ⟨z, rfl⟩ := hπ.1 x
    exact ⟨cA D z, by simp only [RingHom.comp_apply, cA_cA']⟩
  · rw [RingHom.comp_apply, hπ.2.1]
    constructor
    · intro h
      have := congrArg (cA D) h
      rwa [RingHom.map_mul, cA_cA', RingHom.map_zero] at this
    · intro h
      rw [← cA_cA' e, ← RingHom.map_mul, h, RingHom.map_zero]
  · rw [RingHom.comp_apply, cA_algebraMap, hπ.2.2.1]
  · rw [RingHom.comp_apply, ← hπ.2.2.2]
    have h1 : finPart D (cA D e * a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (e * cA D a)) := by
      rw [← GlobalTheory.SplitDualLat.finPart_cA]; congr 1; rw [map_mul, cA_cA']
    have h2 : finPart D (e * cA D a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (cA D e * a)) := by
      rw [← GlobalTheory.SplitDualLat.finPart_cA]; congr 1; rw [map_mul, cA_cA']
    constructor
    · intro h; rw [h2]; exact GlobalTheory.SplitDualLat.sigR_mem_intAE h
    · intro h; rw [h1]; exact GlobalTheory.SplitDualLat.sigR_mem_intAE h

theorem rk_mem_lat (S T : HSp D) (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hs : s ∈ latHat D.host.F D.host.E ΛS)
    {t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E} (ht : t ∈ latHat D.host.F D.host.E ΛT) :
    rk S T a s t ∈ latO S T ΛS ΛT fun _ => True := by
  change rkHom S T a s t ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hs
      obtain ⟨β, hβ, y, hy, rfl⟩ := ht
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun _ h => absurd trivial h, a, ha, x, hx, y, hy, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · ext i j
        change liftFin D (_ * _ * ∑ k, (α ⊗ₜ[D.host.F] star (x k)) * _) = _
        rw [Matrix.of_apply, ← liftFin_tmul]
        congr 1
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [← TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem conj_rk {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (he : IsSplitIdem D e) (hπ : Chart e v π) (S T : HSp D) (a : D.host.E) (s : Fin S.rank → AE D)
    (t : Fin T.rank → AE D) (p : Fin T.rank) (q : Fin S.rank) :
    π (cA D (rk S T a (fun k => finPart D (e * s k)) (fun k => finPart D (cA D e * t k)) p q)) =
      π (cA D (incA D a)) * π (cA D (t p)) * ∑ k, π (s k) * π (cA D (incA D (S.gram k q))) := by
  have h := pi_rk (isSplitIdem_conj he) (chart_conj hπ) S T a s t p q
  simp only [RingHom.comp_apply, cA_cA'] at h
  exact h

theorem frame_cancel {K : Type} [Field K] {m n : ℕ} (B : GL (Fin m) K) (C : GL (Fin n) K) {c : K} (hc : c ≠ 0)
    (y : Matrix (Fin m) (Fin n) K) : (B⁻¹).1 * (c • (B.1 * ((c⁻¹ • y) * (C⁻¹).1))) * C.1 = y := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
    Units.inv_mul, Matrix.mul_one, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem map_cA_sum_apply {K : Type} [CommRing K] (π : AE D →+* K) {S T : HSp D} {n : ℕ} (M : Fin n → WO S T)
    (p : Fin T.rank) (q : Fin S.rank) :
    π (cA D ((∑ l, M l : Matrix (Fin T.rank) (Fin S.rank) (AE D)) p q)) = ∑ l, π (cA D (M l p q)) := by
  rw [Matrix.sum_apply, GlobalTheory.SplitDualLat.ringHom_sum (cA D), GlobalTheory.SplitDualLat.ringHom_sum π]

theorem adjCo_eq_map {v : FinPl D} (φ : SplitProj D v) (hQ : ∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x)
    (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (u : WO S T) :
    adjCo φ S T BS BT u = (BS⁻¹).1 * ((S.gram⁻¹).map (rdQ φ) *
      ((u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map fun x => rdA φ (cA D x))ᵀ * T.gram.map (rdQ φ)) * BT.1 := by
  unfold adjCo
  congr 2
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  simp only [Function.comp_def, hQ]

end GlobalTheory.ConjHalfOnto

namespace GlobalTheory.ConjHalfOnto

open GlobalTheory.SplitHecke GlobalTheory.SplitHomLattice Formalism.L2.NTheta GlobalTheory.LatticeStable GlobalTheory.SplitScalar

set_option maxHeartbeats 1000000 in

theorem conj_half_onto : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ a : D.host.E, a ∈ D.host.AA → a ≠ 0 → ∀ y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v), (∀ i j, Valued.v (y i j) ≤ Valued.v (rdQ φ (star a))) → ∃ u, u ∈ latO S T ΛS ΛT (fun _ => True) ∧ IsHalf (cA D e) u ∧ adjCo φ S T (frCo φ βS) (frCo φ βT) u = y := by
  intro D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he a haA ha0 y hy
  obtain ⟨hπ, -, hQ, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  have hsi : IsSplitIdem D e := he.1
  have hsc : IsSplitIdem D (cA D e) := isSplitIdem_conj hsi
  have hπc := chart_conj hπ
  have hc0 : rdQ φ (star a) ≠ 0 := by
    rw [← hQ]
    intro h
    have h1 : ((rdA φ).comp (incA D)) (star a) = 0 := h
    exact ha0 (star_eq_zero.1 ((map_eq_zero_iff _ ((rdA φ).comp (incA D)).injective).1 h1))
  set c : Fv D.host.F v := rdQ φ (star a) with hcdef
  set BS := frCo φ βS with hBS
  set BT := frCo φ βT with hBT
  have hGmap : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), M.map (rdQ φ) = M.map ((rdA φ).comp (incA D)) := by
    intro m n M; ext i j; simp only [Matrix.map_apply, RingHom.comp_apply, hQ]
  set Gs : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v) := S.gram.map (rdQ φ) with hGs
  set Gt : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v) := T.gram.map (rdQ φ) with hGt
  have hGtu : IsUnit Gt.det := by
    have := (GlobalTheory.LatVac.gram_det_isUnit T).map ((rdA φ).comp (incA D))
    rw [RingHom.map_det] at this
    rw [hGt, hGmap]
    exact this
  have hGsi : (S.gram⁻¹).map (rdQ φ) * Gs = 1 := by
    rw [hGs, hGmap, hGmap, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  set Z : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v) := (BT⁻¹).1 * Gt⁻¹ with hZ
  have hZ1 : Z * (Gt * BT.1) = 1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hGtu, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hZG : Z * Gt = (BT⁻¹).1 := by
    rw [hZ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGtu, Matrix.mul_one]
  set Y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) := c⁻¹ • y with hY
  have hYint : ∀ l m, Valued.v (Y l m) ≤ 1 := by
    intro l m
    rw [hY, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul, map_inv₀,
      inv_mul_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc0))]
    exact hy l m
  choose σ hσ using hπ.1
  clear_value Y Z Gt Gs BT BS c
  obtain ⟨s', hs'⟩ : ∃ s' : Fin S.rank → Fin S.rank → AE D, ∀ l k, s' l k = σ (BS.1 k l) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : Fin S.rank → Fin T.rank → AE D, ∀ l k, t' l k = cA D (σ (((fun m => Y l m) ᵥ* Z) k)) :=
    ⟨_, fun _ _ => rfl⟩
  have hs : ∀ l, (fun k => finPart D (e * s' l k)) ∈ latHat D.host.F D.host.E (ΛS : Set _) := by
    intro l
    refine (GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral D S ΛS βS hS hfS v φ e he (s' l)).2 fun i => ?_
    have h1 : (fun k => rdA φ (s' l k)) = BS.1 *ᵥ Pi.single l 1 := by
      funext k
      rw [hs', hσ, Matrix.mulVec_single_one]
      rfl
    rw [← hBS, h1, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hi : i = l
    · subst hi; rw [Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne hi, map_zero]; exact zero_le_one
  have ht : ∀ l, (fun k => finPart D (cA D e * t' l k)) ∈ latHat D.host.F D.host.E (ΛT : Set _) := by
    intro l
    refine (GlobalTheory.T.conjPart_mem_completedSelfDualLattice_iff_splitPlace D T ΛT βT hT hfT v φ e he (t' l)).2 fun j => ?_
    have h1 : (fun k => rdA φ (cA D (t' l k))) = (fun m => Y l m) ᵥ* Z := by
      funext k
      rw [ht', cA_cA', hσ]
    rw [← hGt, ← hBT, h1, Matrix.vecMul_vecMul, hZ1, Matrix.vecMul_one]
    exact hYint l j
  obtain ⟨U, hU⟩ : ∃ U : WO S T,
      U = ∑ l, rk S T a (fun k => finPart D (e * s' l k)) (fun k => finPart D (cA D e * t' l k)) := ⟨_, rfl⟩
  have hUmem : U ∈ latO S T ΛS ΛT fun _ => True := by
    rw [hU]; exact sum_mem fun l _ => rk_mem_lat S T _ _ haA (hs l) (ht l)
  refine ⟨cA D e • U, smul_mem_latO D S T _ _ _ (cA D e) (idem_int hsc) _ hUmem, fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsc.1]
  · have hentry : ∀ p q, rdA φ (cA D ((cA D e • U) p q)) =
        c * ∑ l, (Y * Z) l p * ∑ k, BS.1 k l * Gs q k := by
      intro p q
      have h0 : (cA D e • U) p q = cA D e * U p q := rfl
      rw [h0, map_mul (cA D), cA_cA', map_mul (rdA φ), he.2.2, one_mul, hU, map_cA_sum_apply]
      refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) (Finset.mul_sum _ _ _).symm
      rw [conj_rk hsi hπ S T a (s' l) (t' l) p q]
      have hYZ : ((fun m => Y l m) ᵥ* Z) p = (Y * Z) l p := rfl
      have hk : ∀ k, rdA φ (s' l k) * rdA φ (cA D (incA D (S.gram k q))) = BS.1 k l * Gs q k := by
        intro k
        rw [hs', hσ, GlobalTheory.SplitDualLat.cA_incA, hQ, GlobalTheory.LatVac.gram_star, hGs, Matrix.map_apply]
      rw [GlobalTheory.SplitDualLat.cA_incA, hQ, ← hcdef, ht', cA_cA', hσ, hYZ, Finset.sum_congr rfl fun k _ => hk k, mul_assoc]
    have hT' : (((cA D e • U : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map fun x => rdA φ (cA D x))ᵀ =
        c • (Gs * (BS.1 * (Y * Z))) := by
      ext q p
      rw [Matrix.transpose_apply, Matrix.map_apply, hentry, Matrix.smul_apply, smul_eq_mul]
      congr 1
      generalize Y * Z = W
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    have key : (S.gram⁻¹).map (rdQ φ) * (c • (Gs * (BS.1 * (Y * Z)))) * Gt = c • (BS.1 * (Y * (BT⁻¹).1)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc _ Gs, hGsi, Matrix.one_mul, Matrix.mul_assoc BS.1,
        Matrix.mul_assoc Y, hZG]
    rw [adjCo_eq_map φ hQ, hT', ← hGt, key, hY]
    exact frame_cancel BS BT hc0 y

end GlobalTheory.ConjHalfOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantPairingUniqueUpToScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covariant_pairing_unique_up_to_scalar : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds p q lam).HK → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → ∃ B₀ : Pol p q r s → (X.ds r s lam').HK.V → (X.ds p q lam).HK.V, ∀ B : Pol p q r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] (X.ds p q lam).HK.V, CoverW (X.ds p q lam) (X.ds r s lam') B → ∃ c : ℂ, ∀ P y, B P y = c • B₀ P y := by
  first | exact @GlobalTheory.PairingLine.pairing_line | exact GlobalTheory.PairingLine.pairing_line | (intros; apply GlobalTheory.PairingLine.pairing_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverHaarPushforwardSignatureUnitaryGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_haar_pushforward_signatureUnitaryGroup : ∀ (p q n : ℕ) (T : GrpData p q) (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) (br : Bool) (μ : Measure (Formalism.REAL.UJ ε)), SignCompat ε e → μ.IsHaarMeasure → ∃ (π : T.G →* Formalism.REAL.UJ ε) (c : NNReal), c ≠ 0 ∧ (∀ g, umat (π g) = phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  first | exact @GlobalTheory.ArchRec.cover_haar_map | exact GlobalTheory.ArchRec.cover_haar_map | (intros; apply GlobalTheory.ArchRec.cover_haar_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteSourcePairCentredBlockParametersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteSource_pair_centred_block_parameters : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ∃ al de : List ℚ, Centred D al [] [] de ∧ parHol D i τ = signed (al ++ []) ([] ++ de) (-(D.hc τ).e i) ∧ parDef D i τ = signed (al ++ block D.R.t ++ de) ([] ++ []) (-(D.hc τ).e i - 1 / 2) := by
  first | exact @GlobalTheory.ArchRec.ParPair.centred_pair | exact GlobalTheory.ArchRec.ParPair.centred_pair | (intros; apply GlobalTheory.ArchRec.ParPair.centred_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwines
section
open scoped InnerProductSpace

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta
open GlobalTheory.SmoothGlob (lieSet)

namespace GlobalTheory.GKLie

theorem dRep_conj_Kset (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ) :
    ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H,
      Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v →
      Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  intro κ hκ X hX v hv
  have h1 : κᴴ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ.1
  have h2 : κ * κᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ.1
  have hu : IsUnit κ := IsUnit.of_mul_eq_one _ h2
  have hinv : κ⁻¹ * κ = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det κ).1 hu)
  have hκU : κ ∈ UJset ε := by
    change κᴴ * Jm ε * κ = Jm ε
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, a * b ∈ UJset ε := fun a ha b hb => by
    change (a * b)ᴴ * Jm ε * (a * b) = Jm ε
    have ha' : aᴴ * Jm ε * a = Jm ε := ha
    have hb' : bᴴ * Jm ε * b = Jm ε := hb
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [ha', hb']
  have hE : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ UJset ε := fun t =>
    GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t
  have hinvU : κ⁻¹ ∈ UJset ε := by
    have hκinv : κ⁻¹ = κᴴ := Matrix.inv_eq_left_inv h1
    rw [hκinv]
    change κᴴᴴ * Jm ε * κᴴ = Jm ε
    rw [Matrix.conjTranspose_conjTranspose, hκ.2, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hfun : (fun t : ℝ => ρ (NormedSpace.exp (t • (κ * X * κ⁻¹))) (ρ κ v)) =
      fun t : ℝ => ρ κ (ρ (NormedSpace.exp (t • X)) v) := by
    funext t
    have hc : NormedSpace.exp (t • (κ * X * κ⁻¹)) = κ * NormedSpace.exp (t • X) * κ⁻¹ := by
      rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
    rw [hc]
    have hA : κ * NormedSpace.exp (t • X) * κ⁻¹ ∈ UJset ε := hmul _ (hmul _ hκU _ (hE t)) _ hinvU
    rw [← ContinuousLinearMap.comp_apply, ← hρ.2 _ hA _ hκU, Matrix.mul_assoc _ κ⁻¹ κ, hinv, Matrix.mul_one,
      hρ.2 _ hκU _ (hE t), ContinuousLinearMap.comp_apply]
  unfold dRep
  rw [hfun]
  have hd := (differentiableAt_orbit hv hX).hasDerivAt
  have hL : HasFDerivAt (ρ κ) ((ρ κ).restrictScalars ℝ) (ρ (NormedSpace.exp ((0 : ℝ) • X)) v) :=
    ((ρ κ).restrictScalars ℝ).hasFDerivAt
  exact (hL.comp_hasDerivAt (0 : ℝ) hd).deriv

end GlobalTheory.GKLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWordsStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_trace_power_cyclic_words : ∀ {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (m : ℕ), Formalism.REAL.etr E (m + 1) = ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => E p.1 p.2).prod := by
  first | exact @GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord | exact GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord | (intros; apply GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord <;> assumption)
end

