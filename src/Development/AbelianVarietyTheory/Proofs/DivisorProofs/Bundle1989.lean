import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0081
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIsoCompatibleLocalLanglandsTwo
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.TypeLawTransport

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.TypeLawTransport.typeLaw_transport_fwd : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → UpperTheory.Zero.LLC.TypeLaw h rc → UpperTheory.Zero.LLC.TypeLaw h' rc' := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i P rc rc' hrel hT
  intro E'' _ _ _ _ _ _ g _ w'' h'' ii hii n hn hg hnorm a'' ha'' K _ _ red hred hker θ hθ τ hτ hτc σ' hσ'
  letI iE : Algebra E E'' := ((algebraMap E' E'').comp j).toAlgebra
  haveI : IsScalarTower E E'' Ω := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E Ω x = algebraMap E'' Ω (algebraMap E' E'' (j x))
    rw [← IsScalarTower.algebraMap_apply]
    exact P.ext x
  haveI := GlobalTheory.LocLanglands.FieldCompat.charZero_compl w
  haveI := GlobalTheory.LocLanglands.FieldCompat.charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i P.cont).1
  have hcont : Continuous (ii.trans i.symm) := hs.comp hii
  obtain ⟨T, hT1, -⟩ := GlobalTheory.transport_irrGL_bijective _ _ i.symm hs
  obtain ⟨σ₀, e, h2, he⟩ := GlobalTheory.TheRecTransport.exists_of_repRel σ' ((hT1 _ _).2 rfl)
  have hR' : RepRel i.symm (cls σ') (cls σ₀) := h2 ▸ (hT1 _ _).2 rfl
  have hR : RepRel i (cls σ₀) (cls σ') := GlobalTheory.LocLanglands.FieldCompat.repRel_symm hR'
  have W := hrel _ _ hR
  have hinf : GlobalTheory.SerSys.TameGen.Inflates (σ₀.ρ.comp (Matrix.GeneralLinearGroup.map (ii.trans i.symm).toRingHom)) τ := by
    obtain ⟨f, hf0, hf⟩ := hσ'
    refine ⟨e.toLinearMap ∘ₗ f, fun h0 => hf0 ?_, fun k v => ?_⟩
    · ext v
      have := congrArg (fun F => F v) h0
      simpa using this
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply] at hf ⊢
      rw [hf, he]
      rfl
  obtain ⟨hm, hp⟩ := hT E'' g w'' h'' (ii.trans i.symm) hcont n hn hg hnorm a'' ha'' K red hred hker θ hθ τ hτ hτc σ₀ hinf
  refine ⟨(monodromy_vanishing_iff_of_weil_deligne_rel W).1 hm, fun t x z hxz hv => ?_⟩
  rw [← hp t x z hxz hv]
  exact (inePol_transport P W fun _ => rfl).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompa
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KInfPol

open GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem at_mul_right {m p q : Type} [Fintype p] {z : Matrix m p (AE F E)} (hz : At (evI F) z)
    (A : Matrix p q (AE F E)) : At (evI F) (z * A) := by
  intro u hu; rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

theorem heisLine_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ) :
    M.heisLine ψ u t 0 = 0 := by
  funext x
  simp [Model.heisLine, Darboux.rho, schr]

theorem sa_of_acts {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) : SA T f f₁ := by
  intro g hg
  refine h (fun x => g (fun i => (x i).2)) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  change g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  change (x i).2 + (z i).2 = (x i).2
  rw [fin_eq_zero_of_at hz, add_zero]

theorem sd_intertwine {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ W.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (1, h)) f g) (hf₁ : Acts (evI F) (om (1, h)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (u * (mat h)ᵀ)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (1, h) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (1, h) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((1, h) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (u * (mat h)ᵀ) := by
    change (1 : Matrix (Fin n) (Fin n) (AE F E)) * (realAd F t • u) * (mat h)ᵀ = _
    rw [Matrix.one_mul, Matrix.smul_mul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

theorem pol_stable_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ ∈ M.Pol B.ψ B.emb := by
  intro F E _ _ _ _ _ σ B n d Y W M om χ₁ χ₂ hB hM hw k hk f hf f₁ hf₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B n d Y W M om χ₁ χ₂ hB hM hw k hk
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine B.ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (heisLine_zero M B.ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ (u * (mat k)ᵀ)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (heisLine_zero M B.ψ _) (sd_intertwine hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    change (mat (k * k⁻¹))ᵀ = 1
    rw [mul_inv_cancel]
    exact Matrix.transpose_one
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), u * (mat k⁻¹)ᵀ * (mat k)ᵀ = u := fun u => by
    rw [Matrix.mul_assoc, hkk, Matrix.mul_one]
  have hle : M.Pol B.ψ B.emb ≤ (M.Pol B.ψ B.emb).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_right hu (mat k⁻¹)ᵀ
      have hv' := at_mul_right hu' (mat k⁻¹)ᵀ
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (B.emb w)) * (mat k).map (piInf (B.emb w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (B.emb w)) * W.θ w = W.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
          calc _ = (mat k⁻¹).map (piInf (B.emb w)) * W.θ w *
                ((mat k).map (piInf (B.emb w)) * (mat k⁻¹).map (piInf (B.emb w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (B.emb w)) * (W.θ w * (mat k).map (piInf (B.emb w))) *
                (mat k⁻¹).map (piInf (B.emb w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.smul_mul]
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_right hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.KInfPol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsIndependentAndSpan
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem card_le_finrank_of_semilinear {K C Y : Type} [Field K] [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup Y] [Module ℂ Y] {σ : K →+* ℂ} (j : C →ₛₗ[σ] Y) {m : ℕ} (f : Fin m → Y) (hf : LinearIndependent ℂ f)
    (hm : ∀ k, f k ∈ Submodule.span ℂ (Set.range j)) : m ≤ Module.finrank K C := by
  let b := Module.finBasis K C
  have hle : Submodule.span ℂ (Set.range j) ≤ Submodule.span ℂ (Set.range fun k => j (b k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h1 := linearIndependent_le_span_aux' f hf (Set.range fun k => j (b k))
    (by rintro _ ⟨k, rfl⟩; exact hle (hm k))
  have h2 : Fintype.card (Set.range fun k => j (b k)) ≤ Module.finrank K C :=
    (Fintype.card_range_le _).trans (Fintype.card_fin _).le
  exact (Fintype.card_fin m).symm.le.trans (h1.trans h2)

theorem linearIndependent_conj {ι : Type} {m : ℕ} {f : Fin m → ι → ℂ} (hf : LinearIndependent ℂ f) :
    LinearIndependent ℂ fun k x => starRingEnd ℂ (f k x) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc k
  have h := hf (fun k => starRingEnd ℂ (c k)) (funext fun x => by
    have := congrArg (starRingEnd ℂ) (congrFun hc x)
    simpa [Finset.sum_apply, map_sum] using this) k
  simpa using h

theorem eval_eq_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (he : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x : H)
    (hx : e x v = 0) : x = 0 := by
  rw [← inner_self_eq_zero (𝕜 := ℂ), he]
  refine mul_eq_zero_of_right _ ?_
  by_cases h : ∃ c, IsMultIP M μ 𝓕 (e x) (e x) c
  · have h1 := (ipM_spec M μ 𝓕 _ _ h v v).2
    simp only [hx, Pi.zero_apply, mul_zero, integral_zero, inner_self_eq_norm_sq_to_K, hv] at h1
    simpa using h1.symm
  · exact dif_neg h

set_option maxHeartbeats 1000000 in

theorem adel_mem_span {D : D7} (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n) (hL : LastPos (T.Q.Dw j) a)
    (hn : 8 * D.R.f * D.R.r + 4 ≤ n) (P : FDSec (T.U j σ).X) (hP : IsHolCusp (T.U j σ).X (laU (T.U j σ) a n) P) :
    adel (T.V j σ) (T.dict j σ) (T.mu j σ) P ∈ Submodule.span ℂ
      (Set.range ((adel (T.V j σ) (T.dict j σ) (T.mu j σ)).comp (rdC (T.U j) σ a n))) := by
  obtain ⟨-, hA, -, -, -, hdeg, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr1 : 1 ≤ D.R.r := (hnum j hj).2.1
  obtain ⟨hrk, hW⟩ := h.modelW j hj σ hσ
  obtain ⟨th, hrk', -, hdict⟩ := h.dictU j hj σ hσ
  have hG := GlobalTheory.RunIn.gamAt_of_lawsJ D T h
  have hle := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr1 hA (fun σ hσ => h.unf j hj σ hσ) σ hσ
    (fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩)
    (by
      intro k ga hga hv
      refine hG j hj σ hσ k ga hga fun x hx => ?_
      obtain ⟨u, hu, he⟩ := hv x hx
      refine ⟨u, hu, ?_⟩
      rw [he, Nat.cast_smul_eq_nsmul]
      exact add_sub_cancel_left _ _)
    a n hD hL
    (by
      rw [hdeg]
      calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
        _ ≤ n := hn)
    (fun k => h.chiTriv j hj σ hσ a n hD k)
  have hle' : GlobalTheory.Dict.holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (Set.range (rdC (T.U j) σ a n)) := by
    refine le_trans hle (Submodule.span_mono ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  have hmem : (fun k => ((T.U j σ).X k).dom.indicator (P k)) ∈ GlobalTheory.Dict.holSub0 (T.U j σ).X (laU (T.U j σ) a n) := by
    refine ⟨Submodule.subset_span fun k => ?_, fun k x hx => Set.indicator_of_notMem hx _⟩
    exact (GlobalTheory.DomCongr.bddSec_cusp_congr _ _ ((T.U j σ).X k) _ (P k) _
      (fun x hx => (Set.indicator_of_mem hx _).symm)).2 (hP k)
  have he : adel (T.V j σ) (T.dict j σ) (T.mu j σ) (fun k => ((T.U j σ).X k).dom.indicator (P k)) =
      adel (T.V j σ) (T.dict j σ) (T.mu j σ) P := by
    funext g
    show T.mu j σ g * ((T.U j σ).X (T.dict j σ g).1).dom.indicator (P (T.dict j σ g).1) (T.dict j σ g).2 =
      T.mu j σ g * P (T.dict j σ g).1 (T.dict j σ g).2
    rw [Set.indicator_of_mem (hdict.2.2.2.1 g)]
  rw [← he]
  have h2 := Submodule.mem_map_of_mem (f := adel (T.V j σ) (T.dict j σ) (T.mu j σ)) (hle' hmem)
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

set_option maxHeartbeats 1000000 in

theorem card_le_finrank_cusp {D : D7} (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n) (hL : LastPos (T.Q.Dw j) a)
    (hn : 8 * D.R.f * D.R.r + 4 ≤ n) (θ : InfFam D) (hθ : IsInfFam θ) (w : D.what₂.Tau → ℕ → ℤ) (e : D.what₂.Tau → ℤ)
    (hmu : ∀ k ∈ T.Kf j σ, T.mu j σ k = 1) (hinf : ∀ ρ, HasInfExp D (T.chiW j σ) ρ (-(e ρ : ℚ)))
    (hw : ∀ k (ρ : D.what₂.Tau) (τ : ((T.U j σ).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r,
      laU (T.U j σ) a n k τ c = w ρ c + e ρ)
    {W : HSp D} (hV : T.V j σ = W) (x : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hx : NegFirst W (D.R.sigW j).2 x) {m : ℕ} (φ : Fin m → GA D W → ℂ) (hφ : LinearIndependent ℂ φ)
    (hh : ∀ k, IsHolFor θ W x (fun ρ c => w ρ c) (φ k)) (hl : ∀ k, ∀ γ ∈ GQ W, ∀ g, φ k (γ * g) = φ k g)
    (hk : ∀ Kf, IsLevelK W (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ κ ∈ Kf, ∀ g, φ k (g * κ) = φ k g)
    (hb : ∀ k, ∃ C : ℝ, ∀ g, ‖φ k g‖ ≤ C) : m ≤ Module.finrank T.Q.c.F (T.cuspA j a n) := by
  subst hV
  obtain ⟨hr, x₀, hB⟩ := GlobalTheory.T.base_dictionary_exists_good_embedding D T h j hj σ hσ θ hθ
  have hK := h.levelK j hj σ hσ
  have hM := h.muUnit j hj σ hσ
  have hq : ∀ k, ((T.U j σ).X k).p0 = (D.R.sigW j).2 := fun k =>
    ((h.unf j hj σ hσ).2.1 k).1.trans (h.pins.2.2.2 j hj).2.1
  obtain ⟨u, hu⟩ := GlobalTheory.T.character_expansion_weight_compat D θ _ _ hr _ _ _ _ x₀ (laU (T.U j σ) a n) x _ (fun ρ c => w ρ c) e (T.mu j σ) hθ hB
    (fun k hk => ((hK k).1 hk).1) hq hx hM.1 hM.2.1 hM.2.2.1 hmu
    (GlobalTheory.T.archimedean_character_det_power D θ _ _ _ e hθ (h.muVal j hj σ hσ) hinf) (fun k ρ τ hτ c => hw k ρ τ hτ _)
    (h.chiTriv j hj σ hσ a n hD) (fun k τ c d hc hd => by
      rw [← hq k] at hc hd
      simp only [laU, if_pos hd, if_neg (not_le.2 hc)]
      omega)
  have : FiniteDimensional T.Q.c.F (T.cuspA j a n) := h.cuspFD j hj a n hD
  refine card_le_finrank_of_semilinear ((adel (T.V j σ) (T.dict j σ) (T.mu j σ)).comp (rdC (T.U j) σ a n))
    (fun k g => φ k (g * u)) ?_ fun k => ?_
  · rw [Fintype.linearIndependent_iff] at hφ ⊢
    intro c hc
    refine hφ c (funext fun g => ?_)
    have := congrFun hc (g * u⁻¹)
    simpa [Finset.sum_apply] using this
  · obtain ⟨P, hP, hPe⟩ := hu (φ k) (hh k) (hl k) (hk _ hK k) (hb k)
    rw [show (fun g => φ k (g * u)) = adel (T.V j σ) (T.dict j σ) (T.mu j σ) P from funext hPe]
    exact adel_mem_span T h j hj σ hσ a n hD hL hn P hP

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def evL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' x y := by simp [evAt]
  map_smul' c x := by simp [evAt]

theorem parAt_sig (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ) = Formalism.L2.NTheta.holPar (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2
      (Formalism.L2.NTheta.kapW (D.hc (lab σ ρ)) _ _) := by
  unfold kapAt
  rw [show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]

set_option maxHeartbeats 1000000 in

theorem finrank_model_le (hP : GlobalTheory.Published.CuspRapidDecay) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hL : R.toLevCh.Is A.μ0)
    (hθ : R.models_inf) (hH : R.models_HW) (h : TieIn T R κ v₀) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank T.Q.c.F (Cu T κ i) := by
  have hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
    have := D.R.m_add_three_le_k
    have := i.2
    simp only [Ranks.sigW, Ranks.r]
    omega
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h1 : ∃ ρ, tauE D ρ = τ
    · exact ⟨h1.choose⟩
    · exact ⟨(not_not.1 (mt (GlobalTheory.SmoothForms.RealPts.tauE_cm D τ).2 h1)).choose⟩
  have hn' : 8 * D.R.f * D.R.r + 4 ≤ (κ i).n := (h.kap i ρ₀).2.2 ▸ hn
  let β := Module.finBasis ℂ (R.HW i σ).H
  have hM : ∀ x, IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv))
      ((R.HW i σ).e x) := fun x =>
    (GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 ((hH i σ).2.1.le ⟨x, rfl⟩)
  have hind : LinearIndependent ℂ fun k => (R.HW i σ).e (β k) (v₀ i σ) :=
    β.linearIndependent.map' (evL T R i σ (v₀ i σ)) (LinearMap.ker_eq_bot'.2 fun x hx =>
      eval_eq_zero _ (R.HW i σ).e _ _ _ (hH i σ).2.2 _ ((h.hv₀ i σ).norm R) x hx)
  have hlev : ∀ Kf, IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ c ∈ Kf, ∀ g,
      (R.HW i σ).e (β k) (v₀ i σ) (g * c) = (R.HW i σ).e (β k) (v₀ i σ) g := fun Kf hK k c hc g => by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.level_character_trivial_on_subgroup D T0 R.toLevCh A.μ0 hL i Kf hK c hc
    rw [(hM _).lev _ c h1, h2, one_mul]
  have hbd : ∀ k, ∃ C : ℝ, ∀ g, ‖(R.HW i σ).e (β k) (v₀ i σ) g‖ ≤ C := fun k =>
    GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ ((hM _).aut _) ((hM _).cusp _)
  have key : ∀ σ' : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ') → (∀ ρ, lab σ' ρ = lab σ ρ) →
      ∀ x, NegFirst (Wc D i) (D.R.sigW ((i : ℕ) + 1)).2 x → ∀ φ : Fin (Module.finrank ℂ (R.HW i σ).H) → GA D (Wc D i) → ℂ,
      LinearIndependent ℂ φ → (∀ k, IsHolFor R.θ (Wc D i) x
        (fun ρ c => wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c) (φ k)) →
      (∀ k, ∀ γ ∈ GQ (Wc D i), ∀ g, φ k (γ * g) = φ k g) →
      (∀ Kf, IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ c ∈ Kf, ∀ g, φ k (g * c) = φ k g) →
      (∀ k, ∃ C : ℝ, ∀ g, ‖φ k g‖ ≤ C) → Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank T.Q.c.F (Cu T κ i) := by
    intro σ' hσ' hlab x hx φ h1 h2 h3 h4 h5
    choose e he using fun ρ => (D.hc (lab σ' ρ)).e_int i
    refine card_le_finrank_cusp T h.laws _ (inR i) _ hσ' _ _ (dom_wtA (κ i)) (GlobalTheory.T.last_weight_positive D T κ h.laws h.kap i) hn' R.θ hθ
      (fun ρ c => wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c) e
      (GlobalTheory.T.level_character_trivial_on_level D G Pl0 T0 A T R h.laws hL h.chiR i σ' hσ') (fun ρ => he ρ ▸ (h.chiR i σ' hσ').2.2.1 ρ)
      (fun k ρ τ hτ c => ?_) (h.laws.spaceW _ (inR i) _ hσ') x hx φ h1 h2 h3 h4 h5
    rw [← hlab ρ]
    exact GlobalTheory.T.weight_label_at_unfolding D T κ h.laws h.alg h.kap i σ' hσ' e (fun ρ => (he ρ).symm) k ρ τ hτ c
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · obtain ⟨x, hx, hhol⟩ := GlobalTheory.T.holomorphic_extremal_negative_first D R.θ _ _ (R.MW i σ) (fun ρ => D.hc (lab σ ρ)) _ _ hθ hpq (rank_Wc i)
      (fun ρ => (if_pos ((GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).1.1 hσ)).trans (parAt_sig i σ ρ)) _ (h.hv₀ i σ).1
    exact key σ hσ (fun _ => rfl) x hx _ hind (fun k => hhol _ _ _ (hM _)) (fun k => ((hM _).aut _).left) hlev hbd
  · obtain ⟨x, hx, hhol⟩ := GlobalTheory.T.antiholomorphic_extremal_negative_first D R.θ _ _ (R.MW i σ) (fun ρ => D.hc (lab σ ρ)) _ _ hθ hpq (rank_Wc i)
      (fun ρ => (if_neg (mt (GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).1.2 hσ)).trans (congrArg dualPar (parAt_sig i σ ρ))) _
      (h.hv₀ i σ).1
    refine key ((starRingEnd ℂ).comp σ) (good_resC T hσ) (fun ρ => (GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).2) x hx _
      (linearIndependent_conj hind) (fun k => hhol _ _ _ (hM _)) (fun k γ hγ g => ?_) (fun Kf hK k c hc g => ?_)
      fun k => (hbd k).imp fun C hC g => ?_
    · exact congrArg _ (((hM _).aut _).left γ hγ g)
    · exact congrArg _ (hlev Kf hK k c hc g)
    · exact (Complex.norm_conj _).trans_le (hC g)

end GlobalTheory.HolRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealGramHermitianSpaceDoubledBlockDiagonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realGram_hermitianSpaceDoubled_blockDiagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
            gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              GlobalTheory.DblSchr.omdOf omd₀ gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  first | exact @GlobalTheory.DblRestr.restr_boxFun | exact GlobalTheory.DblRestr.restr_boxFun | (intros; apply GlobalTheory.DblRestr.restr_boxFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantFactorsProd
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ProdForm
theorem resNe : ∀ (K : Type) [Field K] (P Q : K[X]), P.Monic → Q.Monic → IsCoprime P Q → resultant P Q ≠ 0 := by
  intro K _ P Q _ _ hc
  exact Polynomial.resultant_ne_zero P Q hc

theorem resMap : ∀ (K L : Type) [Field K] [Field L] (f : K →+* L) (P Q : K[X]),
    resultant (P.map f) (Q.map f) = f (resultant P Q) := by
  intro K L _ _ f P Q
  rw [Polynomial.natDegree_map, Polynomial.natDegree_map]
  exact Polynomial.resultant_map_map P Q _ _ f
end GlobalTheory.ProdForm

namespace GlobalTheory.ProdForm

end GlobalTheory.ProdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBoxTensorLeftFixedLinearApplyStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_generated_antidiag_splitPlace_V : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  first | exact @GlobalTheory.DblGenV.mem_of_KD_diag_anti | exact GlobalTheory.DblGenV.mem_of_KD_diag_anti | (intros; apply GlobalTheory.DblGenV.mem_of_KD_diag_anti <;> assumption)
end

