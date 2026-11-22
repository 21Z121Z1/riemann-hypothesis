import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Sector
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.MassBridge

theorem core (D : D7) (V : HSp D) (r : ℕ) (hrk : V.rank = r) (hV : V.SigOK) (P Q : ℕ)
    (hsig : ∀ τ, V.sig τ = (P, Q)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)))
    (hKo : IsOpen {h : GA D V | finE V h ∈ K}) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hF : IsMeasFD V K μ 𝓕) (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ))
    (x : Frame Ψ r) (p0 : Ψ → ℕ) (J : Type)
    (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → GA D V)
    (hr : 2 ≤ r)
    (hx : ∀ τ : Ψ, gram τ.1 (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))) (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ))
    (hΨ : ∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = tauE D ρ)
    (hh : ∀ j, h j ∈ GfC V)
    (h4 : ∀ (j j' : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E), g ∈ GQ V →
      matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
      finE V ((h j')⁻¹ * g * h j) ∈ K → IsIntegral ℤ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det ∧
        ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 → j = j'))
    (h5 : ∀ (j : J) (g : GA D V) (γ : GL (Fin V.rank) D.host.E) (γr : GL (Fin r) D.host.E), g ∈ GQ V →
      matHom V g = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm) =
        (γr : Matrix (Fin r) (Fin r) D.host.E) → (γr : Matrix (Fin r) (Fin r) D.host.E).det = 1 →
      finE V ((h j)⁻¹ * g * h j) ∈ K →
      γr ∈ ratStab (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
        (Λ : Set (Fin r → D.host.E)) (s j)) :
    ENNReal.ofReal ((1 / 32 : ℝ) ^ (D.R.f * r ^ 2)) * ∑' j, covolume
      (inReal Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
        (ratStab (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm)))
          (Λ : Set (Fin r → D.host.E)) (s j)))
      (realSU Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))))
      (riemHaar Ψ (Matrix.transpose ((V.gram).submatrix (Fin.cast hrk.symm) (Fin.cast hrk.symm))) x) ≤ μ 𝓕 := by
  subst hrk
  classical
  change ENNReal.ofReal ((1 / 32 : ℝ) ^ (D.R.f * V.rank ^ 2)) * ∑' j, covolume
      (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) ≤ μ 𝓕
  have hx' : ∀ τ : Ψ, gram τ.1 (V.gram)ᵀ (mat x τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) := hx
  obtain ⟨hLC, hSC, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := hF.1.1
  obtain ⟨⟨θ, hθ⟩, H1⟩ := hF.1.2
  obtain ⟨⟨A, hA⟩, H2⟩ := H1 θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := H2 A hA
  obtain ⟨X₀, σ, x₀, e, hG, hσ, hx₀, hid⟩ := GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification D V P Q hV hsig A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D V θ A hV hθ hA
  let a₀ : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 :=
    fun ρ => (e ρ).symm ⟨0, by omega⟩
  obtain ⟨π, hπc, hπ, hπe⟩ := GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ hid
  have hcard : X₀.Ψ.card = D.R.f := by
    rw [← Fintype.card_coe, ← Fintype.card_congr σ, D.what₂.card_Tau]
  have hf : 1 ≤ D.R.f := UpperTheory.Mu.one_le_f D.R
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; omega
  obtain ⟨eΨ, heΨ⟩ := hΨ
  have hΨX : X₀.Ψ = Ψ := by
    ext τ; constructor
    · intro hτ
      obtain ⟨ρ, hρ⟩ := σ.surjective ⟨τ, hτ⟩
      have e1 : τ = tauE D ρ := by rw [← hσ ρ, hρ]
      rw [e1, ← heΨ ρ]; exact (eΨ ρ).2
    · intro hτ
      obtain ⟨ρ, hρ⟩ := eΨ.surjective ⟨τ, hτ⟩
      have e1 : τ = tauE D ρ := by rw [← heΨ ρ, hρ]
      rw [e1, ← hσ ρ]; exact (σ ρ).2
  have hherm : ∀ a b, cc ((V.gram)ᵀ a b) = (V.gram)ᵀ b a := by
    intro a b
    have e1 := X₀.Gm_herm a b
    rw [hG] at e1
    simp only [cc, Matrix.neg_apply, Matrix.transpose_apply, map_neg, neg_inj] at e1 ⊢
    exact e1
  have htr : ∀ j, covolume (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) =
      covolume (inReal X₀.Ψ X₀.Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
      (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀) := fun j =>
    GlobalTheory.T.gram_frame_congruence_subgroup D.host.E V.rank Ψ X₀.Ψ (V.gram)ᵀ X₀.Gm x x₀ p0 X₀.p0 _ hΨX hG hherm hx' hx₀
  choose F hFm hFcov hFfree using fun j => GlobalTheory.T.exists_packingSet_measure_ge_covolume (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀)
    (inReal X₀.Ψ X₀.Gm (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j))) (GlobalTheory.T.countable_rationalSubgroupInRealSpecialUnitary _ _ _ _ _)
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  let B : J → Set (∀ ρ, Upq V ρ) := fun j => π ⁻¹' F j ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}
  have hBm : ∀ j, MeasurableSet (B j) := fun j =>
    (hπc.measurable (hFm j)).inter (GlobalTheory.T.measurableSet_det_im_pos_at_index D.what₂.Tau _ _ ρ₀)
  let T : J → Set (GA D V) := fun j => {y | finE V ((h j)⁻¹ * y) ∈ K ∧ rp y ∈ B j}
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    ((hKo.preimage (continuous_const.mul continuous_id)).measurableSet).inter (hrpc.measurable (hBm j))
  have hμT : ∀ j, μ (T j) = Measure.pi m (B j) := fun j =>
    GlobalTheory.T.level_measure_finite_part_preimage D V θ A m rp K μ hV hθ hA hm hrpc hrp hKo hF.1 (h j) (hh j) (B j) (hBm j)
  have hlow : ∀ j, ENNReal.ofReal ((1 / 16 : ℝ) ^ (X₀.Ψ.card * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F j) ≤ μ (T j) := by
    intro j
    rw [hμT j]
    exact GlobalTheory.T.archimedean_mass_product_lower_bound_unitary_pq D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ π m ρ₀ (by omega) hid hπc hπ hπe hm (F j) (hFm j)
  have hdisj := GlobalTheory.T.indefinite_frame_real_special_unitary D V θ A rp X₀.Ψ X₀.Gm x₀ σ e π K Λ J s h F ρ₀ hG hθ hrp hid hσ hπe hFfree h4
    (fun j g γ hg hmg hd hK => h5 j g γ γ hg hmg rfl hd hK)
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.mul_iSup]
  refine iSup_le fun J0 => ?_
  let sc : GA D V → ℕ := fun y => UpperTheory.Ram.Sector.sec (NumberField.Units.torsionOrder D.host.E) (UpqT.mat (rp y ρ₀)).det
  have hscm : Measurable sc := by
    have hc : Continuous fun g : Upq V ρ₀ => (UpqT.mat g).det := (continuous_id.matrix_det).comp GlobalTheory.UpqTopology.continuous_mat
    exact (UpperTheory.Ram.Sector.measurable_sec _).comp
      (hc.measurable.comp ((measurable_pi_apply ρ₀).comp hrpc.measurable))
  have hlay : ∀ k, ∑ j ∈ J0, μ (T j ∩ {y | sc y = k}) ≤ μ 𝓕 := by
    intro k
    let Tk : J → Set (GA D V) := fun j => T j ∩ {y | sc y = k}
    have hTkm : ∀ j, MeasurableSet (Tk j) := fun j => (hTm j).inter (hscm (measurableSet_singleton k))
    let S := ⋃ j ∈ J0, Tk j
    have hSm : MeasurableSet S := Finset.measurableSet_biUnion J0 fun j _ => hTkm j
    have hTd : Set.PairwiseDisjoint (↑J0) Tk := by
      intro j _ j' _ hne
      refine Set.disjoint_left.2 fun y hy hy' => hne ?_
      exact (hdisj 1 (GQ V).one_mem j j' y hy.1 (by rw [one_mul]; exact hy'.1) (by rw [one_mul])).2
    have hμS : μ S = ∑ j ∈ J0, μ (Tk j) := measure_biUnion_finset hTd fun j _ => hTkm j
    have hSF : μ S ≤ μ 𝓕 := by
      refine hF.2.measure_le_of_pairwise_disjoint hSm.nullMeasurableSet ?_
      intro g g' hne
      refine Disjoint.aedisjoint (Set.disjoint_left.2 fun z hz hz' => hne ?_)
      obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.1 hz.1
      obtain ⟨y', hy', hyz'⟩ := Set.mem_smul_set.1 hz'.1
      obtain ⟨j, -, hyj⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨j', -, hyj'⟩ := Set.mem_iUnion₂.1 hy'
      have h1 : (g : GA D V) * y = z := hyz
      have h2 : (g' : GA D V) * y' = z := hyz'
      have e1 : ((g'⁻¹ * g : GQ V) : GA D V) * y = y' := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, h1, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
      have e2 := (hdisj _ (g'⁻¹ * g).2 j j' y hyj.1 (by rw [e1]; exact hyj'.1)
        (by rw [e1]; exact (hyj.2 : sc y = k).trans (hyj'.2 : sc y' = k).symm)).1
      have e3 : g'⁻¹ * g = 1 := Subtype.ext e2
      exact (inv_mul_eq_one.1 e3).symm
    exact hμS ▸ hSF
  have hw : NumberField.Units.torsionOrder D.host.E ≤ 2 ^ (D.R.f * V.rank ^ 2) :=
    (UpperTheory.Mu.host_torsionOrder_le D.host).trans (UpperTheory.Ram.Sector.eight_sq_le hf (by omega))
  refine UpperTheory.Ram.Sector.le_of_mul_le hw ?_
  rw [Finset.mul_sum]
  calc ∑ j ∈ J0, ENNReal.ofReal ((1 / 16 : ℝ) ^ (D.R.f * V.rank ^ 2)) *
        covolume (inReal Ψ (V.gram)ᵀ (ratStab (V.gram)ᵀ (Λ : Set (Fin V.rank → D.host.E)) (s j)))
          (realSU Ψ (V.gram)ᵀ) (riemHaar Ψ (V.gram)ᵀ x) ≤ ∑ j ∈ J0, μ (T j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [htr j, ← hcard]
        calc _ ≤ ENNReal.ofReal ((1 / 16 : ℝ) ^ (X₀.Ψ.card * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F j) := by
              gcongr; exact hFcov j
          _ ≤ μ (T j) := hlow j
    _ ≤ _ := UpperTheory.Ram.Sector.sum_le_of_layers μ T sc _
        (fun y => UpperTheory.Ram.Sector.sec_lt (NumberField.Units.torsionOrder_pos D.host.E) _) J0 _ hlay

end GlobalTheory.CovTop.MassBridge

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MassBridge

theorem bridge_bound : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ 𝓕 → letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → Theta.GA D (Wc D i)), (2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f) → (G = Matrix.transpose ((HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm)) ∧ (∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = TH.tauE D ρ) ∧ (∀ j, h j ∈ Theta.GfC (Wc D i)) ∧ (∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((h j')⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j')) ∧ (∀ (j : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) → (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 → Formalism.IndefR.Lev.finE (Wc D i) ((h j)⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → γr ∈ GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) → (letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _; haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩; ENNReal.ofReal (c ^ (D.R.f * D.R.r ^ 2)) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) ≤ μ 𝓕) := by
  refine ⟨1 / 32, by norm_num, by norm_num, ?_⟩
  intro D Tu Cl t0 hCl i μ 𝓕 hF G Λ Ψ x p0 J s h hdata hlink
  obtain ⟨hr, -, -, -, hx, -, -⟩ := hdata
  obtain ⟨hG, hΨ, hh, h4, h5⟩ := hlink
  subst hG
  exact core D (Wc D i) D.R.r (rank_Wc i) (D.sp.W_sig _) _ _ (D.sp.W_sigval _ (Nat.le_add_left _ _) i.2) _
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev _ _ _) μ 𝓕 hF Λ Ψ x p0 J s h hr hx hΨ hh h4 h5

end GlobalTheory.CovTop.MassBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelOfSurjectiveAbelianVarietyHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem cancel_of_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left →
    ∀ (C : AbVar K) (f g : B ⟶ C), p ≫ f = p ≫ g → f = g := by
  intro K _ A B p hp C f g h
  have hB : IsIntegral B.X.left := (GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B).1
  have hsep : IsSeparated C.X.hom := C.ab.proper.toIsSeparated
  apply hom_ext
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated C.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) p.hom.left ?_)
  have := congrArg (fun u => (Hom.hom u).left) h
  simpa only [comp_hom, Over.comp_left] using this

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualPrimePowConvPairing
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem cartier_primePow_pairing (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r :=
  convPow_primePow_apply_pow p R h G n r χ a

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencerStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeformation_gluing_of_logKodairaSpencer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1), IsBaseFrame TF U e v P hU → ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (D.1 r))) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G P.x π → IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' → i ≫ π' = π → (∀ σ k, (ub σ k).left ≫ π = P.u σ k) → GlobalTheory.CechKS.IsCechKS A A' i (Xo.univ.t.PP.L.pull π) (fun a => ub (e.symm a).1 (e.symm a).2) (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) := by
  first | exact @GlobalTheory.CechTransport.cech_of_logKS | exact GlobalTheory.CechTransport.cech_of_logKS | (intros; apply GlobalTheory.CechTransport.cech_of_logKS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowEqMumfordFormulaStatement
section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_zpow_eq_mumford_formula : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (z : T ⟶ A) (n : ℤ), GlobalTheory.CechPic.pull (z ^ n).left (GlobalTheory.CechPic.cls L hL) = tri n • GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) + tri (-n) • GlobalTheory.CechPic.pull (z⁻¹).left (GlobalTheory.CechPic.cls L hL) := by
  first | exact @GlobalTheory.PowPull.pull_zpow | exact GlobalTheory.PowPull.pull_zpow | (intros; apply GlobalTheory.PowPull.pull_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowMulMixedSplitStatement
section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (x y : T ⟶ A) (m n a b : ℤ), a • GlobalTheory.CechPic.pull (x ^ m * y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m * y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL) = (a • GlobalTheory.CechPic.pull (x ^ m).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + (a • GlobalTheory.CechPic.pull (y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + ((a + b) * (m * n)) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
  first | exact @GlobalTheory.CubeMixed.mixed_mul | exact GlobalTheory.CubeMixed.mixed_mul | (intros; apply GlobalTheory.CubeMixed.mixed_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShortSeriesTranslateFrameConstantMultipleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralShortSeriesTranslate_frameConstant_multiple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ z ∈ Subgroup.center G, ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) (actLev T.J.toCore.Q.c (O i).lev2 z⁻¹ ((F₀).1 : T.R ((i : ℕ) + 1))) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  first | exact @GlobalTheory.HeartFrame.central_short_series_frame | exact GlobalTheory.HeartFrame.central_short_series_frame | (intros; apply GlobalTheory.HeartFrame.central_short_series_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartTransitionMapsDescendOverlapsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_transition_maps_descend_overlaps : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ (i j : J) (V : U.left.Opens), (∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j)) → ∃ τ : V.toScheme ⟶ U.left, ∀ (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ V.toScheme), a ≫ e i = b ≫ e j → v ≫ V.ι = a ≫ pullback.fst _ _ → v ≫ τ = b ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.Mum.chart_transition_descends | exact GlobalTheory.Mum.chart_transition_descends | (intros; apply GlobalTheory.Mum.chart_transition_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFubiniStudyTotal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.FSMass

theorem chern_mass_hermitian_O_one_projective : ∀ N : ℕ, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N 1 Set.univ = 1 ∧ ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).chernPart N (-1) Set.univ = 0 := by
  intro N
  have hproj : IsProjOver (PSpace.str ℂ N) := ProjSpace.isProjOver_str ℂ N
  haveI : IsIntegral (PSpace ℂ N) := ProjSpace.isIntegral_of_isDomain ℂ N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).IsCInf := (ProjSpace.hermitianTwistingSheaf ℂ N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf ℂ N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := GlobalTheory.T.exists_projSpace_standardChart_fubiniStudy N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace ℂ N) ∈ ProjSpace.chart ℂ N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace ℂ N)).mem_open_set_iff (ProjSpace.chart ℂ N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := GlobalTheory.T.chernPart_complement_dense_open_null_field ℂ (PSpace ℂ N) (PSpace.str ℂ N) (RingHom.id ℂ) N hproj _ hgen _
    ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)) 1
  rw [← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (GlobalTheory.T.lintegral_fubiniStudy_density_eq_one' N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, GlobalTheory.T.det_complexHessian_fubiniStudy_potential N v]
  simp
end GlobalTheory.FSMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTopPowerPullbackSmallerDimEqZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_topPower_pullback_smaller_dim_eq_zero : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e e' : ℕ), IsArithVar p e → IsArithVar q e' → e < e' → ∀ (g : Y ⟶ X) (hg : g ≫ p = q), g (genericPoint Y) = genericPoint X → ∀ (N : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ), ((N.pull g hg).φ σ).chernPart e' ε = 0 := by
  first | exact @GlobalTheory.ChernLowDim.chernPart_pull_of_lt | exact GlobalTheory.ChernLowDim.chernPart_pull_of_lt | (intros; apply GlobalTheory.ChernLowDim.chernPart_pull_of_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernForms
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTri

theorem coeff_charpolyRev_neg_of_tri {R : Type} [CommRing R] {s : ℕ} (F : Matrix (Fin s) (Fin s) R)
    (h : ∀ i j, j < i → F i j = 0) (k : ℕ) :
    (Matrix.charpolyRev (-F)).coeff k = ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, F i i := by
  rw [Matrix.charpolyRev, Matrix.det_of_upperTriangular]
  · have e : ∀ i, ((1 : Matrix (Fin s) (Fin s) (Polynomial R)) -
        (Polynomial.X : Polynomial R) • (-F).map Polynomial.C) i i = 1 + Polynomial.C (F i i) * Polynomial.X := by
      intro i
      rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, map_neg, smul_eq_mul,
        mul_neg, sub_neg_eq_add, mul_comm]
    simp only [e]
    rw [Finset.prod_one_add, Polynomial.finset_sum_coeff]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, Polynomial.coeff_C_mul_X_pow]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp [eq_comm]
  · intro i j hij
    have hij' : j < i := hij
    simp [h i j hij', hij'.ne']

theorem chernAt_tri : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ j, chernAt T v j = aeval (fun i => ofValues (ddc (fun x => -Real.log (d i x)) v)) (esymm (Fin s) ℂ j) := by
  intro n s T d v hT hd htri j
  have key := GlobalTheory.T.chernCurvature_lowerTriangular_positive_diagonal n s T d v hT hd htri
  rw [chernAt, chernPoly, coeff_charpolyRev_neg_of_tri _ (fun a b hab => by
    simp [curvPoly, fun ξ η => (key ξ η).1 a b hab]), esymm]
  simp only [map_sum, map_prod, aeval_X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have e (i : Fin s) : ofValues (ddc (fun x => -Real.log (d i x)) v) =
      kappa • (aeval sym (curvPoly T v i i) : Ev n) := by
    simp only [ofValues, ddc, curvPoly, Matrix.of_apply, map_sum, map_mul, aeval_C, aeval_X, Finset.smul_sum,
      fun ξ η => (key ξ η).2 i, leviForm_neg, ← Algebra.smul_def, smul_smul, ContinuousLinearMap.neg_apply]
  simp only [e]
  rw [Finset.prod_smul, Finset.prod_const, (Finset.mem_powersetCard.1 ht).2]

end GlobalTheory.ChernTri
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntPullFubiniStudyEqZeroOfNotDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory

theorem chernInt_pull_fubiniStudy_eq_zero_of_not_dominant : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), (∃ x : PSpace ℂ Y.dim, ¬ π (genericPoint Y.X) ⤳ x) → Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = 0 := by
  intro Y π hπ ⟨x, hx⟩
  have := ProjSpace.isIntegral_of_isDomain ℂ Y.dim
  obtain ⟨-, -, -, A', hA'⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  have hA : IsAlgAtlas (ProjAn.finAtlas ℂ (RingHom.id ℂ) Y.dim) := AnRead.isAlgAtlas_finAtlas _
  have hne : π (genericPoint Y.X) ≠ genericPoint (PSpace ℂ Y.dim) := fun h =>
    hx (h ▸ genericPoint_specializes x)
  have hc := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf (RingHom.id ℂ)
  have hs := (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).isSmooth hA.anRead
  rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y _ _ (hc.pull π hπ)).2 A' hA',
    SameForm.mInt_eq (fun _ => hs.sameForm_pull hA hA' π hπ)]
  exact rankDrop _ A' _ (hA.holoMap hA' (f := π) fun _ => rfl)
    (GlobalTheory.T.finrank_range_fderiv_lt_of_not_dominant_charts ℂ _ _ _ _ _ _ _ A' hA hA' π hπ hne) _ (fun _ => hs.isPotential hA) _

end GlobalTheory
end

