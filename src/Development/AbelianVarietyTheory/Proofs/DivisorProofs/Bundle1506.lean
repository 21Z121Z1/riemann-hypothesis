import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSpanTranslatesOfNonzeroSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementInfinitePoints
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

noncomputable section
namespace GlobalTheory.LeviArch
open GlobalTheory.LeviPlane
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem leviElt_mat (σ : E →ₐ[F] E) (B : Base F E) (hcm : IsCMExt F E σ) {d r s : ℕ} (W : Spc F E d)
    (hW : W.IsSkew σ B r s) {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E d d₁) {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (t : (AE F E)ˣ) :
    mat (leviElt σ W W₁ H' t) = lev (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (t : AE F E)
      (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) := by
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hσ := sigma_invol hcm
  have hc : ∀ x, c (c x) = x := fun x => cA_invol hσ x
  have hJ : ∀ i j, c (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    simp only [hcdef, incM, Matrix.map_apply, cAr_inclR, hW.skew, map_neg]
  have hxx : fm c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [fm_inc, hH.xx, map_zero]
  have hyy : fm c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [fm_inc, hH.yy, map_zero]
  have hxy : fm c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [fm_inc, hH.xy, map_one]
  have hι : ∀ j, fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.x) = 0 ∧
      fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.y) = 0 := by
    intro j
    have hcol : (fun i => incM F H'.ι i j) = incV F (H'.ι *ᵥ Pi.single j 1) := by
      ext i; simp [incV, incM, Matrix.mulVec_single_one]
    rw [hcol, fm_inc, fm_inc, (hH.orth _).1, (hH.orth _).2, map_zero]; exact ⟨rfl, rfl⟩
  let L : AE F E → AE F E → Matrix (Fin d) (Fin d) (AE F E) :=
    fun s r => lev c (incM F W.J) (incV F H'.x) (incV F H'.y) s r
  have hmul : ∀ s r s' r', L s r * L s' r' = L (s * s') (r * r') := fun s r s' r' =>
    lev_mul hc hJ hxx hyy hxy s r s' r'
  have h1 : L 1 1 = 1 := lev_one hc hJ hxx hyy hxy
  let g : GL (Fin d) (AE F E) :=
    ⟨L (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)), L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)),
      by rw [hmul, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, h1],
      by rw [hmul, ← map_mul, Units.inv_mul, Units.mul_inv, map_one, h1]⟩
  have hg : g ∈ GlobalTheory.WeilM.UG (cA σ) (incM F W.J) := by
    show (L _ _)ᵀ * incM F W.J * (L _ _).map (cA σ) = incM F W.J
    exact lev_unitary hc hJ hxx hyy hxy (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E))
      (by show (t : AE F E) * cA σ (cA σ _) = 1; rw [cA_invol hσ, Units.mul_inv])
  let m : UA σ W.J := ⟨g, hg⟩
  have hm : IsLevi (W₁ := W₁) H' t 1 m := by
    refine ⟨lev_X hxx hxy _ _, lev_Y hc hJ hxx hyy hxy _ _, ?_⟩
    have : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [this, Matrix.mul_one]
    exact lev_mul_ι _ hι _ _
  have e : leviElt σ W W₁ H' t = m :=
    GlobalTheory.LeviUniq.levi_unique F E σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t _ _ (isLevi_leviElt ⟨_, hm⟩) hm
  rw [e]
  rfl

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (c : R →+* R) (φ : R →+* S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) :
    (lev c J X Y s r).map φ = 1 + (φ s - 1) • Matrix.vecMulVec (fun i => φ (X i)) (fun i => φ ((J *ᵥ fun k => c (Y k)) i))
      - (φ r - 1) • Matrix.vecMulVec (fun i => φ (Y i)) (fun i => φ ((J *ᵥ fun k => c (X k)) i)) := by
  ext i j
  simp only [lev, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, smul_eq_mul, map_add, map_sub, map_mul]
  split_ifs <;> simp

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) : piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  simp [piInf, compInf, inclR, Algebra.TensorProduct.map_tmul]

theorem compInf_cA (σ : E →ₐ[F] E) (w : InfinitePlace F) (b : AE F E) :
    compInf F E w (cA σ b) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem compFin_cA (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (b : AE F E) :
    compFin F E v (cA σ b) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compFin F E v b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem piInf_cA {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (b : AE F E) :
    piInf τ (cA σ b) = star (piInf τ b) := by
  simp only [piInf, RingHom.comp_apply, compInf_cA]
  exact (infEmb_sigR hcm τ _).symm

theorem compFin_of_mem {t : (AE F E)ˣ} (ht : t ∈ idelesInf F E) (v : HeightOneSpectrum (𝓞 F)) :
    compFin F E v (t : AE F E) = 1 := by
  let u : AF F := (0, 1)
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h0 : u • ((t : AE F E) - 1) = 0 := ht u hu
  have hs : compFin F E v (algebraMap (AF F) (AE F E) u) = 1 := by
    have h2 : sndA F u = 1 := rfl
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (u ⊗ₜ[F] (1 : E)) = 1
    rw [Algebra.TensorProduct.map_tmul, evFin, AlgHom.comp_apply, h2, map_one, AlgHom.id_apply]
    rfl
  have h1 := congrArg (compFin F E v) h0
  rw [Algebra.smul_def, map_mul, hs, one_mul, map_sub, map_one, map_zero] at h1
  exact sub_eq_zero.1 h1

theorem leviElt_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ a ∈ idelesInf F E, toGAd hσ W.J hc (leviElt σ W W₁ H' a) ∈ infPts σ (c • W.J.map σ) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w), ∃ z : ℂ, z ≠ 0 ∧ GlobalTheory.Orb.archMat σ (c • W.J.map σ) τ (projArch σ (c • W.J.map σ) w (toGAd hσ W.J hc (leviElt σ W W₁ H' a))) = torMat ((c • W.J.map σ).map τ.1) (fun i => τ.1 (H'.x i)) (fun i => τ.1 (c⁻¹ * H'.y i)) z := by
  intro F E _ _ _ _ _ σ B hcm d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH a ha
  set g := toGAd hσ W.J hc (leviElt σ W W₁ H' a) with hg
  have hM : ((matHom _ σ (c • W.J.map σ) g : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
      lev (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (a : AE F E)
        (cA σ ((a⁻¹ : (AE F E)ˣ) : AE F E)) := by
    rw [matHom_apply, hg, toGAd_mat]
    exact leviElt_mat σ B hcm W hW W₁ H' hH a
  refine ⟨?_, fun w τ => ?_⟩
  · rw [mem_infPts_iff_forall]
    intro v
    apply matHom_injective
    rw [matHom_proj, map_one]
    apply Units.ext
    show (((matHom _ σ (c • W.J.map σ) g : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)).map (compFin F E v)) = 1
    have h1 := compFin_of_mem ha v
    have h2 : compFin F E v ((a⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
      have := congrArg (compFin F E v) a.mul_inv
      rwa [map_mul, h1, one_mul, map_one] at this
    rw [hM, map_lev, compFin_cA, h1, h2, map_one]
    simp
  · have hz : piInf τ (a : AE F E) ≠ 0 := by
      intro h
      have := congrArg (piInf τ) a.mul_inv
      rw [map_mul, h, zero_mul, map_one] at this
      exact zero_ne_one this
    refine ⟨piInf τ (a : AE F E), hz, ?_⟩
    rw [GlobalTheory.Orb.archMat_apply, matHom_projArch]
    change ((((matHom _ σ (c • W.J.map σ) g : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)).map
      (compInf F E w)).map (infEmb τ)) = _
    rw [hM, Matrix.map_map]
    change (lev _ _ _ _ _ _).map (piInf τ) = _
    have hinv : piInf τ ((a⁻¹ : (AE F E)ˣ) : AE F E) = (piInf τ (a : AE F E))⁻¹ := by
      have := congrArg (piInf τ) a.mul_inv
      rw [map_mul, map_one] at this
      exact eq_inv_of_mul_eq_one_right this
    rw [map_lev, piInf_cA hcm, hinv, star_inv₀]
    have hst : ∀ e : E, star (τ.1 e) = τ.1 (σ e) := fun e => (hcm.2.2.2 τ.1 e).symm
    have hcc : τ.1 c⁻¹ * τ.1 c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    set z := piInf τ (a : AE F E)
    ext i j
    simp only [torMat, projL, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, incV, incM, Matrix.map_apply, piInf_inclR,
      AlgHom.coe_toRingHom, cA_inclR, Pi.star_apply, hst]
    have hτc : τ.1 c ≠ 0 := (map_ne_zero _).2 hc
    have hs1 : ∀ k, star (τ.1 c⁻¹ * τ.1 (H'.y k)) * (τ.1 c * τ.1 (σ (W.J k j))) = τ.1 (W.J j k) * τ.1 (σ (H'.y k)) := by
      intro k
      rw [star_mul', hst, hst, hW.skew, map_inv₀, hcs]
      simp only [map_neg, map_inv₀, inv_neg]
      field_simp
    have hs2 : ∀ k, τ.1 (σ (H'.x k)) * (τ.1 c * τ.1 (σ (W.J k j))) = -τ.1 c * (τ.1 (W.J j k) * τ.1 (σ (H'.x k))) := by
      intro k
      rw [hW.skew, map_neg]
      ring
    simp only [cAr_inclR, piInf_inclR, hs1, hs2, ← Finset.mul_sum]
    linear_combination ((star z)⁻¹ - 1) * τ.1 (H'.y i) * (∑ k, τ.1 (W.J j k) * τ.1 (σ (H'.x k))) * hcc

end GlobalTheory.LeviArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_element_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m m' : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m → IsLevi (W₁ := W₁) H' t 1 m' → m = m' := by
  first | exact @GlobalTheory.LeviUniq.levi_unique | exact GlobalTheory.LeviUniq.levi_unique | (intros; apply GlobalTheory.LeviUniq.levi_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstantsStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_form_bounded_by_local_constants : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) := by
  first | exact @GlobalTheory.LinFormBound.main | exact GlobalTheory.LinFormBound.main | (intros; apply GlobalTheory.LinFormBound.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitCubeTranslatesSlabPeriodicLe
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem lintegral_cube_slab_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G)
    (π : G →+ (Fin N → ℝ)) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) (U : Set G)
    (hS : MeasurableSet {w | w - ι (π w) ∈ U})
    (hfin : ∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hper : ∀ w, ∀ u ∈ U, φ (w + u) = φ w) (y : G) :
    μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ := by
  set S : Set G := {w | w - ι (π w) ∈ U} with hSdef
  let ν : Measure (Fin N → ℝ) := (μ.restrict S).map π
  have hν : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsFiniteMeasureOnCompacts ν := ⟨fun A hA => by
    rw [hν A hA.measurableSet]
    exact lt_top_iff_ne_top.2 (hfin A hA)⟩
  have : ν.IsAddLeftInvariant := (forall_measure_preimage_add_iff ν).1 fun t A hA => by
    rw [hν A hA, hν _ (measurable_const_add t hA), ← measure_preimage_add μ (ι t) (π ⁻¹' A ∩ S)]
    congr 1
    ext w
    simp only [hSdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, map_add, hπι, add_sub_add_left_eq_sub]
  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have hcube : MeasurableSet (cube N) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hvol : volume (cube N) = 1 := by
    simp [cube, Real.volume_Icc_pi]
  have hνc : μ (π ⁻¹' cube N ∩ S) = c := by
    rw [← hν _ hcube, hc, Measure.smul_apply, hvol]; simp
  have hf : Measurable fun t => φ (y + ι t) := hφ.comp (measurable_const_add y |>.comp hι.measurable)
  have e1 : ∫⁻ t in cube N, φ (y + ι t) ∂ν = c * ∫⁻ t in cube N, φ (y + ι t) := by
    rw [hc, Measure.restrict_smul, lintegral_smul_measure]; rfl
  rw [hνc, ← e1, setLIntegral_map hcube hf hπ.measurable,
    Measure.restrict_restrict (hπ.measurable hcube)]
  have e2 : ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + ι (π w)) ∂μ = ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + w) ∂μ := by
    refine setLIntegral_congr_fun ((hπ.measurable hcube).inter hS) fun w hw => ?_
    have := hper (y + ι (π w)) _ hw.2
    rw [← this]
    congr 1
    abel
  rw [e2]
  calc ∫⁻ w in π ⁻¹' cube N ∩ S, φ (y + w) ∂μ ≤ ∫⁻ w, φ (y + w) ∂μ := setLIntegral_le_lintegral _ _
    _ = ∫⁻ w, φ w ∂μ := lintegral_add_left_eq_self φ y

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSpanTranslatesOfNonzeroSchwartzStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_span_translates_of_nonzero_schwartz : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : Pl F), Continuous (psiLoc ψ v) →
    (∃ x : Fv F v, psiLoc ψ v x ≠ 1) → ∀ {κ : Type} [Fintype κ] (φ₀ φ : (κ → Fv F v) → ℂ), φ₀ ∈ SB _ → φ₀ ≠ 0 →
    φ ∈ SB _ → φ ∈ Submodule.span ℂ (Set.range fun p => GlobalTheory.FinComm.locOp ψ v p φ₀) := by
  first | exact @GlobalTheory.SchrCyclic.mem_span_locOp | exact GlobalTheory.SchrCyclic.mem_span_locOp | (intros; apply GlobalTheory.SchrCyclic.mem_span_locOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IntegralDetModule

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Module.Basis (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) (Fin n → AE F E) :=
  Pi.basis fun _ => (Module.finBasis F E).baseChange (AF F)

def big {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) :
    Matrix (Σ _ : Fin n, Fin (Module.finrank F E)) (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) :=
  LinearMap.toMatrix (bas F E n) (bas F E n) ((Matrix.toLin' t).restrictScalars (AF F))

theorem big_apply {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) (x y) :
    big t x y = (bas F E n).repr (t *ᵥ bas F E n y) x := by
  rw [big, LinearMap.toMatrix_apply]
  rfl

theorem det_big {n : ℕ} (t : Matrix (Fin n) (Fin n) (AE F E)) :
    (big t).det = Algebra.norm (AF F) t.det := by
  rw [big, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']

theorem bas_eq {n : ℕ} (x) :
    bas F E n x = fun i => inclR (F := F) (AF F) ((Pi.single x.1 (Module.finBasis F E x.2) : Fin n → E) i) := by
  rw [bas, Pi.basis_apply]
  funext i
  by_cases h : i = x.1
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, Module.Basis.baseChange_apply]
    rfl
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem map_norm_det {n : ℕ} {K : Type} [CommRing K] (φ : AF F →+* K) (t : Matrix (Fin n) (Fin n) (AE F E))
    (u : AF F) (hu : φ u = 1) (ht : u • (t - 1) = 0) : φ (Algebra.norm (AF F) t.det) = 1 := by
  rw [← det_big, RingHom.map_det]
  have : φ.mapMatrix (big t) = 1 := by
    ext x y
    have h1 : u • (t *ᵥ bas F E n y) = u • bas F E n y := by
      have h2 : (u • (t - 1)) *ᵥ bas F E n y = 0 := by rw [ht, Matrix.zero_mulVec]
      rwa [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, sub_eq_zero] at h2
    have h3 := congrArg (fun z => φ ((bas F E n).repr z x)) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu, one_mul, Module.Basis.repr_self] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, big_apply, h3, Matrix.one_apply, Finsupp.single_apply]
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_one]

theorem exists_bound {n : ℕ} (W : Spc F E n) (hL : W.L.FG) (v : Pl F) :
    ∃ C : ℝ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ x, ‖evFin F v ((bas F E n).repr z x)‖ ≤ C := by
  first
  | exact @_root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | (apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main ..)

theorem exists_mul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (y : Fin n → E) :
    ∃ D : ℤ, D ≠ 0 ∧ D • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice
  | exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice
  | (apply _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice ..)

theorem exists_entry_bound {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) :
    ∃ C : ℝ, ∀ t : Matrix (Fin n) (Fin n) (AE F E),
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → ∀ x y, ‖evFin F v (big t x y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound W hL.fg v
  choose D hD0 hD using fun x : (Σ _ : Fin n, Fin (Module.finrank F E)) =>
    exists_mul_mem W.L hL (Pi.single x.1 (Module.finBasis F E x.2))
  haveI : CharZero (Fv F v) := algebraRat.charZero _
  refine ⟨∑ y, |C| / ‖(D y : Fv F v)‖, fun t ht x y => ?_⟩
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v) with he
  have he1 : evFin F v e = 1 := GlobalTheory.EmbChart.evFin_atPlace v 1
  have hmem : e • (D y • bas F E n y) ∈ GlobalTheory.InertSph.latAt W v := by
    refine AddSubgroup.subset_closure ⟨e, ?_, ?_, _, hD y, ?_⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, he, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [he1]; exact one_mem _
    · rw [bas_eq]
      congr 1
      funext i
      simp only [Pi.smul_apply, map_zsmul]
  have h1 := hC _ (ht _ hmem) x
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, map_zsmul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    map_mul, he1, one_mul, map_zsmul, zsmul_eq_mul, norm_mul, ← big_apply] at h1
  have hpos : 0 < ‖(D y : Fv F v)‖ := norm_pos_iff.2 (Int.cast_ne_zero.2 (hD0 y))
  calc ‖evFin F v (big t x y)‖ ≤ |C| / ‖(D y : Fv F v)‖ := by
        rw [le_div_iff₀ hpos, mul_comm]; exact h1.trans (le_abs_self C)
    _ ≤ _ := Finset.single_le_sum (f := fun y => |C| / ‖(D y : Fv F v)‖)
        (fun y _ => div_nonneg (abs_nonneg _) (norm_nonneg _)) (Finset.mem_univ y)

theorem norm_le_one {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) (t : Matrix (Fin n) (Fin n) (AE F E))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ‖evFin F v (Algebra.norm (AF F) t.det)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_entry_bound W hL v
  have hk : ∀ k : ℕ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t ^ k) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih => intro z hz; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (ht z hz)
  have hb : ∃ B : ℝ, ∀ k : ℕ, ‖evFin F v (Algebra.norm (AF F) t.det)‖ ^ k ≤ B := by
    refine ⟨(Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E))).factorial •
      C ^ Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E)), fun k => ?_⟩
    rw [← norm_pow, ← map_pow, ← map_pow, ← Matrix.det_pow, ← det_big]
    have := Matrix.det_le (abv := (NormedField.toAbsoluteValue (Fv F v))) (A := (big (t ^ k)).map (evFin F v)) (x := C)
      (fun x y => hC _ (hk k) x y)
    have e : evFin F v (big (t ^ k)).det = ((big (t ^ k)).map (evFin F v)).det :=
      RingHom.map_det (evFin F v).toRingHom _
    rw [e]
    exact this
  obtain ⟨B, hB⟩ := hb
  by_contra h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (not_le.1 h)).eventually_gt_atTop B).exists
  exact absurd (hB k) (not_le.2 hk)

theorem modu_eq_one (a : (AF F)ˣ) (h1 : (a : AF F).1 = 1) (h2 : ∀ v, ‖evFin F v a‖ = 1) :
    (adeleClass F).modu a = 1 := by
  apply NNReal.eq
  change (MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 F), ‖(a : AF F).2 v‖ = 1 := h2
  have h4 : ∀ w : InfinitePlace F, ‖(a : AF F).1 w‖ = 1 := fun w => by
    rw [h1]; exact norm_one
  simp only [h3, h4, one_pow, Finset.prod_const_one, finprod_one, mul_one, NNReal.coe_one]

theorem modu_norm_det {n : ℕ} (W : Spc F E n) (hL : W.L.IsLattice E) (v : Pl F) (t : GL (Fin n) (AE F E))
    (h1 : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1))
    (h2 : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  have h0 := h1 (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  apply modu_eq_one
  · refine map_norm_det (fstA F).toRingHom _ _ ?_ h0
    rw [map_sub, map_one, sub_eq_self]
    rfl
  · intro u
    by_cases hu : u = v
    · subst hu
      have a1 := norm_le_one W hL u _ fun z hz => (h2 z hz).1
      have a2 := norm_le_one W hL u _ fun z hz => (h2 z hz).2
      have a3 : ‖evFin F u (Algebra.norm (AF F) (t : Matrix (Fin n) (Fin n) (AE F E)).det)‖ *
          ‖evFin F u (Algebra.norm (AF F) ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).det)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, map_one, norm_one]
      refine le_antisymm a1 ?_
      rw [← a3]
      exact mul_le_of_le_one_right (norm_nonneg _) a2
    · have := map_norm_det (evFin F u).toRingHom _ _ (by
        rw [map_sub, map_one, sub_eq_self]
        exact evalV_singleFin_ne hu 1) h0
      exact (congrArg norm this).trans norm_one

end GlobalTheory.IntegralDetModule

theorem GlobalTheory.IntegralDetModule.modu_norm_det_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ _ t ht
  exact GlobalTheory.IntegralDetModule.modu_norm_det G.W hT.geo.hW.lat v t ht.1 ht.2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhereStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_entries_bounded_almost_everywhere : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))) ≤ K v := by
  first | exact @GlobalTheory.FixedBound.exists_entry_absFin_bound | exact GlobalTheory.FixedBound.exists_entry_absFin_bound | (intros; apply GlobalTheory.FixedBound.exists_entry_absFin_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicDerivativeStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_eisenstein_holomorphic_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    ∀ z : List (ℝ → GAd σ J) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      GlobalTheory.UAut.dop z (fun g => circleIntegral (fun w => (w - s₀) ^ j * H₀ w g) s₀ r) g =
        circleIntegral (fun w => (w - s₀) ^ j * GlobalTheory.UAut.dop z (H₀ w) g) s₀ r := by
  first | exact @GlobalTheory.CircleDop.dop_circleIntegral | exact GlobalTheory.CircleDop.dop_circleIntegral | (intros; apply GlobalTheory.CircleDop.dop_circleIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeveStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (s : ℕ) (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E, ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧ unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  first | exact @GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin | exact GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin | (intros; apply GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin <;> assumption)
end

