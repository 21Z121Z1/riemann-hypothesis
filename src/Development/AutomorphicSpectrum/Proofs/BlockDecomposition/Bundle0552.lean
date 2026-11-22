import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.ExpNegGlueHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UnipotentVanishing.InfAtUnipInvEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallHeightVectorIsotropic
section
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hermValue_inclR (v : Fin n → E) :
    hermValue F J F (fun i => inclR (F := F) F (v i)) =
      inclR (F := F) F (hE (conj F E).toAlgHom J v v) := by
  have hc : ∀ e : E, conjBase F E F (inclR (F := F) F e) = inclR (F := F) F (conj F E e) := fun e => rfl
  have hb : baseMatrix F J F = J.map (inclR (F := F) F) := rfl
  simp only [hermValue, hc, hb, hE, Formalism.UG.hform, dotProduct, mulVec, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.map_apply, mul_assoc]

theorem ofResVec_cvec (v : Fin n → E) :
    ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v) = fun i => inclR (F := F) F (v i) := by
  apply resVec_injective (ι := Fin n) (Module.finBasis F E) F
  rw [resVec_ofResVec]
  funext p
  simp only [cvec, resVec, Function.comp_apply, coordsVec, coords, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hermCoords_cvec_ne_zero {v : Fin n → E} (h : hE (conj F E).toAlgHom J v v ≠ 0) :
    hermCoords J (Module.finBasis F E) F (cvec F v) ≠ 0 := by
  intro h0
  apply h
  have h1 : hermValue F J F (ofResVec (ι := Fin n) (Module.finBasis F E) F (cvec F v)) = 0 := by
    apply (coords (Module.finBasis F E) F).injective
    rw [map_zero]
    exact h0
  rw [ofResVec_cvec, hermValue_inclR] at h1
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F F).injective (h1.trans (map_zero _).symm)

theorem matHom_mem_unitaryPoints (g : GAd (conj F E).toAlgHom J) :
    matHom (AF F) (conj F E).toAlgHom J g ∈ unitaryPoints F E J (AF F) := by
  rw [← CompanionTheory.SWFin.HR_eq]
  exact g.2

theorem exists_pos_isotropic_of_hgt_lt :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd (conj F E).toAlgHom J) (v : Fin n → E), v ≠ 0 →
      hgt (conj F E).toAlgHom J g v < ε → hE (conj F E).toAlgHom J v v = 0 := by
  obtain ⟨C, hC, hCb⟩ := exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos
    (hermPoly J (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
  refine ⟨min 1 C⁻¹, lt_min one_pos (inv_pos.2 hC), fun g v hv hlt => ?_⟩
  by_contra hne
  rw [hgt_eq] at hlt
  have hx : cvec F v ≠ 0 := cvec_ne_zero hv
  have hz := hermCoords_cvec_ne_zero J hne
  have hy := Reduction.hasFiniteContent_height (trG (conj F E).toAlgHom J g) hx
  have he : (fun k => MvPolynomial.aeval
      (Reduction.ratVec (cvec F v) ᵥ* ((trG (conj F E).toAlgHom J g : GL _ (AF F)) : Matrix _ _ (AF F)))
      (hermPoly J (Module.finBasis F E) k)) =
      Reduction.ratVec (hermCoords J (Module.finBasis F E) F (cvec F v)) := by
    funext k
    rw [aeval_hermPoly]
    exact congrFun (hermCoords_vecMul_trHom J (Module.finBasis F E) (cvec F v)
      ⟨_, matHom_mem_unitaryPoints J g⟩) k
  have hfz := Reduction.hasFiniteContent_ratVec hz
  rw [← he] at hfz
  have h1 := Reduction.one_le_adelicNorm_ratVec hz
  rw [← he] at h1
  have h2 : 1 ≤ C * Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v) ^ 2 :=
    h1.trans (hCb _ hy hfz)
  have h0 := Reduction.height_nonneg (trG (conj F E).toAlgHom J g) (cvec F v)
  set t := Reduction.height (trG (conj F E).toAlgHom J g) (cvec F v)
  have ht1 : t < 1 := hlt.trans_le (min_le_left _ _)
  have htC : t < C⁻¹ := hlt.trans_le (min_le_right _ _)
  have h3 : C * t < 1 := by
    have := mul_lt_mul_of_pos_left htC hC
    rwa [mul_inv_cancel₀ hC.ne'] at this
  have h4 : C * t ^ 2 ≤ C * t := by
    nlinarith [mul_nonneg (mul_nonneg hC.le h0) (sub_nonneg.2 ht1.le)]
  linarith

end GlobalTheory.CompanionTheory.RedCov.Bridge

namespace GlobalTheory.CompanionTheory.RedCov

theorem isotropic_of_hgt_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0 := by
  intro F E _ _ _ _ _ σ h n J _
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((h.2.2.2 τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  exact Bridge.exists_pos_isotropic_of_hgt_lt J

end GlobalTheory.CompanionTheory.RedCov

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantHeckeKernel
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem heckeOp_nilpotent_on_ker :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ T : Module.End ℂ (fixed π J), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ t ht T hT v hv
  set e := leviEmb k (stdBlocks d hd) with he

  have hdom : ∀ r : ℕ, IsDominant k N J d hd (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (isDominant_one_and_mul k N J h d hd).1
    | succ r ih =>
      rw [pow_succ]
      exact (isDominant_one_and_mul k N J h d hd).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, IsHeckeOp π J (e (t ^ r)) (T ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ T]
      exact GlobalTheory.T.jacquet_fixed_first_condition k N h d hd J hJo hJc hJf hpos V π hπ _ _ (hdom r) ht.1 _ _ ih hT

  have key : ∀ u ∈ twKer π (unipRad k (stdBlocks d hd)) 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l (π (e t ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := GlobalTheory.T.strictly_dominant_contracts_unipotent k N h d hd J hJo hJc hJf hpos t ht (n : GL (Fin N) k) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹ ∈ KN k N J d hd := by
        have := (hdom j).1 _ hR
        rw [map_pow] at this
        convert this using 1
        rw [add_comm R j, pow_add]
        group
        rfl
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π (e t ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π (e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹) (π (e t ^ (R + j)) w)
          = π (e t ^ (R + j)) (π (n : GL (Fin N) k) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add, map_add, hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((T ^ R) v : fixed π J) : V) = 0 := by
    refine GlobalTheory.T.fixed_vector_zero_of_dual _ J hJc V π hπ _ ((T ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, map_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Lbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoExpMulPoly
section
noncomputable section

open NumberField MeasureTheory Filter Topology
open scoped ENNReal
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E.E3

namespace GlobalTheory.CompanionTheory.LocExponent

theorem tendsto_exp_mul_poly (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (M : ℕ) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * ε * t)) * (1 + B * (1 + t)) ^ M) atTop (𝓝 0) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop M (show 0 < 2 * ε by positivity)).tendsto_div_nhds_zero
  have h2 := h.const_mul ((1 + 2 * B) ^ M)
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have h0 : 0 ≤ 1 + B * (1 + t) := by nlinarith
    positivity
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have h1 : 1 + B * (1 + t) ≤ (1 + 2 * B) * t := by nlinarith
    have h0 : 0 ≤ 1 + B * (1 + t) := by nlinarith
    have hp := pow_le_pow_left₀ h0 h1 M
    rw [Real.exp_neg, mul_comm (Real.exp (2 * ε * t))⁻¹, ← div_eq_mul_inv, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by rwa [mul_pow] at hp) (Real.exp_pos _).le

theorem re_lt_of_dec {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (μ : Measure G) [μ.IsHaarMeasure] (ρ : ℝ) (a : ℝ → G)
    {F : G → ℂ} (hdecF : PositivityTheory.Rg.Rs.JExpNegGlue.Dec μ ρ a F) (hF0 : F ≠ 0) {c : ℂ}
    (hFeq : ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g) : c.re < ρ := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, F g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (funext h)
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds g₀
  have hFc := hdecF.1
  set I := ∫ g in Q, ‖F g‖ ^ 2 ∂μ with hI
  have hIpos : 0 < I := by
    have hint : IntegrableOn (fun g => ‖F g‖ ^ 2) Q μ := (hFc.norm.pow 2).continuousOn.integrableOn_compact hQc
    rw [hI, setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun g => by show (0 : ℝ) ≤ ‖F g‖ ^ 2; positivity) hint]
    have hopen : IsOpen (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q) :=
      (hFc.norm.pow 2).isOpen_support.inter isOpen_interior
    have hne : (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q).Nonempty :=
      ⟨g₀, by simp [Function.mem_support, hg₀], mem_interior_iff_mem_nhds.2 hQn⟩
    exact lt_of_lt_of_le (hopen.measure_pos μ hne)
      (measure_mono (Set.inter_subset_inter_right _ interior_subset))
  have hval : ∀ t : ℝ, Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖F (a t * g)‖ ^ 2 ∂μ =
      Real.exp (2 * (c.re - ρ) * t) * I := by
    intro t
    have hre : (c * (t : ℂ)).re = c.re * t := by simp
    have hpt : ∀ g, ‖F (a t * g)‖ ^ 2 = Real.exp (c.re * t) ^ 2 * ‖F g‖ ^ 2 := by
      intro g
      rw [hFeq, norm_mul, Complex.norm_exp, mul_pow, hre]
    simp_rw [hpt]
    rw [integral_const_mul, ← mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]
    congr 2; ring
  have hlim := hdecF.2 Q hQc
  rw [tendsto_congr hval] at hlim
  by_contra hge
  push Not at hge
  have hev : ∀ᶠ t in atTop, I ≤ Real.exp (2 * (c.re - ρ) * t) * I := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 : 1 ≤ Real.exp (2 * (c.re - ρ) * t) :=
      Real.one_le_exp (by nlinarith [mul_nonneg (sub_nonneg.2 hge) ht])
    nlinarith
  have := ge_of_tendsto hlim hev
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

omit [IsCMField E] in

theorem mult_of_lat {S : Set (GA E N)} {n : ℕ}
    (h : ∀ x, {γ : An.lat E N | (γ : GA E N) * x ∈ S}.encard ≤ n) : Mult S n := by
  intro x
  have hle : (ratGL E N).range ≤ An.lat E N := le_sup_left
  refine le_trans ?_ (h x)
  have hinj : Set.InjOn (Subgroup.inclusion hle) {γ : (ratGL E N).range | (γ : GA E N) * x ∈ S} :=
    (Subgroup.inclusion_injective hle).injOn
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact hγ

omit [IsCMField E] in
theorem rho_nonneg {r : ℕ} (hrN : r < N) : 0 ≤ An.rho E N r := by
  unfold An.rho
  have : (r : ℝ) ≤ N := by exact_mod_cast hrN.le
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 this)) two_pos.le)

theorem integral_ctn_le (hSize : SizeT) {φ : GA E N → ℂ} (hφ : Continuous φ) (hLoc : Loc φ) {r : ℕ}
    (hr : 0 < r) (hrN : r < N) (μ : Measure (GA E N)) [hμ : μ.IsHaarMeasure] {Q : Set (GA E N)} (hQ : IsCompact Q) :
    ∃ (K B : ℝ) (M : ℕ), 0 ≤ K ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      ∫ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ ^ 2 ∂μ ≤
        K * (Real.exp (2 * An.rho E N r * t) * (1 + B * (1 + t)) ^ M) := by
  obtain ⟨D, hD, hD0⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain
    (K := E) (n := N) (r := r)
  obtain ⟨C₁, hC₁⟩ := l2glue.count_le count_holds hr hrN hD hQ
  obtain ⟨C, M, hCM⟩ := hLoc μ hμ
  obtain ⟨B, hB, hsz⟩ := hSize E N (GroundTheory.Automorphic.AutomorphicForm.unipGL '' D) Q
    (hD.image GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL) hQ
  have hρ : 0 ≤ An.rho E N r := rho_nonneg hrN
  refine ⟨max C 0 * (max C₁ 0 + 1), B, M, by positivity, hB, fun t ht => ?_⟩
  set e := Real.exp (2 * An.rho E N r * t) with he
  set n : ℕ := ⌈C₁ * e⌉₊ with hn
  set R : ℝ := B * (1 + t) with hR
  have hR0 : 0 ≤ R := by positivity
  have hS := l2glue.isCompact_sset r t hD hQ
  have hmult : Mult (l2glue.sset E N r t D Q) n := mult_of_lat (hC₁ t ht)
  have hlog : ∀ g ∈ l2glue.sset E N r t D Q, logSize g ≤ R := by
    rintro _ ⟨⟨X, q⟩, ⟨hX, hq⟩, rfl⟩
    have hx := hsz _ ⟨X, hX, rfl⟩ q hq (fun i : Fin N => if (i : ℕ) < r then t else 0)
    refine hx.trans (mul_le_mul_of_nonneg_left ?_ hB)
    have : ‖fun i : Fin N => if (i : ℕ) < r then t else 0‖ ≤ t := by
      refine (pi_norm_le_iff_of_nonneg ht).2 fun i => ?_
      split_ifs
      · rw [Real.norm_of_nonneg ht]
      · simpa using ht
    linarith
  have h3 := hCM _ hS n R hR0 hmult hlog
  have h2 := l2glue.swap μ φ hφ r t hD hD0 hQ
  have h1 := l2glue.integral_le_toReal (μ.restrict Q) (fun g => An.ctn r φ (An.aR E N r t * g))
  have hP : 0 ≤ (1 + R) ^ M := by positivity
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  have hnle : (n : ℝ) ≤ (max C₁ 0 + 1) * e := by
    have h6 : (n : ℝ) ≤ ⌈max C₁ 0 * e⌉₊ := by
      exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by linarith))
    have h7 := (Nat.ceil_lt_add_one (show 0 ≤ max C₁ 0 * e by positivity)).le
    nlinarith
  have h4 : ENNReal.ofReal (C * n * (1 + R) ^ M) ≤ ENNReal.ofReal (max C 0 * n * (1 + R) ^ M) := by
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hP)
  have h5 : (∫⁻ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ₑ ^ 2 ∂μ).toReal ≤ max C 0 * n * (1 + R) ^ M := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h2.trans (h3.trans h4))
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  calc _ ≤ _ := h1
    _ ≤ _ := h5
    _ ≤ max C 0 * ((max C₁ 0 + 1) * e) * (1 + R) ^ M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnle (by positivity)) hP
    _ = _ := by ring

theorem tendsto_ctn (hSize : SizeT) {φ : GA E N → ℂ} (hφ : Continuous φ) (hLoc : Loc φ) {r : ℕ}
    (hr : 0 < r) (hrN : r < N) (μ : Measure (GA E N)) [hμ : μ.IsHaarMeasure] {ε : ℝ} (hε : 0 < ε)
    {Q : Set (GA E N)} (hQ : IsCompact Q) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * (An.rho E N r + ε) * t)) *
      ∫ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, B, M, hK, hB, hb⟩ := integral_ctn_le hSize hφ hLoc hr hrN μ hQ
  have hlim := (tendsto_exp_mul_poly B ε hB hε M).const_mul K
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by positivity)) ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have h := mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos (-(2 * (An.rho E N r + ε) * t))).le
  refine h.trans (le_of_eq ?_)
  have hee : Real.exp (-(2 * (An.rho E N r + ε) * t)) * Real.exp (2 * An.rho E N r * t) = Real.exp (-(2 * ε * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hee]; ring

end GlobalTheory.CompanionTheory.LocExponent

namespace GlobalTheory.CompanionTheory.LocExponent

open PositivityTheory.Rg.Rs.JExpNegGlue in

theorem locNonPosGlue_holds : LocNonPosGlue := by
  intro hSize E _ _ _ N φ hA hLoc r hr0 hrN c hc
  obtain ⟨haR, -, -, hct⟩ := dict_holds E N
  have hctn := (hct φ hA r hr0 hrN).2
  obtain ⟨F₀, hF₀, F, hFspan, hF0, hFeq⟩ := hc
  obtain ⟨c₀, -, hF₀eq⟩ := hctn F₀ hF₀
  subst hF₀eq
  have hφc : Continuous φ.1 := GlobalTheory.CompanionTheory.ConstTerm.continuous_of_isOpen_stab φ hA.level
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsHaarMeasure := inferInstance
  set a : ℝ → GA E N := aT E N r with ha
  have hcomm : ∀ s t, a s * a t = a t * a s := aT_comm E N r
  have hlt : ∀ ε : ℝ, 0 < ε → c.re < An.rho E N r + ε := by
    intro ε hε
    have hdec_ctn : Dec μ (An.rho E N r + ε) a (An.ctn r φ.1) := by
      refine ⟨continuous_ctn r hφc, fun Q hQ => ?_⟩
      have h := tendsto_ctn hSize hφc hLoc hr0 hrN μ hε hQ
      simp only [ha, haR]
      exact h
    have hdecF : Dec μ (An.rho E N r + ε) a F := by
      refine Submodule.span_induction (p := fun H _ => Dec μ (An.rho E N r + ε) a H) ?_ (dec_zero μ _ a)
        (fun x y _ _ hx hy => dec_add μ _ a hx hy) (fun b x _ hx => dec_smul μ _ a b hx) hFspan
      rintro _ ⟨s, rfl⟩
      convert dec_smul μ _ a c₀ (dec_translate μ _ a hcomm s hdec_ctn) using 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul]
    exact re_lt_of_dec μ _ a hdecF hF0 hFeq
  have hle : c.re ≤ An.rho E N r := le_of_forall_pos_le_add fun ε hε => (hlt ε hε).le
  have hd : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [An.rho] at hle
  unfold pE
  have : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by
    rw [div_le_iff₀ hd]; linarith
  linarith

end GlobalTheory.CompanionTheory.LocExponent

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTest
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem contDiff_mulRight {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) :
    ContDiff ℝ ∞ (fun w : Lie E a => toL (Matrix.of w * Matrix.of X)) := by
  let L : Lie E a →ₗ[ℝ] Lie E a :=
    { toFun := fun w => toL (Matrix.of w * Matrix.of X)
      map_add' := fun w v => by
        simp only [toL]
        exact congrArg Matrix.of.symm (Matrix.add_mul (Matrix.of w) (Matrix.of v) (Matrix.of X))
      map_smul' := fun c w => by
        simp only [toL, RingHom.id_apply]
        exact congrArg Matrix.of.symm (Matrix.smul_mul c (Matrix.of w) (Matrix.of X)) }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem tsupport_dTest_subset {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) (β : Lie E a → ℂ) :
    tsupport (dTest X β) ⊆ tsupport β := by
  refine (closure_mono fun w hw => ?_).trans (tsupport_fderiv_subset ℝ (f := β))
  rw [Function.mem_support] at hw ⊢
  intro h
  apply hw
  simp [dTest, h]

theorem isTest_dTest (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ)
    (hβ : IsTest β) (X : Lie E a) : IsTest (dTest X β) := by
  have hfd := (contDiff_infty_iff_fderiv.mp hβ.contDiff).2
  refine IsTest.mk ?_ ?_ ?_
  · exact hfd.clm_apply (contDiff_mulRight X)
  · exact hβ.compact.mono' ((subset_tsupport _).trans (tsupport_dTest_subset X β))
  · exact (tsupport_dTest_subset X β).trans hβ.support

end GlobalTheory.CompanionTheory.SmoothRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCentralizerCompactPart
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CentOk

theorem centraliser_hyps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G), Continuous θ → ∀ (K I C : Subgroup G) (δ : G), IsCompact (K : Set G) → IsOpen (I : Set G) → IsCompact (C : Set G) → cptPart (twCent θ δ) = twCent θ δ ⊓ C → ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 := by
  intro G _ _ _ _ θ hθ K I C δ hK hI hC hcpt x
  have hTc : IsClosed (twCent θ δ : Set G) := by
    have : (twCent θ δ : Set G) = {g | g * δ = δ * θ g} := rfl
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)
  have hconj : Continuous fun a : G => x * a * x⁻¹ := by fun_prop
  constructor
  · have hKx : IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
      exact hK.image hconj
    intro g hg
    apply Subgroup.subset_closure
    refine ⟨hg.1, ?_⟩
    have hzp : (Subgroup.zpowers g : Set G) ⊆ (K.map (MulAut.conj x).toMonoidHom : Subgroup G) :=
      (Subgroup.zpowers_le (G := G) (H := K.map (MulAut.conj x).toMonoidHom)).2 hg.2
    exact hKx.of_isClosed_subset isClosed_closure (closure_minimal hzp hKx.isClosed)
  · set A : Subgroup G := I.map (MulAut.conj x).toMonoidHom with hA
    have hAo : IsOpen (A : Set G) := by
      rw [hA, Subgroup.coe_map]
      exact (Homeomorph.mulLeft x |>.trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hI
    have hHc : IsCompact (cptPart (twCent θ δ) : Set G) := by
      rw [hcpt, Subgroup.coe_inf]
      exact hC.inter_left hTc
    have hHT : cptPart (twCent θ δ) ≤ twCent θ δ := by
      rw [hcpt]; exact inf_le_left
    have e : (twCent θ δ ⊓ A) ⊓ cptPart (twCent θ δ) = A ⊓ cptPart (twCent θ δ) := by
      ext g
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hHT h.2, h.1⟩, h.2⟩⟩
    rw [← Subgroup.inf_relIndex_right, e, Subgroup.inf_relIndex_right]
    haveI : CompactSpace (cptPart (twCent θ δ)) := isCompact_iff_compactSpace.mp hHc
    have ho : IsOpen ((A.subgroupOf (cptPart (twCent θ δ)) : Subgroup _) : Set (cptPart (twCent θ δ))) :=
      hAo.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.CentOk
end
end

