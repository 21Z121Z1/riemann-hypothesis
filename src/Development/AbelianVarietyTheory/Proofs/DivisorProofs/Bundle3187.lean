import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeUnitaryClassicalTraitCentre
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BergmanFunctionTotalMassExtremal
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp.BergProof

lemma sum_eq_dot {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (w : ι → ℂ) :
    ∑ i, ∑ j, H j i * (w i * (starRingEnd ℂ) (w j)) = star w ⬝ᵥ (H *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring)

lemma berg_eq {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ) (σ : S) (y : Y σ) :
    bergmanDensity μ v σ y = (star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y)).re := by
  rw [bergmanDensity, sum_eq_dot]

lemma ofReal_re_of_nonneg {z : ℂ} (h : 0 ≤ z) : ((z.re : ℝ) : ℂ) = z := by
  have h' := Complex.le_def.mp h
  apply Complex.ext <;> simp [h'.2.symm]

end GlobalTheory.HSAmp.BergProof

open GlobalTheory.HSAmp.BergProof in

theorem GlobalTheory.HSAmp.berg_mass_extremal : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → (∀ σ, Integrable (bergmanDensity μ v σ) (μ σ)) ∧ ∑ᶠ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ = Fintype.card ι ∧ (∀ σ y, 0 ≤ bergmanDensity μ v σ y) ∧ ∀ σ y (M : ℝ), 0 ≤ M → (∀ c : ι → ℂ, cmb v c σ y ≤ M * l2 μ v c) → bergmanDensity μ v σ y ≤ M := by
  intro S Y _ ι _ _ μ v hF hG
  obtain ⟨hHerm, hl2⟩ := GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form S Y ι μ v hF
  have hH : ((gram μ v)⁻¹).PosDef := hG.inv
  have hu : IsUnit (gram μ v).det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hGH : gram μ v * (gram μ v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hHG : (gram μ v)⁻¹ * gram μ v = 1 := Matrix.nonsing_inv_mul _ hu
  have hHh : ((gram μ v)⁻¹).IsHermitian := hH.isHermitian
  have hnn : ∀ σ y, 0 ≤ star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y) := fun σ y =>
    hH.posSemidef.dotProduct_mulVec_nonneg _
  have key : ∀ σ y, (bergmanDensity μ v σ y : ℂ) = star (v σ y) ⬝ᵥ ((gram μ v)⁻¹ *ᵥ v σ y) := fun σ y => by
    rw [berg_eq]; exact ofReal_re_of_nonneg (hnn σ y)
  have hpos : ∀ σ y, 0 ≤ bergmanDensity μ v σ y := fun σ y => by
    rw [berg_eq]; exact (Complex.le_def.mp (hnn σ y)).1
  have hint : ∀ σ, Integrable (fun y => ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun σ => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _
  refine ⟨fun σ => (hint σ).re, ?_, hpos, ?_⟩
  · haveI : Finite S := hF.finite
    haveI := Fintype.ofFinite S
    have hσ : ∀ σ, ∫ y, bergmanDensity μ v σ y ∂μ σ =
        (∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ).re := fun σ => by
      have e1 : ∫ y, bergmanDensity μ v σ y ∂μ σ =
          RCLike.re (∫ y, ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) ∂μ σ) :=
        integral_re (hint σ)
      rw [e1, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]
      change Complex.re _ = Complex.re _
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hF.integrable σ i j).const_mul _]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    have hsum : ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j = (Fintype.card ι : ℂ) := by
      rw [Finset.sum_comm]
      have : ∀ j, ∑ i, (gram μ v)⁻¹ j i * gram μ v i j = ((gram μ v)⁻¹ * gram μ v) j j :=
        fun j => (Matrix.mul_apply).symm
      simp only [this, hHG, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [finsum_eq_sum_of_fintype]
    simp only [hσ]
    rw [← Complex.re_sum]
    have hg : ∀ i j, gram μ v i j = ∑ σ, ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := fun i j => by
      rw [gram, Matrix.of_apply, finsum_eq_sum_of_fintype]
    have hswap : ∑ σ, ∑ i, ∑ j, (gram μ v)⁻¹ j i * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ =
        ∑ i, ∑ j, (gram μ v)⁻¹ j i * gram μ v i j := by
      simp only [hg, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hswap, hsum, Complex.natCast_re]
  · intro σ y M hM h
    set w := v σ y with hw
    set u := (gram μ v)⁻¹ *ᵥ w with hu'
    have hB := key σ y
    rw [← hw] at hB
    have hdot : star u ⬝ᵥ w = star w ⬝ᵥ ((gram μ v)⁻¹ *ᵥ w) := by
      rw [hu', Matrix.star_mulVec, hHh.eq, ← Matrix.dotProduct_mulVec]
    have hc : cmb v (star u) σ y = bergmanDensity μ v σ y ^ 2 := by
      have : ∑ i, star u i * v σ y i = (bergmanDensity μ v σ y : ℂ) := by
        rw [hB, ← hdot]; rfl
      rw [cmb, this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hl : l2 μ v (star u) = bergmanDensity μ v σ y := by
      apply Complex.ofReal_injective
      rw [(hl2 (star u)).2.2, hB, ← hdot]
      have hGu : gram μ v *ᵥ u = w := by
        rw [hu', Matrix.mulVec_mulVec, hGH, Matrix.one_mulVec]
      conv_rhs => rw [← hGu]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def, Complex.conj_conj]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 := h (star u)
    rw [hc, hl] at h2
    have h0 := hpos σ y
    nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelEqConstMulTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigKernel

theorem end_finsupp_sum {α β : Type} (A : Module.End ℂ (β → ℂ)) (Θ : α →₀ ℂ) (f : α → β → ℂ) :
    A (Θ.sum fun d c => c • f d) = Θ.sum fun d c => c • A (f d) := by
  simp only [Finsupp.sum, map_sum, map_smul]

theorem finsupp_sum_apply {α β : Type} (Θ : α →₀ ℂ) (f : α → β → ℂ) (w : β) :
    (Θ.sum fun d c => c • f d) w = Θ.sum fun d c => c * f d w := by
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), pow_add, mul_assoc, hm, mul_one]

set_option maxHeartbeats 1000000 in

theorem kerBig_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ Φ, IsDatumA W e Γ Θ Φ → ∀ g g₁, ∃ ξ : ℂ, ξ ≠ 0 ∧
      ∀ u, kerBig W Θ g g₁ u = ξ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (conjU _ 1 h.JW u) (blkU _ _ e h.JWW (g, g₁)) := by
  intro D T L sc G μ₀ hL W B ρ t i j M Θ Θ' hΘ e Bs Γ X om om' h hTr Φ hΦ g g₁
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hTr.base _ Γ.V _ _ hTr.geo.hV
  obtain ⟨hJ, LS, hLS, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hTr.base _ Γ.W _ _ hTr.geo.hW
  have hξ0 : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have eA : Γ.V.J = (GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hTr.geo.hV.lat h3 (fun _ => (0, 0))).gramᵀ := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; exact (Matrix.transpose_transpose _).symm
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 •
      (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
        inv_mul_cancel₀ (neg_ne_zero.2 hξ0), one_smul])
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ0, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hTr.base
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hTr.geo.hV.lat h3 (fun _ => (0, 0))) Γ.V Γ.W _ _ _ _ hTr.geo.hV hTr.geo.hW eA eB
    Γ.M hTr.geo.hM X.β (X.β / X.α) hTr.chars.heckeβ (isHecke_div hTr.chars.heckeβ hTr.chars.heckeα) hTr.chars.resβ
    (resEtaPow_div hTr.chars.resβ hTr.chars.resα) om hTr.weil
  rw [h.ψ] at hω
  obtain ⟨ξ, hξ, hss⟩ := GlobalTheory.T.bigRoute_seesaw_arrow_kernels_product W t i j M e Bs Γ X om om' h hTr h1 h2 _ hTr.geo.hV.lat h3 _ h4 h5 LS hLS h6 _ ω hω g g₁
  refine ⟨ξ, hξ, fun u => ?_⟩
  obtain ⟨g', h', hh', hg'⟩ := GlobalTheory.WeilSchrodinger.match_pair D
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V.Jᵀ h1 h2 Γ.V.L hTr.geo.hV.lat h3 (fun _ => (0, 0))) Γ.V.J Γ.W.J (-1) eA eB (conjU (spW G i j) 1 h.JW u)
    (blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))
  have key := hth _ _ g' h' hh' hg' Φ hΦ.1
  refine Eq.trans ?_ (congrArg (fun z => ξ * z) key.symm)
  have htr : GlobalTheory.WeilSchrodinger.thetaTr D.host.F Γ.M.co Bs.ψ Φ =
      Θ.sum fun d c => c • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e d := by
    funext w
    show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ w Φ) = _
    rw [h.ψ, hΦ.2 w]
    exact (finsupp_sum_apply _ _ w).symm
  refine Eq.trans ?_ (congrArg (fun f => ξ * ω (g', h') f 0) htr.symm)
  refine Eq.trans ?_ (congrArg (fun z => ξ * z)
    (congrFun (end_finsupp_sum (ω (g', h')) Θ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e)) 0).symm)
  rw [finsupp_sum_apply, kerBig, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨t1, t2⟩ := GlobalTheory.RouteSeesaw.data_theta W B ρ t i j hΘ d hd
  rw [hss d.1.2 d.2 t1 t2 u g' h' hh' hg', mul_left_comm]
  rfl

end GlobalTheory.BigKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantForms
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem map_F1prim_eq_range_rigOfOmega (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A)
    (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] G.RigExt)
    (hL : Function.Surjective L) (hc : ∀ c, IsCan t c (L c)) :
    (PrimitiveSubmodule A).map L = LinearMap.range G.rigOfOmega := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
  apply le_antisymm
  · rintro _ ⟨c, hcF, rfl⟩
    refine ⟨ψ ⟨c, hcF⟩, ?_⟩
    exact GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ (hψ ⟨c, hcF⟩) (hc c)
  · rintro _ ⟨w, rfl⟩
    obtain ⟨c, hcw⟩ := hL (G.rigOfOmega w)
    refine ⟨c, GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hc c) ?_, hcw⟩
    rw [hcw]
    exact G.exact_rigOfOmega_rigToExt.apply_apply_eq_zero w

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBoundedHomogeneousIntFormFamiliesStatement
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_bounded_homogeneous_int_form_families : ∀ (D q δ : ℕ) (R : ℝ), 0 ≤ R → {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}.Finite ∧ {T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ | (∀ i, (T i).IsHomogeneous q) ∧ ∀ i α, |((coeff α (T i) : ℤ) : ℝ)| ≤ R}.ncard = (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ∧ Nat.card {α : Fin (D + 1) →₀ ℕ // α.degree = q} = (q + D).choose D ∧ Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) = (q + D).choose D ∧ Module.Finite ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ q) := by
  first | exact @GlobalTheory.HSAmp.card_bounded_forms | exact GlobalTheory.HSAmp.card_bounded_forms | (intros; apply GlobalTheory.HSAmp.card_bounded_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTopStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) → Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} = ⊤ := by
  first | exact @GlobalTheory.HeightOneDual.adjoin_primitive_eq_top | exact GlobalTheory.HeightOneDual.adjoin_primitive_eq_top | (intros; apply GlobalTheory.HeightOneDual.adjoin_primitive_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogenyStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  first | exact @GlobalTheory.AmpleGen.nv_mix_pair_of_nv | exact GlobalTheory.AmpleGen.nv_mix_pair_of_nv | (intros; apply GlobalTheory.AmpleGen.nv_mix_pair_of_nv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreConstPreconnectedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterLatticeAtFibre_const_preconnected : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y : RatModel o Ω) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Z : Scheme.{0}) (q : Y.Z ⟶ Z) (z : Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → (∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt G w r₀) → ∀ (I T : Type) (f : I → (G ⟶ G)), (∀ e, IsMonHom (f e)) → ∀ (gγ : T → (Over.mk Y.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ t, gγ t ^ L = 1) → (∀ t w, q.base w = z → ExtNear (gγ t) w) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w w' : Y.Z), q.base w = z → q.base w' = z → LatAt f gγ ζ L m c w → LatAt f gγ ζ L m c w' := by
  first | exact @GlobalTheory.UPoinc.GFib.latAt_const_on_fibre | exact GlobalTheory.UPoinc.GFib.latAt_const_on_fibre | (intros; apply GlobalTheory.UPoinc.GFib.latAt_const_on_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreUniqueUpToIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterLatticeAtFibre_unique_up_to_iso : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  first | exact @GlobalTheory.UPoinc.GFibUniq.latAt_unique | exact GlobalTheory.UPoinc.GFibUniq.latAt_unique | (intros; apply GlobalTheory.UPoinc.GFibUniq.latAt_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeUnitaryClassicalTraitCentreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterLattice_unitaryClassicalTrait_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f → GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ → ∀ ζ : X.o₁ˣ, IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) → ∃ (s : ZMod (X.S.r * X.S.N)) (σ : 𝓞 E → 𝓞 E), IsUnit s ∧ Function.Surjective σ ∧ ∀ (ct : UCTrait X p z) (y : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLabW X wi ct yy → ∃ c : X.S.TT X.M z → ct.T.P.D.toPre.X →+ ZMod (X.S.r * X.S.N), LatAt f gγ ζ (X.S.r * X.S.N) (fun a => DistribSMul.toAddMonoidHom ct.T.P.D.toPre.X (σ a)) c (y (cPt p)) ∧ ∀ (a : X.S.Gam) (v : ct.T.P.D.toPre.X) (t : X.S.TT X.M z), yy a = QuotientAddGroup.mk v → c t v = s * eStd X.S.g _ (t : X.S.Gam) a := by
  first | exact @GlobalTheory.UPoinc.GFibCentre.latAt_centre | exact GlobalTheory.UPoinc.GFibCentre.latAt_centre | (intros; apply GlobalTheory.UPoinc.GFibCentre.latAt_centre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOfHilbertBlumenthalStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_of_hilbert_blumenthal : GlobalTheory.Published.HilbertBlumenthal → Chart := by
  first | exact @GlobalTheory.LatJet.An.chart_of_hilbertBlumenthal | exact GlobalTheory.LatJet.An.chart_of_hilbertBlumenthal | (intros; apply GlobalTheory.LatJet.An.chart_of_hilbertBlumenthal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePowStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ) (w : ∀ σ, CxPts p σ → ℝ), chInt (L.pow n) D w = (n : ℝ) ^ D * chInt L D w := by
  first | exact @GlobalTheory.HSAmp.chInt_pow | exact GlobalTheory.HSAmp.chInt_pow | (intros; apply GlobalTheory.HSAmp.chInt_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularConnectionEqEsymmGraded
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem chernFld_ldPart_eq_esymm_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  intro F _ σ X ι _ m E H hH τ j p
  set A := (E.nonempty (under p.pt)).choose with hAdef
  have hA : A ∈ E.S (under p.pt) := (E.nonempty (under p.pt)).choose_spec
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH p.pt A hA τ).2 p.1.1 p.2)
  change ∀ᶠ v in 𝓝 p.crd, MContDiffAt ∞ (fun u => H A (p.ch.symm u) τ) v ∧ (H A (p.ch.symm v) τ).PosDef at hev
  have h0 := hev.self_of_nhds
  have hs := GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth X.dim (m τ) (fun u => H A (p.ch.symm u) τ) p.crd h0.1 h0.2
  have hp0 := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ h0.2
  show chernAt (fun v => ldPart (H A (p.ch.symm v) τ)) p.crd j = _
  refine (GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms X.dim (m τ) (fun v => ldPart (H A (p.ch.symm v) τ))
    (fun i v => grD (H A (p.ch.symm v) τ) i) p.crd hs.1 (fun i => (hp0.2.1 i).1) ?_ j).trans rfl
  filter_upwards [hev] with x hx
  have hpx := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ hx.2
  exact ⟨hpx.2.2.1, fun i => (hpx.2.1 i).2⟩

end GlobalTheory.ChernCalc
end

