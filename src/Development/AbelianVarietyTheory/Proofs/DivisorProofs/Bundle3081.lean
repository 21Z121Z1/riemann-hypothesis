import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0206
import Formalism.LocalRingCardinality.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalGenusBound
section
set_option synthInstance.maxHeartbeats 400000

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.CovGminTop

section Abstract

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem norm_sum_le_of_gram {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    {ι : Type} (s : Finset ι) (f : ι → V) (σ : K →+* ℂ) : N σ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N σ (f i) := by
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, h⟩ := hG
  have e : ∀ x, N σ x = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk σ) x := fun x => by
    rw [(h _).2]
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e]
    · rw [e]; exact (hc σ x).symm
  simp only [e]
  exact PI.Dv.Tr.normAt_sum_le' b X _ s f

theorem char_val {H : Type} [Group H] [Finite H] (χ : H →* Kˣ) (h : H) :
    IsIntegral ℤ ((χ h : Kˣ) : K) ∧ ∀ σ : K →+* ℂ, ‖σ ((χ h : Kˣ) : K)‖ = 1 := by
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : ((χ h : Kˣ) : K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isIntegral_one), fun σ => ?_⟩
  have : ‖σ ((χ h : Kˣ) : K)‖ ^ Nat.card H = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_short_eigen {H : Type} [Group H] [Finite H] (st : H → V →ₗ[K] V)
    (hst : ∀ h h' x, st (h * h') x = st h' (st h x)) (χ : H →* Kˣ) (Λ : Submodule (𝓞 K) V) (hΛ : ∀ h, ∀ x ∈ Λ, st h x ∈ Λ)
    {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (hs : ∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) (hi : ∀ h σ x, N σ (st h x) = N σ x)
    (s : Set V) (hsΛ : s ⊆ Λ) (hsp : Submodule.span K s = ⊤) (B : ℝ) (hB : ∀ y ∈ s, ∀ σ, N σ y ≤ B) :
    ∃ s' : Set V, (∀ y ∈ s', (y ∈ Λ ∧ ∀ h, st h y = ((χ h : Kˣ) : K) • y) ∧ ∀ σ, N σ y ≤ Nat.card H * B) ∧
      ∀ x, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K s' := by
  classical
  letI := Fintype.ofFinite H
  refine ⟨_, ?_, GlobalTheory.eigenvector_mem_span_twistedTrace_image H K V st hst χ s hsp⟩
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨⟨Λ.sum_mem fun h _ => ?_, fun g => ?_⟩, fun σ => ?_⟩
  · rw [← map_inv]
    let a : 𝓞 K := ⟨_, (char_val χ h⁻¹).1⟩
    have := Λ.smul_mem a (hΛ h y (hsΛ hy))
    rwa [← algebraMap_smul K a] at this
  · beta_reduce
    rw [map_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight g) fun h => _ • _ • st h y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, ← hst, smul_smul, Equiv.coe_mulRight, map_mul, mul_inv, ← Units.val_mul, mul_left_comm, mul_inv_cancel, mul_one]
  · refine (norm_sum_le_of_gram hG hc _ _ σ).trans ?_
    rw [Nat.card_eq_fintype_card, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_
    rw [hs, hi, ← map_inv, (char_val χ h⁻¹).2, one_mul]
    exact hB y hy σ

end Abstract

section Point

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem half_lt_laOf (τ : Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)) (hk : (k : ℕ) < (dat p i).p) :
    (((p.κ i).n / 2 : ℕ) : ℤ) < laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k := by
  have h := GlobalTheory.HolRead.lastPos_wtA_of_kapIs D p.T p.κ p.fw.laws p.fw.kap i τ.1 τ.2
  have hm : (dat p i).mult τ.1 = (dat p i).p := by
    unfold Datum.mult
    exact if_pos τ.2
  rw [hm] at h
  have h2 : wtA (p.κ i) (τ.1, (dat p i).p - 1) ≤ wtA (p.κ i) (τ.1, k) := (dom_wtA (p.κ i)).1 τ.1 (show (k : ℕ) ≤ _ by omega)
  have h3 := h (by omega)
  unfold laOf weightOf
  rw [if_pos hk]
  beta_reduce
  omega

theorem one_le_kap (hp : 1 ≤ (dat p i).p) : 1 ≤ kap p i := by
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hne : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [WtShape.card_psi p]; exact hf)).1
  obtain ⟨τ⟩ := hne
  have h := half_lt_laOf p i τ ⟨0, by omega⟩ hp
  have h1 : (1 : ℤ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by omega
  have h2 : (1 : ℝ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by exact_mod_cast h1
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact (h2.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun k => |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem gminAt_of_gens (Y : Cov p i) (hpq : 1 ≤ (dat p i).p + (dat p i).q) (hA : Y.d.l₂.A.Coprime Y.d.l₂.M)
    (hC : KeepsCusp Y.U (Gk p i))
    (hk : ∀ (γ : LevelAut (dat p i) Y.d.l₂) (f g : Y.V (Gk p i)), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f →
      (f ∈ latW Y.U (Gk p i) → g ∈ latW Y.U (Gk p i)) ∧ ∀ σ, Y.nrm (Gk p i) σ g = Y.nrm (Gk p i) σ f)
    (hG : Y.GoodAt (Gk p i)) (S : Subgroup (LevelAut (dat p i) Y.d.l₂)) (χ : S →* (Y.d.c₂.F)ˣ)
    (hN : latDeep p i Y = chiLat S Y.U (Gk p i) χ) (s : Set (Y.V (Gk p i))) (hs : s ⊆ latW Y.U (Gk p i))
    (hsp : Submodule.span Y.d.c₂.F s = ⊤) (B PP : ℝ) (hB : ∀ y ∈ s, ∀ σ, Y.nrm (Gk p i) σ y ≤ Real.exp B)
    (hPP : Real.log (Nat.card S) + B ≤ PP * kap p i) : GminAt p i Y PP := by
  let st : S → Y.V (Gk p i) →ₗ[Y.d.c₂.F] Y.V (Gk p i) := fun h =>
    (pull Y.d.Xo₂ Y.d.c₂ (h : LevelAut (dat p i) Y.d.l₂)).toLinearMap.restrict (hC h)
  obtain ⟨s', h1, h2⟩ := exists_short_eigen st
    (fun h h' x => Subtype.ext ((isRightAct_pull (Xo := Y.d.Xo₂) (c := Y.d.c₂) hpq hA).2 h h' x)) χ (latW Y.U (Gk p i))
    (fun h x hx => (hk h x _ rfl).1 hx) hG.1
    (fun σ f => by rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ])
    (fun σ a x => petW_smul _ _ _ _ _ σ a _) (fun h σ x => (hk h x _ rfl).2 σ) s hs hsp _ hB
  refine ⟨s', fun y hy => ?_, fun y hy σ => ((h1 y hy).2 σ).trans ?_, fun x hx => h2 x fun h => Subtype.ext ?_⟩
  · rw [hN]
    exact (mem_chiLat S Y.U _).2 ⟨(h1 y hy).1.1, fun h => congrArg Subtype.val ((h1 y hy).1.2 h)⟩
  · have hc : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos
    rw [← Real.exp_log hc, ← Real.exp_add]
    exact Real.exp_le_exp.2 hPP
  · rw [hN] at hx
    exact ((mem_chiLat S Y.U _).1 hx).2 h

end Point

theorem num_step {C Z l k PP : ℝ} (hC : 0 ≤ C) (hl : C + 45 ≤ Z) (hk : 1 ≤ k) (hPP : Z ^ 12 ≤ PP) (h : l ≤ 45 * Z ^ 2) :
    l + C * Z ^ 2 * k ≤ PP * k := by
  have h1 : 1 ≤ Z := by linarith
  have h2 : Z ^ 3 ≤ Z ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have h3 : (C + 45) * Z ^ 2 ≤ Z ^ 3 := by
    rw [pow_succ' Z 2]; exact mul_le_mul_of_nonneg_right hl (by positivity)
  have h4 : (C + 45) * Z ^ 2 * k ≤ PP * k := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 45 * Z ^ 2 ≤ 45 * Z ^ 2 * k := le_mul_of_one_le_right (by positivity) hk
  linarith

theorem gmin : Hypotheses2 → Gram → DeepGood → Size → Gmin := by
  intro hP hGr hDG hS
  obtain ⟨C, hC, hg⟩ := GlobalTheory.T.even_domain_weight_bound hP
  refine Closed.imp (((GlobalTheory.T.weight_parameter_strict_antitone hS).and (GlobalTheory.T.size_bounds_for_family hS)).and ((GlobalTheory.T.lattice_level_character_bound hP hGr hDG).and hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, h1⟩, _, -, h2⟩, ⟨_, -, h3⟩, _, -, h4⟩
  obtain ⟨x1, h5⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (C + 45)
  obtain ⟨x0, h⟩ := (h1.and h2).and (h3.and h4)
  refine ⟨0, le_rfl, max x0 x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp
  obtain ⟨b1, b2, b3, -⟩ := a1 i hi
  obtain ⟨c1, c2, c3, c4, c5, c6, -, -, c7, c8, -, c9, c10, -⟩ := a2 i hi Y hY
  obtain ⟨fr, ψ, -, d1, d2, d3⟩ := a3 i hi Y hY
  have hL := (h5 x ((le_max_right _ _).trans hle) ι).2.2.1
  have hn : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (p.κ i).n := by
    rw [WtShape.cols_eq]; exact (Fm.parT x hx ι).nV_ge
  obtain ⟨s, e1, e2, e3⟩ := hg _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 _ c3 c4 c5 c6 le_rfl (wtA (p.κ i)) (p.κ i).n
    (dom_wtA _) (p.κ i).n_even hn (half_lt_laOf p i) (c9.trans (by linarith))
  obtain ⟨k1, k2⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 (Gk p i)
    ((Int.even_coe_nat _).2 (p.κ i).n_even)
  refine gminAt_of_gens p i Y (by omega) d1.coprime k1 k2 (a4 i hi Y hY).1 _ _ d2 s e1 e2 _ _ (fun y hy σ => (e3 y hy σ).1)
    (num_step hC (hL.trans ?_) (one_le_kap p i b1) c10 d3)
  have f1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have f2 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le f1 f2)

end GlobalTheory.CovGminTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityChangeOfChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.ChartChange

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def colSum (H : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det

theorem colSum_mul_left (A : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a) = A.det * colSum H := by
  simp only [colSum, Finset.mul_sum, ← Matrix.det_mul]
  refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
  ext j l
  simp [Matrix.mul_apply]

theorem colSum_transpose (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => (H a).transpose) = colSum H := by
  simp only [colSum, Matrix.det_apply', Matrix.of_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun (τ ρ : Equiv.Perm (Fin D)) => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ i, H (τ i) (ρ i) i)]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun ρ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight ρ⁻¹) _ _ fun τ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Equiv.coe_mulRight]
  congr 1
  refine Fintype.prod_equiv ρ _ _ fun i => ?_
  simp

theorem colSum_mul (A B : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a * B) = A.det * B.det * colSum H := by
  have e : colSum (fun a => H a * B) = B.det * colSum H := by
    rw [← colSum_transpose, ← colSum_transpose H, ← Matrix.det_transpose B, ← colSum_mul_left]
    simp only [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [colSum_mul_left A fun a => H a * B, e, mul_assoc]

theorem dens_eq (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens L c y = (Real.pi ^ D)⁻¹ * (colSum fun a => c.hess (L a).φ (pick (L a).φ.isLB y) y).re := rfl

theorem dens_trans (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  let J : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.of fun l j => (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (ReciprocityTheory.L2DbarEstimates.bas D j)) l
  have h (a) : c.hess (L a).φ (pick (L a).φ.isLB y) y =
      J.transpose * c'.hess (L a).φ (pick (L a).φ.isLB y) y * J.map (starRingEnd ℂ) := by
    have e : (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
        (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, c'.e.left_inv hv.2]
    rw [AlgChart.hess, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp ho hm (c.holo_trans c') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L a).cInf.contDiffAt c' hy' (mem_pick _ y))), e₂]
  have hJ : J.det = transDet c.e c'.e y := ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_jac _
  have hd : J.transpose.det * (J.map (starRingEnd ℂ)).det = ((‖transDet c.e c'.e y‖ ^ 2 : ℝ) : ℂ) := by
    have hm' : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
    rw [hm', Matrix.det_transpose, hJ, Complex.mul_conj']
    push_cast
    rfl
  rw [dens_eq, dens_eq]
  simp only [h]
  rw [colSum_mul, hd, Complex.re_ofReal_mul]
  ring

end

theorem dens_change_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y :=
  fun _ _ _ _ _ _ L c c' _ hy hy' => dens_trans L c c' hy hy'

end GlobalTheory.Mix.ChartChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityPullbackMatchingCharts
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixPull

theorem hess_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (π : Y ⟶ X) (hπ : π ≫ p = q) (A : MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D)
    (H : ∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w))
    (z : CxPts q σ) (hz : z ∈ c'.e.source) :
    c'.hess (A.pull π hπ).φ (pick (A.pull π hπ).φ.isLB z) z = c.hess A.φ (pick A.φ.isLB (ptMap π hπ σ z)) (ptMap π hπ σ z) := by
  have hz' := (H z hz).1
  have hj := mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl)
    (mem_pick (A.φ.pull π hπ).isLB z) PUnit.unit
  rw [c.hess_eq A.cInf hz' hj (mem_pick _ _)]
  show c'.hess (A.φ.pull π hπ) _ z = _
  unfold AlgChart.hess
  rw [← (H z hz).2]
  refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hz)] with v hv
  have hw := c'.e.map_target hv
  obtain ⟨h₁, h₂⟩ := H _ hw
  rw [c'.e.right_inv hv] at h₂
  have e₁ : c.e.symm v = PtsOver.map π hπ (spMap σ) (c'.e.symm v) := by
    exact (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
  rw [e₁]
  exact congrArg _ (A.φ.pull_φ π hπ _ _)

theorem dens_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (π : Y ⟶ X) (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) → ∀ w ∈ c'.e.source, dens (fun i => (L i).pull π hπ) c' w = dens L c (ptMap π hπ σ w) := by
  intro k _ X Y p q σ D π hπ L c c' H w hw
  have e : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
      c'.hess ((fun i => (L i).pull π hπ) (τ l)).φ (pick ((fun i => (L i).pull π hπ) (τ l)).φ.isLB w) w j l) =
      Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (ptMap π hπ σ w)) (ptMap π hπ σ w) j l := by
    intro τ
    ext j l
    simp only [Matrix.of_apply]
    rw [hess_pull π hπ (L (τ l)) c c' H w hw]
  simp only [dens, e]

end GlobalTheory.MixPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityUpdateTensorAdd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem det_perm_update_add {D : ℕ} (F : Fin D → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (P Q : Matrix (Fin D) (Fin D) ℂ) (τ : Equiv.Perm (Fin D)) :
    (Matrix.of fun j l => Function.update F i (P + Q) (τ l) j l).det =
      (Matrix.of fun j l => Function.update F i P (τ l) j l).det +
      (Matrix.of fun j l => Function.update F i Q (τ l) j l).det := by
  have key : ∀ R : Matrix (Fin D) (Fin D) ℂ, (Matrix.of fun j l => Function.update F i R (τ l) j l) =
      (Matrix.of fun j l => Function.update F i 0 (τ l) j l).updateCol (τ.symm i)
        (fun j => R j (τ.symm i)) := by
    intro R
    ext j l
    by_cases h : l = τ.symm i
    · subst h
      simp
    · have hl : τ l ≠ i := fun e => h (by rw [← e, Equiv.symm_apply_apply])
      simp [Matrix.updateCol_ne h, Function.update_of_ne hl]
  rw [key (P + Q), key P, key Q, ← Matrix.det_updateCol_add]
  rfl

theorem dens_update_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (c : AlgChart p σ D), ∀ y ∈ c.e.source, dens (Function.update L i (A.tens B)) c y = dens (Function.update L i A) c y + dens (Function.update L i B) c y := by
  intro k _ X p σ D L i A B c y hy
  let G : MLine p σ → Matrix (Fin D) (Fin D) ℂ := fun M => c.hess M.φ (pick M.φ.isLB y) y
  have hd : ∀ L' : Fin D → MLine p σ, dens L' c y = (Real.pi ^ D)⁻¹ *
      (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => (G ∘ L') (τ l) j l).det).re := fun _ => rfl
  have hT : G (A.tens B) = G A + G B := by
    have ha := mem_pick A.φ.isLB y
    have hb := mem_pick B.φ.isLB y
    have hab : y ∈ ptsIn p σ ((A.tens B).B.U (pick A.φ.isLB y, pick B.φ.isLB y)) :=
      mem_ptsIn_inf.2 ⟨ha, hb⟩
    show c.hess (A.tens B).φ _ y = _
    rw [c.hess_eq (A.tens B).cInf hy hab (mem_pick _ y)]
    have ho := isOpen_over c.e
      (isOpen_ptsIn (p := p) (σ := σ) (A.B.U (pick A.φ.isLB y) ⊓ B.B.U (pick B.φ.isLB y)))
    have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
    have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
      ((contDiffOn_chart (A.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
      ((contDiffOn_chart (B.cInf _) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩) 1 hm
    simp only [one_mul, Complex.ofReal_one, one_smul, Function.comp_apply] at e
    exact e
  rw [hd, hd, hd, Function.comp_update, Function.comp_update, Function.comp_update, hT]
  simp only [det_perm_update_add, Finset.sum_add_distrib, Complex.add_re]
  ring

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApply
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.Mix.PartApply

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def colSum (H : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det

theorem colSum_mul_left (A : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a) = A.det * colSum H := by
  simp only [colSum, Finset.mul_sum, ← Matrix.det_mul]
  refine Finset.sum_congr rfl fun τ _ => congrArg _ ?_
  ext j l
  simp [Matrix.mul_apply]

theorem colSum_transpose (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => (H a).transpose) = colSum H := by
  simp only [colSum, Matrix.det_apply', Matrix.of_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun (τ ρ : Equiv.Perm (Fin D)) => ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∏ i, H (τ i) (ρ i) i)]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun ρ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight ρ⁻¹) _ _ fun τ => ?_
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Equiv.coe_mulRight]
  congr 1
  refine Fintype.prod_equiv ρ _ _ fun i => ?_
  simp

theorem colSum_mul (A B : Matrix (Fin D) (Fin D) ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    colSum (fun a => A * H a * B) = A.det * B.det * colSum H := by
  have e : colSum (fun a => H a * B) = B.det * colSum H := by
    rw [← colSum_transpose, ← colSum_transpose H, ← Matrix.det_transpose B, ← colSum_mul_left]
    simp only [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [colSum_mul_left A fun a => H a * B, e, mul_assoc]

theorem dens_eq (L : Fin D → MLine p σ) (c : AlgChart p σ D) (y : CxPts p σ) :
    dens L c y = (Real.pi ^ D)⁻¹ * (colSum fun a => c.hess (L a).φ (pick (L a).φ.isLB y) y).re := rfl

theorem dens_trans (L : Fin D → MLine p σ) (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : dens L c y = ‖transDet c.e c'.e y‖ ^ 2 * dens L c' y := by
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  let J : Matrix (Fin D) (Fin D) ℂ :=
    Matrix.of fun l j => (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (ReciprocityTheory.L2DbarEstimates.bas D j)) l
  have h (a) : c.hess (L a).φ (pick (L a).φ.isLB y) y =
      J.transpose * c'.hess (L a).φ (pick (L a).φ.isLB y) y * J.map (starRingEnd ℂ) := by
    have e : (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
        (fun v => ((L a).φ.φ (pick (L a).φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
      eventually_of_mem (ho.mem_nhds hm) fun v hv => by
        simp only [Function.comp_apply, c'.e.left_inv hv.2]
    rw [AlgChart.hess, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
      ReciprocityTheory.L2DbarEstimates.Y.cmpa_cHess_comp ho hm (c.holo_trans c') (e₂ ▸
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L a).cInf.contDiffAt c' hy' (mem_pick _ y))), e₂]
  have hJ : J.det = transDet c.e c'.e y := ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_jac _
  have hd : J.transpose.det * (J.map (starRingEnd ℂ)).det = ((‖transDet c.e c'.e y‖ ^ 2 : ℝ) : ℂ) := by
    have hm' : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
    rw [hm', Matrix.det_transpose, hJ, Complex.mul_conj']
    push_cast
    rfl
  rw [dens_eq, dens_eq]
  simp only [h]
  rw [colSum_mul, hd, Complex.re_ofReal_mul]
  ring

end GlobalTheory.Mix.PartApply

namespace GlobalTheory.Mix

theorem part_apply : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (c : AlgChart p σ D) (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ c.e.source → part L ε S = ∫⁻ v in c.e '' S, ENNReal.ofReal ((ε : ℤ) * dens L c (c.e.symm v)) := by
  intro k _ X p σ _ D L ε c S hS hc
  rw [part, glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [PartApply.dens_trans L c c' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)])
    c hS hc, chartMeas_apply_of_subset _ _ hS hc]

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSectionValueProductExpansionTermsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_section_value_product_expansion_terms : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), Act D₁ D₂ b h g g' → ∀ (j j' : ℕ) (w : Frm D₂ F j g'.b) (w' : Frm D₁ F j' g.b) (χ : D₂.X) (δ : D₁.X) (u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ)), Nrm u → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' δ) (y y' : F), MixedConv.IsCoefB j g' w χ f y → MixedConv.IsCoefB j' g w' δ f' y' → ∀ (z : (TF (R := R) F).left) (J), Good (JN D₁ D₂) z J → sval f (g.b.left ≫ b.left) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J * val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J)).val = cst F z (y * y') * (rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s (h χ + δ)) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹).val := by
  first | exact @GlobalTheory.Mum.Two.Mix.val_mixed_eval | exact GlobalTheory.Mum.Two.Mix.val_mixed_eval | (intros; apply GlobalTheory.Mum.Two.Mix.val_mixed_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCountOfEigenCovolumeHypothesesStatement
section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_count_of_eigen_covolume_hypotheses : BridgeSt → EigSt → CovolSt → PointSt := by
  first | exact @GlobalTheory.DetHT.pointSt_of | exact GlobalTheory.DetHT.pointSt_of | (intros; apply GlobalTheory.DetHT.pointSt_of <;> assumption)
end

