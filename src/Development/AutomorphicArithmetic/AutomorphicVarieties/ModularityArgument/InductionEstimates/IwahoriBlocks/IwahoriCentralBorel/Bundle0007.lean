import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ParLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ExistsInjectionIntoL2Cusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.MemOfTranslates
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.FiniteAdeleInclusionMul
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem finite_projection_one {K : Type} [Field K] [NumberField K] {n : ℕ} : fin1 (1 : FA K n) = 1 :=
  map_one (MultiplicityOne.finProj K n)

private theorem finite_adele_inclusion_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (a b : FA K n) : fin1 (a * b) = fin1 a * fin1 b :=
  map_mul (MultiplicityOne.finProj K n) a b

private theorem zt0 {K : Type} [Field K] [NumberField K] : zt K 0 = 1 := by
  have h : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (by simp)
  rw [zt, h, map_one]

private theorem lv0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) :
    ((lv a b 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (a : AdelicGLn.AdelicGL K 2) (b : AdelicGLn.AdelicGL K 2) := by
  rw [blkLaws.1, neg_zero, zt0, mul_one, mul_one]

private theorem hh0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) (x : G1 K (2 + 2)) :
    HH (lv a b 0 * x) = HH x := by
  have h := (hpSpec (K := K)).1 0 a b 0 x
  have h0 : (nn 0 : G1 K (2 + 2)) = 1 := unipOne_zero 2
  rwa [h0, one_mul, zero_add] at h

private theorem sec_ray {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ := by
    apply Subtype.ext
    change Real.exp (-t) = (Real.exp t)⁻¹
    rw [Real.exp_neg]
  rw [Subgroup.coe_mul, blkLaws.1, zt, zt, h]
  simp

private theorem reps_comb {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) {ι : Type} (s : Finset ι) (φ : ι → G1 K n → ℂ) (c : ι → ℂ)
    (h : ∀ i, ∃ v ∈ τ, Reps μ v (φ i)) : ∃ v ∈ τ, Reps μ v (fun y => ∑ i ∈ s, c i * φ i y) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, τ.zero_mem, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa using hy
  | insert i s hi ih =>
    obtain ⟨v, hv, hr⟩ := ih
    obtain ⟨u, hu, hq⟩ := h i
    refine ⟨c i • u + v, τ.add_mem (τ.smul_mem _ hu) hv, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add (c i • u) v),
      (quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul (c i) u), hr, hq] with y e₁ e₂ e₃ e₄
    rw [e₁, Pi.add_apply, e₂, Pi.smul_apply, e₃, e₄, Finset.sum_insert hi, smul_eq_mul]

private theorem flat_lv {K : Type} [Field K] [NumberField K] (f : G1 K (2 + 2) → ℂ) (a b : G1 K 2) (x : G1 K (2 + 2)) :
    flat 0 f (lv a b 0 * x) = Complex.exp (2 * (HH x : ℂ)) * f (lv a b 0 * x) := by
  simp only [flat, zero_add]
  rw [show HP 2 2 (lv a b 0 * x) = HH x from hh0 a b x]

private theorem val_mem {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {κ : Measure (archCompact K (2 + 2))} {e : archCompact K (2 + 2) → ℂ} {κ₂ p₁ p₂ k₀}
    (hL : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (hfa : FixA κ e f)
    {U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)} (hU : Lev U) (hfU : FixF (levOn (im w) U) f) (g : GS (2 + 2) w) :
    (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) ∈
      tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w)) := by
  obtain ⟨d, φ, ψ, hφ, hψ, hx⟩ := hs.levi (arc1 k₀ * fin1 (ι₄ g))
  have hx' : ∀ a b, f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g)) = ∑ i, φ i a * ψ i b := fun a b =>
    hx a b _ (by rw [mul_assoc, Subgroup.coe_mul (x := lv a b 0), lv0])
  obtain ⟨U₂, hU₂, hlev⟩ := levBlock w ι₄ hw h₄ U hU g
  have hv := hL.val f hs hfa (ι₄ g)
  have hcl : Continuous fun p : G1 K 2 × G1 K 2 => f (lv p.1 p.2 0 * arc1 k₀ * fin1 (ι₄ g)) :=
    hs.cont.comp (((blkLaws (K := K)).2.2.2.1.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).mul continuous_const |>.mul continuous_const)
  have hsplit₁ : ∀ a b (u : G1 K 2), lv (a * u) b 0 = lv a b 0 * lv u 1 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hsplit₂ : ∀ a b (u : G1 K 2), lv a (b * u) 0 = lv a b 0 * lv 1 u 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hF : (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) =
      Complex.exp (2 * (HH (arc1 k₀ * fin1 (ι₄ g)) : ℂ)) • fun m : G1 K 2 × G1 K 2 => f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g)) := by
    funext m
    rw [mul_assoc, flat_lv]
    simp [mul_assoc]
  rw [hF]
  refine Submodule.smul_mem _ _ ((tensLaws _ _).2 _ d φ ψ (fun x => hx' x.1 x.2) (fun b => ?_) (fun a => ?_))
  · refine Submodule.subset_span ⟨hcl.comp (continuous_id.prodMk continuous_const), ?_, hv.1 b, U₂, hU₂, fun u hu a => ?_⟩
    · have h := reps_comb μ₂ τ₁ Finset.univ φ (fun i => ψ i b) (fun i => let ⟨v, hv, hr⟩ := (hφ i).2; ⟨v, hv, hr⟩)
      simpa only [hx', mul_comm] using h
    · obtain ⟨u', hu', hk⟩ := hlev u hu 1 (one_mem _)
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₁, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _
  · refine Submodule.subset_span ⟨hcl.comp (continuous_const.prodMk continuous_id), ?_, hv.2 a, U₂, hU₂, fun u hu b => ?_⟩
    · have h := reps_comb μ₂ τ₂ Finset.univ ψ (fun i => φ i a) (fun i => let ⟨v, hv, hr⟩ := (hψ i).2; ⟨v, hv, hr⟩)
      simpa only [hx'] using h
    · obtain ⟨u', hu', hk⟩ := hlev 1 (one_mem _) u hu
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₂, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _

private theorem law_eq {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)}
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₂ : IsEmb w ι₂) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f)
    (k₀ : archCompact K (2 + 2)) (p : ∀ i, PW (w i)) (g : GS (2 + 2) w) (m : G1 K 2 × G1 K 2) :
    flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g))) =
      (dS w p : ℂ) * flat 0 f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * arc1 k₀ * fin1 (ι₄ g)) := by
  obtain ⟨hA, hB⟩ := parLaw w ι₂ ι₄ hw h₂ h₄
  obtain ⟨X, t, hX, ht⟩ := hB p
  obtain ⟨X', hX'⟩ := hA m.1 m.2 0 X
  have hc : Commute (arc1 k₀) (fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k₀ _
  have key : lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g)) =
      nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g)) := by
    have hl : lv m.1 m.2 0 * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t = lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t := by
      rw [blkLaws.2.1, zero_add]
    rw [map_mul, finite_adele_inclusion_mul, ← hl]
    calc lv m.1 m.2 0 * arc1 k₀ * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * fin1 (ι₄ g))
        = lv m.1 m.2 0 * (arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) * fin1 (ι₄ g) := by simp only [mul_assoc]
      _ = lv m.1 m.2 0 * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * arc1 k₀) * fin1 (ι₄ g) := by rw [hc.eq]
      _ = (lv m.1 m.2 0 * nn X) * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t * (arc1 k₀ * fin1 (ι₄ g)) := by
          rw [hX]; simp only [mul_assoc]
      _ = _ := by rw [hX']; simp only [mul_assoc]
  have hray : lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t =
      lv 1 1 t * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 := by
    rw [blkLaws.2.1]; simp
  have hf : f (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) =
      f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * (arc1 k₀ * fin1 (ι₄ g))) := by
    rw [mul_assoc, hs.unip, hray, mul_assoc, sec_ray hs]
  have hh := (hpSpec (K := K)).1 X' (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t (arc1 k₀ * fin1 (ι₄ g))
  rw [key, mul_assoc (lv _ _ 0), flat_lv, ← ht]
  simp only [flat, zero_add]
  rw [show HP 2 2 (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) = t + HH (arc1 k₀ * fin1 (ι₄ g)) from hh, hf]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evMem :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, Pair μ₂ τ₁ τ₂ → ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₂ → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ ∈ IndF (piIncl fun i => PW (w i)) (xS ι₂) (tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w))) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ _ hL r w ι₂ ι₄ hw h₂ h₄ φ hφ
  obtain ⟨hiff, hsm⟩ := zMem μ₂ τ₁ τ₂ κ e hL.idem
  have hop := (hsm w ι₄ hw h₄ φ hφ).1
  obtain ⟨f, hs, hfa, ⟨U, hU, hfU⟩, rfl⟩ := (hiff _ φ).1 hφ
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · refine ⟨fun g => val_mem hL w ι₄ hw h₄ hs hfa hU hfU g, fun p g => ?_⟩
    funext m
    have h := law_eq (τ₁ := τ₁) (τ₂ := τ₂) w ι₂ ι₄ hw h₂ h₄ hs k₀ p g m
    simpa [ev, xS, twist, rightReg, LinearMap.funLeft] using h
  · have hst : ∀ g, rS ι₄ g (flat 0 f) = flat 0 f →
        rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f) := by
      intro g hg
      conv_rhs => rw [← hg]
      funext x m
      simp [ev, rS, rightReg, LinearMap.funLeft, mul_assoc]
    show IsOpen {g | rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f)}
    refine isOpen_iff_mem_nhds.2 fun g₀ hg₀ => ?_
    have h1 : (1 : GS (2 + 2) w) ∈ {g | rS ι₄ g (flat 0 f) = flat 0 f} := by simp
    have hn : (fun x => g₀⁻¹ * x) ⁻¹' {g | rS ι₄ g (flat 0 f) = flat 0 f} ∈ 𝓝 g₀ :=
      ((continuous_const.mul continuous_id).continuousAt (x := g₀)).preimage_mem_nhds
        (hop.mem_nhds (by simpa using h1))
    filter_upwards [hn] with x hx
    have h2 := hst _ hx
    have h3 : x = g₀ * (g₀⁻¹ * x) := by group
    show rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) x _ = _
    rw [h3, map_mul, Module.End.mul_apply, h2]
    exact hg₀
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RayLv
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem ray_lv {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hf : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hf.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ :=
    Subtype.ext (Real.exp_neg t)
  rw [Subgroup.coe_mul, blkLaws.1, Subgroup.coe_one, one_mul, one_mul, zt, zt, h]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evInj :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ = 0 → φ = 0 := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hA r w ι₄ hw hι φ hφ h0
  obtain ⟨f, hf, hfa, ⟨U, -, hU⟩, rfl⟩ := ((zMem μ₂ τ₁ τ₂ κ e hA.idem).1 _ φ).1 hφ
  have h1 : ∀ g m₁ m₂, f (lv m₁ m₂ 0 * arc1 k₀ * fin1 (ι₄ g)) = 0 := fun g m₁ m₂ =>
    (mul_eq_zero.1 (congrFun (congrFun h0 g) (m₁, m₂))).resolve_left (Complex.exp_ne_zero _)
  obtain ⟨ι₂, hι₂⟩ := (embEx (K := K) 2 w hw).1
  have hz : f = 0 := by
    refine hA.inj f hf hfa fun h m₁ m₂ => ?_
    obtain ⟨X, a₁, a₂, t, g, u, hu, hd⟩ := finIwa w ι₄ hw hι h k₀
    obtain ⟨X', hX⟩ := (parLaw w ι₂ ι₄ hw hι₂ hι).1 m₁ m₂ 0 X
    have hl : lv m₁ m₂ 0 * lv a₁ a₂ t = lv 1 1 t * lv (m₁ * a₁) (m₂ * a₂) 0 := by
      rw [blkLaws.2.1, blkLaws.2.1, one_mul, one_mul, zero_add, add_zero]
    have he : lv m₁ m₂ 0 * arc1 k₀ * fin1 h =
        nn X' * (lv 1 1 t * (lv (m₁ * a₁) (m₂ * a₂) 0 * arc1 k₀ * fin1 (ι₄ g))) * fin1 u := by
      rw [mul_assoc, hd]
      simp only [← mul_assoc]
      rw [hX, mul_assoc (nn X'), hl, ← mul_assoc (nn X')]
    rw [he, hU u (hu U), hf.unip, ray_lv hf, h1]
  funext x
  rw [hz]
  exact mul_zero _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.XSimple
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Abs

variable {G : Type} [Group G] [TopologicalSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma orbit_finite [IsTopologicalGroup G] (π : UnitaryRep G H) {L L' : Subgroup G} (hL : IsCompact (L : Set G))
    (hL' : IsOpen (L' : Set G)) {m : H} (hm : ∀ u ∈ L', π u m = m) : ((fun u => π u m) '' (L : Set G)).Finite := by
  have hlc : IsLocallyConstant fun u : G => π u m := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' (L' : Set G), hL'.preimage (by fun_prop), by simp, fun y hy => ?_⟩
    have : y = x * (x⁻¹ * y) := by simp
    rw [this, UnitaryRep.map_mul_apply, hm _ hy]
  haveI : CompactSpace (L : Set G) := isCompact_iff_compactSpace.1 hL
  rw [Set.image_eq_range]
  exact (hlc.comp_continuous continuous_subtype_val).range_finite

private lemma mem_of_closure (π : UnitaryRep G H) (L : Subgroup G) (M E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hst : ∀ u ∈ L, ∀ m ∈ M, π u m ∈ M) (hfin : ∀ m ∈ M, ((fun u => π u m) '' (L : Set G)).Finite)
    (hE : ∀ m ∈ M, (∀ u ∈ L, π u m = m) → m ∈ E) {v : H} (hv : v ∈ closure (M : Set H))
    (hfix : ∀ u ∈ L, π u v = v) : v ∈ M := by
  haveI : FiniteDimensional ℂ ↥(M ⊓ E) := Submodule.finiteDimensional_of_le inf_le_right
  have hcl : IsClosed ((M ⊓ E : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
  suffices h : v ∈ closure ((M ⊓ E : Submodule ℂ H) : Set H) by
    rw [hcl.closure_eq] at h
    exact h.1
  rw [Metric.mem_closure_iff] at hv ⊢
  intro ε hε
  obtain ⟨m, hm, hd⟩ := hv ε hε
  set O := (hfin m hm).toFinset with hO
  have hmem : ∀ x, x ∈ O ↔ ∃ u ∈ L, π u m = x := by
    intro x
    simp [hO]
  have hne : O.Nonempty := ⟨π 1 m, (hmem _).2 ⟨1, L.one_mem, rfl⟩⟩
  have hcard : (0 : ℝ) < O.card := by exact_mod_cast hne.card_pos
  have haM : O.centerMass (fun _ => (1 : ℝ)) id ∈ M := by
    rw [Finset.centerMass]
    refine M.smul_of_tower_mem _ (M.sum_mem fun x hx => M.smul_of_tower_mem _ ?_)
    obtain ⟨u, hu, rfl⟩ := (hmem x).1 hx
    exact hst u hu m hm
  refine ⟨O.centerMass (fun _ => (1 : ℝ)) id, ⟨haM, hE _ haM fun u hu => ?_⟩, ?_⟩
  · rw [Finset.centerMass, ContinuousLinearMap.map_smul_of_tower, map_sum]
    congr 1
    simp only [one_smul, id]
    refine Finset.sum_nbij' (fun x => π u x) (fun x => π u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨u * a, L.mul_mem hu ha, UnitaryRep.map_mul_apply _ _ _ _⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨u⁻¹ * a, L.mul_mem (L.inv_mem hu) ha, UnitaryRep.map_mul_apply _ _ _ _⟩
    · intro x _
      simp [← UnitaryRep.map_mul_apply]
    · intro x _
      simp [← UnitaryRep.map_mul_apply]
  · rw [dist_comm, ← Metric.mem_ball]
    refine (convex_ball v ε).centerMass_mem (fun _ _ => zero_le_one) (by simpa using hcard) fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
    rw [Metric.mem_ball, id, dist_comm, dist_eq_norm, ← hfix a ha, ← map_sub, UnitaryRep.norm_map, ← dist_eq_norm]
    exact hd

end Abs

section Cl

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private lemma continuous_pOp (μ : Measure (G1 K n)) [μ.IsHaarMeasure] {κ : Measure (archCompact K n)}
    {p : archCompact K n → ℂ} (hp : IdemA κ p) : Continuous (pOp μ κ p) := by
  obtain ⟨-, -, -, harc, hcs, -⟩ := levLaws (K := K) n ∅
  haveI := hcs
  haveI := hp.haar.prob
  have hi : ∀ v, Integrable (fun k => p k • rightRegularRep (Gam K n) μ (arc1 k) v) κ := fun v =>
    (hp.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp harc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : ∀ v v', dist (pOp μ κ p v) (pOp μ κ p v') ≤ (∫ k, ‖p k‖ ∂κ) * dist v v' := by
    intro v v'
    rw [dist_eq_norm, dist_eq_norm, pOp, pOp, ← integral_sub (hi v) (hi v'), ← integral_mul_const]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext k
    rw [← smul_sub, ← map_sub, norm_smul, UnitaryRep.norm_map]
  exact (LipschitzWith.of_dist_le' hb).continuous

private lemma mem_fixF (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (U : Subgroup (FA K n)) (v : L2 μ) :
    v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v := by
  simp [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private lemma isClosed_inH (μ : Measure (G1 K n)) [μ.IsHaarMeasure] {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ)
    {κ : Measure (archCompact K n)} {p : archCompact K n → ℂ} (hp : IdemA κ p) (S : Finset (Pl K)) :
    IsClosed {v | InH μ τ κ p S v} := by
  have hf : ∀ U : Subgroup (FA K n), IsClosed (fixF μ U : Set (L2 μ)) := by
    intro U
    have h : (fixF μ U : Set (L2 μ)) = ⋂ u ∈ U, {v | rhoF μ u v = v} := by
      ext v
      simp [mem_fixF]
    rw [h]
    exact isClosed_biInter fun u _ => isClosed_eq (rhoF μ u).continuous continuous_id
  have hs : IsClosed (sphOff μ S : Set (L2 μ)) := by
    rw [sphOff]
    simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun v => isClosed_iInter fun _ => hf _
  exact hτ.closed.inter ((isClosed_eq (continuous_pOp μ hp) continuous_id).inter hs)

end Cl

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xSimple :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), CuspIrr μ τ → RankInf μ τ κ p → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι →
      SimpleIn (rS ι) (Xs μ τ κ p (im w)) ∧ SchurIn (rS ι) (Xs μ τ κ p (im w)) := by
  intro K _ _ _ μ _ τ κ p hτ hR r w ι hw hι
  have hp : IdemA κ p := hR.1
  obtain ⟨hX, hX'⟩ := xMem μ τ κ p hp
  have hstab := fun φ hφ => (hX' hτ w ι hw hι φ hφ).2
  obtain ⟨J, hJi, hJ, hJr, hJU⟩ := exists_injection_into_l2_cusp μ τ κ p hτ hp (im w)
  obtain ⟨-, hcw, hco, -, -, hlev⟩ := (embEx 2 w hw).2 ι hι
  have hcw1 : ∀ i, GM.cf (w i) (1 : FA K 2) = 1 := fun i => by
    have := hcw 1 i
    rwa [map_one] at this
  have hcv1 : ∀ v, GM.cf v (1 : FA K 2) = 1 := fun v => by
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      exact hcw1 i
    · have := hco 1 v hv
      rwa [map_one] at this
  have hCO := (levLaws (K := K) 2 (im w)).1
  have hrS : ∀ g (φ : G1 K 2 → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g)) := fun _ _ _ => rfl

  have hdec : ∀ U, ∀ u ∈ levOn (im w) U, ∃ g, ι g ∈ levOn (im w) U ∧
      ∀ φ ∈ Xs μ τ κ p (im w), ∀ x, φ (x * fin1 u) = rS ι g φ x := by
    intro U u hu
    obtain ⟨g, h', rfl, hg, h1, h2⟩ := (hlev U u).1 hu
    refine ⟨g, (hlev U _).2 ⟨g, 1, (mul_one _).symm, hg, hcw1, fun v => ?_⟩, fun φ hφ x => ?_⟩
    · rw [hcv1]
      exact one_mem _
    · obtain ⟨-, -, -, U', -, hU'⟩ := (hX _ _).1 hφ
      have := hU' h' ((hlev U' _).2 ⟨1, h', by simp, fun i => one_mem _, h1, h2⟩) (x * fin1 (ι g))
      rw [hrS, ← this]
      simp only [fin1, map_mul, mul_assoc]
  let π : UnitaryRep (FA K 2) (L2 μ) :=
    (rightRegularRep (rationalGLOne K 2) μ).compHom (MultiplicityOne.finProj K 2) MultiplicityOne.continuous_finProj
  have hπ : ∀ h, π h = rhoF μ h := fun _ => rfl
  have hfixJ : ∀ (L : Subgroup (FA K 2)) (φ : Xs μ τ κ p (im w)), FixF L φ.1 → ∀ u ∈ L, rhoF μ u (J φ) = J φ :=
    fun L φ hφ u hu => (hJr u φ φ fun x => (hφ u hu x).symm).symm
  have hS : SimpleIn (rS ι) (Xs μ τ κ p (im w)) := by
    refine ⟨fun g φ hφ => hstab φ hφ g, fun Q hQ hQs => ?_⟩
    let M : Submodule ℂ (L2 μ) := (Q.comap (Xs μ τ κ p (im w)).subtype).map J
    have hM : ∀ g, ∀ m ∈ M, rhoF μ (ι g) m ∈ M := by
      rintro g _ ⟨φ, hφ, rfl⟩
      exact ⟨⟨rS ι g φ.1, hstab _ φ.2 g⟩, hQs g _ hφ, hJr _ _ _ fun x => rfl⟩
    have hT := xTop μ τ κ p hτ hR w ι hw hι M.topologicalClosure M.isClosed_topologicalClosure
      (fun v hv => closure_minimal (s := (M : Set (L2 μ))) (by rintro _ ⟨φ, -, rfl⟩; exact (hJ φ).2)
        (isClosed_inH μ hτ hp (im w)) hv)
      (fun g v hv => map_mem_closure (rhoF μ (ι g)).continuous hv (hM g))
    rcases hT with hT | hT
    · left
      rw [eq_bot_iff]
      intro φ hφ
      have h0 : J ⟨φ, hQ hφ⟩ ∈ M.topologicalClosure := M.le_topologicalClosure ⟨⟨φ, hQ hφ⟩, hφ, rfl⟩
      rw [hT, Submodule.mem_bot, ← map_zero J] at h0
      exact congrArg Subtype.val (hJi h0)
    · right
      refine le_antisymm hQ fun φ hφ => ?_
      obtain ⟨-, -, -, U, hU, hφU⟩ := (hX _ _).1 hφ
      obtain ⟨hsur, E, hE, hEU⟩ := hJU U hU
      haveI : FiniteDimensional ℂ ↥(E.comap (Xs μ τ κ p (im w)).subtype) :=
        FiniteDimensional.of_injective
          (((Xs μ τ κ p (im w)).subtype.domRestrict (E.comap (Xs μ τ κ p (im w)).subtype)).codRestrict E fun a => a.2)
          fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : G1 K 2 → ℂ)) h))
      have key : J ⟨φ, hφ⟩ ∈ M := by
        refine mem_of_closure π (levOn (im w) U) M ((E.comap (Xs μ τ κ p (im w)).subtype).map J) ?_ ?_ ?_
          (hT _ (hJ _).2) (hfixJ _ ⟨φ, hφ⟩ hφU)
        · rintro u hu _ ⟨ψ, hψ, rfl⟩
          obtain ⟨g, -, hg⟩ := hdec U u hu
          exact ⟨⟨rS ι g ψ.1, hstab _ ψ.2 g⟩, hQs g _ hψ, hJr _ _ _ fun x => (hg _ ψ.2 x).symm⟩
        · rintro _ ⟨ψ, -, rfl⟩
          obtain ⟨-, -, -, U', hU', hψU⟩ := (hX _ _).1 ψ.2
          exact orbit_finite π (hCO U hU).1.1 (hCO U' hU').1.2 (hfixJ _ ψ hψU)
        · rintro _ ⟨ψ, -, rfl⟩ hf
          obtain ⟨ψ', h1, h2⟩ := hsur _ (hJ ψ).2 ((mem_fixF μ _ _).2 hf)
          exact ⟨ψ', hEU _ ψ'.2 h2, h1⟩
      obtain ⟨ψ, hψ, h⟩ := key
      rw [hJi h] at hψ
      exact hψ
  refine ⟨hS, fun T hT => ?_⟩
  by_cases h0 : ∀ φ : Xs μ τ κ p (im w), φ = 0
  · exact ⟨0, fun v => by rw [h0 (T v), zero_smul]⟩
  push Not at h0
  obtain ⟨φ, hφ0⟩ := h0
  obtain ⟨-, -, -, U, hU, hφU⟩ := (hX _ _).1 φ.2
  obtain ⟨-, E, hE, hEU⟩ := hJU U hU
  let F : Submodule ℂ (Xs μ τ κ p (im w)) :=
    { carrier := {ψ | FixF (levOn (im w) U) ψ.1}
      add_mem' := fun ha hb u hu g => by simp [ha u hu g, hb u hu g]
      zero_mem' := fun u hu g => rfl
      smul_mem' := fun c _ ha u hu g => by simp [ha u hu g] }
  haveI : FiniteDimensional ℂ ↥(E.comap (Xs μ τ κ p (im w)).subtype) :=
    FiniteDimensional.of_injective
          (((Xs μ τ κ p (im w)).subtype.domRestrict (E.comap (Xs μ τ κ p (im w)).subtype)).codRestrict E fun a => a.2)
          fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : G1 K 2 → ℂ)) h))
  haveI : FiniteDimensional ℂ F :=
    Submodule.finiteDimensional_of_le (S₂ := E.comap (Xs μ τ κ p (im w)).subtype) fun ψ hψ => hEU _ ψ.2 hψ
  haveI : Nontrivial F := ⟨⟨⟨φ, hφU⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  have hTF : ∀ ψ ∈ F, T ψ ∈ F := by
    intro ψ hψ u hu x
    obtain ⟨g, hg, hg'⟩ := hdec U u hu
    rw [hg' _ (T ψ).2, ← hT g ψ ψ (funext fun y => (hψ _ hg y).symm)]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hTF)
  obtain ⟨ψ, hψ⟩ := hc.exists_hasEigenvector
  have hψ1 : T ψ.1 = c • ψ.1 := congrArg Subtype.val hψ.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases hS.2 ((Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype) (Submodule.map_subtype_le _ _) (by
    rintro g _ ⟨a, ha, rfl⟩
    refine ⟨⟨rS ι g a.1, hstab _ a.2 g⟩, Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_), rfl⟩
    rw [hT g a _ rfl, Module.End.mem_eigenspace_iff.1 ha]
    simp) with h | h
  · have : (ψ.1 : G1 K 2 → ℂ) ∈ (Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype :=
      ⟨ψ.1, Module.End.mem_eigenspace_iff.2 hψ1, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact absurd (Subtype.ext (Subtype.ext this)) hψ.2
  · intro v
    have : (v : G1 K 2 → ℂ) ∈ (Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype := by
      rw [h]
      exact v.2
    obtain ⟨a, ha, hav⟩ := this
    rw [← Subtype.ext hav]
    exact Module.End.mem_eigenspace_iff.1 ha
end

