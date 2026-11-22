import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
import Development.WeilBound.ThetaLifts.LatticeBasics.Unfold0
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0001
import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0012
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinA
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped SchwartzMap
open GlobalTheory.ThK.Dbl.Dense Complex

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

structure Gau (f : 𝓢(V, ℂ)) (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) : Prop where
  ne : ∀ y, f y ≠ 0
  der : ∀ a y, fderiv ℝ f y a = m a y * f y
  symm : ∀ a y, m a y = m y a
  neg : ∀ a, a ≠ 0 → (m a a).re < 0

theorem gau_of {f : 𝓢(V, ℂ)} (hf : f ≠ 0) {m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ} (hm : ∀ a y, fderiv ℝ f y a = m a y * f y) : Gau f m := by
  obtain ⟨c, Q, Q', hc, pos, e⟩ := GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian f hf m hm
  have ne : ∀ y, f y ≠ 0 := fun y => by rw [e]; exact mul_ne_zero hc (exp_ne_zero _)
  have key : ∀ a y, m a y = -((Q a y + Q y a : ℝ) : ℂ) - I * ((Q' a y + Q' y a : ℝ) : ℂ) := fun a y => by
    have l : HasDerivAt (fun t : ℝ => y + t • a) a 0 := by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add y
    have h1 : HasDerivAt (fun t : ℝ => f (y + t • a)) (fderiv ℝ f y a) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (f.differentiableAt (x := y)).hasFDerivAt l (by simp)
    have q : ∀ P : V →ₗ[ℝ] V →ₗ[ℝ] ℝ, HasDerivAt (fun t : ℝ => ((P (y + t • a) (y + t • a) : ℝ) : ℂ)) ((P a y + P y a : ℝ) : ℂ) 0 :=
      fun P => by
        have e1 : (fun t : ℝ => P (y + t • a) (y + t • a)) = fun t => P y y + t * (P a y + P y a) + t ^ 2 * P a a := by
          funext t; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]; ring
        have : HasDerivAt (fun t : ℝ => P (y + t • a) (y + t • a)) (P a y + P y a) 0 := by
          rw [e1]
          exact ((((hasDerivAt_id (0 : ℝ)).mul_const (P a y + P y a)).const_add (P y y)).fun_add
            ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (P a a))).congr_deriv (by simp)
        exact this.ofReal_comp
    have h2 := (((q Q).neg.sub ((q Q').const_mul I)).cexp).const_mul c
    have h3 : (fun t : ℝ => f (y + t • a)) = _ := funext fun t => e _
    rw [h3] at h1
    have h4 := h1.unique h2
    rw [hm] at h4
    refine mul_right_cancel₀ (ne y) (h4.trans ?_)
    rw [e]; simp; ring
  refine ⟨ne, hm, fun a y => by rw [key, key, add_comm (Q a y), add_comm (Q' a y)], fun a ha => ?_⟩
  have := pos a ha
  rw [key]; simp; linarith

theorem opp {f g : 𝓢(V, ℂ)} {m n : V →ₗ[ℝ] V →ₗ[ℝ] ℂ} (hf : Gau f m) (hg : Gau g n) {a b : V} {L L' : V →L[ℝ] ℝ}
    (h1 : dop b L' f = I • dop a L f) (h2 : dop (-b) (-L') g = I • dop a L g) : a = 0 ∧ L = 0 := by
  have e1 : ∀ y, m b y - 2 * Real.pi * I * L' y = I * (m a y - 2 * Real.pi * I * L y) := fun y => by
    have := congrArg (fun h : 𝓢(V, ℂ) => h y) h1
    simp only [SchwartzMap.smul_apply, dop_apply, hf.der, smul_eq_mul] at this
    exact mul_right_cancel₀ (hf.ne y) (by linear_combination this)
  have e2 : ∀ y, -n b y + 2 * Real.pi * I * L' y = I * (n a y - 2 * Real.pi * I * L y) := fun y => by
    have := congrArg (fun h : 𝓢(V, ℂ) => h y) h2
    simp only [SchwartzMap.smul_apply, dop_apply, hg.der, smul_eq_mul, map_neg, LinearMap.neg_apply,
      ContinuousLinearMap.neg_apply, ofReal_neg] at this
    exact mul_right_cancel₀ (hg.ne y) (by linear_combination this)
  have r1 := fun y => congrArg re (e1 y)
  have i1 := fun y => congrArg im (e1 y)
  have r2 := fun y => congrArg re (e2 y)
  have i2 := fun y => congrArg im (e2 y)
  simp at r1 i1 r2 i2
  have s1 := congrArg im (hf.symm a b)
  have s2 := congrArg im (hg.symm a b)
  have le : ∀ {h : 𝓢(V, ℂ)} {k} (_ : Gau h k) x, (k x x).re ≤ 0 := fun H x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (H.neg x hx).le
  have ha : a = 0 := by
    by_contra ha
    linarith [hf.neg a ha, hg.neg a ha, le hf b, le hg b, r1 b, r2 b, i1 a, i2 a]
  have hb : b = 0 := by
    by_contra hb
    linarith [hf.neg b hb, hg.neg b hb, le hf a, le hg a, r1 b, r2 b, i1 a, i2 a]
  refine ⟨ha, ContinuousLinearMap.ext fun y => ?_⟩
  have := r1 y
  simpa [ha, hb, Real.pi_ne_zero] using this

end GlobalTheory.ThK.Dbl.Box

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

def Stab2Cpt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → IsCompact (K : Set (G2 σ Y))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {z s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem absE_pos (t : (AE F E)ˣ) : 0 < (absE F E t : ℝ) :=
  NNReal.coe_pos.2 (pos_iff_ne_zero.2 ((Group.isUnit t).map (absE F E)).ne_zero)

theorem IsHgt.mul (h : IsHgt K a) {p t} (hp : IsPar p t) (x) :
    a (p * x) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * a x := by
  obtain ⟨p', t', hp', k, hk, rfl⟩ := h.iwa x
  rw [← mul_assoc, h.val _ _ (hp.mul hp') k hk, h.val _ _ hp' k hk, map_mul, map_mul, NNReal.coe_mul]

theorem Law.flat (hf : Law χ z f) (h : IsHgt K a) (h0 : ∀ x, 0 < a x) (s : ℂ) : Law χ (s - s₀ + z) (flat a f s₀ s) := fun p t x hp => by
  rw [Dbl.flat, Dbl.flat, h.mul hp, hf p t x hp, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (absE_pos _).le (h0 x).le,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (absE_pos _).ne')]
  ring

theorem Law.bound (hf : Law χ z f) (hc : Continuous f) (h : IsHgt K a) (hK : IsCompact (K : Set (G2 σ Y))) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * a x ^ z.re := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨p, t, hp, k, hk, rfl⟩ := h.iwa x
  rw [hf p t k hp, h.val p t hp k hk, norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (absE_pos _),
    mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k hk) (Real.rpow_nonneg (absE_pos _).le _)

theorem continuous_flat (hc : Continuous f) (ha : Continuous a) (h0 : ∀ x, 0 < a x) (s : ℂ) : Continuous (flat a f s₀ s) :=
  ((Complex.continuous_ofReal.comp ha).cpow continuous_const fun x => Complex.ofReal_mem_slitPlane.2 (h0 x)).mul hc

def kpair (χ : Chr F E) (e : UA σ Y.J × UA σ Y.J →* G2 σ Y) (μ : Measure (UA σ Y.J)) (D : Set (UA σ Y.J)) (Ê : G2 σ Y → ℂ)
    (φ : UA σ Y.J → ℂ) : ℂ := ∫ y, Ê (e y) * detInv χ y.2 * (φ y.2 * star (φ y.1)) ∂(μ.restrict D).prod (μ.restrict D)

theorem kpair_cont {B : Base F E} {r s : ℕ} (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (h0 : min r s = 0)
    (c : Cpt σ Y.J) (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x, 0 < a x) (cf : Continuous f) (hf : Law χ z f)
    {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ Y.J) D μ) {t₀ : ℝ} (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) :
    (∀ φ, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U) ∧ ∃ t : ℝ, ∀ s : ℂ, t < s.re → s ∈ U ∧
      Integrable (fun g => flat a f s₀ s (e (1, g)) * detInv χ g) μ ∧ ∀ φ, IsRapid φ → kpair χ e μ D (Ê s) φ =
        ∫ g, flat a f s₀ s (e (1, g)) * detInv χ g * pet μ D (fun h => φ (h * g)) φ ∂μ := by
  have hJ := aniso_of hB hY h0
  obtain ⟨t₁, half⟩ := hE.half
  haveI := c.sc; haveI := c.lc
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using c.fin _ _ hμ hD⟩
  have bc : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → An.BC φ := fun h => ⟨h.1, c.bdd h.1 h.2.1⟩
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ ratU σ Y.J, ∀ δ ∈ ratU σ Y.J, ∀ g g', Ê s (e (γ * g, δ * g')) = Ê s (e (g, g')) := fun s hs γ hγ δ hδ g g' =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1, by
      rw [← Prod.mk_mul_mk, map_mul]; exact (hf.flat ha a0 s).eis_inv hχ hJ he (half s hs).2 hγ hδ _⟩) hs
  have ck : ∀ s ∈ U, An.BC fun y : UA σ Y.J × UA σ Y.J => Ê s (e y) * detInv χ y.2 := fun s hs =>
    An.BC.mul ⟨(cE s hs).comp ce, c.bdd₂ c ((cE s hs).comp ce) (iv s hs)⟩
      ⟨(continuous_detInv hχ).comp continuous_snd, 1, fun y => (norm_detInv _ _).le⟩
  have hol : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U := fun {φ} h => by
    have b := ((bc h).comp (continuous_snd (X := UA σ Y.J))).mul ((bc h).comp continuous_fst).star
    refine An.diffOn_integral hE.isOpen (fun s hs => ((ck s hs).mul b).1.aestronglyMeasurable)
      (fun y => ((hE.hol _).mul_const _).mul_const _) fun S hS cS => ?_
    obtain ⟨Ω, hΩ, cov⟩ := c.cov
    obtain ⟨C, hC⟩ := (cS.prod ((hΩ.prod hΩ).image ce)).exists_bound_of_continuousOn
      (hE.cont.mono (Set.prod_mono hS (Set.subset_univ _)))
    obtain ⟨C', hC'⟩ := b.2
    refine ⟨C * C', fun s hs y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    obtain ⟨δ, hδ, h2⟩ := cov y.2
    have := hC (s, e (γ * y.1, δ * y.2)) ⟨hs, _, ⟨h1, h2⟩, rfl⟩
    rw [iv s (hS hs) γ hγ δ hδ] at this
    rw [norm_mul, norm_mul, norm_detInv, mul_one]
    exact mul_le_mul this (hC' y) (norm_nonneg _) ((norm_nonneg _).trans this)
  refine ⟨fun _ => hol, max t₁ (t₀ + s₀.re - z.re), fun s hs => ?_⟩
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt hs)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s - s₀ + z).re (by have := (le_max_right _ _).trans_lt hs; simp; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  exact ⟨u, i2, fun φ h => An.far_right _ μ (ck s u) (bc h) i2
    (unfold0 F E σ B n Y r _ hB hY h0 χ e hχ he _ _ _ cs (cE s u) sm (hf.flat ha a0 s) μ D hμ hD i1 _ h)⟩

theorem I_right {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : Fn F n d) (g h : UA σ W.J) :
    M.I om (om (1, g) Φ) h = M.I om Φ (h * g) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem I_inv {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {om : Rep σ X W} {Φ : Fn F n d}
    (h : ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, theta om Φ (γ * g) (γ' * h) = theta om Φ g h) :
    ∀ γ ∈ ratU σ W.J, ∀ x, M.I om Φ (γ * x) = M.I om Φ x := fun γ hγ x =>
  integral_congr_ae (.of_forall fun g => (one_mul g ▸ h 1 (one_mem _) γ hγ g x :))

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LocMeas
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {v : Pl F}

theorem isOpen_int (hL : Y.L.IsLattice E) (v : Pl F) : IsOpen (intGrp σ Y v : Set (UA σ Y.J)) := by
  classical
  obtain ⟨m, x, hs, hx⟩ := lat_gen hL
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have ce : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  let U : Set (Fin m → AF F) := {a | ∀ i, evFin F v (a i) ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => (Valued.isOpen_valuationSubring _).preimage (ce.comp (continuous_apply i))
  have hV := IsModuleTopology.isOpenMap_of_surjective (gen_surj hL hs) U hU
  set V := (Fintype.linearCombination (AF F) fun i => incV F (x i).1) '' U with eV
  have key : ∀ A : Matrix (Fin n) (Fin n) (AE F E), (∀ i, A *ᵥ incV F (x i).1 ∈ V) → ∀ z ∈ latHat Y, At (evFin F v) z →
      A *ᵥ z ∈ latHat Y := fun A hA z hz h => by
    obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
    rw [← at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
    refine sum_mem fun i _ => ?_
    obtain ⟨b, hb, e⟩ := hA i
    rw [smul_smul, Matrix.mulVec_smul, ← e, Fintype.linearCombination_apply, Finset.smul_sum]
    refine sum_mem fun j _ => ?_
    rw [smul_smul, mul_assoc]
    exact gen_mem (idem_mem (by rw [map_mul]; exact mul_mem ((ha i).2 v) (hb j))) (x j).2
  have x1 : ∀ i, incV F (x i).1 ∈ V := fun i => ⟨Pi.single i 1, fun j => by
    rw [Pi.single_apply, apply_ite (evFin F v), map_one, map_zero]
    split_ifs
    exacts [one_mem _, zero_mem _], by rw [Fintype.linearCombination_apply_single, one_smul]⟩
  have o : IsOpen {g : UA σ Y.J | ∀ i, mat g *ᵥ incV F (x i).1 ∈ V} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => hV.preimage (cont_mat.matrix_mulVec continuous_const)
  have o1 : ∀ i, mat (1 : UA σ Y.J) *ᵥ incV F (x i).1 ∈ V := fun i => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]
    exact x1 i
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (mem_of_superset ((o.inter (o.preimage continuous_inv)).mem_nhds
    ⟨o1, by rw [Set.mem_preimage, inv_one]; exact o1⟩) fun g hg z hz h => ⟨key _ hg.1 z hz h, key _ hg.2 z hz h⟩)

theorem exists_cpt (hL : Y.L.IsLattice E) (v : Pl F) : ∃ C : Set (Matrix (Fin n) (Fin n) (AE F E)), IsCompact C ∧
    ∀ g ∈ locGrp σ Y v, IntAt v g → mat g ∈ C := by
  obtain ⟨m, x, hs, -⟩ := lat_gen hL
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  choose c hc using fun j : Fin n => gen_surj hL hs (Pi.single j 1)
  refine ⟨_, (isCompact_univ_pi fun _ : Fin m => isCompact_latHat hL).image
    (f := fun y => (1 - idem v) • 1 + Matrix.of fun r j => ∑ i, c j i • y i r)
    (continuous_matrix fun r j => by simp only [Matrix.of_apply, Matrix.add_apply]; fun_prop), fun g hg h => ?_⟩
  refine ⟨fun i => mat g *ᵥ (idem v • incV F (x i).1), fun i _ => (h _ ?_ (at_iff.2 (by rw [smul_smul, idem_sq]))).1, ?_⟩
  · exact gen_mem (mul_one (idem v) ▸ idem_mem (by rw [map_one]; exact one_mem _)) (x i).2
  · refine Eq.trans ?_ (congrArg mat (mem_loc.1 hg))
    show (1 - idem v) • 1 + _ = (1 - idem v) • 1 + idem v • mat g
    refine (add_right_inj _).2 (Matrix.ext fun r j => ?_)
    have e := congrFun (congrArg (fun w => idem v • mat g *ᵥ w) (hc j)) r
    simp only [Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.smul_sum, Finset.sum_apply,
      Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply] at e
    simp only [Matrix.of_apply, Matrix.mulVec_smul, Pi.smul_apply, Matrix.smul_apply, ← e]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem isCompact_int (hL : Y.L.IsLattice E) (v : Pl F) : IsCompact {g : locGrp σ Y v | IntAt v g.1} := by
  obtain ⟨C, hC, h⟩ := exists_cpt (σ := σ) hL v
  have := t2Space_cm_host_adeles (F := F) (E := E)
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
  have hc : IsClosed (UG (cA σ) (incM F Y.J) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs)) continuous_const
  have e := (Units.isClosedEmbedding_embedProduct.comp hc.isClosedEmbedding_subtypeVal).comp
    (isClosed_loc (σ := σ) (Y := Y) (v := v)).isClosedEmbedding_subtypeVal
  refine (e.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))).of_isClosed_subset
    ((isClosed_int hL v).preimage continuous_subtype_val) fun g hg => ⟨h _ g.2 hg, _, h _ (inv_mem g.2) ?_, rfl⟩
  exact (intGrp σ Y v).inv_mem hg

theorem _root_.GlobalTheory.ThK.Dbl.locMeas : LocMeas := by
  intro F E _ _ _ _ _ σ B n Y r s _ hY v
  obtain ⟨b1, b2⟩ := lcsc_loc (σ := σ) (Y := Y) v
  let K : TopologicalSpace.PositiveCompacts (locGrp σ Y v) := ⟨⟨_, isCompact_int hY.lat v⟩, 1, mem_interior_iff_mem_nhds.2
    (((isOpen_int hY.lat v).preimage continuous_subtype_val).mem_nhds (intGrp σ Y v).one_mem)⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

end GlobalTheory.ThK.Dbl.Euler

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.PairsB
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dens
open PositivityTheory.ThKF (ArchOp PureAct)
open PositivityTheory.ThK (LocRepEx)

def PolFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ U : Submodule ℂ (SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ U ∧
      ∀ k ∈ KInf σ G.W B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ U

namespace Prs

theorem countable_compactOpen (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsOpen U ∧ IsCompact U}.Countable := by
  have hb := TopologicalSpace.isBasis_countableBasis X
  have hc := TopologicalSpace.countable_countableBasis X
  have hfin : {t : Set (Set X) | t.Finite ∧ t ⊆ TopologicalSpace.countableBasis X}.Countable :=
    Set.countable_setOf_finite_subset hc
  refine (hfin.image fun t => ⋃₀ t).mono ?_
  rintro U ⟨hU, hK⟩
  obtain ⟨S, hS, rfl⟩ := hb.open_eq_sUnion hU
  obtain ⟨t, htS, htf, hcov⟩ := hK.elim_finite_subcover_image (b := S) (c := fun s => s)
    (fun s hs => hb.isOpen (hS hs)) Set.sUnion_eq_biUnion.subset
  refine ⟨t, ⟨htf, htS.trans hS⟩, Set.Subset.antisymm ?_ ?_⟩
  · exact Set.sUnion_subset_sUnion htS
  · simpa [Set.sUnion_eq_biUnion] using hcov

theorem mem_span_indicator {X : Type} [TopologicalSpace X] {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) :
    f ∈ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) := by
  classical
  obtain ⟨hl, hK⟩ := hf
  have hK' : IsCompact (tsupport f) := hK
  obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c})
    (fun c => hl.isOpen_fiber c) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hsum : f = ∑ c ∈ t, c • (f ⁻¹' {c}).indicator (1 : X → ℂ) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      have hx : x ∈ tsupport f := subset_tsupport f (fun h0 => hne (by simpa using h0))
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hx)
      have : f x = c := hxc
      exact h (this ▸ hc)
  rw [hsum]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = 0
  · simp [hc]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨hl.isOpen_fiber c, ?_⟩, rfl⟩)
    refine hK'.of_isClosed_subset (hl.isClosed_fiber c) fun x hx => subset_tsupport f ?_
    have : f x = c := hx
    simpa [Function.mem_support, this] using hc

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  have hle : GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (1 : X → ℂ)) '' {U : Set X | IsOpen U ∧ IsCompact U}) :=
    fun f hf => mem_span_indicator hf
  refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen X).image _)

theorem rank_SB_Fv : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) (κ : Type) [Finite κ],
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  intro F _ _ v κ _
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := secondCountable_of_proper
  exact rank_SB_le _

theorem cartan_one {n r : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hs : HasSig M r 0) (h : IsCartan M θ) : θ = 1 := by
  obtain ⟨rfl, A, hA⟩ := hs
  let P : Matrix (Fin r) (Fin r) ℂ := A.submatrix id Sum.inl
  have e : Pᵀ * (M * P.map star) = 1 := by
    rw [← Matrix.mul_assoc]
    exact Matrix.ext fun i j => congrFun (congrFun hA (Sum.inl i)) (Sum.inl j)
  have e' : P * (M * P.map star)ᵀ = 1 := by
    rw [mul_eq_one_comm, ← transpose_transpose P, ← transpose_mul, transpose_transpose, e, transpose_one]
  have pos : ∀ x : Fin r → ℂ, 0 ≤ (x ⬝ᵥ M *ᵥ star x).re := fun x => by
    obtain ⟨y, rfl⟩ : ∃ y, x = P *ᵥ y := ⟨(M * P.map star)ᵀ *ᵥ x, by rw [mulVec_mulVec, e', one_mulVec]⟩
    have : star (P *ᵥ y) = P.map star *ᵥ star y := funext fun i => by simp [Matrix.mulVec, dotProduct]
    rw [this, mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, e, one_mulVec]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  refine Matrix.ext_iff_mulVec.2 fun u => ?_
  by_contra hu
  rw [one_mulVec] at hu
  have h1 := h.2.2 (θ *ᵥ u - u) (sub_ne_zero.2 hu)
  rw [mulVec_sub, mulVec_mulVec, h.1, one_mulVec, ← neg_sub, neg_dotProduct, Complex.neg_re] at h1
  linarith [pos (θ *ᵥ u - u)]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
  {om' : Rep σ G.V' G.W}

theorem comm_theta (ht : IsTriple B G X om om') (hp : G.p = 0) (hq : G.q = 0) (w) (A) : Commute A (G.W.θ w) := by
  have h := ht.geo.hW.sig w
  rw [hp, hq] at h
  rw [cartan_one h (ht.geo.hW.cartan w)]
  exact Commute.one_right _

theorem deriv_mem {κ : Type} [Fintype κ] (U : Submodule ℂ (SInf F κ)) [FiniteDimensional ℂ U] (u : ℝ → SInf F κ)
    (hu : ∀ t, u t ∈ U) (f : SInf F κ) (h : ∀ x, HasDerivAt (fun t => u t x) (f x) 0) : f ∈ U := by
  let c : SInf F κ →ₗ[ℂ] (κ → mixedEmbedding.mixedSpace F) → ℂ := ⟨⟨fun g => g, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have h1 : Tendsto (fun t : ℝ => c (((t : ℂ)⁻¹) • (u t - u 0))) (𝓝[≠] 0) (𝓝 (c f)) := tendsto_pi_nhds.2 fun x => by
    refine (h x).tendsto_slope_zero.congr fun t => ?_
    show _ = (t : ℂ)⁻¹ * (u t x - u 0 x)
    rw [zero_add, Complex.real_smul, Complex.ofReal_inv]
  obtain ⟨g, hg, e⟩ := (U.map c).closed_of_finiteDimensional.mem_of_tendsto h1
    (Eventually.of_forall fun t => ⟨_, U.smul_mem _ (sub_mem (hu t) (hu 0)), rfl⟩)
  exact (DFunLike.coe_injective e : g = f) ▸ hg

theorem rank_pi (hm : IsMatched B G X om om' R Rf) (v : Pl F) : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
  rw [← rank_top, ← hm.fin.onto v]
  exact (rank_map_le _ _).trans (rank_SB_Fv _ _)

theorem irr_inf (hO : ArchOp) (hF : PolFin) (hm : IsMatched B G X om om' R Rf) (hp : G.p = 0) (hq : G.q = 0) (N : Submodule ℂ R.Pi)
    (h : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F _,
      Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N) : N = ⊥ ∨ N = ⊤ := by
  refine hm.real.irred N (fun γ hγ f hf f₁ hd hN => ?_) h
  obtain ⟨U, hU, H⟩ := hF F E σ B a a' G X om om' hm.triple f hf
  have hk : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ KInf σ G.W B.emb := fun t => ⟨hγ.2 _, fun w => comm_theta hm.triple hp hq w _⟩
  choose A hA using fun t : ℝ => inf_op hO (PositivityTheory.ThKG.pairV hm.triple) (hk t)
  have hM := hm.triple.geo.hM
  have hr := Dat.rest (T := ∅) hM ⟨hf, fun v => (hM.vac v).1, fun _ _ => rfl⟩
  have : ∀ v, ∃ b, G.M.vac v b ≠ 0 ∧
      (G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, b i ∈ v.adicCompletionIntegers F) := fun v => by
    obtain ⟨b, hb⟩ := Function.ne_iff.1 (hM.vac v).2.1
    exact ⟨b, hb, fun e => by rw [e] at hb; exact Set.mem_of_indicator_ne_zero hb⟩
  choose b hb hb' using this
  let y : Fin a × Fin (a + a') → Af F := fun i => ⟨fun v => b v i, hM.std.mono fun v e => hb' v e i⟩
  have hc : (∏ᶠ v, G.M.vac v (b v)) ≠ 0 := finprod_induction (· ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hb
  haveI : FiniteDimensional ℂ ↥(U ⊓ N.comap R.p) := Submodule.finiteDimensional_inf_left _ _
  refine (deriv_mem (U ⊓ N.comap R.p) (fun t => A t f) (fun t => ⟨H _ (hk t) _ (hA t f hf).2,
    h _ (hk t) f hf _ (hA t f hf).2 hN⟩) f₁ fun x => ?_).2
  let z : Fin a × Fin (a + a') → AF F := fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i) : Ainf F × Af F)
  have e : ∀ g : SInf F (Fin a × Fin (a + a')), tens (evI F) g (finPart G.M.vac) z = g x * ∏ᶠ v, G.M.vac v (b v) := fun g =>
    congrArg (fun u => g u * _) (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _)
  have := (hd _ hr z).div_const (∏ᶠ v, G.M.vac v (b v))
  simpa only [fun t => (hA t f hf).2 _ hr, e, mul_div_cancel_right₀ _ hc] using this

theorem fill (hL : LocRepEx) (hP : PureAct) (hO : ArchOp) (hF : PolFin) (hm : IsMatched B G X om om' R Rf) (hp : G.p = 0) (hq : G.q = 0) (T : Finset (Pl F))
    (N : Submodule ℂ (Fn F a (a + a'))) (hN : ∀ h, ∀ Φ ∈ N, om (1, h) Φ ∈ N) {Φ₀ ξ₀} (h0 : Φ₀ ∈ N)
    (c0 : (Φ₀, ξ₀) ∈ Cl B G.M R.p Rf.p T) (n0 : ξ₀ ≠ 0) (ξ) : ∃ Φ ∈ N, (Φ, ξ) ∈ Cl B G.M R.p Rf.p T := by
  let S : Submodule ℂ (PiT R Rf T) := (Cl B G.M R.p Rf.p T ⊓ N.prod ⊤).map (LinearMap.snd _ _ _)
  have mS : ∀ η, η ∈ S ↔ ∃ Φ ∈ N, (Φ, η) ∈ Cl B G.M R.p Rf.p T := fun η =>
    ⟨by rintro ⟨z, ⟨h1, h2, -⟩, rfl⟩; exact ⟨z.1, h2, h1⟩, fun ⟨Φ, h1, h2⟩ => ⟨(Φ, η), ⟨h2, h1, trivial⟩, rfl⟩⟩
  obtain ⟨a₀, ha₀, hy⟩ := exists_tmul_mem (A := R.Pi) (X := fun v : T => Rf.Pi v)
    (fun v => {Op | ∃ h, ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ ∧ Op (Rf.p v φ) = Rf.p v φ₁})
    (fun v => rank_pi hm v) (fun v => hm.fin.nontriv v)
    (fun v P hs => hm.fin.irred v P fun h hh φ hφ φ₁ h₁ hact hφP => by
      obtain ⟨Op, o1, o2, -⟩ := fin_ops hL hm hh
      rw [← o2 φ hφ φ₁ h₁ hact]
      exact hs Op ⟨h, o1⟩ _ hφP) S
    (by
      rintro v Op ⟨h, o⟩ η hη
      obtain ⟨Φ, h1, h2⟩ := (mS η).1 hη
      exact (mS _).2 ⟨_, hN h Φ h1, cl_fin hP hm.triple.geo.hM v _ Op o h2⟩) ξ₀ ((mS _).2 ⟨_, h0, c0⟩) n0
  let Ni : Submodule ℂ R.Pi := ⨅ y, S.comap ((TensorProduct.mk ℂ R.Pi _).flip y)
  have mN : ∀ u, u ∈ Ni ↔ ∀ y, u ⊗ₜ[ℂ] y ∈ S := fun u => Submodule.mem_iInf _
  rcases irr_inf hO hF hm hp hq Ni (fun k hk f hf f₁ hact hmem => (mN _).2 fun y => by
    obtain ⟨Op, o1, o2, -⟩ := inf_ops hO hm hk
    obtain ⟨Φ, h1, h2⟩ := (mS _).1 ((mN _).1 hmem y)
    have := cl_inf hm.triple.geo.hM _ Op o1 h2
    rw [LinearMap.rTensor_tmul, o2 f hf f₁ hact] at this
    exact (mS _).2 ⟨_, hN k Φ h1, this⟩) with hb | ht
  · exact absurd ((Submodule.mem_bot ℂ).1 (hb ▸ (mN _).2 hy)) ha₀
  · refine (mS ξ).1 ?_
    induction ξ using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul u y => exact (mN u).1 (ht ▸ Submodule.mem_top) y

theorem pairs_lin (hm : IsMatched B G X om om' R Rf) {y y'} (h : y ∈ pairs B G X R Rf) (h' : y' ∈ pairs B G X R Rf) (c : ℂ) :
    y + c • y' ∈ pairs B G X R Rf :=
  ⟨add_mem h.1 (Submodule.smul_mem _ c h'.1), polMatch_add_smul hm h.2 h'.2 c⟩

end Prs

open Prs

theorem pairsStable_of (hS : PositivityTheory.ThKEnd.MatchStab) : PairsStable := fun F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hp hq =>
  ⟨fun _ h _ h' c => pairs_lin hm h h' c, fun y hy h =>
    hS F E σ B a a' G X om om' R Rf hm h (fun w => comm_theta hm.triple hp hq w _) y.1 y.2 hy.1 hy.2⟩

theorem pairsIrr_of (hL : LocRepEx) (hP : PureAct) (hO : ArchOp) (hF : PolFin) : PairsIrr := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hp hq N hsub hnull hst
  refine or_iff_not_imp_left.2 fun hn y hy => ?_
  push Not at hn
  obtain ⟨y₀, h0, n0⟩ := hn
  obtain ⟨T₀, hT₀, H₀⟩ := polMatch_big hm (hsub h0).2
  obtain ⟨T₁, -, H₁⟩ := polMatch_big hm hy.2
  have hT : X.T ⊆ T₀ ∪ T₁ := hT₀.trans Finset.subset_union_left
  obtain ⟨ξ₀, c0, -⟩ := H₀ _ (Finset.subset_union_left (s₂ := T₁))
  obtain ⟨ξ, c1, -⟩ := H₁ _ (Finset.subset_union_right (s₁ := T₀))
  obtain ⟨_, ⟨z, hz, rfl⟩, c2⟩ := fill hL hP hO hF hm hp hq _ (N.map (LinearMap.fst _ _ _))
    (by rintro h _ ⟨z, hz, rfl⟩; exact ⟨_, hst z hz h, rfl⟩) ⟨y₀, h0, rfl⟩ c0
    (fun e => n0 (polMatch_iff.2 ⟨_, hT, ξ₀, c0, e ▸ zero_mem _⟩)) ξ
  have h1 := hnull _ (pairs_lin hm hy (hsub hz) (-1))
    (polMatch_iff.2 ⟨_, hT, 0, by simpa [sub_eq_add_neg] using sub_mem c1 c2, zero_mem _⟩)
  simpa using N.add_mem h1 hz

end GlobalTheory.ThK.Dbl

end
end

