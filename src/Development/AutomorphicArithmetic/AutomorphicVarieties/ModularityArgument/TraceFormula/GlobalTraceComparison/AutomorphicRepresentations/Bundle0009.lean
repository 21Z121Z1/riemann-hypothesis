import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFormEx
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

private theorem weight_ex : ∃ w : ℝ → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ s, 0 ≤ w s) ∧
    (∀ s ∈ Set.Ioo (-1 : ℝ) 1, w s ≠ 0) ∧ ∫ s, w s = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.continuous_normed, b.hasCompactSupport_normed, b.nonneg_normed, ?_,
    b.integral_normed⟩
  intro s hs
  have h : s ∈ Function.support (b.normed volume) := by
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.2 hs
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def slabSp (D : Dom E n 0) : Submodule ℂ (GA E n → ℂ) where
  carrier := {f | Slab D f}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl, fun u _ _ => by
    simp only [Pi.zero_apply, zero_mul]
    exact MemLp.zero⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.add_apply, a2, b2]
    · simp only [Pi.add_apply, a3, b3]
    · have h := (a4 u hu hc).add (b4 u hu hc)
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, a4⟩
    refine ⟨a1.const_smul c, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.smul_apply, a2]
    · simp only [Pi.smul_apply, a3]
    · have h := (a4 u hu hc).const_smul c
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem zero_of_ae (hB : Basic) (hA : AeEq) (hn : 1 ≤ n) (D : Dom E n 0) {f : GA E n → ℂ} (hf : Slab D f)
    (h : ∀ᵐ x ∂D.ν, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0) : f = 0 := by
  obtain ⟨hl, hm, -⟩ := hB E n hn
  have hinv : Inv (fun x : H E n 0 => f x.1) := by
    rintro ⟨_, ⟨p, q⟩, rfl⟩ x
    exact hf.2.1 p x.1
  have key := hA E n D (fun x => f x.1) (fun _ => 0) _ (hf.1.comp continuous_fst) continuous_const hinv
    (fun _ _ => rfl) isOpen_Ioo h
  funext g
  have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [hm, hl, neg_add_cancel]
    constructor <;> norm_num
  exact (hf.2.2.1 _ g).symm.trans (key _ h0)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.formEx_pf :
    Basic → AeEq → WtInd → FormEx := by
  intro hB hA hW E _ _ _ n hn D
  obtain ⟨w, wc, ws, w0, wp, w1⟩ := weight_ex
  have uc : Continuous fun s => (w s : ℂ) := Complex.continuous_ofReal.comp wc
  have us : HasCompactSupport fun s => (w s : ℂ) := ws.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have u1 : ∫ s, (w s : ℂ) = 1 := by rw [integral_complex_ofReal, w1, Complex.ofReal_one]
  have hI : ∀ a b : slabSp D, Integrable
      (fun x : H E n 0 => starRingEnd ℂ (a.1 x.1) * b.1 x.1 * (w (ldet x) : ℂ)) D.ν :=
    fun a b => (hW E n hn D a.1 b.1 a.2 b.2 _ uc us).1
  let B : slabSp D →ₗ⋆[ℂ] slabSp D →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun a b => prW D (fun s => (w s : ℂ)) a.1 b.1)
      (fun a a' b => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a' b)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        ring)
      (fun a b b' => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a b')]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring)
  have hBv : ∀ a b, B a b = prW D (fun s => (w s : ℂ)) a.1 b.1 := fun _ _ => rfl
  refine ⟨slabSp D, B, fun _ => Iff.rfl, fun a b => ?_, fun a ha => ?_, fun a b u hu hc => ?_, fun g hg a => ⟨?_, ?_⟩⟩
  · rw [hBv, hBv, prW, prW, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · have he : ∀ x : H E n 0, starRingEnd ℂ (a.1 x.1) * a.1 x.1 * (w (ldet x) : ℂ) =
        ((Complex.normSq (a.1 x.1) * w (ldet x) : ℝ) : ℂ) := fun x => by
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    have hi : Integrable (fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x)) D.ν := by
      have h := (hI a a).re
      simp only [he, RCLike.re_to_complex, Complex.ofReal_re] at h
      exact h
    have hnn : 0 ≤ fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x) :=
      fun x => mul_nonneg (Complex.normSq_nonneg _) (w0 _)
    rw [hBv, prW]
    simp only [he]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    refine lt_of_le_of_ne (integral_nonneg hnn) fun h0 => ha (Subtype.ext ?_)
    refine zero_of_ae hB hA hn D a.2 ?_
    filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hi).1 h0.symm] with x hx hI'
    exact Complex.normSq_eq_zero.1 ((mul_eq_zero.1 hx).resolve_right (wp _ hI'))
  · exact (hW E n hn D a.1 b.1 a.2 b.2 u hu hc).2.1 _ uc us u1
  · exact ((hW E n hn D a.1 a.1 a.2 a.2 _ uc us).2.2 g hg).1
  · intro a' b b' h1 h2
    rw [hBv, hBv, funext h1, funext h2]
    exact ((hW E n hn D a.1 b.1 a.2 b.2 _ uc us).2.2 g hg).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPiFinOf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piFinOf_pf :
    PiAdm → TensType → CvType → CvIn → TypeIn → PiFin := by
  intro hA hT hC hI hY E _ _ _ n hn D π hπ μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨ht, K, W, k1, k2, w1, w2, hl⟩ := hT E n μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨Y, y1, y2, y3⟩ := hA E n hn π hπ K W k1 w1
  refine ⟨Y, y1, y2, fun u hu φ hφ => ?_⟩
  obtain ⟨s0, s1⟩ := hI E n hn D π hπ φ hφ
  obtain ⟨s2, s3, -⟩ := s1 _ u ht hu
  have ty := hC E n D K W _ u φ.1 k2 w1 ht hl hu s0.1
  obtain ⟨φ', m, e⟩ := hY E n hn D π hπ K W k1 k2 w1 w2 _ s2 s3 ty
  refine ⟨φ', y3 φ' m ?_, fun x => congrFun e x⟩
  rw [← e] at ty
  exact ty
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTensType
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open PositivityTheory.Rg.BcB.CG.prime_not_mem_section_base_place
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem uAt_mul' (v : InfinitePlace E) (k k' : Kinf E n) : uAt v (k * k') = uAt v k * uAt v k' := by
  apply Subtype.ext
  show ((k * k' : Kinf E n) : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) =
    (k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) * (k' : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v)
  rw [← Matrix.map_mul]
  rfl

private theorem coef_mul' (M : Mods E n) (I L : IxA M) (x k : Kinf E n) :
    coef M I L (x * k) = ∑ m : IxA M, coef M I m k * coef M m L x := by
  have h1 : ∀ v, ent (M v) ((M v).ρ (uAt v (x * k)⁻¹)) (I v) (L v) =
      ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) := by
    intro v
    rw [_root_.mul_inv_rev, uAt_mul', map_mul, PMul.ent_mul]
  calc coef M I L (x * k)
      = ∏ v, ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) :=
        Finset.prod_congr rfl fun v _ => h1 v
    _ = ∑ m ∈ Fintype.piFinset fun _ => Finset.univ,
          ∏ v, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) (m v) * ent (M v) ((M v).ρ (uAt v x⁻¹)) (m v) (L v) :=
        Finset.prod_univ_sum _ _
    _ = ∑ m : IxA M, coef M I m k * coef M m L x := by
        simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, coef]

private theorem rinv_Wsp (M : Mods E n) : RInv (Wsp M) := by
  intro f hf k
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨p, rfl⟩ := h
    have e : (fun x => coef M p.1 p.2 (x * k)) = ∑ m : IxA M, coef M p.1 m k • coef M m p.2 := by
      funext x
      simp only [coef_mul', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    show (fun x => coef M p.1 p.2 (x * k)) ∈ Wsp M
    rw [e]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(m, p.2), rfl⟩)
  | zero => exact (Wsp M).zero_mem
  | add a b _ _ ha hb => exact (Wsp M).add_mem ha hb
  | smul c a _ ha => exact (Wsp M).smul_mem c ha

private theorem level_open_compact {b : ℕ} (U : Subgroup (Hf E n b)) (hU : IsOpen (U : Set (Hf E n b))) :
    IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) ∧
      IsCompact ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) := by
  have h1 : IsOpen ((U.comap (MonoidHom.inl _ _) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    hU.preimage (Continuous.prodMk_left 1)
  have h2 : IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    h1.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  exact ⟨h2, (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ h2) Set.inter_subset_right⟩

end SlopeTestRemainingChoices

theorem tensType_pf : TensType := by
  intro E _ _ _ n μa μb _ _ Ma Mb κ ka kb va vb R ψ U ha hb hψ hU hlev i j
  obtain ⟨hKo, hKc⟩ := level_open_compact U hU
  refine ⟨tens_cs ha hb hψ i j, _, Wsp Ma, hKo, hKc, fd_Wsp Ma, rinv_Wsp Ma, fun u hu y => ?_, fun y => ?_⟩
  · have e1 : entA ka i.1.1 j.1.1 (finGL E n u * y.1) = entA ka i.1.1 j.1.1 y.1 := by
      have h := entA_fin ka i.1.1 j.1.1 u⁻¹ y.1
      rwa [map_inv, inv_inv] at h
    have e2 : hFin ((finGL E n u, 1) * y) = ((u, 1) : Hf E n 0) * hFin y := by
      show (gFin (finGL E n u * y.1), gFin (1 * y.2)) = (u * gFin y.1, 1 * gFin y.2)
      rw [map_mul, gFin_finGL, one_mul, one_mul]
    show entA ka i.1.1 j.1.1 (finGL E n u * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
        ψ i.2 j.2 (hFin ((finGL E n u, 1) * y)) = entA ka i.1.1 j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)
    rw [e1, one_mul, e2, hlev i.2 j.2 (u, 1) hu.1 (hFin y)]
  · have e : (fun k : Kinf E n => tens ka kb ψ i j (((kI E n k)⁻¹, 1) * y)) =
        ∑ L : IxA Ma, (entA ka L j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)) • coef Ma i.1.1 L := by
      funext k
      have e2 : hFin (((kI E n k)⁻¹, 1) * y) = hFin y := by
        have h1 : gFin (infGL E n (Unitary.toUnits k)) = 1 := pFin_infGL _
        show (gFin ((infGL E n (Unitary.toUnits k))⁻¹ * y.1), gFin (1 * y.2)) = (gFin y.1, gFin y.2)
        rw [map_mul, map_inv, h1, inv_one, one_mul, one_mul]
      show entA ka i.1.1 j.1.1 ((infGL E n (Unitary.toUnits k))⁻¹ * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
          ψ i.2 j.2 (hFin (((kI E n k)⁻¹, 1) * y)) = _
      rw [entA_inf ha, one_mul, e2, Finset.sum_mul, Finset.sum_mul]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun L _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun L _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i.1.1, L), rfl⟩)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTwTrSum
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

attribute [local instance] borelG borelF borelA borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private lemma trace_range_eq (A : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hA : LinearMap.range A ≤ W) (hW : ∀ x ∈ W, A x ∈ W) :
    LinearMap.trace ℂ (LinearMap.range A) (A.restrict fun x _ => LinearMap.mem_range_self A x) =
      LinearMap.trace ℂ W (A.restrict hW) := by
  have hfd : FiniteDimensional ℂ (LinearMap.range A) :=
    Submodule.finiteDimensional_of_le hA
  let f : W →ₗ[ℂ] LinearMap.range A :=
    (A.comp W.subtype).codRestrict _ fun x => LinearMap.mem_range_self A _
  let g : LinearMap.range A →ₗ[ℂ] W := Submodule.inclusion hA
  have e1 : A.restrict (fun x _ => LinearMap.mem_range_self A x) = f ∘ₗ g := by
    ext x; rfl
  have e2 : A.restrict hW = g ∘ₗ f := by
    ext x; rfl
  rw [e1, e2, LinearMap.trace_comp_comm' f g]

private lemma trace_sum {J : Type*} (s : Finset J) (c : J → ℂ) (L : J → V →ₗ[ℂ] V)
    (h : ∀ j ∈ s, FiniteDimensional ℂ (LinearMap.range (L j))) :
    FiniteDimensional ℂ (LinearMap.range (∑ j ∈ s, c j • L j)) ∧
    LinearMap.trace ℂ (LinearMap.range (∑ j ∈ s, c j • L j))
        ((∑ j ∈ s, c j • L j).restrict fun x _ => LinearMap.mem_range_self _ x) =
      ∑ j ∈ s, c j * LinearMap.trace ℂ (LinearMap.range (L j))
        ((L j).restrict fun x _ => LinearMap.mem_range_self _ x) := by
  classical
  let W : Submodule ℂ V := s.sup fun j => LinearMap.range (L j)
  have hfd : FiniteDimensional ℂ W := by
    refine Finset.sup_induction (p := fun U : Submodule ℂ V => FiniteDimensional ℂ U) ?_ ?_ h
    · exact inferInstanceAs (FiniteDimensional ℂ (⊥ : Submodule ℂ V))
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
  have hle : ∀ j ∈ s, LinearMap.range (L j) ≤ W := fun j hj =>
    Finset.le_sup (f := fun j => LinearMap.range (L j)) hj
  have hS : LinearMap.range (∑ j ∈ s, c j • L j) ≤ W := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.sum_apply]
    exact W.sum_mem fun j hj => W.smul_mem _ (hle j hj (LinearMap.mem_range_self _ x))
  have hj' : ∀ j ∈ s, ∀ x ∈ W, L j x ∈ W := fun j hj x _ => hle j hj (LinearMap.mem_range_self _ x)
  have hSW : ∀ x ∈ W, (∑ j ∈ s, c j • L j) x ∈ W := fun x _ => hS (LinearMap.mem_range_self _ x)
  refine ⟨Submodule.finiteDimensional_of_le hS, ?_⟩
  rw [trace_range_eq _ W hS hSW]
  have e : (∑ j ∈ s, c j • L j).restrict hSW =
      ∑ j ∈ s.attach, c j.1 • (L j.1).restrict (hj' j.1 j.2) := by
    ext x
    simp only [LinearMap.restrict_coe_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    rw [← Finset.sum_attach s]
  rw [e, map_sum, ← Finset.sum_attach s]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, trace_range_eq (L j.1) W (hle j.1 j.2) (hj' j.1 j.2)]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.twTrSum_pf :
    TwTrSum := by
  intro E _ _ _ n D π J s c φ t h
  have hL := fun j (hj : j ∈ s) => (h j hj).2
  choose! L e f ht using hL
  have hT := trace_sum s c L f
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  refine ⟨∑ j ∈ s, c j • L j, fun ψ x => ?_, hT.1, ?_⟩
  · have hc : Continuous fun g : GA E n => ψ.1.1 (thetaA E n g) :=
      (DiscreteGroups.T1.G.twtr_cont_of_mem π ψ.2).comp (PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).1
    have hi : ∀ j ∈ s, Integrable (fun y => φ j y * ψ.1.1 (thetaA E n (x * y.1))) D.μ := fun j hj =>
      DiscreteGroups.T1.G.twtr_integrable D.μ (h j hj).1 hc x
    have hv : ((∑ j ∈ s, c j • L j) ψ).1.1 x = ∑ j ∈ s, c j * (L j ψ).1.1 x := by
      simp [LinearMap.sum_apply]
    rw [hv, Finset.sum_congr rfl fun j hj => by rw [e j hj ψ x]]
    simp_rw [← integral_const_mul]
    rw [← integral_finset_sum _ fun j hj => (hi j hj).const_mul _]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Finset.sum_apply, Finset.sum_mul, mul_assoc]
  · rw [hT.2]
    exact Finset.sum_congr rfl fun j hj => by rw [ht j hj]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PWtInd
section
noncomputable section

open NumberField MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc DiscreteGroups.T1.G
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH borelSpace_H

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem slab_rat {D : Dom E n 0} {f : GA E n → ℂ} (hf : Slab D f) (γ : ratH E n 0) (x : GA E n) :
    f ((γ : H E n 0).1 * x) = f x := by
  obtain ⟨_, γ, rfl⟩ := γ
  exact hf.2.1 γ.1 x

private theorem slab_aS {D : Dom E n 0} {f : GA E n → ℂ} (hf : Slab D f) (x : H E n 0) (s : ℝ) :
    f (x * aS E n s).1 = f x.1 := by
  have h : (x * aS E n s).1 = splitCentre E n s * x.1 := (splitCentre_comm _ _).symm
  rw [h]
  exact hf.2.2.1 s x.1

private theorem cont_pair {a b : GA E n → ℂ} (ha : Continuous a) (hb : Continuous b) {u : ℝ → ℂ} (hu : Continuous u) :
    Continuous fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x) :=
  ((Complex.continuous_conj.comp (ha.comp continuous_fst)).mul (hb.comp continuous_fst)).mul
    (hu.comp continuous_ldet)

private theorem pair_integrable {D : Dom E n 0} {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) {u : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) :
    Integrable (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) D.ν := by
  obtain ⟨χ, h1, -, hχs, -⟩ := exists_continuous_one_zero_of_isCompact (X := ℝ) hs.isCompact isClosed_empty
    (Set.disjoint_empty _)
  have hχ : Continuous fun s => ((χ s : ℝ) : ℂ) := Complex.continuous_ofReal.comp χ.continuous
  have hχc : HasCompactSupport fun s => ((χ s : ℝ) : ℂ) := hχs.comp_left Complex.ofReal_zero
  have hA : MemLp (fun x : H E n 0 => star (a x.1 * ((χ (ldet x) : ℝ) : ℂ))) 2 D.ν := (ha.2.2.2 _ hχ hχc).star
  have hB := hb.2.2.2 u hu hs
  refine (hA.integrable_mul hB).congr (ae_of_all _ fun x => ?_)
  by_cases h0 : u (ldet x) = 0
  · simp [h0]
  · have : χ (ldet x) = 1 := h1 (subset_tsupport _ h0)
    simp [this, mul_assoc]

private theorem integral_u_shift (u : ℝ → ℂ) (r c : ℝ) (hc : 0 < c) :
    ∫ s : ℝ, u (r + s * c) = (c : ℂ)⁻¹ * ∫ s, u s := by
  have h := integral_affine u r c hc
  have h2 := integral_neg_eq_self (fun s : ℝ => u (r - s * c)) volume
  have e : (fun s : ℝ => u (r - -s * c)) = fun s => u (r + s * c) := by
    funext s
    congr 1
    ring
  simp only [e] at h2
  rw [h2, h, Complex.real_smul, Complex.ofReal_inv]

private theorem pair_wt (hn : 1 ≤ n) {D : Dom E n 0} {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) {u w : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) (hw : Continuous w) (hws : HasCompactSupport w)
    (hw1 : ∫ s, w s = 1) : prW D u a b = (∫ s, u s) * prW D w a b := by
  have hc : 0 < ldet (aS E n 1) := lg_e_pos hn
  have hinv : ∀ (γ : ratH E n 0) x, (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) ((γ : H E n 0) * x) =
      (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) x := fun γ x => by
    show starRingEnd ℂ (a ((γ : H E n 0).1 * x.1)) * b ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x)) = _
    rw [slab_rat ha, slab_rat hb, ldet_rat]
  have h := (avgInt_holds E n hn D _ hinv (cont_pair ha.1 hb.1 hu) (pair_integrable ha hb hu hs) w hw hws hw1).2
  have hin : ∀ x : H E n 0, w (ldet x) * ∫ s : ℝ, starRingEnd ℂ (a (x * aS E n s).1) * b (x * aS E n s).1 * u (ldet (x * aS E n s)) =
      ((ldet (aS E n 1) : ℂ)⁻¹ * ∫ s, u s) * (starRingEnd ℂ (a x.1) * b x.1 * w (ldet x)) := fun x => by
    simp only [slab_aS ha, slab_aS hb, ldet_mul_aS]
    rw [integral_const_mul, integral_u_shift u _ _ hc]
    ring
  simp only [hin] at h
  rw [integral_const_mul] at h
  have hc' : (ldet (aS E n 1) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  show ∫ x, _ ∂D.ν = (∫ s, u s) * ∫ x, _ ∂D.ν
  rw [h, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]

private theorem ldet_shift {g : GA E n} (hg : logAbs g.val.det = 0) (x : H E n 0) :
    ldet (x * ((g, 1) : H E n 0)) = ldet x := by
  have h : ldet (x * ((g, 1) : H E n 0)) = ldet x + logAbs g.val.det := Dcy.logAbs_det_mul' x.1 g
  rw [h, hg, add_zero]

private theorem slab_rt (D : Dom E n 0) {a : GA E n → ℂ} (ha : Slab D a) {g : GA E n} (hg : logAbs g.val.det = 0) :
    Slab D fun x => a (x * g) := by
  have hc : Continuous fun x => a (x * g) := ha.1.comp (continuous_mul_right g)
  refine ⟨hc, fun γ x => ?_, fun t x => ?_, fun u hu hs => ?_⟩
  · show a (_ * x * g) = a (x * g)
    rw [mul_assoc]
    exact ha.2.1 γ _
  · show a (_ * x * g) = a (x * g)
    rw [mul_assoc]
    exact ha.2.2.1 t _
  · have hm := ha.2.2.2 u hu hs
    have hcm : Continuous fun x : H E n 0 => a (x.1 * g) * u (ldet x) :=
      (hc.comp continuous_fst).mul (hu.comp continuous_ldet)
    refine ⟨hcm.aestronglyMeasurable, ?_⟩
    have hsh := lintegral_shift D (fun x : H E n 0 => ‖a x.1 * u (ldet x)‖ₑ ^ (2 : ENNReal).toReal) (fun γ x => by
      show ‖a ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x))‖ₑ ^ _ = _
      rw [slab_rat ha, ldet_rat]) ((g, 1) : H E n 0)
    simp only [ldet_shift hg] at hsh
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    have h2 := hm.2
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ← hsh] at h2
    exact h2

private theorem pair_rt (D : Dom E n 0) {a b : GA E n → ℂ} (ha : Slab D a) (hb : Slab D b) (u : ℝ → ℂ) {g : GA E n}
    (hg : logAbs g.val.det = 0) : prW D u (fun x => a (x * g)) (fun x => b (x * g)) = prW D u a b := by
  have h := integral_shift D (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) (fun γ x => by
    show starRingEnd ℂ (a ((γ : H E n 0).1 * x.1)) * b ((γ : H E n 0).1 * x.1) * u (ldet ((γ : H E n 0) * x)) = _
    rw [slab_rat ha, slab_rat hb, ldet_rat]) ((g, 1) : H E n 0)
  simp only [ldet_shift hg] at h
  exact h

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.wtInd_pf :
    Basic → WtInd := by
  intro _ E _ _ _ n hn D a b ha hb u hu hs
  exact ⟨pair_integrable ha hb hu hs, fun w hw hws hw1 => pair_wt hn ha hb hu hs hw hws hw1,
    fun g hg => ⟨slab_rt D ha hg, pair_rt D ha hb u hg⟩⟩

end
end

