import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import Development.AutomorphicArithmetic.AdelicGluing.Bundle0001
import Development.AutomorphicArithmetic.AdelicGluing.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MeasureConditions.Cnd
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.GaloisTwistCompUOperatorEqUOperatorSmulPlace
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem prj_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H ≃ₗᵢ[ℂ] H) (W W' : Submodule ℂ H) (hW : IsClosed (W : Set H)) (hW' : IsClosed (W' : Set H))
    (hU : ∀ v, U v ∈ W' ↔ v ∈ W) (v : H) : U (prj W v) = prj W' (U v) := by
  have hc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hc' : W'.topologicalClosure = W' := hW'.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ W.topologicalClosure ↔ v ∈ W := fun v => by rw [hc]
  have hm' : ∀ v, v ∈ W'.topologicalClosure ↔ v ∈ W' := fun v => by rw [hc']
  have a1 : prj W v ∈ W := (hm _).1 (Submodule.starProjection_apply_mem _ v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm' _).2 ((hU _).2 a1)) fun u hu => ?_
  have hu' : U.symm u ∈ W := (hU _).1 (by simpa using (hm' _).1 hu)
  have e : u = U (U.symm u) := by simp
  rw [e, ← map_sub, LinearIsometryEquiv.inner_map_map]
  exact Submodule.starProjection_inner_eq_zero v _ ((hm _).2 hu')

private theorem mk_iff {G G' : Type} [Group G] [Group G'] (s : G ≃* G') (J : Subgroup G) (J' : Subgroup G')
    (hJ : ∀ g, g ∈ J ↔ s g ∈ J') (a b : G) :
    (QuotientGroup.mk (s a) : G' ⧸ J') = QuotientGroup.mk (s b) ↔
      (QuotientGroup.mk a : G ⧸ J) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, QuotientGroup.eq, hJ, map_mul, map_inv]

private theorem cosets {G G' : Type} [Group G] [Group G'] (s : G ≃* G') (J : Subgroup G) (J' : Subgroup G')
    (hJ : ∀ g, g ∈ J ↔ s g ∈ J') (x : G)
    (hS : {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → G),
      Function.Injective (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) ∧
      Set.range (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} ∧
      Function.Injective (fun i => (QuotientGroup.mk (s (y i)) : G' ⧸ J')) ∧
      Set.range (fun i => (QuotientGroup.mk (s (y i)) : G' ⧸ J')) =
        {c | ∃ k ∈ J', c = QuotientGroup.mk (k * s x)} := by
  classical
  let S := {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}
  haveI : Fintype S := hS.fintype
  have hout : ∀ c : S, (QuotientGroup.mk (c.1.out) : G ⧸ J) = c.1 := fun c => QuotientGroup.out_eq' c.1
  refine ⟨S, inferInstance, fun c => c.1.out, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    have h' : (QuotientGroup.mk (a.1.out) : G ⧸ J) = QuotientGroup.mk (b.1.out) := h
    rwa [hout, hout] at h'
  · ext c
    constructor
    · rintro ⟨i, rfl⟩
      have : (QuotientGroup.mk (i.1.out) : G ⧸ J) ∈ S := by rw [hout]; exact i.2
      exact this
    · intro hc
      exact ⟨⟨c, hc⟩, hout ⟨c, hc⟩⟩
  · intro a b h
    apply Subtype.ext
    have h' := (mk_iff s J J' hJ _ _).1 h
    rwa [hout, hout] at h'
  · ext c
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk, e⟩ := i.2
      refine ⟨s k, (hJ k).1 hk, ?_⟩
      have h1 : (QuotientGroup.mk (i.1.out) : G ⧸ J) = QuotientGroup.mk (k * x) := (hout i).trans e
      have h2 := (mk_iff s J J' hJ _ _).2 h1
      rw [map_mul] at h2
      exact h2
    · rintro ⟨k, hk, rfl⟩
      have hk0 : s.symm k ∈ J := (hJ _).2 (by simpa using hk)
      have hc : (QuotientGroup.mk (s.symm k * x) : G ⧸ J) ∈ S := ⟨_, hk0, rfl⟩
      refine ⟨⟨_, hc⟩, ?_⟩
      have h2 := (mk_iff s J J' hJ _ _).2 (hout ⟨_, hc⟩)
      rw [map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2

private theorem cosets_eq {G : Type} [Group G] (J : Subgroup G) (a b x : G) (ha : a ∈ J) (hb : b ∈ J) :
    {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * (a * x * b))} =
      {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} := by
  have key : ∀ k : G, (QuotientGroup.mk (k * (a * x * b)) : G ⧸ J) = QuotientGroup.mk (k * a * x) := fun k => by
    rw [QuotientGroup.eq]
    have e : (k * (a * x * b))⁻¹ * (k * a * x) = b⁻¹ := by group
    rw [e]
    exact J.inv_mem hb
  ext c
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * a, J.mul_mem hk ha, key k⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, J.mul_mem hk (J.inv_mem ha), ?_⟩
    rw [key]
    simp

private theorem fixL_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ k ∈ J, rhoL μ w k v = v := by
  unfold fixL
  rw [(UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))).2.1]
  constructor
  · exact fun h k hk => h _ (Subgroup.mem_map_of_mem _ hk)
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

theorem UpperTheory.galoisTwist_comp_uOperator_eq_uOperator_smul_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n →
          ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ (w : Pl E) (ν : Fin n → ℤ),
            θ.U ∘L Uiw μ w ν = Uiw μ (σ • w) ν ∘L θ.U := by
  intro F E _ _ _ _ _ _ σ n hn μ _ θ hθ w ν
  obtain ⟨s, hs1, hs2, hs3⟩ := UpperTheory.exists_galois_transport_localGL_preserving_iwahori F E σ n hn w
  obtain ⟨U, hU, hint, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary E n μ θ
  have hO := GLnLocal.isOpen_iwahori (w.adicCompletion E) n
  have hC := GLnLocal.isCompact_iwahori (w.adicCompletion E) n
  have hO' := GLnLocal.isOpen_iwahori ((σ • w).adicCompletion E) n
  have hC' := GLnLocal.isCompact_iwahori ((σ • w).adicCompletion E) n
  have hrho : ∀ g v, U (rhoL μ w g v) = rhoL μ (σ • w) (s g) (U v) := fun g v => by
    have e := UpperTheory.galTwist_finProj_eq_of_galAd_finEmb_eq F E σ n hn μ θ hθ _ _ (hs1 g)
    show U (rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n (AdelicGLn.localEmbedding w g)) v) =
      rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n (AdelicGLn.localEmbedding (σ • w) (s g))) (U v)
    rw [hint, e]
  have hfx : ∀ v, U v ∈ fixL μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) ↔
      v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n) := fun v => by
    rw [fixL_iff, fixL_iff]
    constructor
    · intro h k hk
      apply U.injective
      rw [hrho]
      exact h _ ((hs2 k).1 hk)
    · intro h k' hk'
      have e : k' = s (s.symm k') := by simp
      rw [e, ← hrho, h _ ((hs2 _).2 (by simpa using hk'))]
  have hP : ∀ v, U (prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n)) v) =
      prj (fixL μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n)) (U v) :=
    prj_map U _ _ (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).1 (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).1 hfx
  obtain ⟨hf, -, hHP, hsum, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w _
    (Cartan.diagPow (w.adicCompletion E) n ν) hO hC
  obtain ⟨-, -, hHP', hsum', -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ (σ • w) _
    (s (Cartan.diagPow (w.adicCompletion E) n ν)) hO' hC'
  obtain ⟨ι, _, y, i1, r1, i2, r2⟩ := cosets s _ _ hs2 _ hf
  have hmain : ∀ v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n),
      U (Hop μ w (GLnLocal.iwahori (w.adicCompletion E) n) (Cartan.diagPow (w.adicCompletion E) n ν) v) =
        Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) (U v) := fun v hv => by
    rw [hsum ι y i1 r1 v hv, hsum' ι (fun i => s (y i)) i2 r2 (U v) ((hfx v).2 hv), map_sum]
    exact Finset.sum_congr rfl fun i _ => hrho _ _
  obtain ⟨a, ha, b, hb, hab⟩ := hs3 ν
  have hH : Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) =
      Uiw μ (σ • w) ν := by
    unfold Uiw Hop
    rw [hab, cosets_eq _ a b _ ha hb]
  rw [← hU, ← hH]
  refine ContinuousLinearMap.ext fun v => ?_
  have e1 := DFunLike.congr_fun hHP v
  have e2 := DFunLike.congr_fun hHP' (U v)
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  have hm : prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n)) v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n) :=
    (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).2.2.1 v
  show U (Hop μ w (GLnLocal.iwahori (w.adicCompletion E) n) (Cartan.diagPow (w.adicCompletion E) n ν) v) =
    Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) (U v)
  rw [← e1, hmain _ hm, hP, e2]
end

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.HeightBoundedOnSupportOfCompactTestFunctions
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open UpperTheory.ConvolutionTheory.GM.TE

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}

private theorem cmp_val (w : PlacesOver E v) (g : GL (Fin n) (CompletionsOver E v)) (i j : Fin n) :
    (UpperTheory.ConvolutionTheory.GM.cmp w g).val i j = g.val i j w := rfl

private theorem cmp_continuous (w : PlacesOver E v) :
    Continuous (UpperTheory.ConvolutionTheory.GM.cmp (n := n) w) := by
  have hv : Continuous fun g : GL (Fin n) (CompletionsOver E v) => (UpperTheory.ConvolutionTheory.GM.cmp w g).val := by
    refine continuous_matrix fun i j => ?_
    simp only [cmp_val]
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hv, ?_⟩
  have : (fun g : GL (Fin n) (CompletionsOver E v) => ((UpperTheory.ConvolutionTheory.GM.cmp w g)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val)
      = (fun g => (UpperTheory.ConvolutionTheory.GM.cmp w g).val) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  exact this ▸ hv.comp continuous_inv

private theorem loc_bd (w : Pl E) {C : Set (GL (Fin n) (w.adicCompletion E))} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ C, locHeight g ≤ B := by
  have hc : Continuous (locHeight : GL (Fin n) (w.adicCompletion E) → ℝ) := by
    unfold locHeight
    refine continuous_const.max (NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun p _ => Continuous.max ?_ ?_)))
    · exact (Units.continuous_val.matrix_elem _ _).nnnorm
    · exact (Units.continuous_coe_inv.matrix_elem _ _).nnnorm
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩

private theorem infAt_finEmb' (w : InfinitePlace E) (x : AdelicGLn.FiniteAdelicGL E n) : infAt w (finEmb E n x) = 1 := by
  show (AdelicGLn.infiniteEquiv E n (AdelicGLn.prodEquiv E n (finEmb E n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

private theorem lies_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

private theorem under_of_lies {w : Pl E} {v : Pl F} (hl : w.asIdeal.LiesOver v.asIdeal) : w.under (𝓞 F) = v := by
  ext1
  exact (hl.over).symm

end

theorem UpperTheory.height_bounded_on_support_of_compact_test_functions :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (S : Finset (Pl F)) (q : Pl F) (κ : Finset (Pl E))
        (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
        (∀ v ∈ S, HasCompactSupport (ψ v)) → (∀ w ∈ κ, HasCompactSupport (h w)) →
        ∃ Yf : ℝ, 1 ≤ Yf ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n, (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) →
          (∀ w ∈ κ, h w (cf w x) ≠ 0) → x ∈ Cnd S q κ → heightOff q (finEmb E n x) ≤ Yf := by
  classical
  intro F E _ _ _ _ _ n S q κ ψ h hψ hh
  have key : ∀ w : Pl E, ∃ M : ℝ, 1 ≤ M ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n,
      (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) → (∀ w ∈ κ, h w (cf w x) ≠ 0) →
      (w ∈ κ ∨ w.under (𝓞 F) ∈ S) → locHeight (cf w x) ≤ M := by
    intro w
    by_cases hk : w ∈ κ
    · obtain ⟨B, hB1, hB⟩ := loc_bd w (hh w hk).isCompact
      exact ⟨B, hB1, fun x _ h2 _ => hB _ (subset_tsupport _ (Function.mem_support.2 (h2 w hk)))⟩
    · by_cases hs : w.under (𝓞 F) ∈ S
      · have hc := (hψ _ hs).isCompact.image (cmp_continuous (n := n) (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F))))
        obtain ⟨B, hB1, hB⟩ := loc_bd w hc
        refine ⟨B, hB1, fun x h1 _ _ => ?_⟩
        have e : UpperTheory.ConvolutionTheory.GM.cmp (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F)))
            (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) = cf w x := by
          ext i j
          rfl
        rw [← e]
        exact hB _ ⟨_, subset_tsupport _ (Function.mem_support.2 (h1 _ hs)), rfl⟩
      · exact ⟨1, le_rfl, fun x _ _ hd => absurd hd (by simp [hk, hs])⟩
  choose M hM1 hM using key
  let W : Finset (Pl E) := κ ∪ S.biUnion fun v => (Finset.univ : Finset (PlacesOver E v)).image Subtype.val
  have hW : ∀ w, w ∈ W ↔ (w ∈ κ ∨ w.under (𝓞 F) ∈ S) := by
    intro w
    simp only [W, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    refine or_congr Iff.rfl ⟨?_, fun hs => ⟨_, hs, ⟨w, lies_under w⟩, rfl⟩⟩
    rintro ⟨v, hv, p, rfl⟩
    rwa [under_of_lies p.2]
  refine ⟨∏ w ∈ W, M w, Finset.prod_induction _ (fun y : ℝ => 1 ≤ y)
    (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun w _ => hM1 w, ?_⟩
  intro x h1 h2 hx
  unfold heightOff
  have hi : (∏ w : InfinitePlace E, locHeight (infAt w (finEmb E n x)) ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [infAt_finEmb', locHeight_one, one_pow]
  rw [hi, one_mul]
  have hg : ∀ w : Pl E, (∏ᶠ (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w (finEmb E n x))) =
      if w.under (𝓞 F) ≠ q then locHeight (cf w x) else 1 := by
    intro w
    rw [finprod_eq_if]
    rfl
  simp only [hg]
  rw [finprod_eq_prod_of_mulSupport_subset (s := W)]
  · refine Finset.prod_le_prod (fun w _ => ?_) fun w hw => ?_
    · split_ifs
      · exact (locHeight_pos _).le
      · exact zero_le_one
    · split_ifs with hq
      · exact hM w x h1 h2 ((hW w).1 hw)
      · exact hM1 w
  · intro w hw
    by_contra hc
    apply hw
    have hc' : w ∉ W := hc
    rw [hW, not_or] at hc'
    by_cases hq : w.under (𝓞 F) = q
    · simp [hq]
    · simp only [ne_eq, hq, not_false_eq_true, if_true]
      exact locHeight_eq_one_of_mem_integralGL (hx w hc'.1 hc'.2 hq)
end

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.OfinDoubleCosetIndicatorEqHop
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem out_mem_iff {G : Type*} [Group G] (J : Subgroup G) (y : G) (c : G ⧸ J) :
    c.out ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} ↔ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)} := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, ?_⟩
    rw [← QuotientGroup.out_eq' c, e]
    exact QuotientGroup.eq.2 (by simpa [mul_assoc] using J.inv_mem hb)
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J (k * y)
    exact ⟨k, hk, j, j.2, hj⟩

private theorem dc_support {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G) (y : G)
    (hc : IsCompact (J : Set G)) :
    HasCompactSupport ({g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ)) := by
  have hDc : IsCompact {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} := by
    have : {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} = (fun p : G × G => p.1 * y * p.2) ''
        ((J : Set G) ×ˢ (J : Set G)) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists]
      exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, b, ⟨ha, hb⟩, e.symm⟩, fun ⟨a, b, ⟨ha, hb⟩, e⟩ => ⟨a, ha, b, hb, e.symm⟩⟩
    rw [this]
    exact (hc.prod hc).image (by fun_prop)
  exact HasCompactSupport.intro hDc fun x hx => Set.indicator_of_notMem hx _

private theorem dc_inv {G : Type*} [Group G] (J : Subgroup G) (y : G) :
    ∀ k ∈ J, ∀ x, {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ) (x * k) =
      {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator 1 x := by
  have hmem : ∀ k ∈ J, ∀ x, x * k ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} ↔
      x ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} := by
    intro k hk x
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * k⁻¹, J.mul_mem hb (J.inv_mem hk), by rw [← mul_assoc, ← e]; simp⟩
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * k, J.mul_mem hb hk, by rw [e]; simp [mul_assoc]⟩
  intro k hk x
  by_cases hx : x ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem k hk x).2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun q => hx ((hmem k hk x).1 q)]

private theorem dc_sum {G E : Type*} [Group G] [AddCommMonoid E] [Module ℂ E] (J : Subgroup G) (y : G) (ρ : G → E) :
    (∑ᶠ c : G ⧸ J, {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ) c.out • ρ c.out) =
      ∑ᶠ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)}, ρ c.out := by
  rw [finsum_mem_def]
  refine finsum_congr fun c => ?_
  by_cases hcC : c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)}
  · rw [Set.indicator_of_mem hcC, Set.indicator_of_mem ((out_mem_iff J y c).2 hcC)]
    simp
  · rw [Set.indicator_of_notMem hcC, Set.indicator_of_notMem fun q => hcC ((out_mem_iff J y c).1 q)]
    simp

theorem UpperTheory.Ofin_doubleCoset_indicator_eq_Hop :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
      (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (y : GL (Fin n) (w.adicCompletion K)),
      IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
      ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w r → ∀ e₀ e₁ : TF K n,
        (∀ x, e₀ x = r x * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator 1 (cf w x)) →
        (∀ x, e₁ x = r x * {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator 1 (cf w x)) →
        Ofin μ m e₁ = Hop μ w J y ∘L Ofin μ m e₀ := by
  intro K _ _ n hn μ _ m _ w J y ho hc r hr e₀ e₁ h0 h1
  obtain ⟨hfix, heq⟩ := UpperTheory.ConvolutionTheory.GM.stepFin K n hn μ m w J ho _ (dc_support J y hc) (dc_inv J y) r hr e₀ e₁ h0 h1
  refine ContinuousLinearMap.ext fun u => ?_
  rw [heq, dc_sum J y (rhoL μ w)]
  have hp : prj (fixL μ w J) (Ofin μ m e₀ u) = Ofin μ m e₀ u :=
    (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))).2.2.2.1 _ (hfix u)
  simp only [Hop, ContinuousLinearMap.comp_apply, hp]
end

