import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEval
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.ColEval

theorem word_succ {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) {t : ℕ} (u : Fin (t + 1) → Fin N → K) :
    word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem mul_eq_sum {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (v : Fin N → K) :
    mul v = ∑ k, v k • mul (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
  [IsScalarTower (𝓞 F) F A] {S : Sys F A} {E A' : Type} [Field E] [Algebra F E] [AddCommGroup A'] [Module E A']
  {s : Fin S.D → Fin S.N → E} {δ : ℕ}

theorem mul_single_ι (Φ : S.Flat E A' s δ) (k : Fin S.N) (y : A) :
    Φ.mul (Pi.single k 1) (Φ.ι y) = Φ.ι (S.mul (Pi.single k 1) y) := by
  rw [← Φ.mul_ι]
  congr 2
  ext j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem word_ι_expand (Φ : S.Flat E A' s δ) : ∀ (t : ℕ) (U : Fin t → Fin S.N → E) (z : A),
    word Φ.mul U (Φ.ι z) =
      ∑ e : Fin t → Fin S.N, (∏ q, U q (e q)) • Φ.ι (word S.mul (fun q => Pi.single (e q) (1 : F)) z)
  | 0, U, z => by simp [word]
  | t + 1, U, z => by
    rw [word_succ, Module.End.mul_apply, word_ι_expand Φ t, map_sum]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => Fin S.N).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, word_succ,
      Module.End.mul_apply, map_smul, mul_eq_sum Φ.mul (U 0), LinearMap.sum_apply, LinearMap.smul_apply,
      mul_single_ι, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm]

end GlobalTheory.HSShort.ColEval

namespace GlobalTheory.HSShort.ColEval

theorem columns_eval : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ c' : Fin d → A' →ₗ[E] E, (∀ x ∈ Submodule.span E (Φ.ι '' S.V S.T), ∑ i, c' i x • Φ.ι (b i) = x) ∧ ∀ (κ : S.Col) (u : Fin (S.D + 1) × Fin S.N → E), word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x) ∈ Submodule.span E (Φ.ι '' S.V S.T) ∧ ∀ i, aeval u (coordP S.mul (c i) κ.β (κ.x : A)) = c' i (word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x)) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc
  set W := Submodule.span E (Φ.ι '' (S.V S.T : Set A)) with hW
  have hli : LinearIndependent E (fun i => Φ.ι (b i)) := Φ.indep d b b.linearIndependent
  have hιV : ∀ (y : A) (hy : y ∈ S.V S.T), Φ.ι y = ∑ i, algebraMap F E (b.repr ⟨y, hy⟩ i) • Φ.ι (b i) := by
    intro y hy
    conv_lhs => rw [show y = ((⟨y, hy⟩ : S.V S.T) : A) from rfl, ← b.sum_repr ⟨y, hy⟩]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ]
  have hWspan : W = Submodule.span E (Set.range fun i => Φ.ι (b i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [hιV y hy]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.linearEquivFunOnFinite E E (Fin d)).toLinearMap ∘ₗ (hli.repr ∘ₗ Submodule.inclusion (le_of_eq hWspan)))
  have h1 : ∀ x ∈ W, ∑ i, g x i • Φ.ι (b i) = x := by
    intro x hx
    have hx' : x ∈ Submodule.span E (Set.range fun i => Φ.ι (b i)) := hWspan ▸ hx
    have e1 := LinearMap.congr_fun hg ⟨x, hx⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at e1
    rw [e1, show Submodule.inclusion (le_of_eq hWspan) ⟨x, hx⟩ = ⟨x, hx'⟩ from rfl]
    have e2 := hli.linearCombination_repr ⟨x, hx'⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e2
    simpa using e2
  have h2 : ∀ x ∈ W, ∀ a : Fin d → E, ∑ i, a i • Φ.ι (b i) = x → ∀ i, g x i = a i := by
    intro x hx a ha
    have h0 : ∑ i, (g x i - a i) • Φ.ι (b i) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1 x hx, ha, sub_self]
    intro i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  have h3 : ∀ (y : A) (hy : y ∈ S.V S.T) i, g (Φ.ι y) i = algebraMap F E (c i y) := by
    intro y hy i
    rw [h2 _ (Submodule.subset_span ⟨y, hy, rfl⟩) _ (hιV y hy).symm i]
    congr 1
    exact (hc i ⟨y, hy⟩).symm
  refine ⟨fun i => LinearMap.proj i ∘ₗ g, fun x hx => h1 x hx, fun κ u => ?_⟩
  have hmem : ∀ e : Fin κ.t → Fin S.N, word S.mul (fun q => Pi.single (e q) (1 : F)) (κ.x : A) ∈ S.V S.T := by
    intro e
    have := (GlobalTheory.HSShort.wordMem F A S hS κ.j κ.t (by rw [κ.add])).1 (fun q => Pi.single (e q) (1 : F)) κ.x κ.x.2
    rwa [κ.add] at this
  rw [word_ι_expand Φ κ.t]
  refine ⟨Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem e, rfl⟩), fun i => ?_⟩
  simp only [coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.map_smul, LinearMap.coe_proj, Function.eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [h3 _ (hmem e) i, mul_comm]

end GlobalTheory.HSShort.ColEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSystemSlopeBoundOfDeterminantSlopeInequStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSystemSlopeBound_of_determinantSlopeInequality : ∀ (T D : ℕ) (n Λ β Λ₀ ΛD ΛT δ h h' d deg : ℝ), 1 ≤ D → D + 1 ≤ T → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ δ → h - (Real.log n + 1) / 2 ≤ h' → ClaimS T D n Λ β Λ₀ ΛD ΛT δ h' d deg → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT (Real.log Λ₀) δ h d deg := by
  first | exact @GlobalTheory.HSShortNum.claimS_to_hsClaimS | exact GlobalTheory.HSShortNum.claimS_to_hsClaimS | (intros; apply GlobalTheory.HSShortNum.claimS_to_hsClaimS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameUnipotentLeFlagUnipotentStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWittFrame_unipotent_le_flag_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d := by
  first | exact @GlobalTheory.TieStd.unip_le_unipFlag | exact GlobalTheory.TieStd.unip_le_unipFlag | (intros; apply GlobalTheory.TieStd.unip_le_unipFlag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyBoundTwistNegOfRegularSection
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem higherCohomology_bound_twist_neg_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (B : LB X) (hB : B.IsLB) (s : B.Sec), Mono (cutHom F hB s) → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twistZ F B (-1)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL ih F _ hF B hB s hs hb i hi
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hX
  have hcut : suppDim (cut F hB s) ≤ (d : ℕ) := suppDim_cut_le F hB s hF
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 : ∃ C : ℕ, ∀ m : ℕ,
      hdim k (twist (cut F hB s) (lbPow L m)) j ≤ C * ((d + 1) * (m + 1) ^ d) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain ⟨C, hC⟩ := GlobalTheory.T.global_sections_polynomial_growth k X hX d L hL (cut F hB s) hcut
      exact ⟨C, fun m => (hC m).trans
        (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos d)))⟩
    · obtain ⟨C, hC⟩ := ih (cut F hB s) hcut j hj
      exact ⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.le_succ d)
        (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))))⟩
  obtain ⟨C₁, hC₁⟩ := h1
  obtain ⟨C₂, hC₂⟩ := hb (j + 1) hi
  refine ⟨C₁ + C₂, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  have hB' := Twist.isLB_lbZPow hB (-1)
  obtain ⟨M', hM', e'⟩ := cls_surj (cls _ hB' + cls _ hM)
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq F hB' hM hM' e'
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B (lbPow L m) M' hB hM hM' s hs (by
    rw [e', cls_lbZPow hB]; simp)).2.1 j
  have e2 : hdim k (twist (twistZ F B (-1)) (lbPow L m)) (j + 1) = hdim k (twist F M') (j + 1) :=
    hdim_congr k _ e
  rw [e2, add_mul]
  exact key.trans (Nat.add_le_add (hC₁ m) (hC₂ m))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelLatticeSystemHyp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.SysHyp

variable {F : Type} [Field F] [NumberField F]

theorem mulW_comm (G : Geo F) (j : ℕ) (u v : Fin G.N → F) (m : G.Sec j) :
    G.mulW (j + 1) u (G.mulW j v m) = G.mulW (j + 1) v (G.mulW j u m) := by
  simp only [Geo.mulW_apply]
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun i c y hy hi hc => ?_
  rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hc, germ_mulSec _ _ _ _ _ _ _ _ _ hi hc,
    germ_mulSec _ _ _ _ _ _ _ _ _ hi hc, germ_mulSec _ _ _ _ _ _ _ _ _ hi hc]
  exact mul_left_comm _ _ _

theorem shift_comm (G : Geo F) (u v : Fin G.N → F) : shift G u * shift G v = shift G v * shift G u := by
  refine LinearMap.ext fun x => funext fun j => ?_
  rcases j with _ | _ | j
  · rfl
  · change G.mulW 0 u 0 = G.mulW 0 v 0
    rw [map_zero, map_zero]
  · exact mulW_comm G j u v (x j)

theorem shift_single (G : Geo F) (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext l
  rcases l with _ | l
  · rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j).symm]
    rfl
  · change G.mulW l u ((Pi.single j m : Tot G) l) = _
    by_cases h : l = j
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun e => h (Nat.succ_injective e)), map_zero]

variable (X : Data F)

theorem coe_inclEquiv (j : ℕ) (x : X.V j) :
    (inclEquiv X j x : Tot X.toGeo) = Pi.single j (x : X.Sec j) := rfl

theorem coe_eq_single (j : ℕ) (x : LinearMap.range (incl X j)) :
    (x : Tot X.toGeo) = Pi.single j ((inclEquiv X j).symm x : X.Sec j) := by
  rw [← coe_inclEquiv, LinearEquiv.apply_symm_apply]

theorem isFull (Λ₀ : ℝ) (j : ℕ) : IsFull ((sysOf X Λ₀).M j) := by
  refine ⟨(X.full j).fg.map _, ?_⟩
  change Submodule.span F ((inclEquiv X j).toLinearMap '' (X.M j : Set (X.V j))) = ⊤
  rw [← Submodule.map_span, (X.full j).span, Submodule.map_top, LinearEquiv.range]

theorem short (Λ₀ : ℝ) {j : ℕ} {Λ : ℝ} (h : X.ShortFamily j Λ) : (sysOf X Λ₀).Short j Λ := by
  obtain ⟨v, hm, hi, hn⟩ := h
  have hs : ⊤ ≤ Submodule.span F (Set.range v) :=
    (hi.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, X.latRank_M])).ge
  refine ⟨_, (Module.Basis.mk hi hs).map (inclEquiv X j), fun i => ?_⟩
  have e : (Module.Basis.mk hi hs).map (inclEquiv X j) i = inclEquiv X j (v i) := by
    rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  refine e ▸ ⟨⟨v i, hm i, rfl⟩, fun σ => ?_⟩
  change (X.nm j).nrm σ ((inclEquiv X j).symm (inclEquiv X j (v i))) ≤ Λ
  rw [LinearEquiv.symm_apply_apply]
  exact hn i σ

end GlobalTheory.HSShort.SysHyp

namespace GlobalTheory.HSShort

open SysHyp

theorem GeoHyp.sysOf_hyp : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ),
    GeoHyp X Λ₀ → (sysOf X Λ₀).Hyp := by
  intro F _ _ X Λ₀ h
  have := h.totallyComplex
  refine ⟨X.geom.alg.variety.one_le, X.le_T, ⟨?_, X.geom.alg.spans, X.herm, fun k σ => h.normsLe k σ, h.one_le_Lam⟩,
    shift_comm X.toGeo, fun j _ => isFull X Λ₀ j, ?_, ?_, X.one_le_beta, h.hermSysHyp_one_le_lambdaZero, X.one_le_LamD, X.one_le_LamT,
    short X Λ₀ h.short0, short X Λ₀ h.shortD, short X Λ₀ h.shortT⟩
  · obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (X.geom.alg.bpf.ge (Set.mem_univ (genericPoint X.Y)))
    exact j.pos
  · rintro j hj k _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, e⟩ := h.mulStable j hj (X.w.col k) (Submodule.subset_span ⟨k, rfl⟩) f hf
    refine ⟨inclEquiv X (j + 1) g, ⟨g, hg, rfl⟩, ?_⟩
    exact ((shift_single X.toGeo j _ f).trans (congrArg (Pi.single (M := fun l => X.Sec l) (j + 1)) e.symm)).symm
  · intro σ j hj u m c f g e
    refine h.mulBound.mulBoundAt σ j hj u m c (fun i => (inclEquiv X j).symm (f i))
      (fun t => (inclEquiv X (j + 1)).symm (g t)) fun k i => ?_
    have e₁ := (coe_eq_single X (j + 1) (g (k, i))).symm.trans ((e k i).trans
      ((congrArg (shift X.toGeo (Pi.single k 1)) (coe_eq_single X j (f i))).trans (shift_single X.toGeo j _ _)))
    exact Pi.single_injective (M := fun l => X.Sec l) (j + 1) e₁

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionBaseChangeProperties
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort

section Lemmas

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem shift_apply_zero (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

theorem shift_apply_succ (u : Fin G.N → F) (x : Tot G) (j : ℕ) : shift G u x (j + 1) = G.mulW j u (x j) := rfl

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem totExt_apply (x : Tot G) (j : ℕ) : totExt G E x j = G.toExt E j (x j) := rfl

theorem totExt_single (j : ℕ) (s : G.Sec j) :
    totExt G E (Pi.single j s) = Pi.single j (G.toExt E j s) := by
  funext k
  rw [totExt_apply]
  by_cases h : k = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem shift_totExt (u : Fin G.N → F) (x : Tot G) :
    shift (G.baseChange E) (fun k => algebraMap F E (u k)) (totExt G E x) = totExt G E (shift G u x) := by
  funext j
  cases j with
  | zero => rw [shift_apply_zero, totExt_apply, shift_apply_zero, map_zero]
  | succ j =>
    rw [shift_apply_succ, totExt_apply, totExt_apply, shift_apply_succ, Geo.toExt_mulW]
    rfl

end Lemmas

theorem totExt_props : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) (E : Type) [Field E] [NumberField E] [Algebra F E], (∀ (m : ℕ) (v : Fin m → (sysOf X Λ₀).V X.T), LinearIndependent F v → LinearIndependent E fun i => totExt X.toGeo E (v i)) ∧ (∀ u x, shift (X.toGeo.baseChange E) (fun k => algebraMap F E (u k)) (totExt X.toGeo E x) = totExt X.toGeo E (shift X.toGeo u x)) ∧ ∀ j, Submodule.span E (totExt X.toGeo E '' (sysOf X Λ₀).V j) = LinearMap.range (incl (X.baseChange E) j) := by
  intro F _ _ X Λ₀ E _ _ _
  refine ⟨?_, fun u x => shift_totExt X.toGeo E u x, ?_⟩
  · intro m v hv
    have hv' := hv.map' ((sysOf X Λ₀).V X.T).subtype (Submodule.ker_subtype _)
    have hform : ∀ i, ∃ y : X.toGeo.Sec X.T, (v i : Tot X.toGeo) = Pi.single X.T y := by
      intro i
      obtain ⟨y, hy⟩ := (v i).2
      exact ⟨y, hy.symm⟩
    choose f hf using hform
    have h1 : LinearIndependent F (LinearMap.single F (fun k => X.toGeo.Sec k) X.T ∘ f) := by
      have e : (LinearMap.single F (fun k => X.toGeo.Sec k) X.T ∘ f) = ((sysOf X Λ₀).V X.T).subtype ∘ v :=
        funext fun i => (hf i).symm
      rw [e]
      exact hv'
    have h2 := X.toGeo.linearIndependent_toExt E X.T m f h1.of_comp
    have h3 := h2.map' (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) X.T)
      (LinearMap.ker_eq_bot.2 (Pi.single_injective _))
    have e2 : (fun i => totExt X.toGeo E (v i)) =
        (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) X.T ∘ fun i => X.toGeo.toExt E X.T (f i)) := by
      funext i
      rw [hf i, totExt_single]
      rfl
    rw [e2]
    exact h3
  · intro j
    have hset : (totExt X.toGeo E '' ((sysOf X Λ₀).V j : Set (Tot X.toGeo))) =
        (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) j) ''
          (X.toGeo.toExt E j '' (X.V j : Set (X.toGeo.Sec j))) := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨_, ⟨y, y.2, rfl⟩, (totExt_single X.toGeo E j y).symm⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, totExt_single X.toGeo E j y⟩
    rw [hset, ← Submodule.map_span]
    refine Eq.trans ?_ (LinearMap.range_comp ((X.baseChange E).V j).subtype (LinearMap.single E _ j)).symm
    rw [Submodule.range_subtype]
    rfl

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEqStatement
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicFrameTorusElement_matrix_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  first | exact @GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt | exact GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt | (intros; apply GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleOfCharPoly
section
open Matrix GlobalTheory.TorFin

theorem GlobalTheory.isIntMod_of_monic_dvd_affine : ∀ (A : Type) [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H : A),
    (∀ i ∈ I, H * i ∈ I) → ∀ (N : ℕ) (c q : ℕ → A), c N = 1 → (∀ k ≤ N, c k ∈ Z) →
    (∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • c k - (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k ∈ I) →
    IsIntMod Z I H := by
  intro A _ _ Z I H hH N c q hcN hcZ hI
  classical
  let q' : ℕ → A := fun k => if k < N then q k else 0
  let e : ℕ → A := fun k => (if k = 0 then 0 else q' (k - 1)) + H * q' k
  have hE : ∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • e k =
      (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k := by
    intro u
    have h1 : ∑ k ∈ Finset.range (N + 1), u ^ k • (if k = 0 then 0 else q' (k - 1)) =
        ∑ k ∈ Finset.range N, u ^ (k + 1) • q k := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, smul_zero, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      exact Finset.sum_congr rfl fun k hk => by simp [q', Finset.mem_range.1 hk]
    have h2 : ∑ k ∈ Finset.range (N + 1), u ^ k • (H * q' k) = ∑ k ∈ Finset.range N, u ^ k • (H * q k) := by
      rw [Finset.sum_range_succ]
      simp only [q', lt_irrefl, if_false, mul_zero, smul_zero, add_zero]
      exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
    simp only [e, smul_add, Finset.sum_add_distrib]
    rw [h1, h2, add_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by rw [smul_mul_assoc, one_mul, smul_smul, pow_succ']
    · exact Finset.sum_congr rfl fun k _ => (mul_smul_comm _ _ _).symm
  have hT : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * e k = 0 := by
    have h1 : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (if k = 0 then 0 else q' (k - 1)) =
        ∑ k ∈ Finset.range N, (-H) ^ (k + 1) * q k := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, mul_zero, add_zero, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      exact Finset.sum_congr rfl fun k hk => by simp [q', Finset.mem_range.1 hk]
    have h2 : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (H * q' k) = ∑ k ∈ Finset.range N, (-H) ^ k * (H * q k) := by
      rw [Finset.sum_range_succ]
      simp only [q', lt_irrefl, if_false, mul_zero, add_zero]
      exact Finset.sum_congr rfl fun k hk => by simp [Finset.mem_range.1 hk]
    simp only [e, mul_add, Finset.sum_add_distrib]
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pow_succ, mul_assoc, ← mul_add, neg_mul, neg_add_cancel, mul_zero]
  have hd : ∀ k < N + 1, c k - e k ∈ I := GlobalTheory.T.coeff_mem_submodule_of_complex_poly_values_mem A I (N + 1) (fun k => c k - e k) fun u => by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hE]
    exact hI u
  have hpow : ∀ k, ∀ i ∈ I, (-H) ^ k * i ∈ I := by
    intro k
    induction k with
    | zero => intro i hi; simpa using hi
    | succ k ih => intro i hi; rw [pow_succ', mul_assoc, neg_mul]; exact I.neg_mem (hH _ (ih i hi))
  have hcI : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k ∈ I := by
    have : ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k = ∑ k ∈ Finset.range (N + 1), (-H) ^ k * (c k - e k) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hT, sub_zero]
    rw [this]
    exact I.sum_mem fun k hk => hpow k _ (hd k (Finset.mem_range.1 hk))
  refine ⟨N, ?_⟩
  set S := Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z} with hS
  have hterm : ∀ k < N, (-H) ^ k * c k ∈ S := by
    intro k hk
    have hm : H ^ k * c k ∈ S := Submodule.subset_span ⟨k, hk, c k, hcZ k hk.le, rfl⟩
    rw [neg_pow]
    rcases neg_one_pow_eq_or A k with h | h <;> rw [h]
    · simpa using hm
    · rw [neg_one_mul, neg_mul]; exact S.neg_mem hm
  have hN : (-H) ^ N ∈ I ⊔ S := by
    have : (-H) ^ N = ∑ k ∈ Finset.range (N + 1), (-H) ^ k * c k - ∑ k ∈ Finset.range N, (-H) ^ k * c k := by
      rw [Finset.sum_range_succ, hcN, mul_one, add_sub_cancel_left]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hcI)
      (Submodule.mem_sup_right (S.sum_mem fun k hk => hterm k (Finset.mem_range.1 hk)))
  rw [neg_pow] at hN
  rcases neg_one_pow_eq_or A N with h | h <;> rw [h] at hN
  · simpa using hN
  · rw [neg_one_mul] at hN; simpa using (I ⊔ S).neg_mem hN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreduciblePencilLinePolynomialGenericLineStatement
section
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line : ∀ (F : Type) [Field F] (D N : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), Irreducible f → Irreducible (GlobalTheory.PencilDisc.line (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F)) (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  first | exact @GlobalTheory.PencilDisc.irreducible_line_generic | exact GlobalTheory.PencilDisc.irreducible_line_generic | (intros; apply GlobalTheory.PencilDisc.irreducible_line_generic <;> assumption)
end

