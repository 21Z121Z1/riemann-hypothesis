import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionLocalUnits
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.LocalUnit

variable {F : Type} [Field F] [NumberField F] {d β : F}

open Classical in

theorem proj_sum_inc (T : Finset (Pl F)) (c : (u : Pl F) → Kp u) (u : Pl F) :
    proj u (∑ t ∈ T, inc t (c t)) = if u ∈ T then c u else 0 := by
  rw [map_sum]
  by_cases h : u ∈ T
  · rw [if_pos h, Finset.sum_eq_single_of_mem u h]
    · exact proj_inc_same u _
    · intro b _ hb
      exact proj_inc_ne (Ne.symm hb) _
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun t ht => proj_inc_ne (fun e : u = t => h (by rwa [e])) _

theorem q_ext {a b : Q d β (AF F)} (h : ∀ u : Pl F, qmap (proj u) a = qmap (proj u) b) : a = b := by
  ext
  · exact adele_ext fun u => congrArg QuaternionAlgebra.re (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imI (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imJ (h u)
  · exact adele_ext fun u => congrArg QuaternionAlgebra.imK (h u)

def glue (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) : Q d β (AF F) :=
  ⟨1 + ∑ t ∈ T, inc t ((y t).re - 1), ∑ t ∈ T, inc t (y t).imI, ∑ t ∈ T, inc t (y t).imJ,
    ∑ t ∈ T, inc t (y t).imK⟩

theorem qmap_glue_mem (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) {u : Pl F} (h : u ∈ T) :
    qmap (proj u) (glue T y) = y u := by
  classical
  ext
  · change proj u (1 + ∑ t ∈ T, inc t ((y t).re - 1)) = (y u).re
    rw [map_add, map_one, proj_sum_inc T (fun t => (y t).re - 1) u, if_pos h]
    ring
  · change proj u (∑ t ∈ T, inc t (y t).imI) = (y u).imI
    rw [proj_sum_inc T (fun t => (y t).imI) u, if_pos h]
  · change proj u (∑ t ∈ T, inc t (y t).imJ) = (y u).imJ
    rw [proj_sum_inc T (fun t => (y t).imJ) u, if_pos h]
  · change proj u (∑ t ∈ T, inc t (y t).imK) = (y u).imK
    rw [proj_sum_inc T (fun t => (y t).imK) u, if_pos h]

theorem qmap_glue_not_mem (T : Finset (Pl F)) (y : (u : Pl F) → Q d β (Kp u)) {u : Pl F}
    (h : u ∉ T) : qmap (proj u) (glue T y) = 1 := by
  classical
  ext
  · change proj u (1 + ∑ t ∈ T, inc t ((y t).re - 1)) = 1
    rw [map_add, map_one, proj_sum_inc T (fun t => (y t).re - 1) u, if_neg h, add_zero]
  · change proj u (∑ t ∈ T, inc t (y t).imI) = 0
    rw [proj_sum_inc T (fun t => (y t).imI) u, if_neg h]
  · change proj u (∑ t ∈ T, inc t (y t).imJ) = 0
    rw [proj_sum_inc T (fun t => (y t).imJ) u, if_neg h]
  · change proj u (∑ t ∈ T, inc t (y t).imK) = 0
    rw [proj_sum_inc T (fun t => (y t).imK) u, if_neg h]

theorem exists_adelic_unit : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (T : Finset (Pl F))
    (y : (u : Pl F) → (Q d β (Kp u))ˣ),
    ∃ Y : (Q d β (AF F))ˣ, (∀ u ∈ T, qmap (proj u) (Y : Q d β (AF F)) = y u) ∧
      ∀ u, u ∉ T → qmap (proj u) (Y : Q d β (AF F)) = 1 := by
  intro F _ _ d β T y
  classical
  have hl : glue T (fun u => ((y u : (Q d β (Kp u))ˣ) : Q d β (Kp u))) *
      glue T (fun u => (((y u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u))) = 1 := by
    refine q_ext fun u => ?_
    rw [map_mul, map_one]
    by_cases h : u ∈ T
    · rw [qmap_glue_mem T _ h, qmap_glue_mem T _ h]
      exact (y u).mul_inv
    · rw [qmap_glue_not_mem T _ h, qmap_glue_not_mem T _ h, one_mul]
  have hr : glue T (fun u => (((y u)⁻¹ : (Q d β (Kp u))ˣ) : Q d β (Kp u))) *
      glue T (fun u => ((y u : (Q d β (Kp u))ˣ) : Q d β (Kp u))) = 1 := by
    refine q_ext fun u => ?_
    rw [map_mul, map_one]
    by_cases h : u ∈ T
    · rw [qmap_glue_mem T _ h, qmap_glue_mem T _ h]
      exact (y u).inv_mul
    · rw [qmap_glue_not_mem T _ h, qmap_glue_not_mem T _ h, one_mul]
  exact ⟨⟨_, _, hl, hr⟩, fun u h => qmap_glue_mem T _ h, fun u h => qmap_glue_not_mem T _ h⟩

end GlobalTheory.CompanionTheory.PlaneSA.LocalUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicQuaternionNeighbourhood
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.Box

variable {F : Type} [Field F] [NumberField F]

theorem af_box (x : Af F) (W : Set (Af F)) (hW : W ∈ 𝓝 x) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ U : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F),
      (∀ v, U v ∈ 𝓝 (x v)) ∧
      (∀ v, v ∉ S → U v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∧
      ∀ y : Af F, (∀ v ∈ S, y v ∈ U v) →
        (∀ v, v ∉ S → y v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) → y ∈ W := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hAo : ∀ v, IsOpen (A v) := fun v => Valued.isOpen_valuationSubring _
  have hx : Set.Finite {v | x v ∉ A v} := x.2
  let S0 : Finset (HeightOneSpectrum (𝓞 F)) := hx.toFinset
  have hS0 : ∀ v, v ∉ S0 → x v ∈ A v := by
    intro v hv
    by_contra h
    exact hv (by simpa [S0] using h)
  have hS : Filter.cofinite ≤ Filter.principal ((S0 : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact S0.finite_toSet
  have hemb := RestrictedProduct.isOpenEmbedding_inclusion_principal (R := R) hAo hS
  have hr : ∀ y : Af F, (∀ v, v ∉ S0 → y v ∈ A v) →
      y ∈ Set.range (RestrictedProduct.inclusion R A hS) := by
    intro y hy
    rw [RestrictedProduct.range_inclusion]
    exact Filter.eventually_principal.2 fun v hv => hy v hv
  obtain ⟨x', hx'⟩ := hr x hS0
  have hW' : RestrictedProduct.inclusion R A hS ⁻¹' W ∈ 𝓝 x' :=
    hemb.continuous.continuousAt.preimage_mem_nhds (by rw [hx']; exact hW)
  rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
    (S := (S0 : Set (HeightOneSpectrum (𝓞 F)))ᶜ)).isInducing.nhds_eq_comap, Filter.mem_comap] at hW'
  obtain ⟨t, ht, htW⟩ := hW'
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, u, hu, hIu⟩ := ht
  have hval : ∀ v, x' v = x v := fun v => by rw [← hx']; rfl
  refine ⟨S0 ∪ hI.toFinset, fun v => u v ∩ (if v ∈ S0 then Set.univ else A v), ?_, ?_, ?_⟩
  · intro v
    refine Filter.inter_mem (by rw [← hval]; exact hu v) ?_
    by_cases h : v ∈ S0
    · simp [h]
    · simpa [h] using (hAo v).mem_nhds (hS0 v h)
  · intro v hv z hz
    have h : v ∉ S0 := fun h => hv (Finset.mem_union_left _ h)
    have h2 := hz.2
    rw [if_neg h] at h2
    exact h2
  · intro y hy1 hy2
    have hyA : ∀ v, v ∉ S0 → y v ∈ A v := by
      intro v hv
      by_cases h : v ∈ S0 ∪ hI.toFinset
      · simpa [hv] using (hy1 v h).2
      · exact hy2 v h
    obtain ⟨y', hy'⟩ := hr y hyA
    have hval' : ∀ v, y' v = y v := fun v => by rw [← hy']; rfl
    have : y' ∈ RestrictedProduct.inclusion R A hS ⁻¹' W := by
      refine htW (hIu fun v hv => ?_)
      have hv' : v ∈ S0 ∪ hI.toFinset := Finset.mem_union_right _ (by simpa using hv)
      show y' v ∈ u v
      rw [hval']
      exact (hy1 v hv').1
    have hz : RestrictedProduct.inclusion R A hS y' ∈ W := this
    rw [hy'] at hz
    exact hz

theorem pi_box {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (A : Set (∀ i, X i)) (hA : A ∈ 𝓝 x) :
    ∃ t : ∀ i, Set (X i), (∀ i, t i ∈ 𝓝 (x i)) ∧ ∀ y : ∀ i, X i, (∀ i, y i ∈ t i) → y ∈ A := by
  rw [nhds_pi, Filter.mem_pi] at hA
  obtain ⟨I, -, t, ht, hIt⟩ := hA
  exact ⟨t, ht, fun y hy => hIt fun i _ => hy i⟩

theorem adele_box (x : AF F) (W : Set (AF F)) (hW : W ∈ 𝓝 x) :
    ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Kp u),
      (∀ u, U u ∈ 𝓝 (proj u x)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → U (Sum.inr v) ⊆ Ov v) ∧
      ∀ y : AF F, (∀ u ∈ T, proj u y ∈ U u) →
        (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → proj (Sum.inr v) y ∈ Ov v) → y ∈ W := by
  classical
  have hW' : W ∈ 𝓝 ((x.1, x.2) : Ainf F × Af F) := hW
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hW'
  obtain ⟨t, ht, hIt⟩ := pi_box (X := fun w : InfinitePlace F => w.Completion) x.1 A hA
  obtain ⟨S, V, hV, hVO, hSV⟩ := af_box x.2 B hB
  refine ⟨Finset.univ.map Function.Embedding.inl ∪ S.map Function.Embedding.inr,
    fun u => match u with
      | .inl w => t w
      | .inr v => V v, ?_, ?_, ?_, ?_⟩
  · rintro (w | v)
    · exact ht w
    · exact hV v
  · intro w
    exact Finset.mem_union_left _ (Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩)
  · intro v hv
    exact hVO v fun h => hv (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, h, rfl⟩))
  · intro y hy1 hy2
    have h1 : y.1 ∈ A := hIt y.1 fun w =>
      hy1 (Sum.inl w) (Finset.mem_union_left _ (Finset.mem_map.2 ⟨w, Finset.mem_univ _, rfl⟩))
    have h2 : y.2 ∈ B := by
      refine hSV y.2 (fun v hv => ?_) (fun v hv => ?_)
      · exact hy1 (Sum.inr v) (Finset.mem_union_right _ (Finset.mem_map.2 ⟨v, hv, rfl⟩))
      · by_cases h : (Sum.inr v : Pl F) ∈ Finset.univ.map Function.Embedding.inl ∪
            S.map Function.Embedding.inr
        · rcases Finset.mem_union.1 h with h | h
          · obtain ⟨w, -, hw⟩ := Finset.mem_map.1 h
            cases hw
          · obtain ⟨v', hv', e⟩ := Finset.mem_map.1 h
            cases e
            exact absurd hv' hv
        · exact hy2 v h
    exact hAB (Set.mk_mem_prod h1 h2)

theorem basic_nhd {F : Type} [Field F] [NumberField F] (d β : F) (a : Q d β (AF F)) :
    ∀ V ∈ 𝓝 a,
      ∃ T : Finset (Pl F), ∃ U : (u : Pl F) → Set (Q d β (Kp u)),
        (∀ u, U u ∈ 𝓝 (qmap (proj u) a)) ∧ (∀ w : InfinitePlace F, (Sum.inl w : Pl F) ∈ T) ∧
        ∀ b : Q d β (AF F), (∀ u ∈ T, qmap (proj u) b ∈ U u) →
          (∀ v : HeightOneSpectrum (𝓞 F), (Sum.inr v : Pl F) ∉ T → IntQ v (qmap (proj (Sum.inr v)) b)) →
            b ∈ V := by
  classical
  intro V hV
  let e := qHomeo (d := d) (β := β) (R := AF F)
  have h0 : e.symm ⁻¹' V ∈ 𝓝 (a.re, a.imI, a.imJ, a.imK) := by
    refine e.symm.continuous.continuousAt.preimage_mem_nhds ?_
    have : e.symm (a.re, a.imI, a.imJ, a.imK) = a := e.symm_apply_apply a
    rw [this]
    exact hV
  obtain ⟨W1, h1, R1, hR1, hs1⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨W2, h2, R2, hR2, hs2⟩ := mem_nhds_prod_iff.1 hR1
  obtain ⟨W3, h3, W4, h4, hs3⟩ := mem_nhds_prod_iff.1 hR2
  obtain ⟨T1, U1, n1, i1, o1, c1⟩ := adele_box a.re W1 h1
  obtain ⟨T2, U2, n2, -, o2, c2⟩ := adele_box a.imI W2 h2
  obtain ⟨T3, U3, n3, -, o3, c3⟩ := adele_box a.imJ W3 h3
  obtain ⟨T4, U4, n4, -, o4, c4⟩ := adele_box a.imK W4 h4
  refine ⟨T1 ∪ T2 ∪ T3 ∪ T4,
    fun u => {q | q.re ∈ U1 u ∧ q.imI ∈ U2 u ∧ q.imJ ∈ U3 u ∧ q.imK ∈ U4 u}, ?_, ?_, ?_⟩
  · intro u
    have m1 : {q : Q d β (Kp u) | q.re ∈ U1 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_re (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n1 u)
    have m2 : {q : Q d β (Kp u) | q.imI ∈ U2 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imI (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n2 u)
    have m3 : {q : Q d β (Kp u) | q.imJ ∈ U3 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imJ (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n3 u)
    have m4 : {q : Q d β (Kp u) | q.imK ∈ U4 u} ∈ 𝓝 (qmap (proj u) a) :=
      (continuous_imK (d := d) (β := β) (R := Kp u)).continuousAt.preimage_mem_nhds (n4 u)
    filter_upwards [m1, m2, m3, m4] with q q1 q2 q3 q4 using ⟨q1, q2, q3, q4⟩
  · intro w
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (i1 w)))
  · intro b hb1 hb2
    have t1 : T1 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t2 : T2 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t3 : T3 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have t4 : T4 ⊆ T1 ∪ T2 ∪ T3 ∪ T4 := fun u h => by simp [h]
    have b1 : b.re ∈ W1 := c1 b.re (fun u hu => (hb1 u (t1 hu)).1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o1 v hv (hb1 _ h).1
      · exact (hb2 v h).1
    have b2 : b.imI ∈ W2 := c2 b.imI (fun u hu => (hb1 u (t2 hu)).2.1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o2 v hv (hb1 _ h).2.1
      · exact (hb2 v h).2.1
    have b3 : b.imJ ∈ W3 := c3 b.imJ (fun u hu => (hb1 u (t3 hu)).2.2.1) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o3 v hv (hb1 _ h).2.2.1
      · exact (hb2 v h).2.2.1
    have b4 : b.imK ∈ W4 := c4 b.imK (fun u hu => (hb1 u (t4 hu)).2.2.2) fun v hv => by
      by_cases h : (Sum.inr v : Pl F) ∈ T1 ∪ T2 ∪ T3 ∪ T4
      · exact o4 v hv (hb1 _ h).2.2.2
      · exact (hb2 v h).2.2.2
    have hm : (b.re, b.imI, b.imJ, b.imK) ∈ e.symm ⁻¹' V :=
      hs1 (Set.mk_mem_prod b1 (hs2 (Set.mk_mem_prod b2 (hs3 (Set.mk_mem_prod b3 b4)))))
    have hb : e.symm (b.re, b.imI, b.imJ, b.imK) = b := e.symm_apply_apply b
    rw [Set.mem_preimage, hb] at hm
    exact hm

end GlobalTheory.CompanionTheory.PlaneSA.Box
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdicSumExists
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.PowerSeriesSum

theorem adic_sum_exists {W : Type} [CommRing W] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (N : ℕ) (hN : 0 < N) (b : ℕ → W) :
    ∃ L : W, ∀ M, ∃ c : W,
      L - ∑ n ∈ Finset.range M, (p : W) ^ (n / N) * b n = (p : W) ^ (M / N) * c := by
  set I : Ideal W := Ideal.span {(p : W)} with hI
  set g : ℕ → W := fun M => ∑ n ∈ Finset.range M, (p : W) ^ (n / N) * b n with hg
  have key : ∀ e M₁ M₂, e * N ≤ M₁ → M₁ ≤ M₂ → g M₂ - g M₁ ∈ I ^ e := by
    intro e M₁ M₂ h₁ h₂
    simp only [hg]
    rw [← Finset.sum_Ico_eq_sub _ h₂]
    refine Ideal.sum_mem _ fun n hn => ?_
    have hn' : e ≤ n / N := (Nat.le_div_iff_mul_le hN).2 (h₁.trans (Finset.mem_Ico.1 hn).1)
    exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hn'
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := W) inferInstance
    (f := fun k => g (k * N)) (by
      intro m n hmn
      rw [SModEq.sub_mem]
      simp only [smul_eq_mul, Ideal.mul_top]
      have := key m (m * N) (n * N) le_rfl (Nat.mul_le_mul_right N hmn)
      have h2 := (I ^ m).neg_mem this
      simpa using h2)
  refine ⟨L, fun M => ?_⟩
  have h₁ : L - g (M / N * N) ∈ I ^ (M / N) := by
    have := hL (M / N)
    rw [SModEq.sub_mem] at this
    simp only [smul_eq_mul, Ideal.mul_top] at this
    have h2 := (I ^ (M / N)).neg_mem this
    simpa using h2
  have h₂ : g M - g (M / N * N) ∈ I ^ (M / N) := key _ _ _ le_rfl (Nat.div_mul_le_self M N)
  have h₃ : L - g M ∈ I ^ (M / N) := by
    have := (I ^ (M / N)).sub_mem h₁ h₂
    simpa using this
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h₃
  obtain ⟨c, hc⟩ := h₃
  exact ⟨c, by rw [mul_comm, hc]⟩

theorem sum_exists {W B : Type} [CommRing W] [CommRing B] (w : W →+* B) (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (S : Subring B) (T : Finset B)
    (hw : ∀ a, w a ∈ S) (hT : ∀ t ∈ T, t ∈ S)
    (hgen : ∀ s ∈ S, ∃ a : B → W, s = ∑ t ∈ T, t * w (a t))
    (ϖ y : B) (N : ℕ) (hN : 0 < N) (hϖ : ϖ ∈ S) (hy : y ∈ S) (hN' : ϖ ^ N = (p : B) * y)
    (s : ℕ → B) (hs : ∀ n, s n ∈ S) :
    ∃ r ∈ S, ∀ M, ∃ c ∈ S,
      r - ∑ n ∈ Finset.range M, ϖ ^ n * s n = (p : B) ^ (M / N) * c := by
  have hu : ∀ n, ϖ ^ (n % N) * y ^ (n / N) * s n ∈ S := fun n =>
    S.mul_mem (S.mul_mem (S.pow_mem hϖ _) (S.pow_mem hy _)) (hs n)
  choose a ha using fun n => hgen _ (hu n)
  have hpow : ∀ n, ϖ ^ n * s n = (p : B) ^ (n / N) * ∑ t ∈ T, t * w (a n t) := by
    intro n
    rw [← ha n]
    have hϖn : ϖ ^ n = ((p : B) ^ (n / N) * y ^ (n / N)) * ϖ ^ (n % N) := by
      have h0 : ϖ ^ n = ϖ ^ (N * (n / N) + n % N) := by rw [Nat.div_add_mod]
      rw [h0, pow_add, pow_mul, hN', mul_pow]
    rw [hϖn]
    ring
  choose α hα using fun t => adic_sum_exists (W := W) p N hN (fun n => a n t)
  choose c hc using fun t M => hα t M
  refine ⟨∑ t ∈ T, t * w (α t), S.sum_mem fun t ht => S.mul_mem (hT t ht) (hw _), fun M => ?_⟩
  refine ⟨∑ t ∈ T, t * w (c t M), S.sum_mem fun t ht => S.mul_mem (hT t ht) (hw _), ?_⟩
  have hterm : ∀ t, w (α t) = ∑ n ∈ Finset.range M, (p : B) ^ (n / N) * w (a n t)
      + (p : B) ^ (M / N) * w (c t M) := by
    intro t
    have h := congrArg w (hc t M)
    simp only [map_sub, map_sum, map_mul, map_pow, map_natCast] at h
    rw [← h]; ring
  simp only [hpow, hterm, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hswap : ∑ n ∈ Finset.range M, ∑ t ∈ T, (p : B) ^ (n / N) * (t * w (a n t))
      = ∑ t ∈ T, ∑ n ∈ Finset.range M, t * ((p : B) ^ (n / N) * w (a n t)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => by ring
  rw [hswap, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem sum_with_tails {W B : Type} [CommRing W] [CommRing B] (w : W →+* B) (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (S : Subring B) (T : Finset B) :
    (∀ a, w a ∈ S) → (∀ t ∈ T, t ∈ S) → (∀ s ∈ S, ∃ a : B → W, s = ∑ t ∈ T, t * w (a t)) →
    (∀ x, (∀ m : ℕ, ∃ s ∈ S, x = (p : B) ^ m * s) → x = 0) →
    ∀ (ϖ y : B) (N : ℕ), 0 < N → ϖ ∈ S → y ∈ S → ϖ ^ N = (p : B) * y →
    ∀ s : ℕ → B, (∀ n, s n ∈ S) → ∃ r ∈ S, ∀ M, ∃ a ∈ S,
      r - ∑ n ∈ Finset.range M, ϖ ^ n * s n = ϖ ^ M * a := by
  intro hw hT hgen hsep ϖ y N hN hϖ hy hN' s hs
  obtain ⟨r, hrS, hr⟩ := sum_exists w p S T hw hT hgen ϖ y N hN hϖ hy hN' s hs
  refine ⟨r, hrS, fun M => ?_⟩
  obtain ⟨rM, hrMS, hrM⟩ := sum_exists w p S T hw hT hgen ϖ y N hN hϖ hy hN'
    (fun n => s (M + n)) (fun n => hs _)
  refine ⟨rM, hrMS, ?_⟩
  have hd : r - ∑ n ∈ Finset.range M, ϖ ^ n * s n - ϖ ^ M * rM = 0 := by
    refine hsep _ fun m => ?_
    obtain ⟨c₁, hc₁S, hc₁⟩ := hr (M + N * m)
    obtain ⟨c₂, hc₂S, hc₂⟩ := hrM (N * m)
    have hdiv₁ : (M + N * m) / N = M / N + m := Nat.add_mul_div_left _ _ hN
    have hdiv₂ : (N * m) / N = m := Nat.mul_div_cancel_left _ hN
    rw [hdiv₁] at hc₁
    rw [hdiv₂] at hc₂
    refine ⟨(p : B) ^ (M / N) * c₁ - ϖ ^ M * c₂,
      S.sub_mem (S.mul_mem (S.pow_mem (natCast_mem S p) _) hc₁S)
        (S.mul_mem (S.pow_mem hϖ _) hc₂S), ?_⟩
    rw [Finset.sum_range_add] at hc₁
    have e₁ : r = ∑ n ∈ Finset.range M, ϖ ^ n * s n
        + ∑ n ∈ Finset.range (N * m), ϖ ^ (M + n) * s (M + n)
        + (p : B) ^ (M / N + m) * c₁ := by rw [← hc₁]; ring
    have e₂ : rM = ∑ n ∈ Finset.range (N * m), ϖ ^ n * s (M + n) + (p : B) ^ m * c₂ := by
      rw [← hc₂]; ring
    have e₃ : ∑ n ∈ Finset.range (N * m), ϖ ^ (M + n) * s (M + n)
        = ϖ ^ M * ∑ n ∈ Finset.range (N * m), ϖ ^ n * s (M + n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e₁, e₂, e₃]
    ring
  exact sub_eq_zero.1 hd

end GlobalTheory.CompanionTheory.LTPer.PowerSeriesSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturality
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

namespace GlobalTheory.CompanionTheory.GE.FormalShift

attribute [local instance] algebraOfOver

theorem restrict_idealPow_lift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; (∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a)) → ∀ (G : Z.Modules) [G.IsQuasicoherent] (m : ℕ), ∃ g : (idealPow I G m).restrict (φ ⁻¹ᵁ V).ι ⟶ idealPow (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m, g ≫ idealPowι (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m = (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) := by
  intro A _ _ I X Z _ _ φ V hV _
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  intro hcomp G _ m
  haveI : (G.restrict (φ ⁻¹ᵁ V).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have hf : (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) ≫
      cokernel.π (idealSumMap (G.restrict (φ ⁻¹ᵁ V).ι)
        (Ideal.map (toFunctions (A := A) V) I ^ m)) = 0 := by
    refine hom_eq_zero_of_affineOpens _ fun U s ↦ ?_
    have hU : IsAffineOpen (U : (φ ⁻¹ᵁ V).toScheme.Opens) := U.2
    have hU' : IsAffineOpen ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) :=
      hU.image_of_isOpenImmersion _
    have h1 : (idealPowι I G m).app ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) s ∈
        (Ideal.map (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m) • ⊤ :
          Submodule _ _) :=
      (Set.ext_iff.1 (range_idealPowι_app I G hU' m) _).1 ⟨s, rfl⟩
    have hJ : ∀ a ∈ Ideal.map
        (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m),
        ((φ ⁻¹ᵁ V).ι.appIso (U : (φ ⁻¹ᵁ V).toScheme.Opens)).hom a ∈
          Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) := by
      intro a ha
      have h := Ideal.mem_map_of_mem ((φ ⁻¹ᵁ V).ι.appIso (U : (φ ⁻¹ᵁ V).toScheme.Opens)).hom.hom ha
      rw [Ideal.map_map] at h
      rw [← Ideal.map_pow, Ideal.map_map]
      convert h using 2
      ext r
      exact (hcomp U r).symm
    have h2 : ∀ x ∈ (Ideal.map
        (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m) • ⊤ :
          Submodule Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))),
        (G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv x ∈
          (Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) • ⊤ :
              Submodule Γ((φ ⁻¹ᵁ V).toScheme, (U : (φ ⁻¹ᵁ V).toScheme.Opens))
                Γ(G.restrict (φ ⁻¹ᵁ V).ι, (U : (φ ⁻¹ᵁ V).toScheme.Opens))) := by
      intro x hx
      refine Submodule.smul_induction_on
        (p := fun x ↦ (G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv x ∈
          (Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) • ⊤ :
              Submodule Γ((φ ⁻¹ᵁ V).toScheme, (U : (φ ⁻¹ᵁ V).toScheme.Opens))
                Γ(G.restrict (φ ⁻¹ᵁ V).ι, (U : (φ ⁻¹ᵁ V).toScheme.Opens)))) hx ?_ ?_
      · intro a ha y _
        show _ ∈ _
        rw [Scheme.Modules.smul_restrictAppIso_inv_apply]
        exact Submodule.smul_mem_smul (hJ a ha) Submodule.mem_top
      · intro y z hy hz
        show _ ∈ _
        rw [map_add]
        exact Submodule.add_mem _ hy hz
    obtain ⟨y, hy⟩ := (Set.ext_iff.1 (range_idealPowι_app
      (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) hU m) _).2 (h2 _ h1)
    change (cokernel.π (idealSumMap (G.restrict (φ ⁻¹ᵁ V).ι)
        (Ideal.map (toFunctions (A := A) V) I ^ m))).app (U : (φ ⁻¹ᵁ V).toScheme.Opens)
      ((G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv
        ((idealPowι I G m).app ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) s)) = 0
    rw [← hy, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, kernel.condition,
      Scheme.Modules.Hom.zero_app]
    rfl
  exact ⟨kernel.lift _ _ hf, kernel.lift_ι _ _ _⟩

end GlobalTheory.CompanionTheory.GE.FormalShift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_refinement_cohomology_bijective : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 𝒲 : Set X.Opens) (h : St Q₀ 𝒱 ≤ St Q₀ 𝒲) (hc : ∀ W ∈ 𝒲, W ≤ sSup 𝒱) (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := by
  first | exact @GlobalTheory.CompanionTheory.NlZar.zariski_descent | exact GlobalTheory.CompanionTheory.NlZar.zariski_descent | (intros; apply GlobalTheory.CompanionTheory.NlZar.zariski_descent <;> assumption)
end

