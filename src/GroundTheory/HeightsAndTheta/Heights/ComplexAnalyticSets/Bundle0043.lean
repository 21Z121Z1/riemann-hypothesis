import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleFiniteGermProjectionOpenAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

theorem IrreducibleFiniteGermProjectionOpenAt.proof
    (hpts : IrreducibleGermPointsOffDiscriminant.Statement) :
    IrreducibleFiniteGermProjectionOpenAt.Statement := by
  intro σ _ X x d A hX hirr hiso hinj V hV
  obtain ⟨δ, hδa, hδne, hδpts⟩ := hpts σ X x d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hNo.mem_nhds hxN))
  set r' := r / 2 with hr'
  have hr'0 : 0 < r' := by positivity
  have hcb : closedBall x r' ⊆ V ∩ N := (closedBall_subset_ball (by linarith)).trans hrV

  set K : Set (σ → ℂ) := closedBall x r' ∩ ⋂ i, (closedBall x r' ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x r').of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono (hcb.trans inter_subset_right)).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKV : A '' K ⊆ A '' (X ∩ V) := by
    refine image_mono fun z hz => ?_
    have hzN : z ∈ N := (hcb hz.1).2
    have hzX : z ∈ X ∩ N := by
      rw [hXN]
      exact ⟨hzN, fun i => by simpa using ((mem_iInter.mp hz.2) i).2⟩
    exact ⟨hzX.1, (hcb hz.1).1⟩
  have hball : ∀ z ∈ X ∩ ball x r', z ∈ K := by
    intro z hz
    have hzcb : z ∈ closedBall x r' := ball_subset_closedBall hz.2
    have hzN : z ∈ X ∩ N := ⟨hz.1, (hcb hzcb).2⟩
    rw [hXN] at hzN
    exact ⟨hzcb, mem_iInter.mpr fun i => ⟨hzcb, by simpa using hzN.2 i⟩⟩

  obtain ⟨ε₁, hε₁, hε₁a⟩ := hδa.exists_ball_analyticOnNhd
  obtain ⟨ε₂, hε₂, hε₂p⟩ := Metric.eventually_nhds_iff.mp (hδpts (ball x r') (ball_mem_nhds x hr'0))
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ (ball (A x) ε) := hε₁a.mono (ball_subset_ball (min_le_left _ _))
  have hsub : {y | y ∈ ball (A x) ε ∧ δ y ≠ 0} ⊆ A '' K := by
    rintro y ⟨hy, hδy⟩
    have hy2 : dist y (A x) < ε₂ := lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _)
    obtain ⟨x', hx', rfl⟩ := hε₂p hy2 hδy
    exact ⟨x', hball x' hx', rfl⟩
  have hD : ball (A x) ε ⊆ A '' K := by
    intro y hy
    refine (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsub (mem_closure_iff_frequently.mpr ?_)
    intro hev
    have hev' : δ =ᶠ[𝓝 y] 0 := by
      filter_upwards [hev, isOpen_ball.mem_nhds hy] with z hz hzD
      by_contra hz0
      exact hz ⟨hzD, hz0⟩
    have hzero := hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (A x) ε).isPreconnected hy hev'
    apply hδne
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hzero hz
  exact Filter.mem_of_superset (ball_mem_nhds (A x) hε) (hD.trans hKV)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermProjectionImageNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Set

theorem le_of_isolated_fibres (hfi : HolomorphicFibreInfinite.Statement) {e d : ℕ} {O : Set (Fin e → ℂ)}
    {φ : (Fin e → ℂ) → Fin d → ℂ} (hO : IsOpen O) (hne : O.Nonempty) (hφ : DifferentiableOn ℂ φ O)
    (hiso : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → φ v = φ t → v = t) : e ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hy0)
  obtain ⟨y, hy⟩ := hfi e d (ball y0 ρ) φ hlt isOpen_ball ⟨y0, mem_ball_self hρ⟩
    (hφ.mono (ball_subset_closedBall.trans hρO))
  obtain ⟨p, hpK, hpacc⟩ := hy.exists_accPt_of_subset_isCompact (isCompact_closedBall y0 ρ)
    (fun t ht => ball_subset_closedBall ht.1)
  have hpO : p ∈ O := hρO hpK
  have hcl : p ∈ closure {t | t ∈ ball y0 ρ ∧ φ t = y} := mem_closure_iff_nhds.2 fun U hU => by
    obtain ⟨q, hq, -⟩ := accPt_iff_nhds.1 hpacc U hU
    exact ⟨q, hq⟩
  have hφp : φ p = y := by
    have h1 := mem_closure_image ((hφ p hpO).differentiableAt (hO.mem_nhds hpO)).continuousAt hcl
    have h2 : φ '' {t | t ∈ ball y0 ρ ∧ φ t = y} ⊆ {y} := by
      rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    simpa using closure_mono h2 h1
  obtain ⟨W, hW, hWiso⟩ := hiso p hpO
  obtain ⟨q, ⟨hqW, hqB, hqy⟩, hqp⟩ := accPt_iff_nhds.1 hpacc W hW
  exact hqp (hWiso q hqW (hρO (ball_subset_closedBall hqB)) (hqy.trans hφp.symm))

theorem IrreducibleGermProjectionImageNear.proof (hdim : IrreducibleGermRegularDimGe.Statement)
    (hisoN : IsolatedFibreNear.Statement) (hreg : RegularLocusDense.Statement)
    (hopen : HolomorphicIsolatedFibreOpen.Statement) (hfi : HolomorphicFibreInfinite.Statement) :
    IrreducibleGermProjectionImageNear.Statement := by
  intro σ _ X w d A hX hirr hfin hnd
  obtain ⟨N1, hN1, hdimN⟩ := hdim σ X w d A hX hirr hfin hnd
  obtain ⟨N2, hN2, hisoX⟩ := hisoN σ X w d A hX hfin
  obtain ⟨N3, hN3o, hwN3, hdense⟩ := hreg σ X w hX
  refine ⟨interior (N1 ∩ N2) ∩ N3,
    inter_mem (interior_mem_nhds.2 (inter_mem hN1 hN2)) (hN3o.mem_nhds hwN3), ?_⟩
  have hBo : IsOpen (interior (N1 ∩ N2) ∩ N3) := isOpen_interior.inter hN3o
  rintro x ⟨hxX, hxB⟩ h hh hvan
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨V, hV, hVo, hxV⟩ := _root_.mem_nhds_iff.1 hvan
  set V1 := V ∩ (interior (N1 ∩ N2) ∩ N3) ∩ A ⁻¹' ball (A x) ε with hV1
  have hV1o : IsOpen V1 := (hVo.inter hBo).inter (isOpen_ball.preimage A.continuous)
  have hxV1 : x ∈ V1 := ⟨⟨hxV, hxB⟩, mem_ball_self hε⟩
  have hcl := hdense V1 hV1o (fun z hz => hz.1.2.2) ⟨hxX, hxV1⟩
  obtain ⟨r, hr⟩ : (regLocus (X ∩ V1)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, closure_empty] at hcl
    exact hcl
  obtain ⟨hrX, e, A', O, V', g, hO, hV', hrV', hg, hA'g, hXV'⟩ := hr
  have hgX : ∀ t ∈ O, g t ∈ X ∩ V1 := fun t ht => by
    have : g t ∈ X ∩ V1 ∩ V' := hXV' ▸ mem_image_of_mem g ht
    exact this.1
  have hN12 : ∀ z ∈ V1, z ∈ N1 ∩ N2 := fun z hz => interior_subset hz.1.2.1
  have hchart : X ∩ (V1 ∩ V') = g '' O := by rw [← hXV']; exact (inter_assoc X V1 V').symm
  have hde : d ≤ e := hdimN r ⟨hrX.1, (hN12 r hrX.2).1⟩ e A' O (V1 ∩ V') g hO (hV1o.inter hV')
    ⟨hrX.2, hrV'⟩ hg hA'g hchart
  have hφ : DifferentiableOn ℂ (fun y => A (g y)) O :=
    A.differentiable.comp_differentiableOn hg.differentiableOn
  have hisoC : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → A (g v) = A (g t) → v = t := by
    intro t ht
    obtain ⟨W, hW, hiW⟩ := hisoX (g t) ⟨(hgX t ht).1, (hN12 _ (hgX t ht).2).2⟩
    refine ⟨g ⁻¹' W, (hg t ht).continuousAt.preimage_mem_nhds hW, fun v hvW hvO hv => ?_⟩
    have hgv := hiW (g v) ⟨(hgX v hvO).1, hvW⟩ hv
    rw [← hA'g v hvO, ← hA'g t ht, hgv]
  obtain ⟨y0, hy0O, hy0r⟩ : r ∈ g '' O := hXV' ▸ ⟨hrX, hrV'⟩
  have hed : e ≤ d := le_of_isolated_fibres hfi hO ⟨y0, hy0O⟩ hφ hisoC
  obtain rfl : e = d := le_antisymm hed hde
  have hop := hopen e O (fun y => A (g y)) y0 hO hy0O hφ (hisoC y0 hy0O) O (hO.mem_nhds hy0O)
  have hzero : ∀ y ∈ (fun y => A (g y)) '' O, h y = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact hV (hgX t ht).2.1.1 (hgX t ht).1
  have hAr : A (g y0) ∈ ball (A x) ε := (hgX y0 hy0O).2.2
  have hEq : EqOn h 0 (ball (A x) ε) :=
    hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hAr
      (Filter.mem_of_superset hop fun y hy => hzero y hy)
  filter_upwards [ball_mem_nhds (A x) hε] with y hy using hEq hy

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem exists_minimalPrime_mem_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : ∃ P ∈ J.minimalPrimes, x ∈ zeroSet P := by
  have hJ : J ≤ RingHom.ker (eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hJ
  exact ⟨P, hP, fun q hq => (RingHom.mem_ker).1 (hPle hq)⟩

theorem mem_isolatedFibrePts_of_le {n m : ℕ} {J P : Ideal (MvPolynomial (Fin n) ℂ)} (hJP : J ≤ P)
    (Q : Fin m → MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) {x : Fin n → ℂ}
    (hx : x ∈ isolatedFibrePts J Q z) (hxP : x ∈ zeroSet P) : x ∈ isolatedFibrePts P Q z := by
  obtain ⟨-, hQ, V, hV, hiso⟩ := hx
  exact ⟨hxP, hQ, V, hV, fun x' hx' hQ' => hiso x' ⟨fun q hq => hx'.1 q (hJP hq), hx'.2⟩ hQ'⟩

theorem encard_biUnion_finset_le {ι α : Type*} (S : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ S, f i).encard ≤ ∑ i ∈ S, (f i).encard := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add_right ih _)

theorem IsolatedPointsCount.proof (hPrime : IsolatedPointsCountPrime.Statement) :
    IsolatedPointsCount.Statement := by
  classical
  intro n m J Q
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hN : ∀ P ∈ J.minimalPrimes, ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N :=
    fun P hP => hPrime n m P hP.1.1 Q
  choose! N hN using hN
  refine ⟨∑ P ∈ hfin.toFinset, N P, fun z => ?_⟩
  have hsub : isolatedFibrePts J Q z ⊆ ⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := exists_minimalPrime_mem_zeroSet J hx.1
    exact Set.mem_biUnion (hfin.mem_toFinset.2 hP) (mem_isolatedFibrePts_of_le hP.1.2 Q z hx hxP)
  calc (isolatedFibrePts J Q z).encard
      ≤ (⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z).encard := Set.encard_le_encard hsub
    _ ≤ ∑ P ∈ hfin.toFinset, (isolatedFibrePts P Q z).encard := encard_biUnion_finset_le _ _
    _ ≤ ∑ P ∈ hfin.toFinset, ((N P : ℕ) : ℕ∞) :=
        Finset.sum_le_sum fun P hP => hN P (hfin.mem_toFinset.1 hP) z
    _ = ((∑ P ∈ hfin.toFinset, N P : ℕ) : ℕ∞) := by push_cast; rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def LinearFormCut.formMap (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun a := ∑ j, C (a j) * X j
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_eq_C_mul, Finset.mul_sum, mul_assoc]

theorem LinearFormCut.proof : LinearFormCut.Statement := by
  intro n e I hI
  classical
  let S := {Q : Ideal (MvPolynomial (Fin n) ℂ) | Q ∈ I.minimalPrimes ∧ Q ≠ originIdeal n}
  have : Finite S :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset fun Q hQ => hQ.1).to_subtype
  let p : S → Submodule ℂ (Fin n → ℂ) := fun Q => (Q.1.restrictScalars ℂ).comap (formMap n)
  have hp : ∀ Q, p Q ≠ ⊤ := by
    intro Q htop
    apply Q.2.2
    have hle : originIdeal n ≤ Q.1 := by
      rw [originIdeal, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.single j 1 ∈ p Q := htop ▸ Submodule.mem_top
      simpa [p, formMap, Pi.single_apply] using this
    exact ((originIdeal_isMaximal n).eq_of_le Q.2.1.1.1.ne_top hle).symm
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  let B : Matrix (Fin 1) (Fin n) ℂ := Matrix.of fun _ j => a j
  refine ⟨B, ?_⟩
  have hl : formMap n a ∈ linIdeal B := Ideal.subset_span ⟨0, by simp [linPoly, formMap, B]⟩
  rw [ringKrullDim_quotient] at hI ⊢
  refine iSup_le fun l => ?_
  have hIh : I ≤ l.head.1.asIdeal := fun y hy => l.head.2 (Ideal.mem_sup_left hy)
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hIh
  by_cases hQo : Q = originIdeal n
  · have hM : l.head.1.asIdeal.IsMaximal := by
      rw [← (originIdeal_isMaximal n).eq_of_le l.head.1.isPrime.ne_top (hQo ▸ hQle)]
      exact originIdeal_isMaximal n
    have h0 : l.length = 0 := by
      by_contra h
      have hlt : l.head < l.last := l.strictMono (Fin.pos_iff_ne_zero.2 (by simp [Fin.ext_iff]; omega))
      have hlt' : l.head.1.asIdeal < l.last.1.asIdeal := hlt
      exact (hM.eq_of_le l.last.1.isPrime.ne_top hlt'.le ▸ hlt').false
    simp [h0]
  · have hQa : formMap n a ∉ Q := ha ⟨Q, hQ, hQo⟩
    let f : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑(I ⊔ linIdeal B) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      fun x => ⟨x.1, fun y hy => x.2 (Ideal.mem_sup_left hy)⟩
    have hf : StrictMono f := fun x y h => h
    let q0 : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I :=
      ⟨⟨Q, hQ.1.1⟩, fun y hy => hQ.1.2 hy⟩
    have hq : q0 < (l.map f hf).head := by
      refine lt_of_le_of_ne hQle fun h => hQa ?_
      have : formMap n a ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right hl)
      have hQh : Q = l.head.1.asIdeal :=
        congrArg (fun x : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) ↑I => x.1.asIdeal) h
      rwa [hQh]
    have hlen := (Order.LTSeries.length_le_krullDim ((l.map f hf).cons q0 hq)).trans hI
    simp only [RelSeries.cons_length] at hlen
    have : l.length + 1 ≤ e + 1 := by exact_mod_cast hlen
    exact_mod_cast (by omega : l.length ≤ e)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalParametrisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem exists_proper_projection_nbhd {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X w) (hw : w ∈ X)
    (hiso : ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) {U : Set (σ → ℂ)} (hU : U ∈ 𝓝 w) :
    ∃ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)), IsOpen B ∧ B ⊆ U ∧ w ∈ X ∩ B ∧ IsOpen D ∧
      IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
      (∀ x ∈ X ∩ B, A x = A w → x = w) := by
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hisoW⟩ := hiso
  obtain ⟨r₀, hr₀, hball⟩ :=
    Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem hU (hNo.mem_nhds hwN)) hW)
  set r := r₀ / 2 with hr
  have hr0 : 0 < r := half_pos hr₀
  have hcb : Metric.closedBall w r ⊆ U ∩ N ∩ W :=
    (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball

  set Z : Set (σ → ℂ) := Metric.closedBall w r ∩ ⋂ i, (Metric.closedBall w r ∩ f i ⁻¹' {0}) with hZ
  have hZc : IsClosed Z := by
    refine Metric.isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).1.2).preimage_isClosed_of_isClosed
      Metric.isClosed_closedBall isClosed_singleton
  have hZk : IsCompact Z := (isCompact_closedBall w r).of_isClosed_subset hZc Set.inter_subset_left
  have hZX : ∀ z ∈ Metric.closedBall w r, (z ∈ X ↔ z ∈ Z) := by
    intro z hz
    have hzN : z ∈ N := (hcb hz).1.2
    constructor
    · intro hzX
      have h1 : z ∈ X ∩ N := ⟨hzX, hzN⟩
      rw [hXN] at h1
      exact ⟨hz, Set.mem_iInter.2 fun i => ⟨hz, h1.2 i⟩⟩
    · intro hzZ
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => (Set.mem_iInter.1 hzZ.2 i).2⟩
      rw [← hXN] at h2
      exact h2.1

  have hSk : IsCompact (Z ∩ Metric.sphere w r) := hZk.inter_right Metric.isClosed_sphere
  have hAS : A w ∉ A '' (Z ∩ Metric.sphere w r) := by
    rintro ⟨x, ⟨hxZ, hxs⟩, hxA⟩
    have hxcb : x ∈ Metric.closedBall w r := Metric.sphere_subset_closedBall hxs
    have hxw := hisoW x ⟨(hZX x hxcb).2 hxZ, (hcb hxcb).2⟩ hxA
    rw [hxw, Metric.mem_sphere, dist_self] at hxs
    exact hr0.ne hxs
  obtain ⟨ε, hε, hεS⟩ :=
    Metric.mem_nhds_iff.1 ((hSk.image A.continuous).isClosed.isOpen_compl.mem_nhds hAS)
  refine ⟨Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε, Metric.ball (A w) ε,
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage A.continuous), ?_,
    ⟨hw, Metric.mem_ball_self hr0, Metric.mem_ball_self hε⟩, Metric.isOpen_ball,
    (convex_ball _ _).isPreconnected, fun x hx => hx.2.2, ?_, ?_⟩
  · exact fun x hx => (hcb (Metric.ball_subset_closedBall hx.1)).1.1
  · intro K hKD hK
    have heq : {x | x ∈ X ∩ (Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε) ∧ A x ∈ K} =
        Z ∩ A ⁻¹' K := by
      ext x
      constructor
      · rintro ⟨⟨hxX, hxb, -⟩, hxK⟩
        exact ⟨(hZX x (Metric.ball_subset_closedBall hxb)).1 hxX, hxK⟩
      · rintro ⟨hxZ, hxK⟩
        have hxcb : x ∈ Metric.closedBall w r := hxZ.1
        refine ⟨⟨(hZX x hxcb).2 hxZ, ?_, hKD hxK⟩, hxK⟩
        by_contra hxb
        have hxs : x ∈ Metric.sphere w r :=
          Metric.mem_sphere.2 (le_antisymm (Metric.mem_closedBall.1 hxcb)
            (not_lt.1 fun h => hxb (Metric.mem_ball.2 h)))
        exact hεS (hKD hxK) ⟨x, ⟨hxZ, hxs⟩, rfl⟩
    rw [heq]
    exact hZk.inter_right (hK.isClosed.preimage A.continuous)
  · exact fun x hx hxA => hisoW x ⟨hx.1, (hcb (Metric.ball_subset_closedBall hx.2.1)).2⟩ hxA

theorem LocalParametrisation.proof (hproj : GermFiniteProjection.Statement)
    (hcov : FiniteGermProjectionCover.Statement) : LocalParametrisation.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, hiso, hinj⟩ := hproj σ X w hX hirr
  obtain ⟨N₀, hN₀, hcovB⟩ := hcov σ X w d A hX hirr hiso hinj
  obtain ⟨B, D, hBo, hBU, hwB, hDo, hDc, hmaps, hprop, hisoB⟩ :=
    exists_proper_projection_nbhd A hX hirr.1 hiso (Filter.inter_mem hU hN₀)
  obtain ⟨δ, N, hP⟩ :=
    hcovB B D hBo (hBU.trans Set.inter_subset_right) hwB hDo hDc hmaps hprop hisoB
  exact ⟨d, A, B, D, δ, N, hBU.trans Set.inter_subset_left, hP⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocalDepthTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

theorem NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (hm : ¬ (maximalIdeal B).IsPrincipal)
    {x y : B} (hx : x ≠ 0) (hy : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b) : ∃ c, y = x * c := by
  let K := FractionRing B
  by_cases h : ∀ a ∈ maximalIdeal B, ∀ b, a * y = x * b → b ∈ maximalIdeal B
  ·
    set u : K := algebraMap B K y / algebraMap B K x with hu
    have hxK : algebraMap B K x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hx
    let N : Submodule B K := Submodule.map (Algebra.linearMap B K) (maximalIdeal B)
    have hmbot : maximalIdeal B ≠ ⊥ := fun h0 => hm (h0 ▸ ⟨⟨0, by simp⟩⟩)
    have hN : N ≠ ⊥ := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
      intro hN0
      have : algebraMap B K a ∈ N := Submodule.mem_map_of_mem ha
      rw [hN0, Submodule.mem_bot] at this
      exact ha0 ((map_eq_zero_iff _ (IsFractionRing.injective B K)).mp this)
    have hNfg : N.FG := (IsNoetherian.noetherian (maximalIdeal B)).map _
    have hstab : ∀ n ∈ N, u • n ∈ N := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := hy a ha
      refine ⟨b, h a ha b hb, ?_⟩
      change algebraMap B K b = u * algebraMap B K a
      rw [hu, div_mul_eq_mul_div, eq_div_iff hxK, ← map_mul, ← map_mul]
      congr 1
      linear_combination -hb
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      (isIntegral_of_smul_mem_submodule N hN hNfg u hstab)
    refine ⟨c, IsFractionRing.injective B K ?_⟩
    rw [map_mul, hc, hu]
    exact (mul_div_cancel₀ _ hxK).symm
  ·
    push Not at h
    obtain ⟨a, ha, b, hab, hb⟩ := h
    have hbu : IsUnit b := by
      by_contra hb'
      exact hb ((mem_maximalIdeal b).mpr hb')
    by_cases hy0 : y = 0
    · exact ⟨0, by simp [hy0]⟩
    exfalso
    apply hm
    refine ⟨⟨a, le_antisymm ?_ ?_⟩⟩
    · intro a' ha'
      obtain ⟨b', hb'⟩ := hy a' ha'
      have hab' : a' * b = a * b' := mul_right_cancel₀ hy0 (by linear_combination b * hb' - b' * hab)
      refine Submodule.mem_span_singleton.mpr ⟨b' * ↑hbu.unit⁻¹, ?_⟩
      rw [smul_eq_mul, show b' * ↑hbu.unit⁻¹ * a = (a * b') * ↑hbu.unit⁻¹ by ring, ← hab', mul_assoc,
        hbu.mul_val_inv, mul_one]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact ha

theorem NormalLocalDepthTwo.proof : NormalLocalDepthTwo.Statement := by
  intro B _ _ _ _ _
  by_cases hfield : IsField B
  · refine ⟨[], by simp, IsWeaklyRegular.nil B B, ?_⟩
    rw [ringKrullDim_eq_zero_of_isField hfield]
    simp
  have hmbot : maximalIdeal B ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hfield
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
  have hxreg : IsSMulRegular B x := fun a b h => mul_left_cancel₀ hx0 h
  by_cases hp : (maximalIdeal B).IsPrincipal
  ·
    have : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hfield).out 4 0).mp hp
    refine ⟨[x], by simpa using hxm,
      (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hxreg, IsWeaklyRegular.nil _ _⟩, ?_⟩
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp

  have hreg : ∃ y ∈ maximalIdeal B, IsSMulRegular (QuotSMulTop x B) y := by
    by_contra hcon
    push Not at hcon
    have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
        ⋃ p ∈ associatedPrimes B (QuotSMulTop x B), (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      intro y hy
      have h1 := hcon y hy
      rw [isSMulRegular_iff_right_eq_zero_of_smul] at h1
      push Not at h1
      obtain ⟨z, hz, hz0⟩ := h1
      exact ⟨z, hz0, hz⟩
    have hmem := (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (associatedPrimes.finite B (QuotSMulTop x B)) ⊥ ⊥
      (fun I hI _ _ => IsAssociatedPrime.isPrime hI) bot_ne_top bot_ne_top).mp hsub
    obtain ⟨-, z, hz⟩ := isAssociatedPrime_iff.mp hmem
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hyx : ∀ a ∈ maximalIdeal B, ∃ b, a * y = x * b := by
      intro a ha
      rw [hz, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at ha
      obtain ⟨b, -, hb⟩ := ha
      exact ⟨b, by simpa [smul_eq_mul] using hb.symm⟩
    obtain ⟨c, hc⟩ := NormalLocalDepthTwo.mem_span_of_maximalIdeal_mul_le hp hx0 hyx
    have h1 : (1 : B) ∈ maximalIdeal B := by
      rw [hz, Submodule.mem_colon_singleton, one_smul, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨c, trivial, by rw [hc, smul_eq_mul]⟩
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨y, hym, hy⟩ := hreg
  refine ⟨[x, y], ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · exact (isWeaklyRegular_cons_iff _ _ _).mpr
      ⟨hxreg, (isWeaklyRegular_cons_iff _ _ _).mpr ⟨hy, IsWeaklyRegular.nil _ _⟩⟩
  · exact (min_le_left _ _).trans (by simp)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

