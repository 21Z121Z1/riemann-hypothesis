import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace VeryAmpleZChartRing

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_pow_mul_mem_ampleRing (H : LineBundle S x) {m : ℕ} {h : Ω}
    (hh : ∀ I, h ∈ (H.pow m).sub I) {c : Ω} (hc : c ∈ ampleRing H.toSubSystem m h) (K : Chart x)
    (hrat : ∀ I : Chart x, ∃ e : ℕ,
      c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem m h I)
    {y : Ω} (hy : y ∈ ampleChart H.toSubSystem m h K) : ∃ M : ℕ, c ^ M * y ∈ ampleRing H.toSubSystem m h := by
  classical
  have hI : ∀ I : Chart x, ∃ M, c ^ M * y ∈ ampleChart H.toSubSystem m h I := by
    intro I
    have h1 : y ∈ ampleChart H.toSubSystem m h (AmpleAffineGen.unionChart I K) :=
      AmpleAffineGen.ampleChart_mono (AmpleAffineGen.subset_unionChart_right I K) hy
    obtain ⟨D, hD⟩ := AmpleAffineGen.ampleChart_loc H I K h1
    obtain ⟨e, he⟩ := hrat I
    refine ⟨e * D, ?_⟩
    have := mul_mem
      (pow_mem (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from he) D)
      (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hD)
    rwa [show c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) =
        c ^ e * AmpleAffineGen.chartRatio K I from rfl,
      AmpleAffineGen.pow_mul_cancel (AmpleAffineGen.chartRatio_mul_chartRatio I K)] at this
  choose M hM using hI
  refine ⟨Finset.univ.sup M, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : M I ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ I)
  have e1 : c ^ Finset.univ.sup M * y = c ^ (Finset.univ.sup M - M I) * (c ^ M I * y) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e1]
  exact mul_mem
    (pow_mem (show c ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from
      Set.mem_iInter.mp hc I) _)
    (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hM I)

theorem ampleBase_le_chartRing {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J :=
  Algebra.adjoin_le (by
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X j, 1, X_mem_monos hj, isHomogeneous_X S l, isHomogeneous_X S j, by simp⟩)

theorem pow_div_xProd_mem {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) (j : Fin (r + 1)) :
    h j ^ J.1.card / xProd J ∈ chartRing S h J :=
  ⟨X j ^ J.1.card, AmpleAffineGen.monoProd J.1, J.1.card, AmpleAffineGen.monoProd_mem_monos subset_rfl,
    by simpa using (isHomogeneous_X S j).pow J.1.card, AmpleAffineGen.monoProd_isHomogeneous J.1,
    by rw [map_pow, aeval_X, AmpleAffineGen.aeval_monoProd, xProd]⟩

end VeryAmpleZChartRing

open VeryAmpleZChartRing in

theorem VeryAmpleZChartRing.proof : VeryAmpleZChartRing.Statement.{u, w} := by
  intro S _ Ω _ _ N x H r h hv J j hjJ c hc K hrat α hα
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hjJ)
  have hh : ∀ I : Chart x, h j ∈ (H.pow 1).sub I := fun I => by
    rw [SubSystem.pow_sub, pow_one]
    exact (Submodule.mem_iInf _).mp (hv.mem_secs j) I
  have hJ0 : xProd J ≠ 0 := AmpleAffineGen.xProd_ne_zero J
  obtain ⟨n, hn⟩ := hα
  set g : Ω := xProd J / h j ^ J.1.card with hg
  have hy : α * g ^ n ∈ ampleChart H.toSubSystem 1 (h j) K := by
    refine ⟨J.1.card * n, ?_⟩
    have e1 : α * g ^ n * h j ^ (J.1.card * n) = α * xProd J ^ n := by
      rw [hg, div_pow, pow_mul, ← pow_mul, mul_comm J.1.card n, pow_mul, mul_assoc,
        div_mul_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hj0))]
    rw [e1, one_mul]
    exact hn
  obtain ⟨M₀, hM₀⟩ := exists_pow_mul_mem_ampleRing H hh hc K hrat hy
  have hbase := ampleBase_le_chartRing (S := S) J hjJ
  have h1 : c ^ M₀ * (α * g ^ n) ∈ chartRing S h J := hbase (hv.closed j hj0 hM₀)
  have hcJ : c ∈ chartRing S h J := hbase (hv.closed j hj0 hc)
  have h2 : c ^ M₀ * α ∈ chartRing S h J := by
    have e2 : c ^ M₀ * α = c ^ M₀ * (α * g ^ n) * (h j ^ J.1.card / xProd J) ^ n := by
      rw [hg, mul_assoc (c ^ M₀), mul_assoc α, ← mul_pow, div_mul_div_cancel₀ (pow_ne_zero _ hj0),
        div_self hJ0, one_pow, mul_one]
    rw [e2]
    exact mul_mem h1 (pow_mem (pow_div_xProd_mem J j) n)
  refine eventually_atTop.mpr ⟨M₀, fun M hM => ?_⟩
  have e3 : c ^ M * α = c ^ (M - M₀) * (c ^ M₀ * α) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hM]
  rw [e3]
  exact mul_mem (pow_mem hcJ _) h2

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZChartSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace VeryAmpleZChartSpan

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [Module S E] [IsScalarTower S Ω E] in

theorem chart_smul {I : Chart x} (a : chartRing S x I) (e : E) : a • e = (a : Ω) • e := rfl

theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    exact Submodule.subset_span
      ⟨h l, (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp (hh l) I), _, ih, rfl⟩

omit [Module S E] [IsScalarTower S Ω E] in

theorem exists_coeff_of_mem_twist (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x) (g : Finset E)
    (hg : F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E)) {z : E} (hz : z ∈ (F.twist Q).sub I) :
    ∃ γ : E → Ω, (∀ y ∈ g, γ y ∈ Q.sub I) ∧ z = ∑ y ∈ g, γ y • y := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, y', hy', rfl⟩ := hz
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.mp (hg hy')
    refine ⟨fun y => (a y : Ω) * q, fun y _ => ?_, ?_⟩
    · have := Submodule.smul_mem (Q.sub I) (a y) hq
      rwa [chartRing_smul_def] at this
    · rw [← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [chart_smul, smul_smul, mul_comm]
  | zero => exact ⟨0, fun _ _ => Submodule.zero_mem _, by simp⟩
  | add z z' _ _ ih ih' =>
    obtain ⟨γ, hγ, rfl⟩ := ih
    obtain ⟨γ', hγ', rfl⟩ := ih'
    refine ⟨γ + γ', fun y hy => Submodule.add_mem _ (hγ y hy) (hγ' y hy), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]
  | smul a z _ ih =>
    obtain ⟨γ, hγ, rfl⟩ := ih
    refine ⟨fun y => (a : Ω) * γ y, fun y hy => ?_, ?_⟩
    · have := Submodule.smul_mem (Q.sub I) a (hγ y hy)
      rwa [chartRing_smul_def] at this
    · rw [chart_smul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [smul_smul]

theorem proof : VeryAmpleZChartSpan.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh I J g hg e he
  have hJ : xProd J ∈ (H.pow J.1.card).sub I := prod_mem_pow H I hh J.1
  have h0 : xProd J ≠ 0 := AmpleAffineGen.xProd_ne_zero J
  have memB : ∀ {a : Ω}, a ∈ ampleChart H J.1.card (xProd J) I →
      a ∈ AmpleAffineGen.ampleSubalg H J.1.card (xProd J) I hJ := fun ha => ha
  change e ∈ Submodule.span S _ at he
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨n, hn⟩ := he
    obtain ⟨γ, hγ, hz⟩ := exists_coeff_of_mem_twist F _ I g hg hn
    have hp : xProd J ^ n ≠ 0 := pow_ne_zero n h0
    refine ⟨fun y => γ y / xProd J ^ n, fun y hy => ⟨n, ?_⟩, ?_⟩
    · rw [div_mul_cancel₀ _ hp]; exact hγ y hy
    · have he' : e = (xProd J ^ n)⁻¹ • (xProd J ^ n • e) := by
        rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
      rw [he', hz, Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => by
        show _ = (γ y / xProd J ^ n) • y
        rw [smul_smul, div_eq_inv_mul]
  | zero =>
    refine ⟨0, fun _ _ => ⟨0, ?_⟩, by simp⟩
    rw [Pi.zero_apply, zero_mul]; exact Submodule.zero_mem _
  | add e e' _ _ ih ih' =>
    obtain ⟨β, hβ, rfl⟩ := ih
    obtain ⟨β', hβ', rfl⟩ := ih'
    refine ⟨β + β', fun y hy => Subalgebra.add_mem _ (memB (hβ y hy)) (memB (hβ' y hy)), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]
  | smul s e _ ih =>
    obtain ⟨β, hβ, rfl⟩ := ih
    refine ⟨fun y => algebraMap S Ω s * β y,
      fun y hy => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ s) (memB (hβ y hy)), ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [← smul_assoc, Algebra.smul_def]

end VeryAmpleZChartSpan

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZExtend
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

namespace VeryAmpleZExtend

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem prod_mem_pow {r : ℕ} (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ H.secs)
    (I : Chart x) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact one_mem_twistMod_zero I
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    have h1 : h a ∈ (H.pow 1).sub I := by
      rw [SubSystem.pow_sub, pow_one]
      exact (Submodule.restrictScalars_mem _ _ _).mp ((Submodule.mem_iInf _).mp (hh a) I)
    exact AmpleTwistLocal.mul_mem_pow H I ih 1 h1

omit [Module S E] [IsScalarTower S Ω E] in

theorem smul_mem_twist_pow (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    {w : Ω} (hz : z ∈ (F.twist (H.pow a)).sub I) (hw : w ∈ (H.pow b).sub I) :
    w • z ∈ (F.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => w • z ∈ (F.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq b hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro z z' _ _ hz hz'; rw [smul_add]; exact Submodule.add_mem _ hz hz'
  · intro t z _ hz
    have e : w • (t • z) = t • (w • z) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ t hz

omit [Module S E] [IsScalarTower S Ω E] in

theorem gen_smul {r : ℕ} (F : SubSystem S x E) (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (I : Chart x) (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) {c : Ω} {a : ℕ}
    (hc : c * h j ^ a ∈ (H.pow a).sub I) {y : E}
    (hy : ∃ m : ℕ, xProd J ^ m • y ∈ (F.twist (H.pow (J.1.card * m))).sub I) :
    ∃ m : ℕ, xProd J ^ m • (c • y) ∈ (F.twist (H.pow (J.1.card * m))).sub I := by
  classical
  obtain ⟨m, hm⟩ := hy
  have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
  have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
  have hw := AmpleTwistLocal.mul_mem_pow H I hc _
    (AmpleTwistLocal.pow_mem_pow H I (prod_mem_pow H hh I (J.1.erase j)) a)
  refine ⟨m + a, ?_⟩
  have e1 : xProd J ^ (m + a) • (c • y) =
      (c * h j ^ a * (∏ l ∈ J.1.erase j, h l) ^ a) • (xProd J ^ m • y) := by
    rw [smul_smul, smul_smul, hJ]
    congr 1
    ring
  have e2 : J.1.card * (m + a) = J.1.card * m + (a + (J.1.erase j).card * a) := by
    rw [← hcard]; ring
  rw [e1, e2]
  exact smul_mem_twist_pow F H I hm hw

theorem proof : VeryAmpleZExtend.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh J j hj c hc K hK f hf
  classical
  have key : ∀ I : Chart x, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZChart F.toSubSystem H h I J := by
    intro I
    obtain ⟨a, ha⟩ := Set.mem_iInter.mp hc I
    rw [one_mul] at ha
    obtain ⟨e, n, hn⟩ := hK I
    rw [one_mul] at hn
    change c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n ∈ (H.pow n).sub I at hn

    have hfU := F.mono K (AmpleAffineGen.unionChart I K) (AmpleAffineGen.subset_unionChart_right I K) f hf
    obtain ⟨t, ht, htf⟩ := (F.mem_iff I (AmpleAffineGen.unionChart I K)
      (AmpleAffineGen.subset_unionChart_left I K) f).mp hfU
    obtain ⟨v, hv⟩ := ht.exists_left_inv
    obtain ⟨D, hD⟩ := AmpleAffineGen.exists_pow_mul_mem I K v.2
    have hv' : (v : Ω) * (t : Ω) = 1 := congrArg Subtype.val hv
    have hρf : AmpleAffineGen.chartRatio I K ^ D • f ∈ F.sub I := by
      have e1 : AmpleAffineGen.chartRatio I K ^ D • f =
          (⟨_, hD⟩ : chartRing S x I) • ((t : Ω) • f) := by
        rw [Subalgebra.smul_def, smul_smul]
        congr 1
        change _ = AmpleAffineGen.chartRatio I K ^ D * (v : Ω) * (t : Ω)
        rw [mul_assoc, hv', mul_one]
      rw [e1]
      exact Submodule.smul_mem _ _ htf

    have hP := prod_mem_pow H hh I (J.1.erase j)
    have hcard : (J.1.erase j).card + 1 = J.1.card := Finset.card_erase_add_one hj
    have hJ : xProd J = h j * ∏ l ∈ J.1.erase j, h l := (Finset.mul_prod_erase J.1 h hj).symm
    have hz : (c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
        (AmpleAffineGen.chartRatio I K ^ D • f) ∈ (F.toSubSystem.twist (H.pow (n * D))).sub I :=
      Submodule.subset_span ⟨_, AmpleTwistLocal.pow_mem_pow H I hn D, _, hρf, rfl⟩
    have hz2 := smul_mem_twist_pow F.toSubSystem H I hz
      (AmpleTwistLocal.pow_mem_pow H I hP (n * D))
    have h0 : ∃ m : ℕ, xProd J ^ m • (c ^ (e * D) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      refine ⟨n * D, ?_⟩
      have e1 : xProd J ^ (n * D) • (c ^ (e * D) • f) =
          (∏ l ∈ J.1.erase j, h l) ^ (n * D) • ((c ^ e * AmpleAffineGen.chartRatio K I * h j ^ n) ^ D •
            (AmpleAffineGen.chartRatio I K ^ D • f)) := by
        rw [smul_smul, smul_smul, smul_smul, hJ]
        congr 1
        have hr := AmpleAffineGen.chartRatio_mul_chartRatio I K
        calc (h j * ∏ l ∈ J.1.erase j, h l) ^ (n * D) * c ^ (e * D)
            = (∏ l ∈ J.1.erase j, h l) ^ (n * D) * ((c ^ e * h j ^ n) ^ D *
                (AmpleAffineGen.chartRatio K I * AmpleAffineGen.chartRatio I K) ^ D) := by
              rw [hr, one_pow, mul_one]; ring
          _ = _ := by ring
      have e2 : J.1.card * (n * D) = n * D + (J.1.erase j).card * (n * D) := by
        rw [← hcard]; ring
      rw [e1, e2]
      exact hz2

    have hstep : ∀ q : ℕ, ∃ m : ℕ, xProd J ^ m • (c ^ (e * D + q) • f) ∈
        (F.toSubSystem.twist (H.pow (J.1.card * m))).sub I := by
      intro q
      induction q with
      | zero => exact h0
      | succ q ih =>
        rw [← Nat.add_assoc, pow_succ', ← smul_smul]
        exact gen_smul F.toSubSystem H hh I J hj ha ih
    refine eventually_atTop.mpr ⟨e * D, fun M hM => ?_⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hM
    exact Submodule.subset_span (hstep q)
  exact (eventually_all.mpr key).mono fun M hM => (Submodule.mem_iInf _).mpr hM

end VeryAmpleZExtend

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

namespace VeryAmpleZFinite

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {r : ℕ}

theorem ampleBase_le_chartRing {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J := by
  rw [ampleBase, Algebra.adjoin_le_iff]
  rintro _ ⟨l, rfl⟩
  exact ⟨MvPolynomial.X l, MvPolynomial.X j, 1, X_mem_monos hj, MvPolynomial.isHomogeneous_X S l,
    MvPolynomial.isHomogeneous_X S j, by simp⟩

end VeryAmpleZFinite

open VeryAmpleZFinite in

theorem VeryAmpleZFinite.proof (hExt : VeryAmpleZExtend.Statement.{u, v, w})
    (hSpan : VeryAmpleZChartSpan.Statement.{u, v, w}) (hRing : VeryAmpleZChartRing.Statement.{u, w}) :
    VeryAmpleZFinite.Statement.{u, v, w} := by
  classical
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H r h hH J
  obtain ⟨j, hj⟩ := J.2.1
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hj)
  have hsec : ∀ l, h l ∈ H.toSubSystem.secs := hH.mem_secs
  obtain ⟨n, a, b, Jk, ha, hb, hab, hrat⟩ := hH.affine j hj0
  have hA : ∀ z ∈ ampleRing H.toSubSystem 1 (h j), z ∈ chartRing S h J := fun z hz =>
    ampleBase_le_chartRing J hj (hH.closed j hj0 hz)
  choose g hg using fun k => hF (Jk k)

  have hext : ∀ k, ∀ᶠ M in atTop, ∀ y ∈ g k, b k ^ M • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J :=
    fun k => (eventually_all_finset _).mpr fun y hy =>
      hExt S Ω N x E F H.toSubSystem r h hsec J j hj (b k) (hb k) (Jk k) (hrat k) y
        (by rw [← hg k]; exact Submodule.subset_span hy)
  choose M0 hM0 using fun k => eventually_atTop.mp (hext k)
  set T : Finset E := Finset.univ.biUnion fun k => (g k).image fun y => b k ^ M0 k • y with hT
  have hTmem : ∀ k, ∀ y ∈ g k, b k ^ M0 k • y ∈ T := fun k y hy =>
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩
  refine ⟨T, fun z hz => ?_, fun e he => ?_⟩
  · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
    exact hM0 k (M0 k) le_rfl y hy
  rw [Submodule.restrictScalars_mem]

  have hloc : ∀ k, ∀ᶠ L in atTop, b k ^ L • e ∈ Submodule.span (chartRing S h J) (T : Set E) := by
    intro k
    have heK : e ∈ secsOnZChart F.toSubSystem H.toSubSystem h (Jk k) J :=
      (Submodule.mem_iInf _).mp he (Jk k)
    obtain ⟨β, hβ, rfl⟩ := hSpan S Ω N x E F.toSubSystem H.toSubSystem r h hsec (Jk k) J (g k)
      (hg k).ge _ heK
    obtain ⟨L0, hL0⟩ := eventually_atTop.mp ((eventually_all_finset (g k)).mpr fun y hy =>
      hRing S Ω N x H r h hH J j hj (b k) (hb k) (Jk k) (hrat k) (β y) (hβ y hy))
    refine eventually_atTop.mpr ⟨L0 + M0 k, fun L hL => ?_⟩
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    have hmem : b k ^ (L - M0 k) * β y ∈ chartRing S h J := hL0 _ (by omega) y hy
    have e1 : b k ^ L • (β y • y) = (⟨_, hmem⟩ : chartRing S h J) • (b k ^ M0 k • y) := by
      rw [Subalgebra.smul_def, smul_smul, smul_smul]
      congr 1
      change b k ^ L * β y = b k ^ (L - M0 k) * β y * b k ^ M0 k
      rw [mul_comm _ (b k ^ M0 k), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hTmem k y hy))

  choose L hL using fun k => eventually_atTop.mp (hloc k)
  set L' := Finset.univ.sup L
  let bA : Fin n → chartRing S h J := fun k => ⟨b k, hA _ (hb k)⟩
  have htop : Ideal.span (Set.range bA) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun k => ⟨a k, hA _ (ha k)⟩, Subtype.ext ?_⟩
    rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
    exact hab
  have h1 : (1 : chartRing S h J) ∈ Ideal.span (Set.range fun k => bA k ^ L') := by
    have := Ideal.span_pow_eq_top _ htop L'
    rw [← Set.range_comp] at this
    rw [← Ideal.eq_top_iff_one]
    exact this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  have he' : e = ∑ k, c k • (b k ^ L' • e) := by
    have : ∑ k, c k • (b k ^ L' • e) = (∑ k, c k * bA k ^ L') • e := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul]
      simp [bA]
    rw [this, hc, one_smul]
  rw [he']
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (hL k L' (Finset.le_sup (Finset.mem_univ k)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

