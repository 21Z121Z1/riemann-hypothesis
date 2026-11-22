import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleAffineGen
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubFamilyTwistPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem SubFamily.mem_twist_iff (F : SubFamily S x E) (Q : SubFamily S x Ω) (I J : Chart x) (h : I.1 ⊆ J.1)
    (y : E) : y ∈ (F.toSubSystem.twist Q.toSubSystem).sub J ↔
      ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (F.toSubSystem.twist Q.toSubSystem).sub I := by
  constructor
  · intro hy
    refine Submodule.span_induction (p := fun y _ => ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (F.toSubSystem.twist Q.toSubSystem).sub I) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨q, hq, z, hz, rfl⟩
      obtain ⟨a₁, ha₁, hq₁⟩ := (Q.mem_iff I J h q).mp hq
      obtain ⟨a₂, ha₂, hz₂⟩ := (F.mem_iff I J h z).mp hz
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (q • z) = ((a₁ : Ω) • q) • ((a₂ : Ω) • z) := by
        rw [Subalgebra.coe_mul, smul_eq_mul, smul_smul, smul_smul]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨_, hq₁, _, hz₂, rfl⟩
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro y₁ y₂ _ _ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have e : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
          a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_add, smul_smul, smul_smul, Subalgebra.coe_mul,
          mul_comm (a₂ : Ω) (a₁ : Ω)]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
    · rintro b z _ ⟨a, ha, hz⟩
      obtain ⟨c, hc, hcb⟩ := exists_isUnit_mul_mem h b
      refine ⟨c * a, by rw [map_mul]; exact hc.mul ha, ?_⟩
      have e : ((c * a : chartRing S x I) : Ω) • (b • z) =
          (⟨_, hcb⟩ : chartRing S x I) • ((a : Ω) • z) := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, Subalgebra.coe_mul]
        congr 1
        ring
      rw [e]
      exact Submodule.smul_mem _ _ hz
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (F.toSubSystem.twist Q.toSubSystem).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ

def SubFamily.twistFam (F : SubFamily S x E) (Q : SubFamily S x Ω) : SubFamily S x E where
  toSubSystem := F.toSubSystem.twist Q.toSubSystem
  mem_iff := F.mem_twist_iff Q

theorem SubFamily.exists_pow (Q : SubFamily S x Ω) (n : ℕ) :
    ∃ P : SubFamily S x Ω, P.toSubSystem = Q.toSubSystem.pow n := by
  induction n with
  | zero => exact ⟨(twistBundle S x 0).toSubFamily, rfl⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.twistFam Q, ?_⟩
    change P.toSubSystem.twist Q.toSubSystem = (Q.toSubSystem.pow n).twist Q.toSubSystem
    rw [hP]

end

theorem SubFamilyTwistPow.proof : SubFamilyTwistPow.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q a
  obtain ⟨P, hP⟩ := SubFamily.exists_pow Q a
  exact ⟨F.twistFam P, by rw [← hP]; rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Cocycles

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

def FinGradedSub.cellCone (I : StdCell N) : LocMod S N M.coneSub I.1 →ₗ[Poly S N] ConeLaurent S x :=
  if h : I.1 ⊆ support x then locCone M I.1 h else 0

theorem FinGradedSub.cellCone_of_subset {I : StdCell N} (h : I.1 ⊆ support x) :
    M.cellCone I = locCone M I.1 h := dif_pos h

theorem Cech.sgn_mul_self {n : ℕ} (J : Finset (Fin n)) (j : Fin n) : Cech.sgn J j * Cech.sgn J j = 1 := by
  rw [Cech.sgn, ← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem FinGradedSub.cellCone_cocycle {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : Cech.d (locSys S N M.coneSub) locResS 0 z = 0)
    (K K' : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0)
    (hK : K.1.1 ⊆ support x) (hK' : K'.1.1 ⊆ support x) :
    M.cellCone K.1 (z K) = M.cellCone K'.1 (z K') := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · have : K = K' := Subtype.ext (Subtype.ext (ha.trans (hab ▸ hb.symm)))
    subst this; rfl
  let Kp : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, Finset.subset_univ _⟩, Finset.card_pair hab⟩
  have hKp : Kp.1.1 ⊆ support x := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hK (by rw [ha]; exact Finset.mem_singleton_self _)
    · exact hK' (by rw [hb]; exact hi)
  have hfa : ∀ j : Kp.1.1, (j : Fin (N + 1)) = a → Cech.face Kp j = K' := by
    intro j hj
    apply Subtype.ext; apply Subtype.ext
    change ({a, b} : Finset (Fin (N + 1))).erase j = K'.1.1
    rw [hj, hb, Finset.erase_insert (Finset.notMem_singleton.mpr hab)]
  have hfb : ∀ j : Kp.1.1, (j : Fin (N + 1)) = b → Cech.face Kp j = K := by
    intro j hj
    apply Subtype.ext; apply Subtype.ext
    change ({a, b} : Finset (Fin (N + 1))).erase j = K.1.1
    rw [hj, ha, Finset.pair_comm, Finset.erase_insert (Finset.notMem_singleton.mpr (Ne.symm hab))]
  have h0 := congrArg (M.cellCone Kp.1) (congrFun hz Kp)
  rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have hterm : ∀ j : Kp.1.1, M.cellCone Kp.1 (Cech.sgn Kp.1.1 j • locResS (Cech.face Kp j).1 Kp.1
      (Cech.face_subset Kp j) (z (Cech.face Kp j))) =
      Cech.sgn Kp.1.1 j • M.cellCone (Cech.face Kp j).1 (z (Cech.face Kp j)) := by
    intro j
    rw [map_zsmul, M.cellCone_of_subset hKp, M.cellCone_of_subset ((Cech.face_subset Kp j).trans hKp)]
    congr 1
    exact locCone_locRes M (Cech.face_subset Kp j) hKp _
  rw [Finset.sum_congr rfl fun j _ => hterm j] at h0
  rw [Fintype.sum_eq_add (⟨a, Finset.mem_insert_self a {b}⟩ : Kp.1.1)
    (⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩ : Kp.1.1)
    (fun h => hab (congrArg Subtype.val h)) (fun j hj => ?_)] at h0
  · rw [hfa ⟨a, Finset.mem_insert_self a {b}⟩ rfl,
      hfb ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩ rfl] at h0
    have hs : Cech.sgn Kp.1.1 b = -Cech.sgn Kp.1.1 a := by
      have := Cech.sum_sgn_of_card_two (J := Kp.1.1) Kp.2
      rw [show Kp.1.1 = {a, b} from rfl, Finset.sum_pair hab] at this
      linarith
    change Cech.sgn Kp.1.1 a • M.cellCone K'.1 (z K') + Cech.sgn Kp.1.1 b • M.cellCone K.1 (z K) = 0 at h0
    rw [hs, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h0
    have h1 := congrArg (Cech.sgn Kp.1.1 a • ·) h0
    simp only [smul_smul, Cech.sgn_mul_self, one_smul, smul_zero] at h1
    exact (sub_eq_zero.mp h1).symm
  · exfalso
    rcases Finset.mem_insert.mp j.2 with h | h
    · exact hj.1 (Subtype.ext h)
    · exact hj.2 (Subtype.ext (Finset.mem_singleton.mp h))

theorem FinGradedSub.cocycle_eq_coneSingle {c : ℤ} {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) (hK : K.1.1 ⊆ support x) :
    ∃ v ∈ (M.tildeSys c).secs, M.cellCone K.1 (z K) = coneSingle S x c v := by
  obtain ⟨v, -, hzv⟩ := locCone_degLoc M c K.1 hK (hz.2 K (Set.mem_univ _))
  rw [← M.cellCone_of_subset hK] at hzv
  refine ⟨v, ?_, hzv⟩
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro J
  obtain ⟨i, hi⟩ := J.2.1
  let Ki : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
    ⟨⟨{i}, Finset.singleton_nonempty i, Finset.subset_univ _⟩, Finset.card_singleton i⟩
  have hKi : Ki.1.1 ⊆ support x := Finset.singleton_subset_iff.mpr (J.2.2 hi)
  obtain ⟨v', hv', hzv'⟩ := locCone_degLoc M c Ki.1 hKi (hz.2 Ki (Set.mem_univ _))
  rw [← M.cellCone_of_subset hKi, ← M.cellCone_cocycle (LinearMap.mem_ker.mp hz.1) K Ki hK hKi, hzv] at hzv'
  have hvv : v = v' := by
    have := congrArg (coeffAt S x c) hzv'
    rwa [coeffAt_coneSingle_same, coeffAt_coneSingle_same] at this
  rw [hvv]
  exact (M.tildeSys c).mono _ J (Finset.singleton_subset_iff.mpr hi) v' hv'

theorem FinGradedSub.exists_cocycle_of_mem_secs {c : ℤ} {v : Ω} (hv : v ∈ (M.tildeSys c).secs) :
    ∃ z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0,
      ∀ K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0, K.1.1 ⊆ support x →
        M.cellCone K.1 (z K) = coneSingle S x c v := by
  classical
  rw [SubSystem.secs, Submodule.mem_iInf] at hv
  have hl : ∀ (I : StdCell N) (h : I.1 ⊆ support x), ∃ z ∈ degLoc M.coneGraded c I,
      locCone M I.1 h z = coneSingle S x c v :=
    fun I h => exists_locCone_eq M c I h (hv ⟨I.1, I.2.1, h⟩)
  choose w hw hwv using hl
  let u : ∀ I : StdCell N, LocMod S N M.coneSub I.1 := fun I =>
    if h : I.1 ⊆ support x then w I h else 0
  have hcompat : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (u I) = u J := by
    intro I J h
    by_cases hJ : J.1 ⊆ support x
    · apply locCone_injective M J.1 hJ
      have hI : I.1 ⊆ support x := h.trans hJ
      simp only [u, dif_pos hJ, dif_pos hI]
      rw [hwv J hJ]
      exact (locCone_locRes M h hJ (w I hI)).trans (hwv I hI)
    · obtain ⟨i, hiJ, hi⟩ : ∃ i ∈ J.1, x i = 0 := by
        by_contra hne
        push Not at hne
        exact hJ fun i hi => (mem_support x).mpr (hne i hi)
      have := locMod_subsingleton M hiJ hi
      exact Subsingleton.elim _ _
  refine ⟨fun K => u K.1, ⟨LinearMap.mem_ker.mpr (Cech.d_zero_of_compat u hcompat), fun K _ => ?_⟩,
    fun K hK => ?_⟩
  · change u K.1 ∈ degLoc M.coneGraded c K.1
    by_cases hK : K.1.1 ⊆ support x
    · simp only [u, dif_pos hK]; exact hw K.1 hK
    · simp only [u, dif_neg hK]; exact zero_mem _
  · change M.cellCone K.1 (u K.1) = _
    simp only [u, dif_pos hK, M.cellCone_of_subset hK]
    exact hwv K.1 hK

end Cocycles

theorem TildeTail.proof (h : SerreTail.Statement.{u, w}) : TildeTail.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x M hx c₁
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hx (funext hne)
  let K₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
    ⟨⟨{i₀}, Finset.singleton_nonempty i₀, Finset.subset_univ _⟩, Finset.card_singleton i₀⟩
  have hK₀ : K₀.1.1 ⊆ support x := Finset.singleton_subset_iff.mpr ((mem_support x).mpr hi₀)

  let Ψ : Cech.Cochain (locSys S N M.coneSub) 0 →ₗ[Poly S N] ConeLaurent S x :=
    (M.cellCone K₀.1).comp (LinearMap.proj (R := Poly S N)
      (φ := fun K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 => LocMod S N M.coneSub K.1.1) K₀)
  have hΨ : ∀ z, Ψ z = M.cellCone K₀.1 (z K₀) := fun z => rfl
  obtain ⟨t, ht, hspan⟩ := h S N M.coneSub M.coneGraded M.coneSub_finite c₁

  let G : Submodule S (Cech.Cochain (locSys S N M.coneSub) 0) :=
    { carrier := {z | ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧ (d < c₁ → coeffAt S x d (Ψ z) = 0)}
      add_mem' := fun {a b} ha hb d => by
        rw [map_add, map_add]
        exact ⟨add_mem (ha d).1 (hb d).1, fun hd => by rw [(ha d).2 hd, (hb d).2 hd, add_zero]⟩
      zero_mem' := fun d => by rw [map_zero, map_zero]; exact ⟨zero_mem _, fun _ => rfl⟩
      smul_mem' := fun s z hz d => by
        rw [LinearMap.map_smul_of_tower, map_smul]
        exact ⟨Submodule.smul_mem _ s (hz d).1, fun hd => by rw [(hz d).2 hd, smul_zero]⟩ }
  have hG : H0tail M.coneGraded c₁ ≤ G := by
    refine iSup₂_le fun c hc z hz => ?_
    show ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧ (d < c₁ → coeffAt S x d (Ψ z) = 0)
    intro d
    obtain ⟨v, hv, hzv⟩ := M.cocycle_eq_coneSingle hz K₀ hK₀
    rw [hΨ, hzv]
    by_cases hcd : c = d
    · subst hcd
      rw [coeffAt_coneSingle_same]
      exact ⟨hv, fun h => absurd hc (not_le.mpr h)⟩
    · rw [coeffAt_coneSingle_ne hcd]
      exact ⟨zero_mem _, fun _ => rfl⟩
  have hgood : ∀ z ∈ t, ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧
      (d < c₁ → coeffAt S x d (Ψ z) = 0) := fun z hz => hG (ht z hz)

  let D : Finset ℤ := (t.biUnion fun z => coneSupp (Ψ z)).filter (c₁ ≤ ·)
  let e := (t ×ˢ D).equivFin.symm
  refine ⟨(t ×ˢ D).card, fun j => (e j).1.2, fun j => coeffAt S x (e j).1.2 (Ψ (e j).1.1),
    fun j => ?_, fun c hc y hy => ?_⟩
  · have hm := Finset.mem_product.mp (e j).2
    exact ⟨(Finset.mem_filter.mp hm.2).2, (hgood _ hm.1 _).1⟩
  obtain ⟨z, hz, hzy⟩ := M.exists_cocycle_of_mem_secs hy
  have hzt : z ∈ H0tail M.coneGraded c₁ :=
    (le_iSup₂ (f := fun c (_ : c₁ ≤ c) =>
      Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0) c hc) hz
  let Sp : ℤ → Submodule S Ω := fun d => Submodule.span S {w | ∃ (j : Fin (t ×ˢ D).card) (f : Poly S N)
    (k : ℕ), f.IsHomogeneous k ∧ (k : ℤ) + (e j).1.2 = d ∧ w = aeval x f * coeffAt S x (e j).1.2 (Ψ (e j).1.1)}
  have hmulSp : ∀ (f : Poly S N) (k : ℕ), f.IsHomogeneous k → ∀ d, ∀ u ∈ Sp (d - k),
      aeval x f * u ∈ Sp d := by
    intro f k hf d u hu
    refine Submodule.span_induction (p := fun u _ => aeval x f * u ∈ Sp d) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, g, k', hg, hgk, rfl⟩
      exact Submodule.subset_span ⟨j, f * g, k + k', hf.mul hg, by push_cast; omega,
        by rw [map_mul, mul_assoc]⟩
    · rw [mul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact add_mem ha hb
    · intro s a _ ha; rw [mul_smul_comm]; exact Submodule.smul_mem _ s ha
  have key : ∀ w ∈ Submodule.span (Poly S N) (t : Set (Cech.Cochain (locSys S N M.coneSub) 0)),
      ∀ d, coeffAt S x d (Ψ w) ∈ Sp d := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∀ d, coeffAt S x d (Ψ w) ∈ Sp d) ?_ ?_ ?_ ?_ hw
    · intro z' hz' d
      by_cases h0 : coeffAt S x d (Ψ z') = 0
      · rw [h0]; exact zero_mem _
      · have hd : c₁ ≤ d := by
          by_contra hlt
          exact h0 ((hgood z' hz' d).2 (not_le.mp hlt))
        have hmem : (z', d) ∈ t ×ˢ D := Finset.mem_product.mpr ⟨hz', Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨z', hz', mem_coneSupp.mpr h0⟩, hd⟩⟩
        refine Submodule.subset_span ⟨e.symm ⟨(z', d), hmem⟩, 1, 0, isHomogeneous_one _ _, ?_, ?_⟩
        · simp
        · simp
    · intro d; rw [map_zero, map_zero]; exact zero_mem _
    · intro a b _ _ ha hb d; rw [map_add, map_add]; exact add_mem (ha d) (hb d)
    · intro p a _ ha d
      rw [map_smul, ← sum_homogeneousComponent p, Finset.sum_smul, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [coeffAt_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous k p)]
      exact hmulSp _ k (homogeneousComponent_isHomogeneous k p) d _ (ha (d - k))
  have hyc := key z (hspan hzt) c
  rwa [hΨ, hzy K₀ hK₀, coeffAt_coneSingle_same] at hyc

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AmpleAffineGen

noncomputable section

universe u w

namespace VeryAmpleDim

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs {H : SubSystem k x Ω} {s : Ω} (hs : s ∈ H.secs) (I : Chart x) :
    s ∈ H.sub I :=
  (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp hs I)

theorem ampleBase_le_funField {r : ℕ} (h : Fin (r + 1) → Ω) {j : Fin (r + 1)} (hj : h j ≠ 0) {a : Ω}
    (ha : a ∈ ampleBase (S := k) h j) : a ∈ funField (k := k) h := by
  have hle : ampleBase (S := k) h j ≤ (funField (k := k) h).toSubalgebra :=
    Algebra.adjoin_le (by
      rintro _ ⟨l, rfl⟩
      exact IntermediateField.subset_adjoin k _ ⟨j, l, hj, rfl⟩)
  exact hle ha

theorem mem_funField_of_mem_chartRing {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ chartRing k x (singleChart hi)) : a ∈ funField (k := k) x :=
  ampleBase_le_funField x hi (mem_ampleBase_of_mem_chartRing hi ha)

theorem funField_le (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    funField (k := k) h ≤ funField (k := k) x := by
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, l, hj, rfl⟩
  obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hi)
  have hone : (1 : Ω) ∈ Nb.sub (singleChart hi) * Q' := by
    rw [hQ']; exact Submodule.one_le.mp le_rfl
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hc
    push Not at hc
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hc
    rw [hbot, Submodule.mul_bot] at hone
    exact one_ne_zero ((Submodule.mem_bot _).mp hone)
  have hmem : ∀ l, h l * q ∈ chartRing k x (singleChart hi) := by
    intro l
    have hl := Submodule.mul_mem_mul (mem_sub_of_mem_secs (hv.mem_secs l) (singleChart hi)) hq
    rw [hQ'] at hl
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hl
    rw [← ha]
    exact a.2
  have e : h l / h j = (h l * q) / (h j * q) := (mul_div_mul_right _ _ hq0).symm
  rw [e]
  exact div_mem (mem_funField_of_mem_chartRing hi (hmem l)) (mem_funField_of_mem_chartRing hi (hmem j))

theorem le_funField (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {j₀ : Fin (r + 1)} (hj₀ : h j₀ ≠ 0) :
    funField (k := k) x ≤ funField (k := k) h := by
  classical
  obtain ⟨n, a, b, J, -, hb, hsum, hloc⟩ := hv.affine j₀ hj₀
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hsum
  have hh : ∀ I : Chart x, h j₀ ∈ (Nb.toSubSystem.pow 1).sub I := fun I =>
    Submodule.subset_span ⟨h j₀, mem_sub_of_mem_secs (hv.mem_secs j₀) I, 1,
      one_mem_twistMod_zero (S := k) I, by rw [smul_eq_mul, mul_one]⟩
  have hF : ∀ z ∈ ampleRing Nb.toSubSystem 1 (h j₀), z ∈ funField (k := k) h := fun z hz =>
    ampleBase_le_funField h hj₀ (hv.closed j₀ hj₀ hz)
  obtain ⟨c, hc⟩ := (J t).2.1
  have hxc : x c ≠ 0 := (mem_support x).mp ((J t).2.2 hc)
  have key : ∀ l, x l / x c ∈ funField (k := k) h := by
    intro l
    have hA : x l / x c ∈ chartRing k x (J t) :=
      ⟨X l, X c, 1, X_mem_monos hc, isHomogeneous_X k l, isHomogeneous_X k c, by simp⟩
    have hE : ∀ I : Chart x, ∃ E : ℕ,
        b t ^ E * (x l / x c) ∈ ampleChart Nb.toSubSystem 1 (h j₀) I := by
      intro I
      obtain ⟨e, he⟩ := hloc t I
      obtain ⟨D, hD⟩ := exists_pow_mul_mem I (J t)
        (chartRing_mono (subset_unionChart_right I (J t)) hA)
      refine ⟨e * D, ?_⟩
      rw [← pow_mul_cancel (u := b t) (y := x l / x c) (chartRatio_mul_chartRatio I (J t)) e D]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show _ ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from he) D)
        (mem_ampleSubalg_of_mem_chartRing (hh I) hD)
    choose E hE using hE
    have hmem : b t ^ (∑ I, E I) * (x l / x c) ∈ ampleRing Nb.toSubSystem 1 (h j₀) := by
      refine Set.mem_iInter.mpr fun I => ?_
      have hle : E I ≤ ∑ I, E I := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
      have e : b t ^ (∑ I, E I) * (x l / x c) = b t ^ ((∑ I, E I) - E I) * (b t ^ E I * (x l / x c)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show b t ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from Set.mem_iInter.mp (hb t) I) _)
        (hE I)
    rw [← mul_div_cancel_left₀ (x l / x c) (pow_ne_zero (∑ I, E I) ht)]
    exact div_mem (hF _ hmem) (pow_mem (hF _ (hb t)) _)
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, l, hi, rfl⟩
  have e : x l / x i = (x l / x c) / (x i / x c) := by field_simp
  rw [e]
  exact div_mem (key l) (key i)

end VeryAmpleDim

theorem VeryAmpleDim.proof : VeryAmpleDim.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hx hv
  obtain ⟨i, hi⟩ := hx.relevant
  have hxi : x i ≠ 0 := by
    intro h0
    apply hi
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]
  obtain ⟨j, hj⟩ : ∃ j, h j ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hxi)
    have hbot : Nb.sub (singleChart hxi) = ⊥ := by
      rw [← hv.generates (singleChart hxi), Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      exact hc l
    rw [hbot, Submodule.bot_mul] at hQ'
    have h1 : (1 : Ω) ∈ (⊥ : Submodule (chartRing k x (singleChart hxi)) Ω) := by
      rw [hQ']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hfield : funField (k := k) x = funField (k := k) h :=
    le_antisymm (VeryAmpleDim.le_funField Nb hv hj) (VeryAmpleDim.funField_le Nb hv hxi)
  have hdx : dimCl k x = e := (DimTie.proof k Ω N x (Function.ne_iff.mpr ⟨i, hxi⟩) e).mp hx
  refine (DimTie.proof k Ω r h (Function.ne_iff.mpr ⟨j, hj⟩) e).mpr ?_
  rw [← hdx]
  unfold dimCl
  rw [hfield]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

