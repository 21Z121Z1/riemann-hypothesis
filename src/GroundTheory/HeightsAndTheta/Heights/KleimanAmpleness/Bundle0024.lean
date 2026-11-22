import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0017

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefExtendIso
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

namespace NefExtendIso

variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem map_mem_monos_hom {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    {I : Finset (Fin (N + 1))} {s : Kleiman.Poly R N} (hs : s ∈ Kleiman.monos I) :
    map g s ∈ Kleiman.monos (S := R') I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem map_homogeneousComponent {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ)
    (f : Kleiman.Poly R N) : map g (homogeneousComponent d f) = homogeneousComponent d (map g f) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

theorem map_pre (hφ : Function.Bijective (algebraMap S F)) (f : Kleiman.Poly F N) :
    map (algebraMap S F) (map ((RingEquiv.ofBijective _ hφ).symm : F →+* S) f) = f := by
  have hc : (algebraMap S F).comp ((RingEquiv.ofBijective _ hφ).symm : F →+* S) = RingHom.id F :=
    RingHom.ext fun y => (RingEquiv.ofBijective _ hφ).apply_symm_apply y
  rw [map_map, hc, map_id]

theorem mem_chartRing_iff (hφ : Function.Bijective (algebraMap S F)) {I : Kleiman.Chart x} {a : Ω} :
    a ∈ Kleiman.chartRing F x I ↔ a ∈ Kleiman.chartRing S x I := by
  constructor
  · rintro ⟨f, s, e, hs, hf, hse, rfl⟩
    let g : F →+* S := (RingEquiv.ofBijective _ hφ).symm
    refine ⟨map g f, map g s, e, map_mem_monos_hom g hs, hf.map g, hse.map g, ?_⟩
    rw [← aeval_map_algebraMap F x (map g f), ← aeval_map_algebraMap F x (map g s), map_pre hφ,
      map_pre hφ]
  · exact Kleiman.mem_chartRing_extend

theorem span_coe_submodule (hφ : Function.Bijective (algebraMap S F)) (I : Kleiman.Chart x)
    (M : Submodule (Kleiman.chartRing S x I) Ω) :
    ((Submodule.span (Kleiman.chartRing F x I) (M : Set Ω) : Submodule _ Ω) : Set Ω) = M := by
  apply le_antisymm
  · intro z hz
    refine Submodule.span_induction (p := fun z _ => z ∈ M) (fun y hy => hy) M.zero_mem
      (fun _ _ _ _ ha hb => M.add_mem ha hb) ?_ hz
    intro a z _ hz
    have : a • z = (⟨(a : Ω), (mem_chartRing_iff hφ).mp a.2⟩ : Kleiman.chartRing S x I) • z := by
      rw [Kleiman.chartRing_smul_def, Kleiman.chartRing_smul_def]
    rw [this]
    exact M.smul_mem _ hz
  · exact Submodule.subset_span

theorem span_same (hφ : Function.Bijective (algebraMap S F)) (I : Kleiman.Chart x) (P : Set Ω) :
    ((Submodule.span (Kleiman.chartRing S x I) P : Submodule _ Ω) : Set Ω) =
      (Submodule.span (Kleiman.chartRing F x I) P : Submodule _ Ω) := by
  rw [← Kleiman.span_extend_span (S := S) (F := F) I P, span_coe_submodule hφ]

def Same (A : Kleiman.SubSystem S x Ω) (B : Kleiman.SubSystem F x Ω) : Prop :=
  ∀ I, (A.sub I : Set Ω) = B.sub I

theorem same_extend (hφ : Function.Bijective (algebraMap S F)) (Q : Kleiman.SubSystem S x Ω) :
    Same Q (Q.extend F) := fun I => (span_coe_submodule hφ I (Q.sub I)).symm

theorem same_twist (hφ : Function.Bijective (algebraMap S F)) {A A' : Kleiman.SubSystem S x Ω}
    {B B' : Kleiman.SubSystem F x Ω} (h : Same A B) (h' : Same A' B') :
    Same (A.twist A') (B.twist B') := by
  intro I
  have hX : {z : Ω | ∃ q ∈ A'.sub I, ∃ y ∈ A.sub I, z = q • y} =
      {z : Ω | ∃ q ∈ B'.sub I, ∃ y ∈ B.sub I, z = q • y} := by
    ext z
    constructor
    · rintro ⟨q, hq, y, hy, rfl⟩
      exact ⟨q, (Set.ext_iff.mp (h' I) q).mp hq, y, (Set.ext_iff.mp (h I) y).mp hy, rfl⟩
    · rintro ⟨q, hq, y, hy, rfl⟩
      exact ⟨q, (Set.ext_iff.mp (h' I) q).mpr hq, y, (Set.ext_iff.mp (h I) y).mpr hy, rfl⟩
  change ((Submodule.span (Kleiman.chartRing S x I) {z : Ω | ∃ q ∈ A'.sub I, ∃ y ∈ A.sub I, z = q • y} :
      Submodule _ Ω) : Set Ω) =
    (Submodule.span (Kleiman.chartRing F x I) {z : Ω | ∃ q ∈ B'.sub I, ∃ y ∈ B.sub I, z = q • y} :
      Submodule _ Ω)
  rw [← hX, span_same hφ]

theorem same_twistSys (hφ : Function.Bijective (algebraMap S F)) (c : ℤ) :
    Same (Kleiman.twistSys S x c) (Kleiman.twistSys F x c) := by
  have := same_extend hφ (Kleiman.twistSys S x c)
  rwa [Kleiman.SubSystem.extend_twistSys] at this

theorem same_tensorSub (hφ : Function.Bijective (algebraMap S F)) {n : ℕ}
    {L : Fin n → Kleiman.SubSystem S x Ω} {L' : Fin n → Kleiman.SubSystem F x Ω}
    (hL : ∀ i, Same (L i) (L' i)) (T : Finset (Fin n)) :
    Same (Kleiman.tensorSub L T) (Kleiman.tensorSub L' T) := by
  have key : ∀ (l : List (Fin n)) (A : Kleiman.SubSystem S x Ω) (B : Kleiman.SubSystem F x Ω),
      Same A B → Same (l.foldl (fun G i => G.twist (L i)) A) (l.foldl (fun G i => G.twist (L' i)) B) := by
    intro l
    induction l with
    | nil => intro A B h; exact h
    | cons i l ih => intro A B h; exact ih _ _ (same_twist hφ h (hL i))
  exact key _ _ _ (same_twistSys hφ 0)

theorem same_idealSys (hφ : Function.Bijective (algebraMap S F)) (p' : Ideal (Kleiman.Poly F N)) :
    Same (Kleiman.idealSys x (p'.comap (map (algebraMap S F)))) (Kleiman.idealSys x p') := by
  intro I
  let g : F →+* S := (RingEquiv.ofBijective _ hφ).symm
  have hG : {a : Ω | ∃ (f s : Kleiman.Poly S N) (e : ℕ), f ∈ p'.comap (map (algebraMap S F)) ∧
      s ∈ Kleiman.monos I.1 ∧ f.IsHomogeneous e ∧ s.IsHomogeneous e ∧ a = aeval x f / aeval x s} =
      {a : Ω | ∃ (f s : Kleiman.Poly F N) (e : ℕ), f ∈ p' ∧ s ∈ Kleiman.monos I.1 ∧ f.IsHomogeneous e ∧
        s.IsHomogeneous e ∧ a = aeval x f / aeval x s} := by
    ext a
    constructor
    · rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      exact ⟨map (algebraMap S F) f, map (algebraMap S F) s, e, Ideal.mem_comap.mp hf,
        map_mem_monos_hom _ hs, hfe.map _, hse.map _, by
          rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩
    · rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      refine ⟨map g f, map g s, e, Ideal.mem_comap.mpr (by rwa [map_pre hφ]),
        map_mem_monos_hom g hs, hfe.map g, hse.map g, ?_⟩
      rw [← aeval_map_algebraMap F x (map g f), ← aeval_map_algebraMap F x (map g s), map_pre hφ,
        map_pre hφ]
  change ((Submodule.span (Kleiman.chartRing S x I) _ : Submodule _ Ω) : Set Ω) =
    (Submodule.span (Kleiman.chartRing F x I) _ : Submodule _ Ω)
  rw [hG, span_same hφ]

omit [Algebra S F] [IsScalarTower S F Ω] in

theorem same_secs {A : Kleiman.SubSystem S x Ω} {B : Kleiman.SubSystem F x Ω} (h : Same A B) :
    (A.secs : Set Ω) = B.secs := by
  ext z
  simp only [SetLike.mem_coe, Kleiman.SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  exact forall_congr' fun I => Set.ext_iff.mp (h I) z

theorem length_quot_eq (hφ : Function.Bijective (algebraMap S F)) (X Y : Submodule S Ω)
    (X' Y' : Submodule F Ω) (hX : (X : Set Ω) = X') (hY : (Y : Set Ω) = Y') :
    Module.length S (X ⧸ Y.comap X.subtype) = Module.length F (X' ⧸ Y'.comap X'.subtype) := by
  obtain rfl : X = X'.restrictScalars S := SetLike.coe_injective hX
  obtain rfl : Y = Y'.restrictScalars S := SetLike.coe_injective hY
  rw [← Module.length_eq_of_surjective (S := S) hφ.2]
  exact (Submodule.Quotient.restrictScalarsEquiv S (Y'.comap X'.subtype)).length_eq

theorem restrLen_eq (hφ : Function.Bijective (algebraMap S F)) {p : Ideal (Kleiman.Poly S N)}
    {p' : Ideal (Kleiman.Poly F N)} (hp : Same (Kleiman.idealSys x p) (Kleiman.idealSys x p'))
    {A : Kleiman.SubSystem S x Ω} {B : Kleiman.SubSystem F x Ω} (h : Same A B) :
    Kleiman.restrLen p A = Kleiman.restrLen p' B := by
  unfold Kleiman.restrLen
  rw [length_quot_eq hφ _ _ _ _ (same_secs h) (same_secs (same_twist hφ h hp))]

theorem interNum_extend (hφ : Function.Bijective (algebraMap S F)) (Q : Kleiman.SubSystem S x Ω)
    (p' : Ideal (Kleiman.Poly F N)) :
    Kleiman.interNum p' ![Q.extend F] = Kleiman.interNum (p'.comap (map (algebraMap S F))) ![Q] := by
  have hL : ∀ i, Same (![Q] i) (![Q.extend F] i) := Fin.forall_fin_one.mpr (same_extend hφ Q)
  unfold Kleiman.interNum
  congr 1
  funext c
  unfold Kleiman.interSum
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [restrLen_eq hφ (same_idealSys hφ p')
    (same_twist hφ (same_tensorSub hφ hL T) (same_twistSys hφ (c : ℤ)))]

theorem isSubvar_comap (hφ : Function.Bijective (algebraMap S F)) {p' : Ideal (Kleiman.Poly F N)} {e : ℕ}
    (hp' : Kleiman.IsSubvar x p' e) : Kleiman.IsSubvar x (p'.comap (map (algebraMap S F))) e where
  isPrime := by have := hp'.isPrime; exact Ideal.comap_isPrime _ _
  homog f hf d := by
    rw [Ideal.mem_comap, map_homogeneousComponent]
    exact hp'.homog _ hf d
  le f hf := by
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen] at hf
    apply hp'.le
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen, aeval_map_algebraMap]
    exact hf
  relevant := by
    obtain ⟨i, hi⟩ := hp'.relevant
    exact ⟨i, fun h => hi (by rwa [Ideal.mem_comap, map_X] at h)⟩
  dim := by
    let e' : Kleiman.Poly S N ≃+* Kleiman.Poly F N := mapEquiv _ (RingEquiv.ofBijective _ hφ)
    have he : (e' : Kleiman.Poly S N →+* Kleiman.Poly F N) = map (algebraMap S F) := RingHom.ext fun _ => rfl
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ p' e' ?_)).trans hp'.dim
    rw [he, Ideal.map_comap_of_surjective _ (fun f => ⟨_, map_pre hφ f⟩)]

end NefExtendIso

theorem NefExtendIso.proof : NefExtendIso.Statement := by
  intro S _ F _ _ Ω _ _ _ _ N x Q hφ hQ p' _ hp'
  rw [NefExtendIso.interNum_extend hφ Q p']
  exact hQ _ bot_le (NefExtendIso.isSubvar_comap hφ hp')

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointGenerated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace PointGenerated

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem inv_mem_chartRing (hx : IsSubvar x (primeOf (S := k) x) 0) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing k x I) : a⁻¹ ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set K := (HilbertPoint.affRing k x i).toIntermediateField' (HilbertPoint.isField_affRing hx hxi)

  have h1 : ∀ b ∈ K, b ∈ chartRing k x I := by
    intro b hb
    change b ∈ HilbertPoint.affRing k x i at hb
    rw [HilbertPoint.affRing, ← Algebra.adjoin_range_eq_range_aeval] at hb
    refine Algebra.adjoin_le (S := chartRing k x I) ?_ hb
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X k l, isHomogeneous_X k i, by
      simp [HilbertPoint.aff]⟩

  have h2 : a ∈ K := by
    obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
    have hs0 := eval_ne_zero_of_mem_monos I hs
    have hxe : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    have heq : aeval x f / aeval x s =
        aeval (HilbertPoint.aff x i) f / aeval (HilbertPoint.aff x i) s := by
      rw [HilbertPoint.aff_def, aeval_div_of_isHomogeneous hf, aeval_div_of_isHomogeneous hse]
      field_simp
    rw [heq]
    exact div_mem (show _ ∈ HilbertPoint.affRing k x i from ⟨f, rfl⟩)
      (show _ ∈ HilbertPoint.affRing k x i from ⟨s, rfl⟩)
  exact h1 _ (inv_mem h2)

theorem mem_sub_iff_of_subset (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) {I J : Chart x}
    (h : I.1 ⊆ J.1) (y : Ω) : y ∈ Q.sub J ↔ y ∈ Q.sub I := by
  refine ⟨fun hy => ?_, Q.mono I J h y⟩
  obtain ⟨a, ha, hay⟩ := (Q.mem_iff I J h y).mp hy
  have ha0 : (a : Ω) ≠ 0 := by
    intro h0
    apply ha.ne_zero
    exact Subtype.ext h0
  have hy' : y = (⟨(a : Ω)⁻¹, inv_mem_chartRing hx I a.2⟩ : chartRing k x I) • ((a : Ω) • y) := by
    rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  rw [hy']
  exact Submodule.smul_mem _ _ hay

theorem mem_sub_iff (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) (I J : Chart x)
    (y : Ω) : y ∈ Q.sub I ↔ y ∈ Q.sub J := by
  let K : Chart x := ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩
  rw [← mem_sub_iff_of_subset hx Q (show I.1 ⊆ K.1 from Finset.subset_union_left),
    mem_sub_iff_of_subset hx Q (show J.1 ⊆ K.1 from Finset.subset_union_right)]

end PointGenerated

theorem PointGenerated.proof : PointGenerated.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q hx I
  have hsecs : ∀ y, y ∈ Q.toSubSystem.secs ↔ y ∈ Q.sub I := by
    intro y
    rw [SubSystem.secs, Submodule.mem_iInf]
    exact ⟨fun h => h I, fun h J => (PointGenerated.mem_sub_iff hx Q I J y).mp h⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    exact (hsecs y).mp hy
  · intro y hy
    exact Submodule.subset_span ((hsecs y).mpr hy)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PQuotSectionsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra

theorem QuotSectionsFinite.proof (hE : Extension.Statement.{u, w, w})
    (hI : IdealTwistFamily.Statement.{u, w}) (hT : TildeFinite.Statement.{u, w})
    (hQ : QuotientH0Finite.Statement.{u, w, w}) : QuotSectionsFinite.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q J

  let J' : Ideal (Poly k N) := Ideal.span {f | f ∈ J ∧ ∃ e, f.IsHomogeneous e}
  have hJ'hom : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J' := by
    have h : J'.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
      Ideal.homogeneous_span _ _ fun f hf =>
        ⟨_, (mem_homogeneousSubmodule _ f).mpr hf.2.choose_spec⟩
    exact fun p hp d => homogeneousComponent_mem_of_mem h hp d
  have hforms : ∀ (f : Poly k N) (e : ℕ), f.IsHomogeneous e → (f ∈ J ↔ f ∈ J') := fun f e hf =>
    ⟨fun h => Ideal.subset_span ⟨h, e, hf⟩, fun h => (Ideal.span_le.mpr fun _ hg => hg.1) h⟩
  have hsys : idealSys x J = idealSys x J' := SubSystem.ext_sub fun I => by
    change idealMod J I = idealMod J' I
    unfold idealMod
    congr 1
    ext a
    constructor <;> rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mp hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mpr hf, hs, hfe, hse, rfl⟩

  obtain ⟨F, hF, hFfg⟩ := hI k Ω N x Q J' hJ'hom
  obtain ⟨M, -, hM⟩ := hE k Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨M', -, hM'⟩ := hE k Ω N x Ω F hFfg
  have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
  have h1 : M'.tildeSys 0 = Q.toSubSystem.twist (idealSys x J) := by
    rw [hsys, ← hF]
    exact SubSystem.ext_sub hM'

  have hle : ∀ I, (Q.toSubSystem.twist (idealSys x J)).sub I ≤ Q.toSubSystem.sub I := by
    intro I
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.span_induction (p := fun q _ => q • y ∈ Q.sub I) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨f, s, e, _, hs, hf, hse, rfl⟩
      exact (Q.sub I).smul_mem ⟨_, ⟨f, s, e, hs, hf, hse, rfl⟩⟩ hy
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq'; rw [smul_assoc]; exact Submodule.smul_mem _ a hq'
  have hH0 : Module.Finite k (Q.toSubSystem.H 0) := by
    rw [← h0]; exact hT k Ω N x M 0 0
  have hH1 : Module.Finite k ((Q.toSubSystem.twist (idealSys x J)).H 1) := by
    rw [← h1]; exact hT k Ω N x M' 1 0
  exact hQ k Ω N x Ω Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) hle hH0 hH1

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

theorem SectionCount.proof (hT : SectionCount.Top.Statement.{u, w})
    (hD : SectionCount.Drop.Statement.{u, w}) : SectionCount.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨C₁, h₁⟩ := hT k Ω N x d Nb hZ hN
  obtain ⟨C₂, h₂⟩ := hD k Ω N x d Nb b hZ hN hb
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n hn₁ hn₂ hn
  set f : ℕ → ℝ := fun i =>
    (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) with hf
  set Y : ℝ := (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) with hY
  set X : ℝ := (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω)
    (twistSys k x (b : ℤ)) (fun _ : Fin d => Nb.toSubSystem)) : ℝ) with hX
  have h0 : f 0 = (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) :=
    congrArg (fun m : ℤ => (Module.finrank k (twistMul Nb.toSubSystem n m).secs : ℝ)) (by simp)
  have htel : f 0 - f n = ∑ i ∈ Finset.range n, (f i - f (i + 1)) := by
    rw [Finset.sum_range_sub']
  have hsum : ∑ i ∈ Finset.range n, (f i - f (i + 1)) ≤
      ∑ _i ∈ Finset.range n, (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) :=
    Finset.sum_le_sum fun i hi => hn₂ i (Finset.mem_range.mp hi)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : ((d + 1).factorial : ℝ) = ((d : ℝ) + 1) * (d.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have key : (n : ℝ) * (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) =
      ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) + C₂ * (n : ℝ) ^ d := by
    rw [hfac]; field_simp; ring
  rw [key] at hsum
  rw [← h0] at hn₁
  have hgoal : f n = (Module.finrank k (twistMul Nb.toSubSystem n (-((n : ℤ) * b))).secs : ℝ) := rfl
  rw [← hgoal]
  push_cast
  have e1 : (Y - ((d : ℝ) + 1) * X) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) =
      Y * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) -
        ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by ring
  rw [e1]
  linarith

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

theorem SubvarDrop.proof : SubvarDrop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d pp hx hpp hhom hle hrel hf
  have := hpp
  obtain ⟨f, hfp, hfq⟩ := hf
  obtain ⟨j, hj⟩ := hrel

  have hup : ringKrullDim (Poly k N ⧸ pp) + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hx.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hfp

  have hnf : ¬ IsField (Poly k N ⧸ pp) := by
    intro hF
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel (a := Ideal.Quotient.mk pp (X j))
      (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk pp), Ideal.Quotient.eq] at hv
    have h0 := hhom _ hv 0
    rw [homogeneousComponent_zero] at h0
    have h1 : (1 : Poly k N) ∈ pp := by
      have hc : coeff 0 (X j * g - 1 : Poly k N) = -1 := by
        change constantCoeff (X j * g - 1 : Poly k N) = -1; simp
      rw [hc, map_neg, map_one] at h0
      simpa using pp.neg_mem h0
    exact hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hne0 : ringKrullDim (Poly k N ⧸ pp) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ pp) := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr h0
    exact hnf Ring.KrullDimLE.isField_of_isDomain
  have hnn : 0 ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_nonneg_of_nontrivial

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize hD : ringKrullDim (Poly k N ⧸ pp) = D at hup hne0 hnn
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe n =>
      obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by
        have : n ≠ 0 := by rintro rfl; exact hne0 rfl
        omega⟩
      refine ⟨e, ?_, ⟨hpp, hhom, hle, ⟨j, hj⟩, hD⟩⟩
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have : ((e + 1 + 1 : ℕ) : ℕ∞) ≤ ((d + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have := Nat.cast_le.mp this
      omega

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def RestrLenRestrict.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (K' : Type w) [Field K'] [Algebra k K'] (y : Fin (N + 1) → K') (hxy : ∀ i, y i ≠ 0 → x i ≠ 0),
    primeOf (S := k) x ≤ primeOf (S := k) y →
    ∀ (pp : Ideal (Poly k N)) (e : ℕ), IsSubvar y pp e →
    ∀ (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∀ᶠ c : ℕ in atTop, restrLen pp (Q'.toSubSystem.twist (twistSys k y (c : ℤ))) =
        restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

