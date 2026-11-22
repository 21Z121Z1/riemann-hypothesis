import ReciprocityTheory.GroupCohomology.Bundle0010
import ReciprocityTheory.GroupCohomology.InfIsoA

-- bundled from ReciprocityTheory.GroupCohomology.FiveTerm
section
namespace ReciprocityTheory.Coh

universe u

theorem fiveTerm_holds : FiveTermStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ N _ hN Q P hP I hI
  obtain ⟨tg, -, -, h₁, h₂⟩ := transgression_holds R G M N hN Q P hP I hI
  exact ⟨tg, h₁, h₂⟩

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.InfIsoB
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Inv

variable {N : Subgroup G} [N.Normal]

theorem inv_disc {A : TRep R G} [DiscreteTopology A.V] {Q : TRep R (G ⧸ N)} {P : Pair Q A}
    (hP : IsInvRep A N Q P) : DiscreteTopology Q.V := hP.2.1.discreteTopology

theorem inv_mem {A : TRep R G} {Q : TRep R (G ⧸ N)} {P : Pair Q A} (hP : IsInvRep A N Q P) (q : Q.V) :
    ∀ g ∈ N, A.rho g (P.u q) = P.u q := (hP.2.2 _).1 ⟨q, rfl⟩

theorem inv_equiv {A : TRep R G} {Q : TRep R (G ⧸ N)} {P : Pair Q A} (hP : IsInvRep A N Q P) (g : G)
    (q : Q.V) : P.u (Q.rho (g : G ⧸ N) q) = A.rho g (P.u q) := by
  have h := P.equiv g q
  rw [hP.1] at h
  exact h

def invLin {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)} {PB : Pair QB B}
    (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) : QA.V →ₗ[R] QB.V :=
  (LinearEquiv.ofInjective PB.u hB.2.1.injective).symm.toLinearMap.comp
    ((a.comp PA.u).codRestrict (LinearMap.range PB.u) fun q => (hB.2.2 _).2 fun g hg => by
      rw [LinearMap.comp_apply, ← ha, inv_mem hA q g hg])

theorem invLin_spec {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (q : QA.V) : PB.u (invLin hA hB a ha q) = a (PA.u q) := by
  unfold invLin
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply]
  rfl

def invPair {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)} {PB : Pair QB B}
    [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB) (a : A.V →ₗ[R] B.V)
    (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) : Pair QA QB :=
  have := inv_disc hA
  Pair.ofMap (invLin hA hB a ha) continuous_of_discreteTopology fun y q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    apply hB.2.1.injective
    rw [inv_equiv hB, invLin_spec, invLin_spec, inv_equiv hA, ha]

theorem invPair_u {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB)
    (a : A.V →ₗ[R] B.V) (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (q : QA.V) :
    PB.u ((invPair hA hB a ha).u q) = a (PA.u q) := invLin_spec hA hB a ha q

theorem invPair_comm {A B : TRep R G} {QA : TRep R (G ⧸ N)} {PA : Pair QA A} {QB : TRep R (G ⧸ N)}
    {PB : Pair QB B} [DiscreteTopology A.V] (hA : IsInvRep A N QA PA) (hB : IsInvRep B N QB PB)
    (a : A.V →ₗ[R] B.V) (ha : ∀ g m, a (A.rho g m) = B.rho g (a m)) (hac : Continuous a) (n : ℕ)
    (x : QA.coch.X n) :
    PB.hom.f n ((invPair hA hB a ha).hom.f n x) = (Pair.ofMap a hac ha).hom.f n (PA.hom.f n x) := by
  refine Subtype.ext (funext fun g => ?_)
  show PB.u ((invPair hA hB a ha).u (x.1 fun i => (invPair hA hB a ha).φ (PB.φ (g i)))) =
    a (PA.u (x.1 fun i => PA.φ (g i)))
  rw [invPair_u, hA.1, hB.1]
  rfl

theorem deg0 (A : TRep R G) (Q : TRep R (G ⧸ N)) (P : Pair Q A) (hP : IsInvRep A N Q P) :
    Bijective (P.hom.H 0) := by
  have hsub : ∀ {X : Type u} (f f' : Fin 0 → X), f = f' := fun f f' => Subsingleton.elim _ _
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [InflationRestrictionInvariants.H_mk, InflationRestrictionInvariants.mk_eq_zero_iff] at hz
    have h0 : P.hom.f 0 x = 0 := hz
    have hx0 : x = 0 := by
      refine Subtype.ext (funext fun f => ?_)
      have : P.u (x.1 fun i => P.φ (![] i)) = 0 := congrArg (fun y : A.coch.X 0 => y.1 ![]) h0
      apply hP.2.1.injective
      refine (show P.u (x.1 f) = P.u 0 from ?_)
      rw [map_zero, hsub f (fun i => P.φ (![] i))]
      exact this
    rw [InflationRestrictionInvariants.mk_eq_zero_iff]
    subst hx0
    exact Submodule.zero_mem _
  · intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hy' : A.coch.d 0 y = 0 := hy
    have hinvG : ∀ a, A.rho a (y.1 ![]) = y.1 ![] := fun a => by
      have := congrArg (fun w : A.coch.X 1 => w.1 (InflationRestrictionInvariants.e1 a)) hy'
      simp only [InflationRestrictionInvariants.zeroDifferential_val] at this
      exact sub_eq_zero.1 this
    obtain ⟨q, hq⟩ := (hP.2.2 (y.1 ![])).2 fun g _ => hinvG g
    have hdq : Q.coch.d 0 (InflationRestrictionInvariants.const0 Q q) = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      rw [InflationRestrictionInvariants.oneCochain_apply_fin_one, InflationRestrictionInvariants.zeroDifferential_val]
      show Q.rho (g 0) q - q = 0
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (g 0)
      rw [← ha, sub_eq_zero]
      apply hP.2.1.injective
      rw [inv_equiv hP, hq, hinvG]
    refine ⟨Submodule.Quotient.mk ⟨InflationRestrictionInvariants.const0 Q q, hdq⟩, ?_⟩
    rw [InflationRestrictionInvariants.H_mk]
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun f => ?_))
    show P.u q = y.1 f
    rw [hq, hsub f ![]]

end Inv

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]

abbrev Mbot (M : TRep R G) : TRep R (⊥ : Subgroup (G ⧸ N)) := M.res 1 continuous_const

def evC (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) : Pair QC (Mbot (N := N) M) :=
  have := inv_disc hC
  { φ := (⊥ : Subgroup (G ⧸ N)).subtype
    u := (coindEv (⊥ : Subgroup G) (M.resSub ⊥)).u.comp PC.u
    φ_cont := continuous_subtype_val
    u_cont := continuous_of_discreteTopology
    equiv := fun g m => by
      have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
      subst hg
      show _ = M.rho 1 _
      rw [map_one, map_one, map_one]
      rfl }

theorem evC_rho (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) (q : QC.V) (g : G) :
    (evC M hC).u (QC.rho (g : G ⧸ N) q) = (PC.u q).1 g := by
  show (PC.u (QC.rho (g : G ⧸ N) q)).1 1 = _
  rw [inv_equiv hC]
  show (PC.u q).1 (1 * g) = _
  rw [one_mul]

theorem QC_coind (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) : IsCoind (⊥ : Subgroup (G ⧸ N)) (Mbot M) QC (evC M hC) := by
  have := inv_disc hC
  have : DiscreteTopology (Mbot (N := N) M).V := ‹DiscreteTopology M.V›
  have := cmap_disc (G ⧸ N) (Mbot (N := N) M).V
  let j : QC.V → C(G ⧸ N, (Mbot (N := N) M).V) := fun q =>
    ⟨fun y => (evC M hC).u (QC.rho y q),
      (evC M hC).u_cont.comp (QC.cont.comp (f := fun y => (y, q)) (continuous_id.prodMk continuous_const))⟩
  have hj : ∀ q (g : G), j q (g : G ⧸ N) = (PC.u q).1 g := evC_rho M hC
  refine ⟨rfl, j, emb_disc _ fun q q' h => ?_, fun c g => rfl, fun f _ => ?_⟩
  · apply hC.2.1.injective
    refine Subtype.ext (ContinuousMap.ext fun g => ?_)
    rw [← hj, ← hj, h]
  · let F : (CG M).V := ⟨f.comp ⟨QuotientGroup.mk, continuous_quot_mk⟩, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      subst hx
      show f ((((1 : (⊥ : Subgroup G)) : G) * g : G) : G ⧸ N) = M.rho 1 (f (g : G ⧸ N))
      rw [map_one, Subgroup.coe_one, one_mul]
      rfl⟩
    obtain ⟨q, hq⟩ := (hC.2.2 F).2 fun n hn => Subtype.ext (ContinuousMap.ext fun h => by
      show f ((h * n : G) : G ⧸ N) = f (h : G ⧸ N)
      rw [QuotientGroup.mk_mul_of_mem h hn])
    refine ⟨q, ContinuousMap.ext fun y => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hj, hq]
    rfl

theorem QC_acyc (M : TRep R G) [DiscreteTopology M.V] {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)}
    (hC : IsInvRep (CG M) N QC PC) (m : ℕ) (z : QC.H (m + 1)) : z = 0 := by
  have hq := shapiro_holds R (G ⧸ N) (⊥ : Subgroup (G ⧸ N)) (Mbot M) QC (evC M hC) (QC_coind M hC)
    ⟨fun _ => 1, continuous_const, fun x g => by
      have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 x.2)
      rw [hx, one_mul]⟩
  have : Subsingleton (⊥ : Subgroup (G ⧸ N)) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  refine (hq (m + 1)).1 ?_
  rw [map_zero]
  exact FiniteLevelCohomology.H_succ_trivial _ m _

end InflationIsomorphism

end

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.MemCoboundariesOfCocycleProcyclic
section
namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def tr (M : TRep R G) (f : G × G → M.V) (s : G) : ℕ → M.V
  | 0 => f (1, 1)
  | j + 1 => tr M f s j - f (s ^ j, s)

theorem tr_key (M : TRep R G) (f : G × G → M.V) (hf : f ∈ Z2 M.rho) (s : G) (i j : ℕ) :
    f (s ^ i, s ^ j) = M.rho (s ^ i) (tr M f s j) - tr M f s (i + j) + tr M f s i := by
  have hc := hf.2
  induction j with
  | zero =>
    have e := hc (s ^ i) 1 1
    simp only [mul_one] at e
    rw [sub_add_cancel, sub_eq_zero] at e
    simp only [pow_zero, add_zero]
    rw [sub_add_cancel]
    exact e.symm
  | succ j ih =>
    have e := hc (s ^ i) (s ^ j) s
    rw [← pow_add, ← pow_succ, ih] at e
    have e2 : tr M f s (j + 1) = tr M f s j - f (s ^ j, s) := rfl
    have e3 : tr M f s (i + (j + 1)) = tr M f s (i + j) - f (s ^ (i + j), s) := rfl
    rw [e2, e3, map_sub, ← sub_eq_zero, ← e]
    abel

theorem tr_add (M : TRep R G) (f : G × G → M.V) (s : G) (j t : ℕ) :
    tr M f s (j + t) = tr M f s j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : tr M f s (j + (t + 1)) = tr M f s (j + t) - f (s ^ (j + t), s) := rfl
    rw [e, ih, Finset.sum_range_succ]
    abel

end ProcyclicCohomology

end ReciprocityTheory.Coh

namespace ReciprocityTheory.Coh

namespace ProcyclicCohomology

open ReciprocityTheory.Gal Topology Function

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_coboundaries_of_cocycle_procyclic [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) (f : G × G → M.V) (hf : f ∈ Z2 M.rho) :
    f ∈ B2 M.rho := by
  obtain ⟨N, -, hNo, hconst, hfix⟩ := FiniteLevelCohomology.exists_open_normal M (n := 2)
    (fun v : Fin 2 → G => f (v 0, v 1))
    (hf.1.comp ((continuous_apply 0).prodMk (continuous_apply 1)))
  have hbi : ∀ g h w w', w ∈ N → w' ∈ N → f (g * w, h * w') = f (g, h) := by
    intro g h w w' hw hw'
    have := hconst ![g, h] ![w, w'] (fun i => by fin_cases i <;> simpa)
    simpa using this
  have hfixf : ∀ g h, ∀ a ∈ N, M.rho a (f (g, h)) = f (g, h) := by
    intro g h a ha
    simpa using hfix ![g, h] a ha
  set T := tr M f s
  set n := N.index
  have hsn : s ^ n ∈ N := by simpa using (zpow_mem_iff hc hs hNo (n : ℤ)).2 dvd_rfl

  set a := ∑ i ∈ Finset.range n, f (s ^ i, s)
  have hwin : ∀ j, ∑ i ∈ Finset.range n, f (s ^ (j + i), s) = a := by
    intro j
    induction j with
    | zero => simp [a]
    | succ j ih =>
      have h1 : ∑ i ∈ Finset.range (n + 1), f (s ^ (j + i), s) =
          ∑ i ∈ Finset.range n, f (s ^ (j + 1 + i), s) + f (s ^ (j + 0), s) := by
        rw [Finset.sum_range_succ']
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show j + (i + 1) = j + 1 + i by omega]
      have h2 := Finset.sum_range_succ (fun i => f (s ^ (j + i), s)) n
      have hp : f (s ^ (j + n), s) = f (s ^ (j + 0), s) := by
        rw [pow_add, add_zero]
        simpa using hbi (s ^ j) s (s ^ n) 1 hsn N.one_mem
      rw [← ih]
      rw [hp] at h2
      exact add_right_cancel (h1.symm.trans h2)
  have hTn : ∀ j t, T (j + n * t) = T j - t • a := by
    intro j t
    induction t with
    | zero => simp
    | succ t ih =>
      have htadd : ∀ j t, T (j + t) = T j - ∑ i ∈ Finset.range t, f (s ^ (j + i), s) :=
        tr_add M f s
      rw [Nat.mul_succ, ← add_assoc, htadd, ih, hwin, succ_nsmul]; abel
  obtain ⟨k, hk0, hka⟩ := htor a
  have hn0 : 0 < n := index_pos hc hNo
  obtain ⟨W0, hW0o, hW0i⟩ := hidx (n * k) (Nat.mul_pos hn0 hk0)
  set W := N ⊓ W0
  have hWo : IsOpen (W : Set G) := hNo.inter hW0o
  have hWN : W ≤ N := inf_le_left
  have hdvd : n * k ∣ W.index := hW0i ▸ Subgroup.index_dvd_of_le inf_le_right
  have hper : ∀ j, T (j + W.index) = T j := by
    obtain ⟨t, ht⟩ := hdvd
    intro j; rw [ht]
    refine per_mul _ _ (fun j => ?_) j t
    rw [hTn, hka, sub_zero]
  have hfixT : ∀ w ∈ N, ∀ j, M.rho w (T j) = T j := by
    intro w hw j
    induction j with
    | zero => exact hfixf 1 1 w hw
    | succ j ih =>
      show M.rho w (T j - f (s ^ j, s)) = T j - f (s ^ j, s)
      rw [map_sub, ih, hfixf _ _ w hw]
  have hex := exists_pow hc hs hWo
  refine ⟨desc W hex T, desc_continuous hc hs hWo hex T hper, ?_⟩
  funext ⟨g, h⟩
  have hg := Classical.choose_spec (hex g)
  have hh := Classical.choose_spec (hex h)
  set i := Classical.choose (hex g)
  set j := Classical.choose (hex h)
  have hgh : (g * h)⁻¹ * s ^ (i + j) ∈ W := by
    have e : (g * h)⁻¹ * s ^ (i + j) = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by
      calc (g * h)⁻¹ * s ^ (i + j) = h⁻¹ * (g⁻¹ * s ^ i) * s ^ j := by
            rw [mul_inv_rev, pow_add]; group
        _ = (g⁻¹ * s ^ i) * (h⁻¹ * s ^ j) := by rw [hc h⁻¹ (g⁻¹ * s ^ i), mul_assoc]
    rw [e]; exact W.mul_mem hg hh
  have e1 : desc W hex T (g * h) = T (i + j) := desc_eq hc hs hWo hex _ hper hgh
  have e2 : desc W hex T g = T i := rfl
  have e3 : desc W hex T h = T j := rfl
  have hgeq : g = s ^ i * (g⁻¹ * s ^ i)⁻¹ := by group
  have hheq : h = s ^ j * (h⁻¹ * s ^ j)⁻¹ := by group
  rw [d1_apply, e1, e2, e3]
  have hr : M.rho g (T j) = M.rho (s ^ i) (T j) := by
    conv_lhs => rw [hgeq, map_mul, Module.End.mul_apply]
    rw [hfixT _ (hWN (W.inv_mem hg))]
  have hfv : f (g, h) = f (s ^ i, s ^ j) := by
    conv_lhs => rw [hgeq, hheq]
    exact hbi _ _ _ _ (hWN (W.inv_mem hg)) (hWN (W.inv_mem hh))
  rw [hr, hfv, tr_key M f hf s i j]

theorem subsingleton_H2_of_procyclic_of_torsion [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {s : G}
    (hc : ∀ a b : G, a * b = b * a) (hs : Dense (Subgroup.zpowers s : Set G))
    (hidx : ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k)
    (htor : ∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) : Subsingleton (H2 M.rho) := by
  have hz : ∀ z : H2 M.rho, z = 0 := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_coboundaries_of_cocycle_procyclic M hc hs hidx htor z.1 z.2)
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end ProcyclicCohomology

end ReciprocityTheory.Coh
end

