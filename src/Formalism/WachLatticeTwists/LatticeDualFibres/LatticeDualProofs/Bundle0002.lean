import Formalism.WachLatticeTwists.LatticeDualFibres.Bundle0001
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.Bundle0001

-- bundled from Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ConnTors
section
universe u
open ReciprocityTheory.Gal
namespace Formalism.RepresentationBoundsCohomology.LOC

theorem connTors : StatConnTors.{u} := by
  intro O G T V A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρT ρV ρA j q hj ej eq hq hker hc hdiv htors
  classical
  have hjinj : Function.Injective j := hj.injective
  let W : Submodule O V := (H0 ρA).comap q
  have hW : ∀ v ∈ W, ∀ g, ∃ t, j t = ρV g v - v := by
    intro v hv g
    have h : ρV g v - v ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, eq, (mem_riemannRochSpace_iff_regularAt_everywhere ρA _).1 hv g, sub_self]
    rw [hker] at h
    exact h
  choose! s hs using hW
  let c : W →ₗ[O] Z1 ρT :=
    { toFun := fun v => ⟨fun g => s v g, by
          refine ⟨hj.continuous_iff.2 ?_, fun g h => hjinj ?_⟩
          · have : (j ∘ fun g => s (v:V) g) = fun g => ρV g v - v := funext fun g => hs v v.2 g
            rw [this]
            exact (hc.comp (continuous_id.prodMk continuous_const)).sub continuous_const
          · rw [map_add, ej, hs v v.2, hs v v.2, hs v v.2, map_mul, Module.End.mul_apply, map_sub]
            abel⟩
      map_add' := fun v w => Subtype.ext (funext fun g => hjinj (by
          show j (s ((v + w : W) : V) g) = j (s v g + s w g)
          rw [map_add, hs _ (v+w).2, hs v v.2, hs w w.2, Submodule.coe_add, map_add]; abel))
      map_smul' := fun r v => Subtype.ext (funext fun g => hjinj (by
          show j (s ((r • v : W) : V) g) = j (r • s v g)
          rw [map_smul, hs _ (r • v).2, hs v v.2, Submodule.coe_smul, map_smul, smul_sub])) }
  let δ0 : W →ₗ[O] H1 ρT := (Submodule.mkQ _).comp c
  let qW : W →ₗ[O] H0 ρA := q.restrict (fun v hv => hv)
  have hqW : Function.Surjective qW := fun a => by
    obtain ⟨v, hv⟩ := hq a
    exact ⟨⟨v, by show q v ∈ H0 ρA; rw [hv]; exact a.2⟩, Subtype.ext hv⟩
  have hk : LinearMap.ker qW ≤ LinearMap.ker δ0 := by
    intro v hv
    have h1 : q v = 0 := congrArg Subtype.val hv
    have h2 : (v:V) ∈ LinearMap.range j := hker ▸ h1
    obtain ⟨t, ht⟩ := h2
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (c v) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_coboundaries1 _ _).2 ⟨t, fun g => hjinj ?_⟩
    show j (s v g) = _
    rw [hs v v.2, map_sub, ej, ht]
  let δ : H0 ρA →ₗ[O] H1 ρT :=
    ((LinearMap.ker qW).liftQ δ0 hk).comp (qW.quotKerEquivOfSurjective hqW).symm.toLinearMap
  have hδ : ∀ v : W, δ (qW v) = δ0 v := by
    intro v
    have : (qW.quotKerEquivOfSurjective hqW).symm (qW v) = Submodule.Quotient.mk v :=
      (LinearEquiv.symm_apply_eq _).2 rfl
    show (LinearMap.ker qW).liftQ δ0 hk ((qW.quotKerEquivOfSurjective hqW).symm (qW v)) = _
    rw [this]; rfl
  refine ⟨δ, ?_⟩
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c0, hc0, hca⟩ := htors a
    refine (Submodule.mem_torsion_iff _).2 ⟨⟨c0, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
    show c0 • δ a = 0
    rw [← map_smul, show c0 • a = 0 from Subtype.ext hca, map_zero]
  · intro hx
    obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff _).1 hx
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      have hn' : (Submodule.Quotient.mk ((n : O) • z) : H1 ρT) = 0 := hn
      rw [Submodule.Quotient.mk_eq_zero] at hn'
      obtain ⟨t, ht⟩ := (mem_coboundaries1 _ _).1 hn'
      have hn0 : (n : O) ≠ 0 := nonZeroDivisors.coe_ne_zero n
      obtain ⟨v, hv⟩ := (hdiv n hn0).2 (j t)
      have hv' : (n : O) • v = j t := hv
      have hz : ∀ g, ρV g v - v = j (z.1 g) := by
        intro g
        apply (hdiv n hn0).1
        show (n : O) • (ρV g v - v) = (n : O) • j (z.1 g)
        have e := ht g
        have e' : (n : O) • z.1 g = ρT g t - t := e
        rw [smul_sub, ← map_smul, hv', ← ej, ← map_sub, ← e', map_smul]
      have hvW : v ∈ W := by
        refine (mem_riemannRochSpace_iff_regularAt_everywhere ρA _).2 fun g => ?_
        have : q (ρV g v - v) = 0 := by
          rw [hz g]
          exact LinearMap.mem_ker.1 (hker ▸ LinearMap.mem_range_self j _)
        rw [map_sub, eq, sub_eq_zero] at this
        exact this
      refine ⟨qW ⟨v, hvW⟩, ?_⟩
      rw [hδ]
      show Submodule.Quotient.mk (c ⟨v, hvW⟩) = Submodule.Quotient.mk z
      congr 1
      refine Subtype.ext (funext fun g => hjinj ?_)
      show j (s v g) = _
      rw [hs v hvW, hz]

end Formalism.RepresentationBoundsCohomology.LOC
end

-- bundled from Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsBasisOfLattice
section
universe u

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

open Module

namespace Lat2

section SlopeTestRemainingChoices

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem map_frac_smul {V W : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup W] [Module O W] [Module (FractionRing O) W]
    [IsScalarTower O (FractionRing O) W] (f : V →ₗ[O] W) (c : FractionRing O) (x : V) :
    f (c • x) = c • f x :=
  (f.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)).map_smul c x

section One

variable {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V']
  [IsScalarTower O (FractionRing O) V']

theorem exists_basis_of_lattice {T : Submodule O V} (hT : IsLatticeIn T) :
    ∃ (n : ℕ) (e : Basis (Fin n) (FractionRing O) V),
      T = Submodule.span O (Set.range e) ∧ finrank O T = n := by
  have : Submodule.IsLattice (FractionRing O) T := ⟨hT.1, hT.2⟩
  let B := Module.finBasis O T
  refine ⟨_, B.extendOfIsLattice (FractionRing O), ?_, rfl⟩
  have h : Set.range (B.extendOfIsLattice (FractionRing O)) = T.subtype '' Set.range B := by
    rw [← Set.range_comp]
    congr 1
    ext i
    simp
  rw [h, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem isLatticeIn_span_basis {n : ℕ} (e : Basis (Fin n) (FractionRing O) V) :
    IsLatticeIn (Submodule.span O (Set.range e)) := by
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  rw [Submodule.span_span_of_tower, e.span_eq]

theorem finrank_span_basis {n : ℕ} (e : Basis (Fin n) (FractionRing O) V) :
    finrank O (Submodule.span O (Set.range e)) = n := by
  have h : LinearIndependent O e :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).2 e.linearIndependent
  rw [finrank_span_eq_card h, Fintype.card_fin]

theorem exists_dual_basis {b : V →ₗ[O] V' →ₗ[O] FractionRing O} (hb : PerfectRight b) {n : ℕ}
    (e : Basis (Fin n) (FractionRing O) V) :
    ∃ f : Basis (Fin n) (FractionRing O) V',
      (∀ i x, e.repr x i = b x (f i)) ∧ (∀ i w, f.repr w i = b (e i) w) := by
  choose f hf using fun i => (hb (e.coord i)).exists
  have hexp : ∀ w : V', w = ∑ i, b (e i) w • f i := by
    intro w
    refine (hb ((b.flip w).extendScalarsOfIsLocalization (nonZeroDivisors O)
      (FractionRing O))).unique (fun x => rfl) (fun x => ?_)
    rw [LinearMap.extendScalarsOfIsLocalization_apply', LinearMap.flip_apply, map_sum]
    conv_rhs => rw [← e.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_frac_smul, hf, map_frac_smul b, LinearMap.smul_apply, Basis.coord_apply, smul_eq_mul,
      smul_eq_mul, mul_comm]
  have hli : LinearIndependent (FractionRing O) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := congrArg (b (e j)) hc
    rw [map_sum, map_zero] at h
    rw [← h, Finset.sum_eq_single j]
    · rw [map_frac_smul, hf, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    · intro i _ hij
      rw [map_frac_smul, hf, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne hij,
        smul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range f) := by
    intro w _
    rw [hexp w]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨Basis.mk hli hsp, fun i x => ?_, fun i w => ?_⟩
  · rw [Basis.mk_apply, hf, Basis.coord_apply]
  · conv_lhs => rw [hexp w]
    have : ∑ i, b (e i) w • f i = ∑ i, b (e i) w • (Basis.mk hli hsp) i := by
      simp only [Basis.mk_apply]
    rw [this, Basis.repr_sum_self]

omit [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] in

theorem dualLat_span {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {n : ℕ} (e : Fin n → V)
    (f : Basis (Fin n) (FractionRing O) V') (h : ∀ i w, f.repr w i = b (e i) w) :
    dualLat b (Submodule.span O (Set.range e)) = Submodule.span O (Set.range f) := by
  ext w
  rw [Basis.mem_span_iff_repr_mem]
  constructor
  · intro hw i
    rw [h]
    exact Submodule.mem_one.1 (hw (e i) (Submodule.subset_span (Set.mem_range_self i)))
  · intro hw
    have hle : Submodule.span O (Set.range e) ≤
        (1 : Submodule O (FractionRing O)).comap (b.flip w) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have := hw i
      rw [h] at this
      exact Submodule.mem_one.2 this
    exact fun x hx => hle hx

theorem dualLat_props {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V}
    (hT : IsLatticeIn T) (hb : PerfectRight b) :
    IsLatticeIn (dualLat b T) ∧ finrank O (dualLat b T) = finrank O T ∧
      dualLat b.flip (dualLat b T) = T := by
  obtain ⟨n, e, hTe, hn⟩ := exists_basis_of_lattice hT
  obtain ⟨f, h1, h2⟩ := exists_dual_basis hb e
  have hd : dualLat b T = Submodule.span O (Set.range f) := by
    rw [hTe]; exact dualLat_span e f h2
  refine ⟨?_, ?_, ?_⟩
  · rw [hd]; exact isLatticeIn_span_basis f
  · rw [hd, hn]; exact finrank_span_basis f
  · rw [hd, hTe]; exact dualLat_span (b := b.flip) f e h1

omit [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
  [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V'] in

theorem dualLat_stable {G : Type u} [Group G] {ε : G →* Oˣ} {ρ : Representation O G V}
    {ρ' : Representation O G V'} {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V}
    (hs : StableUnder ρ T) (he : EquivPair ε ρ ρ' b) : StableUnder ρ' (dualLat b T) := by
  intro g f hf x hx
  have hx' : x = ρ g (ρ g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hx', he]
  exact Submodule.smul_mem _ _ (hf _ (hs g⁻¹ x hx))

end One

end SlopeTestRemainingChoices

end Lat2

open Lat2

theorem dualLattice : StatDualLattice.{u} := by
  intro O G V V' _ _ _ _ _ _ _ _ _ _ _ _ ε ρ ρ' b T hT hs hb he
  obtain ⟨h1, h2, h3⟩ := dualLat_props hT hb
  exact ⟨h1, h2, dualLat_stable hs he, h3⟩

namespace Lat2

section Fib

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {VY VT VY' VT' : Type u}
  [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY] [IsScalarTower O (FractionRing O) VY]
  [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT'] [Module O VT']

omit [IsDomain O] [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in
theorem zero_mem_fibre {Y : Submodule O VY} {T : Submodule O VT} (φ : Y →ₗ[O] VT ⧸ T) {x : VT}
    (hx : x ∈ T) : ((0 : VY), x) ∈ fibre Y T φ := by
  refine ⟨Y.zero_mem, ?_⟩
  have : (⟨((0 : VY), x).1, Y.zero_mem⟩ : Y) = 0 := rfl
  rw [this, map_zero]
  exact ((Submodule.Quotient.mk_eq_zero T).2 hx).symm

def pairB (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O) (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) :
    (VY × VT) →ₗ[O] (VT' × VY') →ₗ[O] FractionRing O :=
  bY.compl₁₂ (LinearMap.fst O VY VT) (LinearMap.snd O VT' VY') -
    bT.compl₁₂ (LinearMap.snd O VY VT) (LinearMap.fst O VT' VY')

omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in
theorem pairB_apply (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (p : VY × VT) (q : VT' × VY') :
    pairB bY bT p q = bY p.1 q.2 - bT p.2 q.1 := rfl

omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in

theorem fibreDual_eq (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (Y : Submodule O VY) (T : Submodule O VT)
    (φ : Y →ₗ[O] VT ⧸ T) :
    fibreDual bY bT Y T φ = dualLat (pairB bY bT) (fibre Y T φ) := by
  ext ⟨f, g⟩
  constructor
  · rintro ⟨_, h2⟩ ⟨y, x⟩ ⟨hy, hφ⟩
    rw [pairB_apply]
    exact h2 ⟨y, hy⟩ x hφ
  · intro h
    refine ⟨fun x hx => ?_, fun y x hyx => ?_⟩
    · have := h (0, x) (zero_mem_fibre φ hx)
      rw [pairB_apply] at this
      simp only [map_zero, LinearMap.zero_apply, zero_sub] at this
      exact (Submodule.neg_mem_iff _).1 this
    · have := h (y, x) ⟨y.2, hyx⟩
      rw [pairB_apply] at this
      exact this

omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT] in

theorem zero_mem_fibreDual_iff (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (Y : Submodule O VY) (T : Submodule O VT)
    (φ : Y →ₗ[O] VT ⧸ T) (g : VY') :
    ((0 : VT'), g) ∈ fibreDual bY bT Y T φ ↔ g ∈ dualLat bY Y := by
  constructor
  · rintro ⟨_, h⟩ y hy
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective T (φ ⟨y, hy⟩)
    have := h ⟨y, hy⟩ x hx.symm
    simpa using this
  · intro h
    refine ⟨Submodule.zero_mem _, fun y x _ => ?_⟩
    have := h y y.2
    simpa using this

end Fib

end Lat2

end Formalism.RepresentationBoundsCohomology.LOC
end
end

-- bundled from Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
section
universe u

open Formalism.NG (KO)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

section SlopeTestRemainingChoices

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_pow_smul_integral {ϖ : O} (hϖ : Irreducible ϖ) (k : FractionRing O) :
    ∃ (n : ℕ) (a : O), (ϖ ^ n) • k = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, a * ((w⁻¹ : Oˣ) : O), ?_⟩
  have hne : algebraMap O (FractionRing O) ((w : O) * ϖ ^ n) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hb0
  rw [Algebra.smul_def, ← mul_div_assoc, div_eq_iff hne, ← map_mul, ← map_mul]
  congr 1
  have : ((w⁻¹ : Oˣ) : O) * (w : O) = 1 := by simp
  calc ϖ ^ n * a = ϖ ^ n * a * (((w⁻¹ : Oˣ) : O) * (w : O)) := by rw [this, mul_one]
    _ = a * ((w⁻¹ : Oˣ) : O) * ((w : O) * ϖ ^ n) := by ring

theorem exists_pow_smul_mem {V : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] {T : Submodule O V}
    (hT : Submodule.span (FractionRing O) (T : Set V) = ⊤) {ϖ : O} (hϖ : Irreducible ϖ) (x : V) :
    ∃ n : ℕ, (ϖ ^ n) • x ∈ T := by
  have hx : x ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact T.smul_mem _ hn
    · rw [pow_add, mul_smul]; exact T.smul_mem _ hm
  | smul k x _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, a, ha⟩ := exists_pow_smul_integral hϖ k
    refine ⟨m + n, ?_⟩
    have : (ϖ ^ (m + n)) • k • x = a • (ϖ ^ n) • x := by
      rw [pow_add, mul_comm, mul_smul, ← smul_assoc (ϖ ^ m) k x, ha, algebraMap_smul,
        smul_comm]
    rw [this]; exact T.smul_mem _ hn

end SlopeTestRemainingChoices

theorem quotEmbeds : StatQuotEmbeds.{u} := by
  intro O V _ _ _ _ _ _ _ T hT
  have hfin : Module.Finite O T := Module.Finite.iff_fg.mpr hT.1
  have htfV : Module.IsTorsionFree O V := Module.IsTorsionFree.trans (R := FractionRing O)
  have htf : Module.IsTorsionFree O T := inferInstance
  have hfree : Module.Free O T := inferInstance
  let b := Module.finBasis O T
  let v : Fin (Module.finrank O T) → V := fun i => (b i : V)
  have hliO : LinearIndependent O v :=
    b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO
  have hTv : ∀ t : T, (t : V) = ∑ i, b.repr t i • v i := by
    intro t
    have h := congrArg T.subtype (b.sum_repr t)
    rw [map_sum] at h
    simpa [v] using h.symm
  have hsp : ⊤ ≤ Submodule.span (FractionRing O) (Set.range v) := by
    rw [← hT.2, Submodule.span_le]
    intro t ht
    have h : t = ∑ i, b.repr ⟨t, ht⟩ i • v i := hTv ⟨t, ht⟩
    rw [h]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul (FractionRing O)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B : Module.Basis (Fin (Module.finrank O T)) (FractionRing O) V := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = v i := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨?_, ?_⟩
  · rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  · let f : V →ₗ[O] (Fin (Module.finrank O T) → KO O) :=
      LinearMap.pi fun i => (toKO O) ∘ₗ ((B.coord i).restrictScalars O)
    have hker : LinearMap.ker f = T := by
      apply le_antisymm
      · intro x hx
        have hx' : ∀ i, B.repr x i ∈ (1 : Submodule O (FractionRing O)) := by
          intro i
          have := congrFun (LinearMap.mem_ker.mp hx) i
          exact (Submodule.Quotient.mk_eq_zero _).mp this
        rw [← B.sum_repr x]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hx' i)
        rw [← ha, algebraMap_smul, hB]
        exact T.smul_mem _ (b i).2
      · intro x hx
        rw [LinearMap.mem_ker]
        funext i
        have hrep : B.repr x i = algebraMap O (FractionRing O) (b.repr ⟨x, hx⟩ i) := by
          have h1 : x = ∑ j, algebraMap O (FractionRing O) (b.repr ⟨x, hx⟩ j) • B j := by
            have h : x = ∑ i, b.repr ⟨x, hx⟩ i • v i := hTv ⟨x, hx⟩
            simpa [hB] using h
          have h2 := DFunLike.congr_fun (congrArg B.repr h1) i
          rw [B.repr_sum_self] at h2
          exact h2
        change toKO O (B.repr x i) = 0
        rw [hrep]
        exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_one.mpr ⟨_, rfl⟩)
    refine ⟨T.liftQ f hker.ge, ?_⟩
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hker, Submodule.mkQ_map_self]

end Formalism.RepresentationBoundsCohomology.LOC
end
end

-- bundled from Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.PropLoc
section
universe u

namespace Formalism.RepresentationBoundsCohomology.LOC

theorem propLoc : StatPropLoc.{u} := propLoc_of locQuotLen

end Formalism.RepresentationBoundsCohomology.LOC
end

