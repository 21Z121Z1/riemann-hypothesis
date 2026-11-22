import Development.EtaleCohomology.TateTwists.Bundle0024
import Development.EtaleCohomology.TateTwists.TensorVanishing.TensZero
import Development.EtaleCohomology.TateTwists.Bundle0025
import Development.EtaleCohomology.TateTwists.Bundle0027

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorCycleLocallyLowersTopDegreeOfRowExact
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleFoundations

local macro "TI " w:term:max : term => `({p : ℤ × ℤ // p.1 + p.2 = $w})

local macro "TF " C:term:max J:term:max U:term:max w:term:max : term =>
  `(fun q : {p : ℤ × ℤ // p.1 + p.2 = $w} => Sec (HomologicalComplex.X $C q.1.1) $U ⊗[ULift.{1} _] Sec (HomologicalComplex.X $J q.1.2) $U)

def stD {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') :
    Tens C J U w →ₗ[ULift.{1} R] Tens C J U w' :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩) ∘ₗ
        TensorProduct.map ((C.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
      ((p.1.1.negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(p.1.1, p.1.2 + 1), by have := p.2; omega⟩) ∘ₗ
        TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

theorem stD_lof {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (a b : ℤ) (hab : a + b = w)
    (v : Sec (C.X a) U ⊗[ULift.{1} R] Sec (J.X b) U) :
    stD C J U w w' h (DirectSum.lof (ULift.{1} R) (TI w) (TF C J U w) ⟨(a, b), hab⟩ v) =
      DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(a + 1, b), by omega⟩
          (TensorProduct.map ((C.d a (a + 1)).hom.app (op U)).hom LinearMap.id v) +
        (a.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(a, b + 1), by omega⟩
          (TensorProduct.map LinearMap.id ((J.d b (b + 1)).hom.app (op U)).hom v) := by
  unfold stD
  rw [DirectSum.toModule_lof]
  rfl

theorem lift_lof {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) (U : Scheme.{0}) (w : ℤ) (p : TI w)
    (v : Sec (C.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) : τ.lift U w (DirectSum.lof (ULift.{1} R) (TI w) (TF C J U w) p v) =
      TensorProduct.lift (τ.mul U p.1.1 p.1.2 w p.2) v := by
  unfold Pair.lift
  rw [DirectSum.toModule_lof]

theorem stD_lift {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w')
    (y : Tens C J U w) : τ.lift U w' (stD C J U w w' h y) = Sec.map (T.d w w') (τ.lift U w y) := by
  subst h
  have key : (τ.lift U (w + 1)).comp (stD C J U w (w + 1) rfl) =
      ((T.d w (w + 1)).hom.app (op U)).hom.comp (τ.lift U w) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    refine TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply]
    rw [stD_lof, map_add, map_zsmul, lift_lof, lift_lof, lift_lof]
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.id_apply]
    have := τ.leibniz U a b w hab u v
    rw [Units.smul_def] at this
    exact this.symm
  exact LinearMap.congr_fun key y

theorem stD_res {R : Type} [CommRing R] (C J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w w' : ℤ) (h : w + 1 = w')
    (y : Tens C J U w) : stD C J V w w' h (Tens.res g w y) = Tens.res g w' (stD C J U w w' h y) := by
  have key : (stD C J V w w' h).comp (Tens.res g w) = (Tens.res g w').comp (stD C J U w w' h) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    refine TensorProduct.ext' fun u v => ?_
    have n1 := stair_map_res (C.d a (a + 1)) g u
    have n2 := stair_map_res (J.d b (b + 1)) g v
    simp only [Sec.map, Sec.res] at n1 n2
    simp only [LinearMap.comp_apply]
    rw [Tens.res, Tens.res, DirectSum.lmap_lof, stD_lof, stD_lof, map_add, map_zsmul, DirectSum.lmap_lof, DirectSum.lmap_lof]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [n1, n2]
  exact LinearMap.congr_fun key y

theorem lift_res {R : Type} [CommRing R] {C J T : Cx R} (τ : Pair C J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (y : Tens C J U w) : τ.lift V w (Tens.res g w y) = Sec.res g (τ.lift U w y) := by
  have key : (τ.lift V w).comp (Tens.res g w) = ((T.X w).obj.map g.op).hom.comp (τ.lift U w) := by
    refine DirectSum.linearMap_ext _ fun p => ?_
    refine TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply]
    rw [Tens.res, DirectSum.lmap_lof, lift_lof, lift_lof]
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul]
    exact (τ.nat g _ _ _ p.2 u v).symm
  exact LinearMap.congr_fun key y

theorem lof_reidx {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w' a a' b : ℤ) (ha : a + 1 = a')
    (h1 : a + 1 + b = w') (h2 : a' + b = w') (v : Sec (C.X a) U ⊗[ULift.{1} R] Sec (J.X b) U) :
    DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(a + 1, b), h1⟩
        (TensorProduct.map ((C.d a (a + 1)).hom.app (op U)).hom LinearMap.id v) =
      DirectSum.lof (ULift.{1} R) (TI w') (TF C J U w') ⟨(a', b), h2⟩
        (TensorProduct.map ((C.d a a').hom.app (op U)).hom LinearMap.id v) := by
  subst ha; rfl

theorem stD_low {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (n : ℤ)
    (y : Tens C J U w) (hy : ∀ p : TI w, n < p.1.1 → y p = 0) :
    ∀ q : TI w', n + 1 < q.1.1 → stD C J U w w' h y q = 0 := by
  classical
  intro q hq
  rw [← DirectSum.sum_support_of y, map_sum, DFinsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpn : p.1.1 ≤ n := by
    by_contra hc; exact (DFinsupp.mem_support_iff.1 hp) (hy p (by omega))
  obtain ⟨⟨a, b⟩, hab⟩ := p
  simp only at hpn
  rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
    DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
  · intro he; rw [he] at hq; simp only at hq; omega
  · intro he; rw [he] at hq; simp only at hq; omega

theorem stD_top {R : Type} [CommRing R] (C J : Cx R) (U : Scheme.{0}) (w w' : ℤ) (h : w + 1 = w') (s : ℤ)
    (y : Tens C J U w) (hy : ∀ p : TI w, s < p.1.1 → y p = 0) (h0 : s + (w - s) = w) (h1 : s + 1 + (w - s) = w') :
    stD C J U w w' h y ⟨(s + 1, w - s), h1⟩ =
      TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id (y ⟨(s, w - s), h0⟩) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_of y]
  rw [map_sum, DFinsupp.finset_sum_apply]
  have hz : ∀ p ∈ DFinsupp.support y, p ≠ ⟨(s, w - s), h0⟩ →
      stD C J U w w' h (DirectSum.of (TF C J U w) p (y p)) ⟨(s + 1, w - s), h1⟩ = 0 := by
    intro p hp hne
    have hps : p.1.1 < s := by
      have hle : p.1.1 ≤ s := by
        by_contra hc; exact (DFinsupp.mem_support_iff.1 hp) (hy p (by omega))
      rcases lt_or_eq_of_le hle with h' | h'
      · exact h'
      · exact absurd (Subtype.ext (Prod.ext h' (by have := p.2; simp only at this ⊢; omega))) hne
    obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only at hps
    rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
    · intro he; have := congrArg (fun q : TI w' => q.1.1) he; simp only at this; omega
    · intro he; have := congrArg (fun q : TI w' => q.1.1) he; simp only at this; omega
  by_cases hm : (⟨(s, w - s), h0⟩ : TI w) ∈ DFinsupp.support y
  · rw [Finset.sum_eq_single_of_mem _ hm hz]
    rw [← DirectSum.lof_eq_of (ULift.{1} R), stD_lof, DFinsupp.add_apply, DFinsupp.smul_apply,
      DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne, smul_zero, add_zero]
    intro he; have := congrArg (fun q : TI w' => q.1.1) he; simp only at this; omega
  · rw [Finset.sum_eq_zero fun p hp => hz p hp (fun he => hm (he ▸ hp))]
    have : y ⟨(s, w - s), h0⟩ = 0 := by simpa [DFinsupp.mem_support_iff] using hm
    rw [this, map_zero]

theorem next_fix {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {U : Scheme.{0}} (y : Sec (T.X w) U)
    (h : Sec.map (T.sc w).g y = 0) : Sec.map (T.d w (w + 1)) y = 0 := by
  change Sec.map (T.d w ((ComplexShape.up ℤ).next w)) y = 0 at h
  rwa [CochainComplex.next ℤ w] at h

theorem prev_fix {R : Type} [CommRing R] (T : Cx R) (w : ℤ) {V : Scheme.{0}} (z : Sec (T.X (w - 1)) V) :
    ∃ z' : Sec (T.sc w).X₁ V, Sec.map (T.sc w).f z' = Sec.map (T.d (w - 1) w) z := by
  change ∃ z' : Sec (T.X ((ComplexShape.up ℤ).prev w)) V, Sec.map (T.d ((ComplexShape.up ℤ).prev w) w) z' = _
  rw [CochainComplex.prev ℤ w]
  exact ⟨z, rfl⟩

theorem etale_tensor_cycle_locally_lowers_top_degree_of_row_exact : EtaleTensorCycleLocallyLowersTopDegree := by
  intro R _ C J T τ hτ hrow w s U x hx hc
  have hc' : τ.lift U (w + 1) (stD C J U w (w + 1) rfl x) = 0 := by
    rw [stD_lift]; exact next_fix T w _ hc
  refine stair_loc_bind U _ _ (hτ.2 U (w + 1) _ hc') ?_
  intro V g hV
  have hy : ∀ p : TI w, s < p.1.1 → Tens.res g w x p = 0 := by
    intro p hp; rw [Tens.res, DirectSum.lmap_apply, hx p hp, map_zero]
  have hrow0 : TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id
      (Tens.res g w x ⟨(s, w - s), by omega⟩) = 0 := by
    rw [← stD_top C J V w (w + 1) rfl s _ hy (by omega) (by omega), stD_res, hV]; rfl
  refine stair_loc_mono V _ _ (hrow s (w - s) V _ hrow0) ?_
  rintro W k ⟨e, he⟩
  have hlow : ∀ q : TI (w - 1), s - 1 < q.1.1 →
      (DirectSum.lof (ULift.{1} R) (TI (w - 1)) (TF C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e) q = 0 := by
    intro q hq
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne]
    intro he'; rw [he'] at hq; simp only at hq; omega
  refine ⟨Tens.res k w (Tens.res g w x) - stD C J W (w - 1) w (by omega)
      (DirectSum.lof (ULift.{1} R) (TI (w - 1)) (TF C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e), ?_, ?_⟩
  · intro p hp
    rw [DFinsupp.sub_apply]
    rcases lt_or_eq_of_le (show s ≤ p.1.1 by omega) with hps | hps
    · rw [stD_low C J W (w - 1) w (by omega) (s - 1) _ hlow p (by omega), sub_zero,
        show Tens.res k w (Tens.res g w x) p = TensorProduct.map ((C.X p.1.1).obj.map k.op).hom
          ((J.X p.1.2).obj.map k.op).hom (Tens.res g w x p) from DirectSum.lmap_apply _ _ _, hy p hps, map_zero]
    · obtain ⟨⟨a, b⟩, hab⟩ := p
      simp only at hps
      subst hps
      obtain rfl : b = w - s := by simp only at hab; omega
      rw [stD_lof, lof_reidx C J W w (s - 1) s (w - s) (by omega) _ (by omega), DFinsupp.add_apply, DFinsupp.smul_apply,
        DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_of_ne, smul_zero, add_zero,
        sub_eq_zero]
      · exact he.symm
      · intro he'; have := congrArg (fun q : TI w => q.1.1) he'; simp only at this; omega
  · obtain ⟨z', hz'⟩ := prev_fix T w (τ.lift W (w - 1)
      (DirectSum.lof (ULift.{1} R) (TI (w - 1)) (TF C J W (w - 1)) ⟨(s - 1, w - s), by omega⟩ e))
    refine ⟨z', ?_⟩
    rw [map_sub, lift_res, lift_res, stair_res_res, stD_lift]
    exact congrArg (fun t => _ - t) hz'.symm

end LateralTheory.EtaleFoundations
end
end

-- bundled from Development.EtaleCohomology.TateTwists.TensorVanishing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R] {C J T : Cx R}

theorem tens_zero' {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} R) M]
    [Module (ULift.{1} R) N] (hN : ∀ m : N, m = 0) (x : M ⊗[ULift.{1} R] N) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [hN n, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

theorem res_apply {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) (p : Ix w) :
    (Tens.res g w x) p = TensorProduct.map ((C.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom (x p) := by
  unfold Tens.res; rw [DirectSum.lmap_apply]

theorem nat_tens {V U : Scheme.{0}} (g : V ⟶ U) (s s' t : ℤ) (v : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U) :
    TensorProduct.map ((C.d s s').hom.app (op V)).hom LinearMap.id
        (TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom v) =
      TensorProduct.map ((C.X s').obj.map g.op).hom ((J.X t).obj.map g.op).hom
        (TensorProduct.map ((C.d s s').hom.app (op U)).hom LinearMap.id v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    congr 1; exact map_res (C.d s s') g a
  | add a b ha hb => simp only [map_add, ha, hb]

theorem lift_Dm' (τ : Pair C J T) (U : Scheme.{0}) (w w' : ℤ) (hw : w + 1 = w') (x : Tens C J U w) :
    τ.lift U w' (Dm U w w' hw x) = Sec.map (T.d w w') (τ.lift U w x) := by
  subst hw; exact lift_Dm τ U w x

theorem lof_shift (U : Scheme.{0}) (n s s' t : ℤ) (hs : s + 1 = s') (h1 : (s + 1) + t = n) (h2 : s' + t = n)
    (y : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U) :
    DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(s + 1, t), h1⟩
        (TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id y) =
      DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(s', t), h2⟩
        (TensorProduct.map ((C.d s s').hom.app (op U)).hom LinearMap.id y) := by
  subst hs; rfl

theorem lof_ne (U : Scheme.{0}) (n : ℤ) (i j : Ix n) (h : i.1.2 ≠ j.1.2) (v : Cmp C J U n i) :
    (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) i v) j = 0 := by
  classical
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_of_ne _ _ _ (fun e => h (by rw [e]))

theorem lof_same (U : Scheme.{0}) (n : ℤ) (i : Ix n) (v : Cmp C J U n i) :
    (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) i v) i = v := by
  classical
  rw [DirectSum.lof_eq_of]
  exact DirectSum.of_eq_same _ _

theorem smap_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem smap_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ _ _
theorem smap_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sres_sub {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ _ _
theorem sres_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

def Step : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (τ : Pair C J T), τ.IsTensor → LateralTheory.EtaleFoundations.acyc.ColExact C J →
    ∀ (n t0 : ℤ) (V : Scheme.{0}) (x : Tens C J V n), (∀ p : Ix n, p.1.2 < t0 → x p = 0) →
      Sec.map (T.d n (n + 1)) (τ.lift V n x) = 0 →
      Loc V fun W h => ∃ (x' : Tens C J W n) (Y : Tens C J W (n - 1)),
        (∀ p : Ix n, p.1.2 < t0 + 1 → x' p = 0) ∧ Tens.res h n x = x' + Dm W (n - 1) n (by ring) Y

theorem main (hS : Step) (τ : Pair C J T) (a : ℤ) [C.IsStrictlyGE a] (hτ : τ.IsTensor)
    (hc : LateralTheory.EtaleFoundations.acyc.ColExact C J) (n : ℤ) :
    ∀ k : ℕ, ∀ (V : Scheme.{0}) (x : Tens C J V n), (∀ p : Ix n, p.1.2 < n - a + 1 - k → x p = 0) →
      Sec.map (T.d n (n + 1)) (τ.lift V n x) = 0 →
      Loc V fun W h => ∃ y : Sec (T.X (n - 1)) W, Sec.map (T.d (n - 1) n) y = Sec.res h (τ.lift V n x) := by
  intro k
  induction k with
  | zero =>
    intro V x hx _
    obtain rfl : x = 0 := DFinsupp.ext fun p => by
      by_cases hp : p.1.2 < n - a + 1 - ((0 : ℕ) : ℤ)
      · exact hx p hp
      · exact tens_zero (fun m => sec_zero a (by have := p.2; push_cast at hp; omega) m) (x p)
    exact loc_all fun W h => ⟨0, by rw [smap_zero, map_zero, sres_zero]⟩
  | succ k ih =>
    intro V x hx hd
    refine loc_bind (hS R τ hτ hc n (n - a + 1 - ((k + 1 : ℕ) : ℤ)) V x hx hd) fun W h hW => ?_
    obtain ⟨x', Y, hv, he⟩ := hW
    have hl : τ.lift W n x' = Sec.res h (τ.lift V n x) - Sec.map (T.d (n - 1) n) (τ.lift W (n - 1) Y) := by
      rw [← lift_res, he, map_add, lift_Dm']; abel
    have hd' : Sec.map (T.d n (n + 1)) (τ.lift W n x') = 0 := by
      rw [hl, smap_sub, map_res, hd, sres_zero, map_dd, sub_zero]
    refine loc_mono (ih W x' (fun p hp => hv p (by push_cast at hp ⊢; omega)) hd') fun W' h' hy => ?_
    obtain ⟨y, hy⟩ := hy
    refine ⟨y + Sec.res h' (τ.lift W (n - 1) Y), ?_⟩
    rw [smap_add, map_res, hy, hl, sres_sub, res_comp]; abel

end LateralTheory.EtaleFoundations.stairPf

open LateralTheory.EtaleFoundations.acyc LateralTheory.EtaleFoundations.stairPf in
theorem LateralTheory.EtaleFoundations.acyc.stair_of (hS : Step) : LateralTheory.EtaleFoundations.acyc.stair := by
  intro R _ C J T a b _ _ τ hτ hc U n z hz
  refine loc_bind (hτ.1 U n z) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  have key := main hS τ a hτ hc n ((n - a + 1 - b).toNat) V x
    (fun p hp => tens_zero' (fun m => sec_zero (C := J) b
      (by have := Int.self_le_toNat (n - a + 1 - b); have := p.2; omega) m) (x p))
    (by rw [hx, map_res, hz, sres_zero])
  exact loc_mono key fun W h hy => by
    obtain ⟨y, hy⟩ := hy
    exact ⟨y, by rw [hy, hx, res_comp]⟩
end
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensExPfSh
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

noncomputable section

abbrev shK {I J : Cx R} (T : TensPre I J) : Cx R :=
  ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj T.P

abbrev tS {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →ₗ[ULift.{1} R] Sec ((shK T).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom ∘ₗ (T.e U w).toLinearMap

theorem tS_nat {I J : Cx R} (T : TensPre I J) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (tS T U w x) = tS T V w (Tens.res g w x) := by
  have h1 := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).naturality g.op) (T.e U w x)
  simp only [ConcreteCategory.comp_apply] at h1
  show Sec.res g (((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op U)).hom (T.e U w x)) =
    ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w (Tens.res g w x))
  rw [T.nat]
  exact h1.symm

theorem tS_d {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((shK T).d w (w + 1)) (tS T U w x) =
      ((toSheafify Scheme.etaleTopology.{0} (T.P.X (w + 1))).app (op U)).hom
        (((T.P.d w (w + 1)).app (op U)).hom (T.e U w x)) := by
  simp only [tS, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (ConcreteCategory.congr_hom (congrArg (fun f => NatTrans.app f (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} (T.P.d w (w + 1)))) _).symm

def shPair {I J : Cx R} (T : TensPre I J) : Pair I J (shK T) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (tS T U w ∘ₗ DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w} (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply, tS_nat]
    congr 1
    rw [Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul]
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply, DirectSum.lof_eq_of]
    rw [tS_d, T.leibniz]
    rw [map_add, Units.smul_def, Units.smul_def, map_zsmul]
    rfl

theorem shPair_lift {I J : Cx R} (T : TensPre I J) (U : Scheme.{0}) (w : ℤ) :
    (shPair T).lift U w = tS T U w := by
  classical
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp [Pair.lift, shPair, DirectSum.toModule_lof]

theorem shPair_isTensor {I J : Cx R} (T : TensPre I J) : (shPair T).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := tt_sheafify_locSurj (T.P.X w) U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨(T.e V w).symm x, ?_⟩
    rw [shPair_lift]
    show ((toSheafify Scheme.etaleTopology.{0} (T.P.X w)).app (op V)).hom (T.e V w ((T.e V w).symm x)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hx
  · rw [shPair_lift] at hx
    obtain ⟨S, hS, hP⟩ := tt_sheafify_locInj (T.P.X w) U (T.e U w x) hx
    refine ⟨S, hS, fun V g hg => ?_⟩
    have h2 := hP V g hg
    simp only at h2 ⊢
    rw [← T.nat] at h2
    exact (LinearEquiv.map_eq_zero_iff _).mp h2

theorem etale_presheaf_tensor_data_sheafification_is_tensor_complex : tt_tens_sheafify := fun _ _ _ _ T => ⟨_, shPair T, shPair_isTensor T⟩

end

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TwSecLocPfZarR
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  intro q _ V ζ ξ
  obtain ⟨s, hs, hf⟩ := hA q Γ(V, ⊤) ζ ξ
  let U : s → V.Opens := fun f => V.basicOpen f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, V.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := V.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f),
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩), ?_⟩
  rintro W g ⟨Y, h, _, ⟨i⟩, rfl⟩
  obtain ⟨a, n, hn⟩ := hf i.1 i.2
  refine ⟨a, ?_⟩
  have hle : (U i).ι ''ᵁ ⊤ ≤ V.basicOpen i.1 := by simp [U]
  have hu : IsUnit ((U i).ι.appTop.hom i.1) := by
    have := (V.toRingedSpace.isUnit_res_basicOpen i.1).map (V.presheaf.map (homOfLE hle).op).hom
    have e : V.presheaf.map (homOfLE (x := (U i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        V.presheaf.map (homOfLE (V.basicOpen_le i.1)).op ≫ V.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  have key : (U i).ι.appTop.hom ξ.1 = ((U i).ι.appTop.hom ζ.1) ^ (a : ZMod q).val := by
    have h0 : (U i).ι.appTop.hom (i.1 ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) = 0 := by rw [hn, map_zero]
    rw [map_mul, map_pow, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)
  have hc : ∀ x, (h ≫ (U i).ι).appTop.hom x = h.appTop.hom ((U i).ι.appTop.hom x) := fun x => by
    rfl
  show (h ≫ (U i).ι).appTop.hom ξ.1 = ((h ≫ (U i).ι).appTop.hom ζ.1) ^ _
  rw [hc, hc, key]
  exact map_pow _ _ _

theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.EtaleFoundations.TwSecLocPf
end
end

