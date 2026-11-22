import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0011

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TowerFin
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem tf_mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha m _ i => ?_) (fun y z hy hz i => ?_)
    · simpa using J.mul_mem_right (m i) ha
    · simpa using J.add_mem (hy i) (hz i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem tf_isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (r : ℕ) : IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec (I := I) inferInstance (f := fun n => f n i) (fun {m n} hmn => ?_)
    have := (tf_mem_smul_top_pi (I ^ m) _).1 (SModEq.sub_mem.1 (hf hmn)) i
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    simpa using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, tf_mem_smul_top_pi]
  intro i
  have := SModEq.sub_mem.1 (hL i n)
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at this
  simpa using this

private theorem tf_key {R F : Type} [CommRing R] [AddCommGroup F] [Module R F] (a : Ideal R)
    [IsPrecomplete a F] (K : ℕ → Submodule R F) (hK : Antitone K)
    (h1 : ∀ n, (a ^ n • ⊤ : Submodule R F) ≤ K n)
    (h2 : ∀ n, K n ≤ (a ^ n • ⊤ : Submodule R F) ⊔ K (n + 1)) (k : ℕ) (x : F) (hx : x ∈ K k) :
    ∃ y ∈ (a ^ k • ⊤ : Submodule R F), ∀ n, x - y ∈ K n := by
  classical
  have step : ∀ n, ∀ v ∈ K n, ∃ y ∈ (a ^ n • ⊤ : Submodule R F), ∃ w ∈ K (n + 1), y + w = v :=
    fun n v hv => Submodule.mem_sup.1 (h2 n hv)
  choose hd hdm tl htlm hsum using step
  obtain ⟨w, hw0, hwS⟩ : ∃ w : ∀ j, {v : F // v ∈ K (k + j)}, (w 0).1 = x ∧
      ∀ j, (w (j + 1)).1 = tl (k + j) (w j).1 (w j).2 :=
    ⟨fun j => Nat.rec (motive := fun j => {v : F // v ∈ K (k + j)}) ⟨x, hx⟩
      (fun j v => ⟨tl (k + j) v.1 v.2, htlm _ _ _⟩) j, rfl, fun j => rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ → F, ∀ j, z j = hd (k + j) (w j).1 (w j).2 := ⟨_, fun _ => rfl⟩
  have hzm : ∀ j, z j ∈ (a ^ (k + j) • ⊤ : Submodule R F) := fun j => by rw [hz]; exact hdm _ _ _
  have hsplit : ∀ j, z j + (w (j + 1)).1 = (w j).1 := fun j => by rw [hz, hwS]; exact hsum _ _ _
  have hpart : ∀ j, x - ∑ i ∈ Finset.range j, z i = (w j).1 := by
    intro j
    induction j with
    | zero => simp [hw0]
    | succ j ih =>
      rw [Finset.sum_range_succ, ← sub_sub, ih, sub_eq_iff_eq_add']
      exact (hsplit j).symm
  have hcau : ∀ {m n : ℕ}, m ≤ n → (∑ i ∈ Finset.range m, z i) ≡ (∑ i ∈ Finset.range n, z i)
      [SMOD (a ^ m • ⊤ : Submodule R F)] := by
    intro m n hmn
    rw [SModEq.sub_mem, ← Finset.sum_range_add_sum_Ico _ hmn]
    have e : ∑ i ∈ Finset.range m, z i - (∑ i ∈ Finset.range m, z i + ∑ i ∈ Finset.Ico m n, z i)
        = -∑ i ∈ Finset.Ico m n, z i := by abel
    rw [e]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    have := (Finset.mem_Ico.1 hi).1
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (hzm i)
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (I := a) inferInstance
    (f := fun n => ∑ i ∈ Finset.range n, z i) hcau
  refine ⟨y, ?_, fun n => ?_⟩
  · have h1' := SModEq.sub_mem.1 (hy k)
    have h2' : ∑ i ∈ Finset.range k, z i ∈ (a ^ k • ⊤ : Submodule R F) :=
      Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (hzm i)
    have := Submodule.sub_mem _ h2' h1'
    simpa using this
  · have h1' := SModEq.sub_mem.1 (hy n)
    have e : x - y = (w n).1 + (∑ i ∈ Finset.range n, z i - y) := by rw [← hpart n]; abel
    rw [e]
    exact Submodule.add_mem _ (hK (Nat.le_add_left n k) (w n).2) (h1 n h1')

theorem UpperTheory.V.AlgebraTools.exists_tower_limit :
    ∀ (R : Type) [CommRing R] (a : Ideal R) [IsAdicComplete a R] (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (π : ∀ k, P (k + 1) →ₗ[R] P k),
      (∀ k, Function.Surjective (π k)) → (∀ k, LinearMap.ker (π k) = a ^ k • ⊤) → (∀ k, (a ^ k • ⊤ : Submodule R (P k)) = ⊥) →
      Module.Finite R (P 1) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (q : ∀ k, M →ₗ[R] P k), Module.Finite R M ∧
        (∀ k, Function.Surjective (q k)) ∧ (∀ k, LinearMap.ker (q k) = a ^ k • ⊤) ∧ (∀ k x, π k (q (k + 1) x) = q k x) ∧
        ∀ x : M, (∀ k, q k x = 0) → x = 0 := by
  intro R _ a _ P _ _ π hsurj hker hbot hfin
  classical
  have nak : ∀ {N : Type} [AddCommGroup N] [Module R N] (S : Submodule R N) (j : ℕ),
      (⊤ : Submodule R N) ≤ S ⊔ a • ⊤ → (a ^ j • ⊤ : Submodule R N) = ⊥ → S = ⊤ := by
    intro N _ _ S j hS hj
    have key : ∀ i, (⊤ : Submodule R N) ≤ S ⊔ a ^ i • ⊤ := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        calc (⊤ : Submodule R N) ≤ S ⊔ a • ⊤ := hS
          _ ≤ S ⊔ a • (S ⊔ a ^ i • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl ih) _
          _ ≤ S ⊔ a ^ (i + 1) • ⊤ := by
            rw [Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ']
            exact sup_le le_sup_left (sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right)
    have := key j
    rw [hj, sup_bot_eq] at this
    exact top_le_iff.1 this
  have hz : ∀ n (r : R) (v : P n), r ∈ a ^ n → r • v = 0 := fun n r v hr => by
    have := Submodule.smul_mem_smul hr (Submodule.mem_top (x := v))
    rw [hbot n] at this
    simpa using this
  have hP0 : ∀ v : P 0, v = 0 := fun v => by simpa using hz 0 1 v (by simp)
  obtain ⟨r, ψ1, hψ1⟩ := Module.Finite.exists_fin' R (P 1)
  haveI := tf_isPrecomplete_pi a r
  have lift : ∀ n (g : (Fin r → R) →ₗ[R] P n), ∃ h : (Fin r → R) →ₗ[R] P (n + 1), (π n).comp h = g :=
    fun n g => Module.projective_lifting_property (π n) g (hsurj n)
  choose L hL using lift
  obtain ⟨ψ', hψ'0, hψ'S⟩ : ∃ ψ' : ∀ j, (Fin r → R) →ₗ[R] P (j + 1), ψ' 0 = ψ1 ∧
      ∀ j, ψ' (j + 1) = L (j + 1) (ψ' j) :=
    ⟨fun j => Nat.rec (motive := fun j => (Fin r → R) →ₗ[R] P (j + 1)) ψ1
      (fun j g => L (j + 1) g) j, rfl, fun j => rfl⟩
  have hcomp' : ∀ j v, π (j + 1) (ψ' (j + 1) v) = ψ' j v := by
    intro j v
    have h := LinearMap.congr_fun (hL (j + 1) (ψ' j)) v
    rw [hψ'S]
    simpa using h
  have hψ's : ∀ j, Function.Surjective (ψ' j) := by
    intro j
    induction j with
    | zero => rw [hψ'0]; exact hψ1
    | succ j ih =>
      rw [← LinearMap.range_eq_top]
      have hS : (⊤ : Submodule R (P (j + 1 + 1))) ≤ LinearMap.range (ψ' (j + 1)) ⊔ a • ⊤ := by
        intro p _
        obtain ⟨f, hf⟩ := ih (π (j + 1) p)
        have hk : p - ψ' (j + 1) f ∈ LinearMap.ker (π (j + 1)) := by
          rw [LinearMap.mem_ker, map_sub, hcomp', hf, sub_self]
        rw [hker] at hk
        refine Submodule.mem_sup.2 ⟨ψ' (j + 1) f, LinearMap.mem_range_self _ f,
          p - ψ' (j + 1) f, ?_, by abel⟩
        exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) hk
      exact nak _ (j + 1 + 1) hS (hbot (j + 1 + 1))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ n, (Fin r → R) →ₗ[R] P n, ∀ n, ψ n = (π n).comp (ψ' n) :=
    ⟨_, fun _ => rfl⟩
  have hcomp : ∀ n v, π n (ψ (n + 1) v) = ψ n v := by
    intro n v
    simp only [hψ, LinearMap.comp_apply, hcomp']
  have hψs : ∀ n, Function.Surjective (ψ n) := by
    intro n
    rw [hψ, LinearMap.coe_comp]
    exact (hsurj n).comp (hψ's n)
  obtain ⟨Msub, hmem⟩ : ∃ S : Submodule R (∀ k, P k),
      ∀ x, x ∈ S ↔ ∀ k, π k (x (k + 1)) = x k :=
    ⟨{ carrier := {x | ∀ k, π k (x (k + 1)) = x k}
       add_mem' := by
         intro x y hx hy
         simp only [Set.mem_setOf_eq] at hx hy ⊢
         intro k; simp [hx k, hy k]
       zero_mem' := by simp
       smul_mem' := by
         intro c x hx
         simp only [Set.mem_setOf_eq] at hx ⊢
         intro k; simp [hx k] }, fun x => Iff.rfl⟩
  have hφmem : ∀ v, LinearMap.pi (fun k => ψ k) v ∈ Msub :=
    fun v => (hmem _).2 fun k => by simpa using hcomp k v
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin r → R) →ₗ[R] Msub, ∀ v k, (φ v : ∀ k, P k) k = ψ k v :=
    ⟨LinearMap.codRestrict Msub (LinearMap.pi fun k => ψ k) hφmem, fun v k => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ∀ k, Msub →ₗ[R] P k, ∀ k x, q k x = (x : ∀ k, P k) k :=
    ⟨fun k => (LinearMap.proj k).comp Msub.subtype, fun k x => rfl⟩
  have hsep : ∀ x : Msub, (∀ k, q k x = 0) → x = 0 := fun x h =>
    Subtype.ext (funext fun k => by simpa [hq] using h k)
  have hK : Antitone (fun n => LinearMap.ker (ψ n)) := antitone_nat_of_succ_le fun n v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← hcomp, hv, map_zero]
  have h1 : ∀ n, (a ^ n • ⊤ : Submodule R (Fin r → R)) ≤ LinearMap.ker (ψ n) := fun n =>
    Submodule.smul_le.2 fun r hr v _ => by
      rw [LinearMap.mem_ker, map_smul]
      exact hz n r _ hr
  have h2 : ∀ n, LinearMap.ker (ψ n) ≤ (a ^ n • ⊤ : Submodule R (Fin r → R)) ⊔ LinearMap.ker (ψ (n + 1)) := by
    intro n v hv
    rw [LinearMap.mem_ker] at hv
    have hk : ψ (n + 1) v ∈ LinearMap.ker (π n) := by rw [LinearMap.mem_ker, hcomp, hv]
    rw [hker n, ← LinearMap.range_eq_top.2 (hψs (n + 1)), LinearMap.range_eq_map,
      ← Submodule.map_smul''] at hk
    obtain ⟨g, hg, hgv⟩ := Submodule.mem_map.1 hk
    refine Submodule.mem_sup.2 ⟨g, hg, v - g, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hgv, sub_self]
  have hφs : Function.Surjective φ := by
    intro m
    have hm : ∀ k, π k ((m : ∀ k, P k) (k + 1)) = (m : ∀ k, P k) k := (hmem _).1 m.2
    have step : ∀ n (f : Fin r → R), ψ n f = (m : ∀ k, P k) n →
        ∃ g ∈ (a ^ n • ⊤ : Submodule R (Fin r → R)), ψ (n + 1) (f + g) = (m : ∀ k, P k) (n + 1) := by
      intro n f hf
      obtain ⟨f', hf'⟩ := hψs (n + 1) ((m : ∀ k, P k) (n + 1))
      have hd : f' - f ∈ LinearMap.ker (ψ n) := by
        rw [LinearMap.mem_ker, map_sub, ← hcomp, hf', hm, hf, sub_self]
      obtain ⟨g, hg, h, hh, hgh⟩ := Submodule.mem_sup.1 (h2 n hd)
      refine ⟨g, hg, ?_⟩
      rw [LinearMap.mem_ker] at hh
      have e : f + g = f' - h := by rw [eq_sub_iff_add_eq, add_assoc, hgh]; abel
      rw [e, map_sub, hf', hh, sub_zero]
    choose G hG hGψ using step
    have h0 : ψ 0 0 = (m : ∀ k, P k) 0 := by rw [map_zero]; exact (hP0 _).symm
    obtain ⟨s, hs0, hsS⟩ : ∃ s : ∀ n, {f : Fin r → R // ψ n f = (m : ∀ k, P k) n},
        (s 0).1 = 0 ∧ ∀ n, (s (n + 1)).1 = (s n).1 + G n (s n).1 (s n).2 :=
      ⟨fun n => Nat.rec (motive := fun n => {f : Fin r → R // ψ n f = (m : ∀ k, P k) n}) ⟨0, h0⟩
        (fun n t => ⟨t.1 + G n t.1 t.2, hGψ n t.1 t.2⟩) n, rfl, fun n => rfl⟩
    have hcau : ∀ {m' n : ℕ}, m' ≤ n →
        (s m').1 ≡ (s n).1 [SMOD (a ^ m' • ⊤ : Submodule R (Fin r → R))] := by
      intro m' n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact SModEq.refl _
      | succ n hmn ih =>
        rw [SModEq.sub_mem] at ih ⊢
        rw [hsS, ← sub_sub]
        exact Submodule.sub_mem _ ih
          (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) (hG _ _ _))
    obtain ⟨Lim, hLim⟩ := IsPrecomplete.prec (I := a) inferInstance (f := fun n => (s n).1) hcau
    refine ⟨Lim, Subtype.ext (funext fun k => ?_)⟩
    rw [hφ]
    have hdk : (s k).1 - Lim ∈ LinearMap.ker (ψ k) := h1 k (SModEq.sub_mem.1 (hLim k))
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hdk
    rw [← hdk]
    exact (s k).2
  refine ⟨Msub, inferInstance, inferInstance, q, Module.Finite.of_surjective φ hφs, ?_, ?_,
    fun k x => by rw [hq, hq]; exact (hmem _).1 x.2 k, hsep⟩
  · intro k p
    obtain ⟨v, hv⟩ := hψs k p
    exact ⟨φ v, by rw [hq, hφ, hv]⟩
  · intro k
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker, hq] at hx
      obtain ⟨v, rfl⟩ := hφs x
      rw [hφ] at hx
      obtain ⟨y, hy, hvy⟩ := tf_key a (fun n => LinearMap.ker (ψ n)) hK h1 h2 k v
        (LinearMap.mem_ker.2 hx)
      have hz0 : φ (v - y) = 0 := hsep _ fun n => by
        rw [hq, hφ]
        exact hvy n
      rw [map_sub, sub_eq_zero] at hz0
      rw [hz0]
      have hmap := Submodule.mem_map_of_mem (f := φ) hy
      rw [Submodule.map_smul''] at hmap
      exact Submodule.smul_mono le_rfl le_top hmap
    · intro hx
      exact (Submodule.smul_le.2 (fun r hr y _ => by
        rw [LinearMap.mem_ker, map_smul]
        exact hz k r _ hr) : (a ^ k • ⊤ : Submodule R Msub) ≤ LinearMap.ker (q k)) hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.VrRange
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section aux

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι] [DecidableEq ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private noncomputable def vrEnt (w : E) : (U.oddForm p q).Ext :=
  (U.oddForm p q).el (T.tr w)
    (cornerProj B (U.ep p) (U.ep q) w + cornerProj B (U.ep p) (U.ep q) (T.st w))

private noncomputable def vrRec (a b : ι) (z : (U.oddForm p q).Ext) : E :=
  if a = b then z.ev • U.ep a else if a = p then z.od.1 else T.st z.od.1

omit [DecidableEq ι] in
private theorem vrEnt_od (w : E) :
    (vrEnt U p q w).od.1 = U.ep p * w * U.ep q + U.ep p * T.st w * U.ep q := by
  simp only [mul_assoc]; rfl

omit [DecidableEq ι] in
private theorem vrEnt_ev (w : E) : (vrEnt U p q w).ev = T.tr w := rfl

omit [DecidableEq ι] in
private theorem sand (a b c d : ι) (w : E) (hw : U.ep a * w * U.ep b = w) (h : c ≠ a ∨ b ≠ d) :
    U.ep c * w * U.ep d = 0 := by
  rw [← hw]
  simp only [mul_assoc]
  rcases h with h | h
  · rw [← mul_assoc (U.ep c), U.coi.ortho h, zero_mul]
  · rw [U.coi.ortho h, mul_zero, mul_zero, mul_zero]

omit [DecidableEq ι] in
private theorem sand_st (a b : ι) (w : E) (hw : U.ep a * w * U.ep b = w) :
    U.ep b * T.st w * U.ep a = T.st w := by
  conv_rhs => rw [← hw]
  rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]

private theorem ent_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q) (w : E)
    (hw : U.ep a * w * U.ep b = w) :
    ((a = b → (vrEnt U p q w).od = 0) ∧ (a ≠ b → (vrEnt U p q w).ev = 0)) ∧
      vrRec U p q a b (vrEnt U p q w) = w := by
  have hst := sand_st U a b w hw
  refine ⟨⟨fun hab => ?_, fun hab => ?_⟩, ?_⟩
  · rw [← hab] at hw hst
    have h1 : p ≠ a ∨ a ≠ q := by
      rcases ha with h | h
      · exact Or.inr (fun h' => hpq (h.symm.trans h'))
      · exact Or.inl (fun h' => hpq (h'.trans h))
    apply Subtype.ext
    rw [vrEnt_od, sand U a a p q w hw h1, sand U a a p q (T.st w) hst h1, add_zero]
    rfl
  · rw [vrEnt_ev, ← hw]
    exact (units_basic T o U).2.2.1 a b w hab
  · unfold vrRec
    split_ifs with h1 h2
    · rw [← h1] at hw
      rw [vrEnt_ev]
      conv_rhs => rw [← hw, U.corner_eq, hw]
    · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
      rw [h2, hb'] at hw hst
      rw [vrEnt_od, hw, sand U q p p q (T.st w) hst (Or.inl hpq), add_zero]
    · have ha' : a = q := ha.resolve_left h2
      have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
      rw [ha', hb'] at hw hst
      rw [vrEnt_od, sand U q p p q w hw (Or.inl hpq), zero_add, hst, T.st_st]

private theorem rec_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (z : (U.oddForm p q).Ext) (hz : (a = b → z.od = 0) ∧ (a ≠ b → z.ev = 0)) :
    U.ep a * vrRec U p q a b z * U.ep b = vrRec U p q a b z ∧ vrEnt U p q (vrRec U p q a b z) = z := by
  have hid : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hmem : U.ep p * (z.od : E) * U.ep q = z.od := by
    obtain ⟨y, hy⟩ := z.od.2
    rw [← hy]
    show U.ep p * (U.ep p * (y * U.ep q)) * U.ep q = U.ep p * (y * U.ep q)
    rw [← mul_assoc (U.ep p) (U.ep p), hid, mul_assoc, mul_assoc, hid]
  have hoff : U.ep p * T.st (z.od : E) * U.ep q = 0 :=
    sand U q p p q _ (sand_st U p q _ hmem) (Or.inl hpq)
  unfold vrRec
  split_ifs with h1 h2
  · have hod := hz.1 h1
    have hpa : U.ep p * U.ep a * U.ep q = 0 := by
      rcases ha with h | h
      · rw [h, hid, U.coi.ortho hpq]
      · rw [h, U.coi.ortho hpq, zero_mul]
    refine ⟨?_, ?_⟩
    · rw [← h1, mul_smul_comm, smul_mul_assoc, hid, hid]
    · apply OddForm.Ext.ext
      · rw [vrEnt_ev, map_smul, U.tr_ep, smul_eq_mul, mul_one]
      · apply Subtype.ext
        rw [vrEnt_od, hod, map_smul, U.st_ep]
        simp only [mul_smul_comm, smul_mul_assoc, hpa, smul_zero, add_zero]
        rfl
  · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
    have hev := hz.2 h1
    rw [h2, hb']
    refine ⟨hmem, ?_⟩
    apply OddForm.Ext.ext
    · rw [vrEnt_ev, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · apply Subtype.ext
      rw [vrEnt_od, hmem, hoff, add_zero]
  · have ha' : a = q := ha.resolve_left h2
    have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
    have hev := hz.2 h1
    rw [ha', hb']
    refine ⟨sand_st U p q _ hmem, ?_⟩
    apply OddForm.Ext.ext
    · rw [vrEnt_ev, T.tr_st, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · apply Subtype.ext
      rw [vrEnt_od, T.st_st, hmem, hoff, zero_add]

end aux

theorem UpperTheory.V.AlgebraTools.vr_range :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → Function.Injective (U.vr p q) ∧ ∀ Y : Matrix ι ι (U.oddForm p q).Ext, Y ∈ Set.range (U.vr p q) ↔ ∀ i j, (o i = o j → (Y i j).od = 0) ∧ (o i ≠ o j → (Y i j).ev = 0) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hxx, -, -, -, -, hsum, hcor⟩ := units_basic T o U
  have hvr : ∀ w i j, U.vr p q w i j = vrEnt U p q (U.x i * w * T.st (U.x j)) :=
    fun _ _ _ => rfl
  have hrec : ∀ w i j, vrRec U p q (o i) (o j) (U.vr p q w i j) = U.x i * w * T.st (U.x j) := by
    intro w i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).2
  have hx : ∀ i k, U.x i * T.st (U.x k) = if i = k then U.ep (o i) else 0 := by
    intro i k
    split_ifs with h
    · rw [h, U.x_st]
    · exact hxx i k h
  refine ⟨fun w w' h => ?_, fun Y => ⟨?_, ?_⟩⟩
  · rw [hsum w, hsum w']
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← hrec w i j, ← hrec w' i j, h]
  · rintro ⟨w, rfl⟩ i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).1
  · intro hY
    refine ⟨∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l, ?_⟩
    refine Matrix.ext (fun i j => ?_)
    rw [hvr]
    have hr := rec_spec U p q hpq (o i) (o j) (ho i) (ho j) (Y i j) (hY i j)
    have key : U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
        T.st (U.x j) = vrRec U p q (o i) (o j) (Y i j) := by
      calc U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
            T.st (U.x j)
          = ∑ k, ∑ l, (U.x i * T.st (U.x k)) * vrRec U p q (o k) (o l) (Y k l) *
              (U.x l * T.st (U.x j)) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = U.ep (o i) * vrRec U p q (o i) (o j) (Y i j) * U.ep (o j) := by
            simp [hx]
        _ = vrRec U p q (o i) (o j) (Y i j) := hr.1
    rw [key]
    exact hr.2
end

