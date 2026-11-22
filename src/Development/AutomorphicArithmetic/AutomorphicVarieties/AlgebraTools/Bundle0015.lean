import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SpBasis
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private def UpperTheory.V.AlgebraTools.spIdx (n d : ℕ) (hd : d = n + 1) :
    (Fin d × ∀ i : Fin n, Fin (n - i)) ≃ (∀ i : Fin (n + 1), Fin (n + 1 - i)) where
  toFun p := fun i => Fin.cases (motive := fun i : Fin (n + 1) => Fin (n + 1 - i))
    ⟨p.1, by have := p.1.2; simp; omega⟩
    (fun j => ⟨p.2 j, by have := (p.2 j).2; simp only [Fin.val_succ]; omega⟩) i
  invFun c := (⟨c 0, by have := (c 0).2; simp at this; omega⟩,
    fun j => ⟨c j.succ, by have := (c j.succ).2; simp only [Fin.val_succ] at this; omega⟩)
  left_inv p := by
    ext <;> rfl
  right_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem UpperTheory.V.AlgebraTools.spCard (n : ℕ) :
    Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.card_congr (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), Fintype.card_prod,
      Fintype.card_fin, ih, Nat.factorial_succ]

theorem UpperTheory.V.AlgebraTools.splitAlg_basis :
    ∀ (n : ℕ) (R : Type) [CommRing R] (P : Polynomial R), P.Monic → P.natDegree = n →
      (∃ b : Module.Basis (∀ i : Fin n, Fin (n - i)) R (SplitAlg P n), ∀ c, b c = ∏ i, SplitAlg.root P n i ^ (c i : ℕ)) ∧
      Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  intro n
  induction n with
  | zero =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard 0⟩
    have hP : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    let f : SplitAlg P 0 →ₐ[R] R :=
      SplitAlg.lift P 0 (A := R) (fun i => i.elim0) (by simp [hP])
    have hfg : (Algebra.ofId R (SplitAlg P 0)).comp f = AlgHom.id R _ :=
      SplitAlg.hom_ext P 0 (fun i => i.elim0)
    have hgf : f.comp (Algebra.ofId R (SplitAlg P 0)) = AlgHom.id R R := Algebra.ext_id _ _ _
    let e : R ≃ₐ[R] SplitAlg P 0 := AlgEquiv.ofAlgHom (Algebra.ofId R _) f hfg hgf
    refine ⟨(Module.Basis.singleton (∀ i : Fin 0, Fin (0 - i)) R).map e.toLinearEquiv, fun c => ?_⟩
    simp [Module.Basis.singleton_apply]
  | succ n ih =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard (n + 1)⟩
    obtain ⟨inst1, inst2, h3, e, he⟩ := splitAlg_succ_equiv R n P hm hd
    have hroot : (Polynomial.map (algebraMap R (AdjoinRoot P)) P).IsRoot (AdjoinRoot.root P) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.isRoot_root P
    have hmul := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hQm : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).Monic := by
      refine Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C (AdjoinRoot.root P)) ?_
      rw [hmul]
      exact hm.map _
    have hQd : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).natDegree = n := by
      rcases subsingleton_or_nontrivial (AdjoinRoot P) with hs | hs
      · exfalso
        have hR : Nontrivial R := by
          rcases subsingleton_or_nontrivial R with hR | hR
          · rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
            omega
          · exact hR
        have hne := (AdjoinRoot.powerBasis' hm).basis.ne_zero
          ⟨0, by rw [AdjoinRoot.powerBasis'_dim, hd]; omega⟩
        exact hne (Subsingleton.elim _ _)
      · rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
          hm.natDegree_map, hd, Polynomial.natDegree_X_sub_C]
        rfl
    obtain ⟨c, hc⟩ := (ih (AdjoinRoot P) _ hQm hQd).1
    let b := (AdjoinRoot.powerBasis' hm).basis.reindex
      (finCongr (by rw [AdjoinRoot.powerBasis'_dim, hd]))
    let c' := c.map e.symm.toLinearEquiv
    refine ⟨(b.smulTower c').reindex (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), fun k => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.smulTower_apply, Fin.prod_univ_succ]
    have hb : ∀ j, b j = AdjoinRoot.root P ^ (j : ℕ) := by
      intro j
      simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
      rfl
    have hinv : ∀ i : Fin n, e.symm (SplitAlg.root _ n i) = SplitAlg.root P (n + 1) i.succ := by
      intro i
      rw [AlgEquiv.symm_apply_eq, he]
    simp only [c', Module.Basis.map_apply, hb, hc, Algebra.smul_def, map_pow, h3, map_prod,
      AlgEquiv.toLinearEquiv_apply, hinv]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ThetaDiag
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private def theta : E →ₗ[B] (U.oddForm p q).Ext where
  toFun z := (U.oddForm p q).el (T.tr z)
    (cornerProj B (U.ep p) (U.ep q) z + cornerProj B (U.ep p) (U.ep q) (T.st z))
  map_add' z w := by
    apply OddForm.Ext.ext
    · simp
    · simp only [map_add, OddForm.od_el, OddForm.od_add]; abel
  map_smul' c z := by
    apply OddForm.Ext.ext
    · simp
    · simp only [map_smul, OddForm.od_el, OddForm.od_smul, RingHom.id_apply, smul_add]

private theorem theta_ev (z : E) : (theta U p q z).ev = T.tr z := rfl

private theorem theta_od (z : E) :
    (theta U p q z).od.1 = U.ep p * (z * U.ep q) + U.ep p * (T.st z * U.ep q) := rfl

private theorem theta_st (z : E) : theta U p q (T.st z) = theta U p q z := by
  apply OddForm.Ext.ext
  · rw [theta_ev, theta_ev, T.tr_st]
  · apply Subtype.ext
    rw [theta_od, theta_od, T.st_st, add_comm]

variable {p q}

private theorem theta_ep (hpq : p ≠ q) {a : ι} (ha : a = p ∨ a = q) : theta U p q (U.ep a) = 1 := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  apply OddForm.Ext.ext
  · rw [theta_ev, OddForm.ev_one, U.tr_ep]
  · apply Subtype.ext
    rw [theta_od, U.st_ep, OddForm.od_one]
    rcases ha with h | h
    · rw [h, ← mul_assoc, (U.coi.idem p).eq, hpq0]
      simp
    · rw [h, (U.coi.idem q).eq, hpq0]
      simp

private theorem theta_diag (hpq : p ≠ q) {a : ι} (ha : a = p ∨ a = q) {u : E}
    (hu : U.ep a * u * U.ep a = u) : theta U p q u = T.tr u • 1 := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hsu : U.ep a * T.st u * U.ep a = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, mul_assoc]
  have L1 : ∀ w : E, U.ep p * w * U.ep p = w → U.ep p * (w * U.ep q) = 0 := by
    intro w hw
    rw [← hw]
    simp [mul_assoc, hpq0]
  have L2 : ∀ w : E, U.ep q * w * U.ep q = w → U.ep p * (w * U.ep q) = 0 := by
    intro w hw
    rw [← hw]
    simp only [mul_assoc]
    rw [← mul_assoc (U.ep p), hpq0, zero_mul]
  apply OddForm.Ext.ext
  · rw [theta_ev, OddForm.ev_smul, OddForm.ev_one, mul_one]
  · apply Subtype.ext
    rw [theta_od, OddForm.od_smul, OddForm.od_one, smul_zero]
    rcases ha with h | h
    · rw [h] at hu hsu
      rw [L1 u hu, L1 _ hsu]
      simp
    · rw [h] at hu hsu
      rw [L2 u hu, L2 _ hsu]
      simp

private theorem theta_pq (hpq : p ≠ q) {u : E} (hu : U.ep p * u * U.ep q = u) :
    (theta U p q u).ev = 0 ∧ (theta U p q u).od.1 = u := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hqp0 : U.ep q * U.ep p = 0 := U.coi.ortho hpq.symm
  have hsu : U.ep q * T.st u * U.ep p = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [theta_ev, ← hu, T.tr_comm, ← mul_assoc, hqp0, zero_mul, map_zero]
  · have h0 : U.ep p * (T.st u * U.ep q) = 0 := by
      rw [← hsu]
      simp [mul_assoc, hpq0]
    rw [theta_od, h0, add_zero, ← mul_assoc, hu]

private theorem theta_qp (hpq : p ≠ q) {u : E} (hu : U.ep q * u * U.ep p = u) :
    (theta U p q u).ev = 0 ∧ (theta U p q u).od.1 = T.st u := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hqp0 : U.ep q * U.ep p = 0 := U.coi.ortho hpq.symm
  have hsu : U.ep p * T.st u * U.ep q = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [theta_ev, ← hu, T.tr_comm, ← mul_assoc, hpq0, zero_mul, map_zero]
  · have h0 : U.ep p * (u * U.ep q) = 0 := by
      rw [← hu]
      simp [mul_assoc, hpq0]
    rw [theta_od, h0, zero_add, ← mul_assoc, hsu]

private theorem theta_mul (hpq : p ≠ q) {a b c : ι} (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (hc : c = p ∨ c = q) {u v : E} (hu : U.ep a * u * U.ep b = u) (hv : U.ep b * v * U.ep c = v) :
    theta U p q (u * v) = theta U p q u * theta U p q v := by
  have hidem : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hL : ∀ {i j : ι} {w : E}, U.ep i * w * U.ep j = w → U.ep i * w = w := by
    intro i j w hw
    calc U.ep i * w = U.ep i * (U.ep i * w * U.ep j) := by rw [hw]
      _ = U.ep i * U.ep i * w * U.ep j := by simp only [mul_assoc]
      _ = w := by rw [hidem, hw]
  have hR : ∀ {i j : ι} {w : E}, U.ep i * w * U.ep j = w → w * U.ep j = w := by
    intro i j w hw
    calc w * U.ep j = U.ep i * w * U.ep j * U.ep j := by rw [hw]
      _ = U.ep i * w * (U.ep j * U.ep j) := by simp only [mul_assoc]
      _ = w := by rw [hidem, hw]
  have hsc : ∀ {i : ι} {w : E}, U.ep i * w * U.ep i = w → w = T.tr w • U.ep i := by
    intro i w hw
    have h := U.corner_eq i w
    rwa [hw] at h
  have hbe : ∀ x y, (U.oddForm p q).be x y = T.tr ((x : E) * T.st (y : E)) := fun x y => rfl
  have hleft : ∀ {i k : ι}, (i = p ∨ i = q) → U.ep i * u * U.ep i = u → U.ep i * v * U.ep k = v →
      theta U p q (u * v) = theta U p q u * theta U p q v := by
    intro i k hi hu' hv'
    have huv : u * v = T.tr u • v := by
      conv_lhs => rw [hsc hu', smul_mul_assoc, hL hv']
    rw [huv, map_smul, theta_diag U hpq hi hu', smul_mul_assoc, one_mul]
  have hright : ∀ {i k : ι}, (k = p ∨ k = q) → U.ep k * v * U.ep k = v → U.ep i * u * U.ep k = u →
      theta U p q (u * v) = theta U p q u * theta U p q v := by
    intro i k hk hv' hu'
    have huv : u * v = T.tr v • u := by
      conv_lhs => rw [hsc hv', mul_smul_comm, hR hu']
    rw [huv, map_smul, theta_diag U hpq hk hv', mul_smul_comm, mul_one]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rw [ha, hb] at hu <;> rw [hb, hc] at hv
  · exact hleft (Or.inl rfl) hu hv
  · exact hleft (Or.inl rfl) hu hv
  · have huv : U.ep p * (u * v) * U.ep p = u * v := by
      rw [← mul_assoc, hL hu, mul_assoc, hR hv]
    rw [theta_diag U hpq (Or.inl rfl) huv]
    obtain ⟨h1, h2⟩ := theta_pq U hpq hu
    obtain ⟨h3, h4⟩ := theta_qp U hpq hv
    apply OddForm.Ext.ext
    · rw [OddForm.ev_smul, OddForm.ev_one, mul_one, OddForm.ev_mul, h1, h3, zero_mul, zero_add, hbe, h2, h4, T.st_st]
    · rw [OddForm.od_smul, OddForm.od_one, smul_zero, OddForm.od_mul, h1, h3, zero_smul, zero_smul, add_zero]
  · exact hright (Or.inr rfl) hv hu
  · exact hright (Or.inl rfl) hv hu
  · have huv : U.ep q * (u * v) * U.ep q = u * v := by
      rw [← mul_assoc, hL hu, mul_assoc, hR hv]
    rw [theta_diag U hpq (Or.inr rfl) huv]
    obtain ⟨h1, h2⟩ := theta_qp U hpq hu
    obtain ⟨h3, h4⟩ := theta_pq U hpq hv
    apply OddForm.Ext.ext
    · rw [OddForm.ev_smul, OddForm.ev_one, mul_one, OddForm.ev_mul, h1, h3, zero_mul, zero_add, hbe, h2, h4, ← T.st_mul, T.tr_st, T.tr_comm]
    · rw [OddForm.od_smul, OddForm.od_one, smul_zero, OddForm.od_mul, h1, h3, zero_smul, zero_smul, add_zero]
  · exact hleft (Or.inr rfl) hu hv
  · exact hleft (Or.inr rfl) hu hv

end

theorem UpperTheory.V.AlgebraTools.vr_hom :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → ∃ φ : E →ₐ[B] Matrix ι ι (U.oddForm p q).Ext, (∀ y, φ y = U.vr p q y) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = algebraMap B _ (T.tr y) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hA, hB, -, hD, -, -, hG⟩ := units_basic T o U
  have hvr : ∀ y i j, U.vr p q y i j = theta U p q (U.x i * y * T.st (U.x j)) := fun _ _ _ => rfl
  have hmul : ∀ y z, U.vr p q (y * z) = U.vr p q y * U.vr p q z := by
    intro y z
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply]
    simp only [hvr]
    have hs : U.x i * (y * z) * T.st (U.x j) = ∑ k, (U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j)) := by
      calc U.x i * (y * z) * T.st (U.x j) = U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j) := by
            rw [hB, mul_one, mul_assoc (U.x i) y z]
        _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact theta_mul U hpq (ho i) (ho k) (ho j) (hG i k y) (hG k j z)
  have hone : U.vr p q 1 = 1 := by
    refine Matrix.ext fun i j => ?_
    rw [hvr, mul_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [U.x_st]
      exact theta_ep U hpq (ho i)
    · rw [hA i j h, map_zero]
  have hadd : ∀ y z, U.vr p q (y + z) = U.vr p q y + U.vr p q z := by
    intro y z
    refine Matrix.ext fun i j => ?_
    simp only [hvr, Matrix.add_apply, mul_add, add_mul, map_add]
  have hzero : U.vr p q 0 = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [hvr, mul_zero, zero_mul, map_zero, Matrix.zero_apply]
  have hsmul : ∀ (r : B) y, U.vr p q (r • y) = r • U.vr p q y := by
    intro r y
    refine Matrix.ext fun i j => ?_
    simp only [hvr, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hcomm : ∀ r : B, U.vr p q (algebraMap B E r) = algebraMap B (Matrix ι ι (U.oddForm p q).Ext) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hsmul, hone]
  have hst : ∀ y, U.vr p q (T.st y) = (U.vr p q y)ᵀ := by
    intro y
    refine Matrix.ext fun i j => ?_
    rw [Matrix.transpose_apply, hvr, hvr, ← theta_st U p q (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have htr : ∀ y, (U.vr p q y).trace = algebraMap B _ (T.tr y) := by
    intro y
    rw [Matrix.trace, Algebra.algebraMap_eq_smul_one, hD y, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, hvr]
    exact theta_diag U hpq (ho i) (hG i i y)
  let φ : E →ₐ[B] Matrix ι ι (U.oddForm p q).Ext := { toFun := U.vr p q, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd, commutes' := hcomm }
  exact ⟨φ, fun y => rfl, hst, htr⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimConst
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.const_bijective :
    ∀ (R ι : Type) [CommRing R] (U : Ultrafilter ι) (m : Ideal R) (Z : Type) [AddCommGroup Z] [Module R Z], IsAdicComplete m Z →
      (∀ j : ℕ, Finite (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) →
      Function.Bijective fun z : Z => ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) fun _ => z := by
  intro R ι _ U m Z _ _ hc hfin
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : ULim.mk (U : Filter ι) (fun j => m ^ j) (fun _ => Z) (fun _ => a - b) = 0 := by
      have h1 : (fun _ : ι => a - b) = (fun _ : ι => a) - (fun _ : ι => b) := rfl
      rw [h1, map_sub]
      exact sub_eq_zero.2 hab
    rw [ULim.mk_eq_zero] at h0
    refine sub_eq_zero.1 (IsHausdorff.haus hc.toIsHausdorff _ fun j => ?_)
    obtain ⟨_, h⟩ := (h0 j).exists
    exact SModEq.zero.2 h
  · obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
    have hz : ∀ j : ℕ, ∃ z : Z, ∀ᶠ i in (U : Filter ι), p i ≡ z [SMOD (m ^ j • ⊤ : Submodule R Z)] := by
      intro j
      haveI := hfin j
      obtain ⟨q, hq⟩ := Ultrafilter.eq_pure_of_finite
        (U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)))
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨z, ?_⟩
      have h : ({Submodule.Quotient.mk z} : Set (Z ⧸ (m ^ j • ⊤ : Submodule R Z))) ∈
          U.map fun i => (Submodule.Quotient.mk (p i) : Z ⧸ (m ^ j • ⊤ : Submodule R Z)) := by
        rw [hq]; simp
      exact h
    choose z hz using hz
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := z) (fun {j k} hjk => by
      obtain ⟨i, h1, h2⟩ := ((hz j).and (hz k)).exists
      exact h1.symm.trans (h2.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hjk))))
    refine ⟨L, ?_⟩
    show ULim.mk _ _ _ _ = _
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
    intro j
    refine (hz j).mono fun i hi => ?_
    exact SModEq.sub_mem.1 (hi.trans (hL j)).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsOneBlock
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.units_one_block :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p : ι), (∀ i, o i = p) → ∃ φ : E ≃ₐ[B] Matrix ι ι B, (∀ y i j, φ y i j = T.tr (U.x i * y * T.st (U.x j))) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = T.tr y := by
  intro B E _ _ _ T ι _ _ o U p ho
  obtain ⟨hA, hB, -, hD, hE, hF, -⟩ := units_basic T o U
  have hidem : U.ep p * U.ep p = U.ep p := (U.coi.idem p).eq
  have hte : T.tr (U.ep p) = 1 := U.tr_ep p
  have hxs : ∀ i j, U.x i * T.st (U.x j) = if i = j then U.ep p else 0 := by
    intro i j
    split_ifs with h
    · subst h
      rw [U.x_st, ho]
    · exact hA i j h
  have hex : ∀ j, U.ep p * U.x j = U.x j := by
    intro j
    have h := U.x_mem j
    rw [ho] at h
    calc U.ep p * U.x j = U.ep p * (U.ep p * U.x j * U.ep j) := by rw [h]
      _ = U.ep p * U.ep p * U.x j * U.ep j := by simp only [mul_assoc]
      _ = U.x j := by rw [hidem, h]
  have hE' : ∀ i j y, U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep p := by
    intro i j y
    have h := hE i j y (by rw [ho i, ho j])
    rwa [ho i] at h
  have hpair : ∀ a b : E, a = T.tr a • U.ep p → b = T.tr b • U.ep p → T.tr (a * b) = T.tr a * T.tr b := by
    intro a b ha hb
    calc T.tr (a * b) = T.tr ((T.tr a • U.ep p) * (T.tr b • U.ep p)) := by rw [← ha, ← hb]
      _ = T.tr a * T.tr b := by rw [smul_mul_smul_comm, hidem, map_smul, hte, smul_eq_mul, mul_one]
  let f : E → Matrix ι ι B := fun y => Matrix.of fun i j => T.tr (U.x i * y * T.st (U.x j))
  let g : Matrix ι ι B → E := fun M => ∑ i, ∑ j, M i j • (T.st (U.x i) * U.x j)
  have hfmul : ∀ y z, f (y * z) = f y * f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.mul_apply]
    calc T.tr (U.x i * (y * z) * T.st (U.x j))
        = T.tr (U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j)) := by
          rw [hB, mul_one, mul_assoc (U.x i) y z]
      _ = ∑ k, T.tr ((U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j))) := by
          simp only [Finset.mul_sum, Finset.sum_mul, map_sum, mul_assoc]
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          exact hpair _ _ (hE' i k y) (hE' k j z)
  have hfadd : ∀ y z, f (y + z) = f y + f z := by
    intro y z
    ext i j
    simp only [f, Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add]
  have hfsmul : ∀ (r : B) y, f (r • y) = r • f y := by
    intro r y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hf1 : f 1 = 1 := by
    ext i j
    simp only [f, Matrix.of_apply, mul_one, hxs, Matrix.one_apply]
    split_ifs <;> simp [hte]
  have hgf : ∀ y, g (f y) = y := by
    intro y
    simp only [g, f, Matrix.of_apply]
    conv_rhs => rw [hF y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := hE' i j y
    set c := T.tr (U.x i * y * T.st (U.x j)) with hc
    rw [h, mul_smul_comm, smul_mul_assoc, mul_assoc, hex]
  have hfg : ∀ M, f (g M) = M := by
    intro M
    ext i j
    have hq : ∀ k l, U.x i * (T.st (U.x k) * U.x l) * T.st (U.x j) = (U.x i * T.st (U.x k)) * (U.x l * T.st (U.x j)) := by
      intro k l
      simp only [mul_assoc]
    simp only [f, g, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, hq, hxs]
    simp [ite_mul, mul_ite, hidem, hte, apply_ite]
  have hfst : ∀ y, f (T.st y) = (f y)ᵀ := by
    intro y
    ext i j
    simp only [f, Matrix.of_apply, Matrix.transpose_apply]
    rw [← T.tr_st (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have hftr : ∀ y, (f y).trace = T.tr y := by
    intro y
    simp only [Matrix.trace, Matrix.diag, f, Matrix.of_apply]
    exact (hD y).symm
  have hcomm : ∀ r : B, f (algebraMap B E r) = algebraMap B (Matrix ι ι B) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hfsmul, hf1]
  let φ : E ≃ₐ[B] Matrix ι ι B := { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg, map_mul' := hfmul, map_add' := hfadd, commutes' := hcomm }
  exact ⟨φ, fun y i j => rfl, hfst, hftr⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.VrReduction
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.vr_reduction :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) {F : Type} [CommRing F] [Algebra B F] (r : E →ₐ[B] Matrix ι ι F) (p q : ι), (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (o i) i 1) → (∀ y i j, o i ≠ o j → r y i j = 0) → (∀ y i j, algebraMap B F (U.vr p q y i j).ev = r y i j) ∧ (o p = p → o q = q → p ≠ q → (U.oddForm p q).red ≤ RingHom.ker (algebraMap B F)) := by
  intro B E _ _ _ T ι _ _ o U F _ _ r p q hst hx hr
  obtain ⟨-, -, h3, h4, h5, -, h7⟩ := units_basic T o U
  have hep : ∀ k, r (U.ep (o k)) = Matrix.single (o k) (o k) 1 := by
    intro k
    rw [← U.x_base k, hx, U.o_o]
  have hz : ∀ w i j, r (U.x i * w * T.st (U.x j)) = Matrix.single (o i) (o j) (r w i j) := by
    intro w i j
    rw [map_mul, map_mul, hst, hx, hx, Matrix.transpose_single, Matrix.single_mul_mul_single, one_mul, mul_one]
  have key : ∀ w i j, algebraMap B F (T.tr (U.x i * w * T.st (U.x j))) = r w i j := by
    intro w i j
    by_cases hij : o i = o j
    · have e := congrArg (fun M => M (o i) (o j)) (hz w i j)
      simp only [Matrix.single_apply_same] at e
      rw [← e]
      conv_rhs => rw [h5 i j w hij, map_smul, hep i, ← hij]
      simp [Matrix.smul_apply, Algebra.smul_def]
    · rw [hr w i j hij, ← h7 i j w, h3 _ _ _ hij, map_zero]
  refine ⟨fun y i j => ?_, ?_⟩
  · show algebraMap B F (T.tr (U.x i * y * T.st (U.x j))) = _
    exact key y i j
  · intro hp hq hpq
    refine Ideal.span_le.mpr ?_
    rintro c ⟨b, b', rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show algebraMap B F (T.tr ((b : E) * T.st (b' : E))) = 0
    obtain ⟨z, hz'⟩ := b.2
    have hb : r (b : E) = 0 := by
      rw [← hz']
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, map_mul]
      have hpp := hep p
      rw [hp] at hpp
      have hqq := hep q
      rw [hq] at hqq
      rw [hpp, hqq, ← mul_assoc, Matrix.single_mul_mul_single, hr z p q (by rw [hp, hq]; exact hpq)]
      simp
    rw [h4, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [key, map_mul, hb, zero_mul, Matrix.zero_apply]
end

