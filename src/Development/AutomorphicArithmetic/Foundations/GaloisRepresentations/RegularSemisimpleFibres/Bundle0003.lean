import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInvStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0015

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PJdIso
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Transport

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')

private theorem coe_phi {n : ℕ} (x : GL (Fin n) F) :
    ((Matrix.GeneralLinearGroup.map r.toRingHom x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F).map r := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private def phiE (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  right_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]

private theorem inPar_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (Matrix.GeneralLinearGroup.map r.toRingHom x) ↔ InPar a x := by
  unfold InPar
  simp only [coe_phi, Matrix.map_apply]
  constructor
  · intro h i j hj hi
    exact (map_eq_zero_iff r r.injective).1 (h i j hj hi)
  · intro h i j hj hi
    rw [h i j hj hi, map_zero]

private theorem ent_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map r) i j = r (ent M i j) := by
  unfold ent
  split_ifs
  · rfl
  · exact (map_zero r).symm

private theorem tl_map (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map r) = (tl a M).map r := by
  ext i j
  simp [tl, ent_map]

private theorem br_map (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map r) = (br a b M).map r := by
  ext i j
  simp [br, ent_map]

private theorem isUnit_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map r) ↔ IsUnit M := by
  have := isUnit_map_iff (r.mapMatrix (m := Fin n)) M
  simpa [RingEquiv.mapMatrix_apply] using this

private theorem coe_toG {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold toG
  rw [dif_pos h]
  rfl

private theorem toG_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map r) = Matrix.GeneralLinearGroup.map r.toRingHom (toG M) := by
  by_cases h : IsUnit M
  · apply Units.ext
    rw [coe_toG ((isUnit_map r M).2 h), coe_phi, coe_toG h]
  · have h' : ¬ IsUnit (M.map r) := fun k => h ((isUnit_map r M).1 k)
    unfold toG
    rw [dif_neg h, dif_neg h', map_one]

private theorem tlG_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (tlG a x) := by
  unfold tlG
  rw [coe_phi, tl_map, toG_map]

private theorem brG_phi (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (brG a b x) := by
  unfold brG
  rw [coe_phi, br_map, toG_map]

include r in
private theorem card_phi (a n : ℕ) :
    Nat.card {p : GL (Fin n) F' // InPar a p} = Nat.card {p : GL (Fin n) F // InPar a p} :=
  (Nat.card_congr ((phiE r n).subtypeEquiv fun x => (inPar_phi r a x).symm)).symm

private theorem gal_id {K : Type} [Field K] (n : ℕ) (y : GL (Fin n) K) : gal (RingHom.id K) n y = y := by
  apply Units.ext
  ext i j
  simp [gal, Matrix.GeneralLinearGroup.map_apply]

private theorem hc_phi (a b : ℕ) (α : GL (Fin a) F' → ℂ) (β : GL (Fin b) F' → ℂ) (n : ℕ)
    (g : GL (Fin n) F) :
    hc a b α β n (Matrix.GeneralLinearGroup.map r.toRingHom g) =
      hc a b (fun x => α (Matrix.GeneralLinearGroup.map r.toRingHom x))
        (fun x => β (Matrix.GeneralLinearGroup.map r.toRingHom x)) n g := by
  unfold hc hcTw
  simp only [gal_id]
  rw [card_phi r a n, ← finsum_comp_equiv (phiE r n)]
  congr 1
  refine finsum_congr fun y => ?_
  have e : (phiE r n y)⁻¹ * Matrix.GeneralLinearGroup.map r.toRingHom g * phiE r n y =
      Matrix.GeneralLinearGroup.map r.toRingHom (y⁻¹ * g * y) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  simp only [inPar_phi, tlG_phi, brG_phi]

private theorem detc_phi (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ)
    (t k : ℕ) (x : GL (Fin t) F) :
    detc θ t k (Matrix.GeneralLinearGroup.map r.toRingHom x) = detc (θ.comp j.toMonoidHom) t k x := by
  unfold detc
  have e : ((x : Matrix (Fin t) (Fin t) F).map r).det = r (x : Matrix (Fin t) (Fin t) F).det :=
    (RingHom.map_det r.toRingHom _).symm
  rw [coe_phi, e, ← hj]
  rfl

end Transport

theorem UpperTheory.Gal.InertialTypesAlt.jdIso :
    CuspIso → JDIso := by
  intro hC F F' _ _ _ r j hj θ D L n g
  have hJ : ∀ (L : List (ℕ × ℕ)) (n : ℕ) (g : GL (Fin n) F),
      J θ L n (Matrix.GeneralLinearGroup.map r.toRingHom g) = J (θ.comp j.toMonoidHom) L n g := by
    intro L
    induction L with
    | nil => intro n g; rfl
    | cons p L ih =>
      intro n g
      rw [J_cons, J_cons, hc_phi]
      congr 1
      · funext x
        exact hC F F' r j hj θ p.1 p.2 x
      · funext x
        exact ih _ x
  induction D generalizing n g with
  | nil => exact hJ L n g
  | cons p D ih =>
    rw [JD_cons, JD_cons, hc_phi]
    congr 1
    · funext x
      exact detc_phi r j hj θ p.1 p.2 x
    · funext x
      exact ih _ x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLeTop
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem label_le_preserves_splitting (h₁ : LiftOk) (h₂ : LiftBlocks) {a b : Lbl} (ha : a.Ok) (hab : a.Le b) :
    b.Ok ∧ b.rk = a.rk ∧ ∀ Q, b.Splits Q → a.Splits Q ∧ b.blocks Q = a.blocks Q := by
  induction hab with
  | refl => exact ⟨ha, rfl, fun Q hQ => ⟨hQ, rfl⟩⟩
  | @tail m c _ hstep ih =>
    obtain ⟨l, hl, rfl⟩ := hstep
    obtain ⟨hb, hrk, hS⟩ := ih
    obtain ⟨hc, hrk'⟩ := h₁ m l hl hb
    refine ⟨hc, hrk'.trans hrk, fun Q hQ => ?_⟩
    obtain ⟨hbQ, hblk⟩ := h₂ m l Q hl hb hQ
    obtain ⟨haQ, hblk'⟩ := hS Q hbQ
    exact ⟨haQ, hblk.trans hblk'⟩

theorem UpperTheory.Gal.InertialTypesAlt.leTop :
    LiftOk → LiftBlocks → LeRank → LeTop := by
  intro h₁ h₂ h₃ a b ha hab hs
  obtain ⟨hb, hrk, hS⟩ := label_le_preserves_splitting h₁ h₂ ha hab
  obtain ⟨f, hf, hq, hd⟩ := hs
  obtain ⟨c, hc, hbq, hp⟩ := h₃ a b ha hab
  have hcf : c = f := Nat.pow_right_injective ha.1 (hbq.symm.trans hq)
  subst hcf
  have hone : ∀ p ∈ b.L, p.1 = 1 := by
    intro p hpL
    obtain ⟨r, hr, hpr⟩ := hp p hpL
    have hr0 : 0 < r.1 := (ha.2.2 r hr).1
    rw [Nat.gcd_eq_left (hd r hr)] at hpr
    exact Nat.eq_of_mul_eq_mul_right hr0 (by simpa using hpr)
  refine ⟨hb, hrk, hone, (hS b.q ⟨1, Nat.one_pos, (pow_one _).symm, fun p hpL => ?_⟩).2⟩
  rw [hone p hpL]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftBlocks
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma geo_mul (x l : ℕ) (hx : 1 ≤ x) :
    (∑ i ∈ Finset.range l, x ^ i) * (x - 1) = x ^ l - 1 := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have := geom_sum_mul_add y l
  simp only [Nat.add_sub_cancel]
  omega

private lemma div_id (N a b S : ℕ) (ha : 0 < a) (hS : S * a = b) (hb : b ∣ N) (hb0 : 0 < b) :
    S * (N / b) = N / a := by
  obtain ⟨c, rfl⟩ := hb
  rw [Nat.mul_div_cancel_left c hb0]
  subst hS
  rw [show S * a * c = a * (S * c) by ring, Nat.mul_div_cancel_left _ ha]

private lemma sub_one_dvd (x e : ℕ) : x - 1 ∣ x ^ e - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow x 1 e

private lemma ms_sum {α : Type*} (n : ℕ) (g : ℕ → α) :
    (Multiset.range n).map g = ∑ j ∈ Finset.range n, ({g j} : Multiset α) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ih, add_comm,
      Multiset.singleton_add]

private lemma list_sum {α : Type*} (l : ℕ) (F : ℕ → Multiset α) :
    ((List.range l).map F).sum = ∑ i ∈ Finset.range l, F i := by
  induction l with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private lemma block_mul {α : Type*} (l m' : ℕ) (g : ℕ → α) :
    ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m', ({g (i + l * j)} : Multiset α) =
      ∑ n ∈ Finset.range (l * m'), ({g n} : Multiset α) := by
  induction m' with
  | zero => simp
  | succ m ih =>
    calc ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range (m + 1), ({g (i + l * j)} : Multiset α)
        = ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            {g (i + l * m)}) := Finset.sum_congr rfl fun i _ => Finset.sum_range_succ _ m
      _ = ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m, ({g (i + l * j)} : Multiset α) +
            ∑ i ∈ Finset.range l, ({g (i + l * m)} : Multiset α) := Finset.sum_add_distrib
      _ = ∑ n ∈ Finset.range (l * (m + 1)), ({g n} : Multiset α) := by
          rw [ih, Nat.mul_succ, Finset.sum_range_add]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]

private lemma perm_map {α : Type*} (l m : ℕ) (hc : Nat.Coprime l m) (hm : 0 < m) (G : ℕ → α)
    (hG : ∀ n, G (n + m) = G n) :
    (Multiset.range m).map (fun j => G (l * j)) = (Multiset.range m).map G := by
  have hper : Function.Periodic G m := hG
  have hinj : Set.InjOn (fun j => l * j % m) (Finset.range m : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < m := by simpa using hx
    have hy' : y < m := by simpa using hy
    have h1 : l * x ≡ l * y [MOD m] := hxy
    have h2 : x ≡ y [MOD m] := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hx' hy'
  have himg : (Finset.range m).image (fun j => l * j % m) = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (Nat.mod_lt _ hm)
    · rw [Finset.card_image_of_injOn hinj]
  rw [ms_sum, ms_sum]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun j _ => by rw [hper.map_mod_nat]

private def lbk (Q q : ℕ) (p : ℕ × ℕ) : Multiset (ℕ × ZMod (Q - 1)) :=
  (Multiset.range p.1).map fun j =>
    ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))

private lemma lbk_dvd (Q q l m' k : ℕ) :
    ((List.range l).map fun i => lbk Q (q ^ l) (m', k * q ^ i)).sum = lbk Q q (l * m', k) := by
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j =>
    ((1 : ℕ), ((k * q ^ j * ((Q - 1) / (q ^ (l * m') - 1)) : ℕ) : ZMod (Q - 1))) with hGdef
  have h1 : ∀ i, lbk Q (q ^ l) (m', k * q ^ i) =
      ∑ j ∈ Finset.range m', ({G (i + l * j)} : Multiset _) := by
    intro i
    rw [← ms_sum (n := m') (g := fun j => G (i + l * j))]
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef, ← pow_mul, pow_add, mul_assoc]
  have h2 : lbk Q q (l * m', k) = (Multiset.range (l * m')).map G := rfl
  rw [list_sum, h2, ms_sum, ← block_mul]
  exact Finset.sum_congr rfl fun i _ => h1 i

private lemma lbk_ndvd (Q q l f m k : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f)
    (hm : 0 < m) (hmf : m ∣ f) (hnd : ¬ l ∣ m) :
    lbk Q (q ^ l) (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) = lbk Q q (m, k) := by
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hql : 1 < (q ^ l) ^ m := Nat.one_lt_pow hm.ne' (Nat.one_lt_pow hl.ne_zero (by omega))
  have hT : (∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ m - 1) = (q ^ l) ^ m - 1 := by
    have := geo_mul (q ^ m) l hqm.le
    simp only [← pow_mul] at this ⊢
    rw [this, Nat.mul_comm l m]
  have hd1 : (q ^ l) ^ m - 1 ∣ Q - 1 := by
    obtain ⟨e, rfl⟩ := hmf
    rw [hQ, pow_mul]
    exact sub_one_dvd _ e
  have hd2 : q ^ m - 1 ∣ Q - 1 := (Dvd.intro_left _ hT).trans hd1
  have hC := div_id (Q - 1) (q ^ m - 1) ((q ^ l) ^ m - 1) _ (by omega) hT hd1 (by omega)
  have hC2 : (Q - 1) / (q ^ m - 1) * (q ^ m - 1) = Q - 1 := Nat.div_mul_cancel hd2
  set C := (Q - 1) / (q ^ m - 1) with hCdef
  set T := ∑ i ∈ Finset.range l, q ^ (m * i) with hTdef
  set G : ℕ → ℕ × ZMod (Q - 1) := fun j => ((1 : ℕ), ((k * q ^ j * C : ℕ) : ZMod (Q - 1))) with hGdef
  have hG : ∀ n, G (n + m) = G n := by
    intro n
    obtain ⟨u, hu⟩ : ∃ u, q ^ m = u + 1 := ⟨q ^ m - 1, by omega⟩
    have hCu : C * u = Q - 1 := by rw [hu] at hC2; simpa using hC2
    have : k * q ^ (n + m) * C = k * q ^ n * C + k * q ^ n * (Q - 1) := by
      rw [pow_add, hu, ← hCu]; ring
    simp only [hGdef, this]
    push_cast [ZMod.natCast_self]
    simp [ZMod.natCast_self]
  have hL : lbk Q (q ^ l) (m, k * T) = (Multiset.range m).map fun j => G (l * j) := by
    unfold lbk
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [hGdef]
    rw [← hC, pow_mul]
    congr 2
    ring
  rw [hL, perm_map l m ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd) hm G hG]
  rfl

private lemma lbkL (Q q l f : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hQ : Q = (q ^ l) ^ f) :
    ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1) → (∀ p ∈ liftAll q l L, p.1 ∣ f) →
      ((liftAll q l L).map (lbk Q (q ^ l))).sum = (L.map (lbk Q q)).sum := by
  intro L
  induction L with
  | nil => intro _ _; simp [liftAll]
  | cons p L ih =>
    intro h0 hd
    obtain ⟨m, k⟩ := p
    have hsplit : liftAll q l ((m, k) :: L) = (if l ∣ m then liftL q l [(m, k)] else
        [(m, k * ∑ i ∈ Finset.range l, q ^ (m * i))]) ++ liftAll q l L := by
      simp [liftAll]
    rw [hsplit] at hd ⊢
    have hdL : ∀ p ∈ liftAll q l L, p.1 ∣ f := fun p hp => hd p (List.mem_append_right _ hp)
    rw [List.map_append, List.sum_append, ih (fun p hp => h0 p (List.mem_cons_of_mem _ hp)) hdL,
      List.map_cons, List.sum_cons]
    congr 1
    by_cases hlm : l ∣ m
    · obtain ⟨m', rfl⟩ := hlm
      have : liftL q l [(l * m', k)] = (List.range l).map fun i => (m', k * q ^ i) := by
        simp [liftL, Nat.mul_div_cancel_left _ hl.pos]
      rw [if_pos (dvd_mul_right _ _), this, List.map_map]
      exact lbk_dvd Q q l m' k
    · rw [if_neg hlm] at hd ⊢
      have hmf : m ∣ f := hd (m, _) (List.mem_append_left _ (List.mem_singleton.2 rfl))
      simpa using lbk_ndvd Q q l f m k hq hl hQ (h0 (m, k) List.mem_cons_self) hmf hlm

private lemma splitsL (q l f : ℕ) (hl : l.Prime) (L : List (ℕ × ℕ))
    (hd : ∀ p ∈ liftAll q l L, p.1 ∣ f) : ∀ p ∈ L, p.1 ∣ l * f := by
  rintro ⟨m, k⟩ hp
  by_cases hlm : l ∣ m
  · have h1 : (m / l, k * q ^ 0) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp only [if_pos hlm, liftL]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.mem_map.2 ⟨0, List.mem_range.2 hl.pos, rfl⟩
    have h2 := hd _ h1
    obtain ⟨m', rfl⟩ := hlm
    rw [Nat.mul_div_cancel_left _ hl.pos] at h2
    exact Nat.mul_dvd_mul_left l h2
  · have h1 : (m, k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∈ liftAll q l L := by
      refine List.mem_flatMap.2 ⟨(m, k), hp, ?_⟩
      simp [if_neg hlm]
    exact (hd _ h1).mul_left l

theorem UpperTheory.Gal.InertialTypesAlt.liftBlocks :
    LiftBlocks := by
  intro a l Q hl ha hs
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq, hD, hL⟩ := ha
  obtain ⟨f, hf, hQ, hdiv⟩ := hs
  have hq' : 2 ≤ q := hq
  have hQ' : Q = (q ^ l) ^ f := hQ
  have hdiv' : ∀ p ∈ liftAll q l L, p.1 ∣ f := hdiv
  have hL0 : ∀ p ∈ L, 0 < p.1 := fun p hp => (hL p hp).1
  refine ⟨⟨l * f, Nat.mul_pos hl.pos hf, by rw [hQ', pow_mul], splitsL q l f hl L hdiv'⟩, ?_⟩
  have hS := geo_mul q l (by omega)
  have hql : 1 < q ^ l := Nat.one_lt_pow hl.ne_zero (by omega)
  have hDid : (∑ i ∈ Finset.range l, q ^ i) * ((Q - 1) / (q ^ l - 1)) = (Q - 1) / (q - 1) :=
    div_id (Q - 1) (q - 1) (q ^ l - 1) _ (by omega) hS (by rw [hQ']; exact sub_one_dvd _ f) (by omega)
  have hDpart : ((⟨q, D, L⟩ : Lbl).lift l).D.map (fun p =>
        (p.1, ((p.2 * ((Q - 1) / (((⟨q, D, L⟩ : Lbl).lift l).q - 1)) : ℕ) : ZMod (Q - 1)))) =
      D.map (fun p => (p.1, ((p.2 * ((Q - 1) / (q - 1)) : ℕ) : ZMod (Q - 1)))) := by
    show (D.map _).map _ = _
    rw [List.map_map]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp]
    rw [← hDid, mul_assoc]
    rfl
  have hLpart := lbkL Q q l f hq' hl hQ' L hL0 hdiv'
  unfold Lbl.blocks
  rw [hDpart]
  congr 1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PMeetsIff
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sum_ne_iff {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (κ : Representation ℂ H W) :
    (∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0) ↔
      ∃ f : W →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g x, f (κ g x) = ρ g (f x) := by
  classical
  haveI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have key := Representation.card_inv_mul_sum_char_mul_char_eq_finrank κ ρ
  have hsum : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g * κ.character g⁻¹ :=
    Finset.sum_congr rfl fun g _ => mul_comm _ _
  have hc : (Nat.card H : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [hsum]
  constructor
  · intro h
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at key
      exact h ((mul_eq_zero.mp key).resolve_left hc)
    haveI := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hpos)
    obtain ⟨φ, hφ⟩ := exists_ne (0 : Representation.IntertwiningMap κ ρ)
    refine ⟨φ.toLinearMap, ?_, fun g x => Representation.IntertwiningMap.isIntertwining κ ρ φ g x⟩
    intro h0
    exact hφ (Representation.IntertwiningMap.ext (by simpa using h0))
  · rintro ⟨f, hf0, hf⟩
    let φ := f.intertwiningMap_of_isIntertwiningMap κ ρ hf
    have hφ : φ ≠ 0 := by
      intro h0
      apply hf0
      ext x
      have := congrArg (fun ψ : Representation.IntertwiningMap κ ρ => ψ x) h0
      simpa [φ] using this
    have hpos : Module.finrank ℂ (Representation.IntertwiningMap κ ρ) ≠ 0 := by
      rw [← (Representation.invariantsEquivIntertwiningMap κ ρ).finrank_eq]
      apply Nat.pos_iff_ne_zero.mp
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨(Representation.invariantsEquivIntertwiningMap κ ρ).symm φ, ?_⟩
      simpa using hφ
    intro hs
    rw [hs, mul_zero] at key
    exact hpos (by exact_mod_cast key.symm)

theorem UpperTheory.Gal.InertialTypesAlt.meetsIff :
    MeetsIff := by
  intro H V W _ _ _ _ _ _ _ _ ρ κ
  classical
  haveI := Fintype.ofFinite H
  have hstar : ∀ g : H, star (LinearMap.trace ℂ W (κ g)) = κ.character g⁻¹ := by
    intro g
    have hmem : (fun g => algebraMap ℂ ℂ (κ.character g)) ∈ GlobalTheory.BI.Virt ℂ ℂ H :=
      AddSubgroup.subset_closure (GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ H W κ).1
    have := GlobalTheory.T.star_virtualCharacter_eq_apply_inv H _ hmem g
    change star (κ.character g) = _
    simpa using this
  have hM : Meets ρ (fun g => LinearMap.trace ℂ W (κ g)) ↔
      ∑ g : H, κ.character g⁻¹ * ρ.character g ≠ 0 := by
    unfold Meets
    rw [finsum_eq_sum_of_fintype]
    simp only [hstar]
    rfl
  have hswap : (∑ g : H, κ.character g⁻¹ * ρ.character g) =
      ∑ g : H, ρ.character g⁻¹ * κ.character g :=
    Fintype.sum_equiv (Equiv.inv H) _ _ fun g => by simp [mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hM, hswap]
    exact sum_ne_iff κ ρ
  · rw [hM]
    exact sum_ne_iff ρ κ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTameChars
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.tameChars :
    TameChars := by
  intro k _ _ _ _ N V _ _ π ω h
  obtain ⟨μ, hμ, H⟩ := h
  have hs : ∀ j, IsSmoothChar (μ j) := fun j => isSmoothChar_of_isTame (hμ j).isTame
  refine ⟨μ, hs, fun j u hu => ?_, ?_, fun j u => hμ j u⟩
  · exact (hμ j).isTame u hu
  · have := hasSupport_of_isCuspSupport H
    exact this
end

