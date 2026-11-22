import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.AnyLevel
import Development.AutomorphicArithmetic.MeanSquareBounds.realDecomp
import Development.AutomorphicArithmetic.MeanSquareBounds.Bundle0001

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.KerChiAny
section
open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top

private theorem ann_zpowers {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (u : (ZMod M)ˣ) :
    u ∈ EvenGrp.ann (Subgroup.zpowers χ) ↔ χ u = 1 := by
  rw [EvenGrp.mem_ann]
  constructor
  · intro h
    exact h χ (Subgroup.mem_zpowers χ)
  · intro h ψ hψ
    rw [Subgroup.zpowers_eq_closure] at hψ
    induction hψ using Subgroup.closure_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h
    | one => exact MulChar.one_apply_coe u
    | mul x y _ _ hx hy => rw [MulChar.mul_apply, hx, hy, one_mul]
    | inv x _ hx => rw [MulChar.inv_apply_eq_inv', hx, inv_one]

private theorem xiW_eq_one {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (e : ℕ)
    (u : (ZMod (Nat.lcm (2 ^ (e + 2)) M))ˣ) :
    EvenGrp.xiW (Subgroup.zpowers χ) e u = 1 ↔ χ (ZMod.unitsMap (Nat.dvd_lcm_right _ _) u : (ZMod M)ˣ) = 1 := by
  change QuotientGroup.mk' _ (ZMod.unitsMap (Nat.dvd_lcm_right (2 ^ (e + 2)) M) u) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ann_zpowers]

private theorem dvd_QS {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (hχ : χ.IsPrimitive) (e : ℕ) :
    M ∣ EvenGrp.QS (Subgroup.zpowers χ) e := by
  obtain ⟨hQL, h2Q, hgood⟩ := EvenGrp.good_QS (Subgroup.zpowers χ) e
  set Q := EvenGrp.QS (Subgroup.zpowers χ) e with hQ
  haveI : NeZero ((2 ^ (e + 2)).lcm M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  have hf : χ.FactorsThrough (Q.gcd M) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_right Q M)).mpr ?_
    intro x hx
    rw [MonoidHom.mem_ker, unitsMap_eq_one_iff] at hx
    obtain ⟨z, hz1, hz2⟩ := Nat.chineseRemainder' hx.symm
    have hzM : z.Coprime M := hz2.gcd_eq.trans (ZMod.val_coe_unit_coprime x)
    have hzQ : z.Coprime Q := hz1.gcd_eq.trans (Nat.gcd_one_left Q)
    have hz2e : z.Coprime (2 ^ (e + 2)) := hzQ.coprime_dvd_right h2Q
    have hzL : z.Coprime ((2 ^ (e + 2)).lcm M) :=
      (Nat.Coprime.mul_right hz2e hzM).coprime_dvd_right (Nat.lcm_dvd_mul _ _)
    have hw := hgood (ZMod.unitOfCoprime z hzL) (by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact ((Nat.mod_modEq z _).of_dvd hQL).trans hz1)
    rw [xiW_eq_one, unitsMap_unitOfCoprime] at hw
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    have hx' : ((ZMod.unitOfCoprime z (hzL.coprime_dvd_right (Nat.dvd_lcm_right _ _)) : (ZMod M)ˣ) : ZMod M) = x := by
      rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (x : ZMod M)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hz2
    rw [← hx']
    exact hw
  have hc0 : χ.conductor ≤ Q.gcd M := Nat.sInf_le hf
  have hχ' : χ.conductor = M := hχ
  rw [hχ'] at hc0
  have hg : Q.gcd M = M :=
    le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.gcd_dvd_right _ _)) hc0
  have h := Nat.gcd_dvd_left Q M
  rwa [hg] at h

private theorem hcl_nat (e a : ℕ) (h : a.Coprime (2 ^ (e + 2))) :
    hcl e (ZMod.unitOfCoprime a h) = 1 ↔ (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) := by
  have h1 : hcl e 1 = 1 := rfl
  rw [← h1, hcl_eq_hcl_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_neg,
    Units.val_one]
  apply or_congr
  · rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  · rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff,
      Nat.modEq_zero_iff_dvd]

private theorem art_iff (D : ModData) {q d : ℕ} (hH : HostHyp q d) (a : ℕ) (h : a.Coprime (D.m * q * d)) :
    D.art hH (ZMod.unitOfCoprime a h) = 1 ↔
      D.eta (ZMod.unitOfCoprime a (h.coprime_dvd_right (D.m_dvd q d))) = 1 ∧
        jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1 := by
  have hv : ((ZMod.unitOfCoprime a h : ZMod (D.m * q * d)).val) ≡ a [MOD D.m * q * d] := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq a _
  have jq : jacobiSym (((ZMod.unitOfCoprime a h : ZMod (D.m * q * d)).val : ℕ) : ℤ) q =
      jacobiSym (a : ℤ) q := D7.jac_congr (hv.of_dvd (D.q_dvd q d))
  have jd : jacobiSym (((ZMod.unitOfCoprime a h : ZMod (D.m * q * d)).val : ℕ) : ℤ) d =
      jacobiSym (a : ℤ) d := D7.jac_congr (hv.of_dvd (D.d_dvd q d))
  have hm : ZMod.unitsMap (D.m_dvd q d) (ZMod.unitOfCoprime a h) =
      ZMod.unitOfCoprime a (h.coprime_dvd_right (D.m_dvd q d)) := unitsMap_unitOfCoprime _ _ _
  constructor
  · intro h1
    have a1 : (D.art hH (ZMod.unitOfCoprime a h)).1.1 = 1 := by rw [h1]; rfl
    have a2 : (D.art hH (ZMod.unitOfCoprime a h)).1.2 = 1 := by rw [h1]; rfl
    have a3 : (D.art hH (ZMod.unitOfCoprime a h)).2 = 1 := by rw [h1]; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [D.art_snd, a1, map_one, mul_one, D.toA_eq_one_iff, hm] at a3
      exact a3
    · rw [← jq, ← D.art_ps hH, a1, Units.val_one]
    · rw [← jd, ← D.art_ch hH, a2, Units.val_one]
  · rintro ⟨he, hq, hd⟩
    apply D.art_eq_one
    · apply Units.ext
      rw [D.art_ps, jq, hq, Units.val_one]
    · apply Units.ext
      rw [D.art_ch, jd, hd, Units.val_one]
    · rw [hm]
      exact he

theorem UpperTheory.Top.kerChiAny :
    ∀ (ψ : PChar) (e q d : ℕ) (hH : HostHyp q d) (hc : Nat.Coprime ψ.N (q * d)) (he : 2 ≤ e)
      (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ ψ.N → jacobiSym (-(d : ℤ)) l = 1),
      KerChi ψ (AnyGrp.host (Subgroup.zpowers ψ.χ) e hH hc he hs) := by
  intro ψ e q d hH hc he hs
  haveI := ψ.ne
  set D := AnyGrp.data (Subgroup.zpowers ψ.χ) e with hD
  have hM : ψ.N ∣ D.m := dvd_QS ψ.χ ψ.prim e
  refine ⟨hM, fun a h => ?_⟩
  have h' : a.Coprime (D.m * q * d) := h
  change D.art hH (ZMod.unitOfCoprime a h') = 1 ↔
    (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ ψ.val a = 1 ∧
      jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1
  refine (art_iff D hH a h').trans ?_
  have h1 : a.Coprime D.m := h'.coprime_dvd_right (D.m_dvd q d)
  have hT : 2 ^ (e + 2) ∣ D.m := D.tower
  have h2 : a.Coprime (2 ^ (e + 2)) := h1.coprime_dvd_right hT
  have hL : (2 ^ (e + 2)).lcm ψ.N ∣ D.m := Nat.lcm_dvd hT hM
  have hcL : a.Coprime ((2 ^ (e + 2)).lcm ψ.N) := h1.coprime_dvd_right hL
  have hcl1 : D.cl (ZMod.unitOfCoprime a h1) = hcl e (ZMod.unitOfCoprime a h2) := by
    rw [ModData.cl, MonoidHom.comp_apply, unitsMap_unitOfCoprime]
    rfl
  have hxi : D.ξ (ZMod.unitOfCoprime a h1) =
      EvenGrp.xiW (Subgroup.zpowers ψ.χ) e (ZMod.unitOfCoprime a hcL) := by
    rw [← EvenGrp.xi_unitsMap, unitsMap_unitOfCoprime]
    rfl
  have hw : EvenGrp.xiW (Subgroup.zpowers ψ.χ) e (ZMod.unitOfCoprime a hcL) = 1 ↔ ψ.val a = 1 := by
    rw [xiW_eq_one, unitsMap_unitOfCoprime, ZMod.coe_unitOfCoprime]
    rfl
  have key : D.eta (ZMod.unitOfCoprime a h1) = 1 ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ ψ.val a = 1 := by
    rw [ModData.eta, MonoidHom.prod_apply, Prod.mk_eq_one]
    refine Iff.and ?_ ?_
    · rw [hcl1]
      exact hcl_nat e a h2
    · rw [hxi]
      exact hw
  rw [key, and_assoc]
end

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.OrdAny
section
open Formalism.HC Formalism.FrobeniusOrbits UpperTheory.Top

private theorem ord_eq_mul (D : ModData) : D.frame.ord = Nat.card (D.cl.ker.map D.ξ) * 2 ^ D.e := by
  rw [D.ord_eq, ← Group.card_H D.e]
  have hk : Nat.card D.R = Nat.card D.p1.ker * Nat.card (HGrp D.e) := by
    rw [← Subgroup.card_mul_index D.p1.ker, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr D.projection_surjective, Subgroup.card_top]
  rw [hk]
  congr 1
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨(x.1 : HGrp D.e × D.B).2, ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨⟨y, u, hu⟩, hx⟩ := x
    have h1 : y.1 = 1 := hx
    refine ⟨u, ?_, ?_⟩
    · change D.cl u = 1
      rw [← h1, ← hu]
      rfl
    · exact congrArg Prod.snd hu
  · rintro ⟨⟨x, hx⟩, hx1⟩ ⟨⟨y, hy⟩, hy1⟩ h
    have a1 : x.1 = 1 := hx1
    have b1 : y.1 = 1 := hy1
    have h2 : x.2 = y.2 := congrArg Subtype.val h
    ext1
    ext1
    exact Prod.ext (a1.trans b1.symm) h2
  · rintro ⟨b, u, hu, rfl⟩
    refine ⟨⟨⟨D.eta u, u, rfl⟩, ?_⟩, rfl⟩
    exact hu

private theorem cl_eq_one_iff (D : ModData) (u : (ZMod D.m)ˣ) :
    D.cl u = 1 ↔ ZMod.unitsMap D.tower u = 1 ∨ ZMod.unitsMap D.tower u = -1 := by
  change (QuotientGroup.mk' _ (ZMod.unitsMap D.tower u) : HGrp D.e) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    rcases Int.even_or_odd k with hk2 | hk2
    · exact Or.inl hk2.neg_one_zpow
    · exact Or.inr hk2.neg_one_zpow
  · rintro (h | h)
    · exact ⟨0, by rw [h, zpow_zero]⟩
    · exact ⟨1, by rw [h, zpow_one]⟩

private theorem unitsMap_unitsMap {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (u : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 u) = ZMod.unitsMap (h1.trans h2) u := by
  rw [← ZMod.unitsMap_comp h1 h2]
  rfl

private theorem step {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ) (b : EvenGrp.B Ξ)
    (hb : b ∈ (AnyGrp.data Ξ (e + 1)).cl.ker.map (AnyGrp.data Ξ (e + 1)).ξ) :
    b ∈ (AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ := by
  obtain ⟨u, hu, rfl⟩ := hb
  have hL : (2 ^ (e + 2)).lcm M ∣ (2 ^ (e + 1 + 2)).lcm M :=
    Nat.lcm_dvd (dvd_trans (pow_dvd_pow 2 (by omega)) (Nat.dvd_lcm_left _ _)) (Nat.dvd_lcm_right _ _)
  haveI : NeZero ((2 ^ (e + 1 + 2)).lcm M) := ⟨Nat.lcm_ne_zero (by positivity) (NeZero.ne M)⟩
  obtain ⟨w, rfl⟩ := ZMod.unitsMap_surjective (EvenGrp.QS_dvd Ξ (e + 1)) u
  have h23 : 2 ^ (e + 2) ∣ 2 ^ (e + 1 + 2) := pow_dvd_pow 2 (by omega)
  have t0 : 2 ^ (e + 2) ∣ EvenGrp.QS Ξ e := (AnyGrp.data Ξ e).tower
  have t1 : 2 ^ (e + 1 + 2) ∣ EvenGrp.QS Ξ (e + 1) := (AnyGrp.data Ξ (e + 1)).tower
  refine ⟨ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hL w), ?_, ?_⟩
  · have hu' := (cl_eq_one_iff (AnyGrp.data Ξ (e + 1)) (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) w)).mp hu
    refine (cl_eq_one_iff (AnyGrp.data Ξ e) (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hL w))).mpr ?_
    change ZMod.unitsMap t0 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hL w)) = 1 ∨
      ZMod.unitsMap t0 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ e) (ZMod.unitsMap hL w)) = -1
    change ZMod.unitsMap t1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) w) = 1 ∨
      ZMod.unitsMap t1 (ZMod.unitsMap (EvenGrp.QS_dvd Ξ (e + 1)) w) = -1 at hu'
    rw [unitsMap_unitsMap, unitsMap_unitsMap]
    rw [unitsMap_unitsMap] at hu'
    rcases hu' with h | h
    · left
      have := congrArg (ZMod.unitsMap h23) h
      rw [unitsMap_unitsMap, map_one] at this
      exact this
    · right
      have := congrArg (ZMod.unitsMap h23) h
      rw [unitsMap_unitsMap, D7.unitsMap_neg_one] at this
      exact this
  · change EvenGrp.xi Ξ e _ = EvenGrp.xi Ξ (e + 1) _
    rw [EvenGrp.xi_unitsMap, EvenGrp.xi_unitsMap]
    change QuotientGroup.mk' _ (ZMod.unitsMap _ (ZMod.unitsMap hL w)) = QuotientGroup.mk' _ (ZMod.unitsMap _ w)
    rw [unitsMap_unitsMap]

theorem UpperTheory.Top.ordAny :
    ∀ (M : ℕ) [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)), ∃ c e0 : ℕ, 1 ≤ c ∧ c ≤ Nat.card Ξ ∧
      ∀ e ≥ e0, (AnyGrp.frame Ξ e).ord = c * 2 ^ e := by
  intro M _ Ξ
  haveI hB : Finite (EvenGrp.B Ξ) :=
    Nat.finite_of_card_ne_zero (by rw [EvenGrp.card_B]; exact Nat.card_pos.ne')
  haveI : ∀ e, Finite (AnyGrp.data Ξ e).B := fun _ => hB
  let n : ℕ → ℕ := fun e => Nat.card ((AnyGrp.data Ξ e).cl.ker.map (AnyGrp.data Ξ e).ξ)
  have hanti : Antitone n :=
    antitone_nat_of_succ_le (fun e => Subgroup.card_le_of_le (fun b hb => step Ξ e b hb))
  have hpos : ∀ e, 1 ≤ n e := fun e => Nat.card_pos
  have hle : ∀ e, n e ≤ Nat.card Ξ := fun e => by
    rw [← EvenGrp.card_B]
    exact Subgroup.card_le_card_group _
  obtain ⟨e0, he0⟩ : sInf (Set.range n) ∈ Set.range n := Nat.sInf_mem (Set.range_nonempty n)
  refine ⟨n e0, e0, hpos e0, hle e0, fun e he => ?_⟩
  change (AnyGrp.data Ξ e).frame.ord = _
  rw [ord_eq_mul]
  have h1 : n e ≤ n e0 := hanti he
  have h2 : n e0 ≤ n e := he0 ▸ Nat.sInf_le ⟨e, rfl⟩
  have h3 : n e = n e0 := le_antisymm h1 h2
  exact congrArg (· * 2 ^ e) h3
end

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.RealSplit
section
open Formalism.HC UpperTheory.Top

private theorem UpperTheory.Top.realSplit_step (f q i : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f) (hξ : ξ.IsPrimitive)
    (hq : q.Prime) (h2 : q ≠ 2) (hf : ¬ q ∣ f) (hi : i ≤ 1) :
    ∃ (M : ℕ) (ψ : DirichletCharacter ℂ M), M = f * q ^ i ∧ ψ.IsPrimitive ∧
      ∀ n : ℕ, ψ (n : ZMod M) = ξ (n : ZMod f) * QH.J q n ^ i := by
  interval_cases i
  · exact ⟨f, ξ, by simp, hξ, fun n => by simp⟩
  · obtain ⟨ψ, h1, -, h3⟩ := QH.twist_prim f q ξ hξ hq h2 hf
    exact ⟨f * q, ψ, by simp, h1, fun n => by simpa using h3 n⟩

private theorem UpperTheory.Top.realSplit_J (q n i : ℕ) (h : n.Coprime q) : (QH.J q n ^ i) ^ 2 = 1 := by
  have h1 : jacobiSym (n : ℤ) q = 1 ∨ jacobiSym (n : ℤ) q = -1 :=
    jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact h)
  rw [← pow_mul, mul_comm, pow_mul]
  unfold QH.J
  rcases h1 with h1 | h1 <;> simp [h1]

private theorem im_dirichletCharacter_eq_zero_of_coprime (c N₀ : ℕ) [NeZero c] [NeZero N₀] (ρ : DirichletCharacter ℂ c)
    (hc : c ∣ N₀) (h : ∀ n : ℕ, n.Coprime N₀ → (ρ n).im = 0) : ∀ x : ZMod c, (ρ x).im = 0 := by
  intro x
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hc u
    have hn : (v : ZMod N₀).val.Coprime N₀ :=
      (ZMod.isUnit_iff_coprime _ _).1 (by rw [ZMod.natCast_zmod_val]; exact v.isUnit)
    have hux : (u : ZMod c) = ((v : ZMod N₀).val : ZMod c) := by
      rw [← hv, ZMod.unitsMap_val, ZMod.cast_eq_val]
    rw [hux]
    exact h _ hn
  · rw [MulChar.map_nonunit _ hx]
    simp

private theorem im_mul_intCast_eq_zero_of_im_eq_zero (z : ℂ) (hz : z.im = 0) (A B : ℤ) : (z * (A : ℂ) * (B : ℂ)).im = 0 := by
  simp [Complex.mul_im, hz]

private theorem exists_real_pchar_twist_decomposition (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχp : χ.IsPrimitive) (S q d : ℕ) (hreal' : ∀ x : ZMod N, (χ x).im = 0) (hS : 0 < S)
    (hq : q.Prime) (hd : d.Prime) (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d)
    (hcop : Nat.Coprime S (q * d)) (hdvd : N ∣ S * q * d) :
    ∃ (ρ : PChar) (i j : Fin 2), ρ.IsReal ∧ ρ.N ∣ 8 * ordCompl[2] S ∧
      N = ρ.N * q ^ (i : ℕ) * d ^ (j : ℕ) ∧ ∀ a : ℕ, χ a = tw ρ.val q d i j a := by
  have hN₀ : 0 < 8 * ordCompl[2] S := Nat.mul_pos (by norm_num) (Nat.ordCompl_pos 2 hS.ne')
  have hnd : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ S → ¬ r ∣ 8 * ordCompl[2] S := by
    intro r hr hr2 hrS h
    rcases (hr.dvd_mul).1 h with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
        (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 3 by norm_num; exact h)))
    · exact hrS (h.trans (Nat.ordCompl_dvd S 2))
  have hqS : ¬ q ∣ S := fun h => (Nat.Prime.coprime_iff_not_dvd hq).1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_right q d) hcop).symm h
  have hdS : ¬ d ∣ S := fun h => (Nat.Prime.coprime_iff_not_dvd hd).1
    (Nat.Coprime.coprime_dvd_right (dvd_mul_left d q) hcop).symm h
  have hq8 := hnd q hq hq2 hqS
  have hd8 := hnd d hd hd2 hdS
  have hsq : χ ^ 2 = 1 := MulChar.ext fun u => by
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have h1 := DirichletCharacter.unit_norm_eq_one χ u
    have h2 : (starRingEnd ℂ) (χ u) = χ u := Complex.conj_eq_iff_im.2 (hreal' u)
    calc χ u ^ 2 = χ u * (starRingEnd ℂ) (χ u) := by rw [h2, sq]
      _ = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; norm_num
  have hNdvd : N ∣ 8 * ordCompl[2] S * q * d := by
    refine QH.real_cond _ q d N χ hχp hsq (dvd_mul_right 8 _) hq hd fun p hp hpN => ?_
    have h := hpN.trans hdvd
    rcases (hp.dvd_mul).1 h with h | h
    · rcases (hp.dvd_mul).1 h with h | h
      · left
        by_cases hp2 : p = 2
        · subst hp2
          exact Dvd.dvd.mul_right (by norm_num) _
        · refine Dvd.dvd.mul_left ?_ 8
          have hc2 : p.Coprime (2 ^ S.factorization 2) :=
            ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right _
          refine Nat.Coprime.dvd_of_dvd_mul_left hc2 ?_
          rw [Nat.ordProj_mul_ordCompl_eq_self]
          exact h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hd).1 h))
  obtain ⟨ξ, a, b, ha, hb, hξ⟩ :=
    QH.real_decomp _ q d N χ hsq hN₀ hq hd hq2 hd2 hqd hq8 hd8 hNdvd
  haveI : NeZero (8 * ordCompl[2] S) := ⟨hN₀.ne'⟩
  haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  haveI : NeZero (8 * ordCompl[2] S * q * d) :=
    ⟨mul_ne_zero (mul_ne_zero hN₀.ne' hq.ne_zero) hd.ne_zero⟩
  have hprim : ∀ n : ℕ, n.Coprime (8 * ordCompl[2] S) → ξ n = ξ.primitiveCharacter n := by
    intro n hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter
      ξ.conductor_dvd_level (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    rw [Int.cast_natCast, Int.cast_natCast] at h
    exact h
  have hcN₀ : ξ.conductor ∣ 8 * ordCompl[2] S := ξ.conductor_dvd_level
  have hqc : ¬ q ∣ ξ.conductor := fun h => hq8 (h.trans hcN₀)
  obtain ⟨M1, ψ1, hM1, hψ1, hψ1eq⟩ := UpperTheory.Top.realSplit_step ξ.conductor q a
    ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq hq2 hqc ha
  subst hM1
  haveI : NeZero (ξ.conductor * q ^ a) := ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hq.ne_zero)⟩
  have hdc : ¬ d ∣ ξ.conductor * q ^ a := by
    intro h
    rcases (hd.dvd_mul).1 h with h | h
    · exact hd8 (h.trans hcN₀)
    · exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).1 (hd.dvd_of_dvd_pow h)).symm
  obtain ⟨M2, ψ2, hM2, hψ2, hψ2eq⟩ :=
    UpperTheory.Top.realSplit_step (ξ.conductor * q ^ a) d b ψ1 hψ1 hd hd2 hdc hb
  subst hM2
  haveI : NeZero (ξ.conductor * q ^ a * d ^ b) :=
    ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ hd.ne_zero)⟩
  have hbig : ξ.conductor ∣ 8 * ordCompl[2] S * q * d := hcN₀.trans (Dvd.intro (q * d) (by ring))
  have heq := QH.ind_unique N (ξ.conductor * q ^ a * d ^ b) (8 * ordCompl[2] S * q * d) χ ψ2
    (mul_ne_zero (mul_ne_zero hN₀.ne' hq.ne_zero) hd.ne_zero) hχp hψ2 (fun n hn => by
      rw [hξ n hn, hψ2eq, hψ1eq,
        hprim n (Nat.Coprime.coprime_dvd_right (Dvd.intro (q * d) (by ring)) hn)])
  obtain ⟨hN, hχψ⟩ := Sigma.mk.inj_iff.1 heq
  subst hN
  have hc : χ = ψ2 := eq_of_heq hχψ
  subst hc
  have hρreal := im_dirichletCharacter_eq_zero_of_coprime ξ.conductor (8 * ordCompl[2] S * q * d) ξ.primitiveCharacter hbig
    (fun n hn => by
      rw [← hprim _ (Nat.Coprime.coprime_dvd_right (Dvd.intro (q * d) (by ring)) hn)]
      have hJq := UpperTheory.Top.realSplit_J q n a
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) (Nat.Coprime.coprime_dvd_right
          (Dvd.intro d rfl) hn))
      have hJd := UpperTheory.Top.realSplit_J d n b
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hn)
      have hξn : ξ n = χ n * QH.J q n ^ a * QH.J d n ^ b := by
        rw [hξ n hn]
        linear_combination (-(ξ n) * (QH.J d n ^ b) ^ 2) * hJq + (-(ξ n)) * hJd
      have e1 : QH.J q n ^ a = ((jacobiSym n q ^ a : ℤ) : ℂ) := by
        unfold QH.J
        push_cast
        rfl
      have e2 : QH.J d n ^ b = ((jacobiSym n d ^ b : ℤ) : ℂ) := by
        unfold QH.J
        push_cast
        rfl
      rw [hξn, e1, e2]
      exact im_mul_intCast_eq_zero_of_im_eq_zero _ (hreal' n) _ _)
  refine ⟨⟨ξ.conductor, ξ.primitiveCharacter, ξ.primitiveCharacter_isPrimitive⟩, ⟨a, by omega⟩,
    ⟨b, by omega⟩, hρreal, hcN₀, rfl, fun n => ?_⟩
  simp only [PChar.val, tw]
  rw [hψ2eq, hψ1eq]
  rfl

theorem UpperTheory.Top.realSplit :
    ∀ (χ : PChar) (S q d : ℕ), χ.IsReal → 0 < S → q.Prime → d.Prime → q ≠ 2 → d ≠ 2 → q ≠ d → Nat.Coprime S (q * d) → χ.N ∣ S * q * d →
      ∃ (ρ : PChar) (i j : Fin 2), ρ.IsReal ∧ ρ.N ∣ 8 * ordCompl[2] S ∧ χ.N = ρ.N * q ^ (i : ℕ) * d ^ (j : ℕ) ∧
        ∀ a : ℕ, a.Coprime χ.N → χ.val a = tw ρ.val q d i j a := by
  intro χ0
  cases χ0 with
  | mk N χ hχp =>
    intro S q d hreal hS hq hd hq2 hd2 hqd hcop hdvd
    obtain ⟨ρ, i, j, hρ, hρN, hN, hval⟩ :=
      exists_real_pchar_twist_decomposition N χ hχp S q d hreal hS hq hd hq2 hd2 hqd hcop hdvd
    exact ⟨ρ, i, j, hρ, hρN, hN, fun a _ => hval a⟩
end

