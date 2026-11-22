import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0003
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDegree
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem mem_fixingSubgroup_adjoinRoots (m : ℕ) (g : Gal(AlgebraicClosure E/E)) :
    g ∈ (adjoinRoots E m).fixingSubgroup ↔ ∀ ζ : AlgebraicClosure E, ζ ^ m = 1 → g ζ = ζ := by
  constructor
  · intro hg ζ hζ
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg ζ
      (IntermediateField.subset_adjoin E _ hζ)
  · intro h
    have hle : adjoinRoots E m ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      intro ζ hζ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      have : Subgroup.zpowers g ≤ MulAction.stabilizer Gal(AlgebraicClosure E/E) ζ := by
        rw [Subgroup.zpowers_le]
        exact h ζ hζ
      exact fun f hf => this hf
    exact (IntermediateField.le_iff_le _ _).1 hle (Subgroup.mem_zpowers g)

private theorem comap_princ_eq [CharZero E] (n : ℕ) :
    (princ l n).comap (eps l E) = (adjoinRoots E (l ^ n)).fixingSubgroup := by
  ext g
  rw [Subgroup.mem_comap, eps_mem_princ_iff, mem_fixingSubgroup_adjoinRoots]

theorem card_map_redPow_galImage [CharZero E] (n : ℕ) :
    Nat.card ((galImage l E).map (redPow l n)) = Module.finrank E (adjoinRoots E (l ^ n)) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← comap_princ_eq, princ,
    MonoidHom.comap_ker, Subgroup.index_ker, galImage, MonoidHom.map_range]

theorem resOrder_galImage [CharZero E] :
    resOrder l (galImage l E) = Module.finrank E (adjoinRoots E l) := by
  have h := comap_princ_eq (l := l) (E := E) 1
  rw [pow_one] at h
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← h, princ_one_eq_ker,
    MonoidHom.comap_ker, Subgroup.index_ker, resOrder, galImage, MonoidHom.map_range]

theorem le_depth_galImage_iff [CharZero E] (n : ℕ) :
    (n : ℕ∞) ≤ depth l (galImage l E) ↔
      ∀ ζ : AlgebraicClosure E, ζ ^ l ^ n = 1 → ζ ∈ adjoinRoots E l := by
  have h := comap_princ_eq (l := l) (E := E) 1
  rw [pow_one] at h
  rw [depth, le_nu_iff_pow_mem_princ]
  constructor
  · intro H ζ hζ
    rw [← InfiniteGalois.fixedField_fixingSubgroup (adjoinRoots E l),
      IntermediateField.mem_fixedField_iff]
    intro g hg
    rw [← h, Subgroup.mem_comap] at hg
    have := H (eps l E g) ⟨⟨g, rfl⟩, hg⟩
    rw [pow_one, eps_mem_princ_iff] at this
    exact this ζ hζ
  · rintro H u ⟨⟨g, rfl⟩, hg⟩
    rw [pow_one, eps_mem_princ_iff]
    intro ζ hζ
    have hg' : g ∈ (adjoinRoots E l).fixingSubgroup := by
      rw [← h]
      exact hg
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg' ζ (H ζ hζ)

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LevelLift
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem unitsMap_unitsMap' {n m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) (a : (ZMod d)ˣ) :
    ZMod.unitsMap hm (ZMod.unitsMap hd a) = ZMod.unitsMap (dvd_trans hm hd) a := by
  rw [← ZMod.unitsMap_comp hm hd]; rfl

private theorem unitsMap_redPow' {j c : ℕ} (h : l ^ j ∣ l ^ c) (u : ℤ_[l]ˣ) :
    ZMod.unitsMap h (redPow l c u) = redPow l j u := by
  have hjc : j ≤ c := (Nat.pow_dvd_pow_iff_le_right (Fact.out : l.Prime).one_lt).1 h
  apply Units.ext
  rw [ZMod.unitsMap_val]
  exact PadicInt.cast_toZModPow j c hjc (u : ℤ_[l])

private theorem crt_units {n m M : ℕ} [NeZero M] (hn : n ∣ M) (hm : m ∣ M)
    (h : (ZMod n)ˣ) (w : (ZMod m)ˣ)
    (hw : ZMod.unitsMap (Nat.gcd_dvd_left n m) h = ZMod.unitsMap (Nat.gcd_dvd_right n m) w) :
    ∃ a : (ZMod M)ˣ, ZMod.unitsMap hn a = h ∧ ZMod.unitsMap hm a = w := by
  have : NeZero n := ⟨fun h0 => NeZero.ne M (by simpa [h0] using hn)⟩
  have : NeZero m := ⟨fun h0 => NeZero.ne M (by simpa [h0] using hm)⟩
  have hc : (h : ZMod n).val ≡ (w : ZMod m).val [MOD Nat.gcd n m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
    exact congrArg Units.val hw
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hc
  have e1 : (k : ZMod n) = h := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hk1, ZMod.natCast_zmod_val]
  have e2 : (k : ZMod m) = w := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hk2, ZMod.natCast_zmod_val]
  have c1 : k.Coprime n := (ZMod.isUnit_iff_coprime k n).1 (e1 ▸ h.isUnit)
  have c2 : k.Coprime m := (ZMod.isUnit_iff_coprime k m).1 (e2 ▸ w.isUnit)
  have c3 : k.Coprime (Nat.lcm n m) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul n m) (Nat.Coprime.mul_right c1 c2)
  have hl : Nat.lcm n m ∣ M := Nat.lcm_dvd hn hm
  obtain ⟨a, ha⟩ := ZMod.unitsMap_surjective hl (ZMod.unitOfCoprime k c3)
  refine ⟨a, ?_, ?_⟩
  · rw [← unitsMap_unitsMap' (Nat.dvd_lcm_left n m) hl, ha]
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_left n m), e1]
  · rw [← unitsMap_unitsMap' (Nat.dvd_lcm_right n m) hl, ha]
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_right n m), e2]

private theorem unitsMap_congr_pow {g j n c : ℕ} (hg : g = l ^ j) (h1 : g ∣ n) (h2 : g ∣ l ^ c)
    (hn : n ≠ 0) (h : (ZMod n)ˣ) (u : ℤ_[l]ˣ)
    (hu : ZMod.unitsMap (Nat.ordProj_dvd n l) h = redPow l (n.factorization l) u) :
    ZMod.unitsMap h1 h = ZMod.unitsMap h2 (redPow l c u) := by
  subst hg
  have hj : l ^ j ∣ l ^ n.factorization l :=
    pow_dvd_pow l (((Fact.out : l.Prime).pow_dvd_iff_le_factorization hn).1 h1)
  rw [unitsMap_redPow', ← unitsMap_redPow' hj, ← hu, unitsMap_unitsMap']

private theorem lift_aux {n c M : ℕ} [NeZero M] (hn : n ∣ M) (hm : l ^ c ∣ M)
    (h : (ZMod n)ˣ) (u : ℤ_[l]ˣ)
    (hu : ZMod.unitsMap (Nat.ordProj_dvd n l) h = redPow l (n.factorization l) u) :
    ∃ a : (ZMod M)ˣ, ZMod.unitsMap hn a = h ∧ ZMod.unitsMap hm a = redPow l c u := by
  have hn0 : n ≠ 0 := fun h0 => NeZero.ne M (by simpa [h0] using hn)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (Nat.gcd_dvd_right n (l ^ c))
  exact crt_units hn hm h _ (unitsMap_congr_pow hj _ _ hn0 h u hu)

theorem exists_lift_level {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) (u : ℤ_[l]ˣ)
    (hu : ZMod.unitsMap (Nat.ordProj_dvd N l) h = redPow l (N.factorization l) u) (b : ℕ) :
    ∃ a : (ZMod (N * l ^ b))ˣ, ZMod.unitsMap (Nat.dvd_mul_right N (l ^ b)) a = h ∧
      ZMod.unitsMap (Nat.dvd_mul_left (l ^ b) N) a = redPow l b u := by
  have : NeZero (N * l ^ b) :=
    ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  exact lift_aux _ _ h u hu

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFinite
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nf_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem nf_exists_unit {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

private theorem nf_mem_princ {a s : ℕ} (h : s ≤ a) {u : ℤ_[l]ˣ}
    (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) : u ∈ princ l s := by
  rw [mem_princ, hu]
  exact pow_dvd_pow _ h

private theorem nf_emult {a : ℕ} {u : ℤ_[l]ˣ} (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) :
    emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
  rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]

theorem depth_le_of_princ_le {U : Subgroup ℤ_[l]ˣ} {s : ℕ} (h : princ l s ≤ U) :
    depth l U ≤ ((max 1 s : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (le_max_left 1 s)
  have hm : u ∈ U ⊓ princ l 1 :=
    ⟨h (nf_mem_princ (le_max_right 1 s) hu), nf_mem_princ (le_max_left 1 s) hu⟩
  have := nf_nu_le hm 1
  rwa [pow_one, nf_emult hu] at this

theorem nu_le_of_princ_le {U : Subgroup ℤ_[l]ˣ} {s tr : ℕ} (h : princ l s ≤ U) (htr : Odd tr) :
    nu l U tr ≤ ((max 1 s + padicValNat l tr : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (le_max_left 1 s)
  have hm : u ∈ U := h (nf_mem_princ (le_max_right 1 s) hu)
  by_cases hl : l = 2
  · subst hl
    rw [(nu_two_of_odd U htr).1]
    have := nf_nu_le hm 1
    rw [pow_one, nf_emult hu] at this
    exact this.trans (by exact_mod_cast Nat.le_add_right _ _)
  · have h1 : (l : ℤ_[l]) ∣ (u : ℤ_[l]) - 1 := by
      rw [hu]
      exact dvd_pow_self _ (by omega)
    have := nf_nu_le hm tr
    rw [emultiplicity_pow_sub_one_odd hl h1, nf_emult hu,
      ← padicValNat_eq_emultiplicity htr.pos.ne'] at this
    rw [Nat.cast_add]
    exact this

theorem nu_ne_top {U : Subgroup ℤ_[l]ˣ} (hU : IsOpen (U : Set ℤ_[l]ˣ)) {tr : ℕ} (htr : tr ≠ 0) :
    nu l U tr ≠ ⊤ := by
  obtain ⟨s, h⟩ := (isOpen_iff_princ_le U).mp hU
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (a := s + 2) (by omega)
  have hm : u ∈ U := h (nf_mem_princ (by omega) hu)
  have h1 : (l : ℤ_[l]) ^ 2 ∣ (u : ℤ_[l]) - 1 := by
    rw [hu]
    exact pow_dvd_pow _ (by omega)
  have := nf_nu_le hm tr
  rw [emultiplicity_pow_sub_one_sq h1, nf_emult hu,
    ← padicValNat_eq_emultiplicity htr, ← Nat.cast_add] at this
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) this

private theorem nf_not_dvd_two (hl : l ≠ 2) : ¬ (l : ℤ_[l]) ∣ 2 := by
  intro h
  have h2 : (l : ℤ_[l]) ∣ ((2 : ℕ) : ℤ_[l]) := by simpa using h
  rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff] at h2
  exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)

theorem nu_of_neg_one_mem {U : Subgroup ℤ_[l]ˣ} (h : -1 ∈ U) {tr : ℕ} (htr : Odd tr) :
    nu l U tr = (if l = 2 then 1 else 0) ∧ (l ≠ 2 → Even (resOrder l U)) := by
  have key : ∀ {t : ℕ}, Odd t → nu l U t ≤ emultiplicity (l : ℤ_[l]) 2 := by
    intro t ht
    have := nf_nu_le h t
    have e : (((-1 : ℤ_[l]ˣ)) : ℤ_[l]) ^ t - 1 = -2 := by
      rw [Units.val_neg, Units.val_one, ht.neg_one_pow]; ring
    rwa [e, emultiplicity_neg] at this
  have odd : l ≠ 2 → ∀ {t : ℕ}, Odd t → nu l U t = 0 := by
    intro hl t ht
    have := key ht
    rw [emultiplicity_eq_zero.2 (nf_not_dvd_two hl)] at this
    exact le_antisymm this bot_le
  refine ⟨?_, fun hl => ?_⟩
  · split_ifs with hl
    · subst hl
      refine le_antisymm ?_ (nu_two_of_odd U htr).2
      have hs : emultiplicity ((2 : ℕ) : ℤ_[2]) 2 = 1 := by
        simpa using emultiplicity_pow_self_of_prime (PadicInt.prime_p (p := 2)) 1
      exact hs ▸ key htr
    · exact odd hl htr
  · by_contra hn
    have h0 := odd hl (Nat.not_even_iff_odd.mp hn)
    have := (nu_pos_iff U (resOrder l U)).mpr dvd_rfl
    exact this.ne' h0

end KStar.TotallyRealRoots
end

