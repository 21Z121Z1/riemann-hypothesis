import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoHeckeQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckeTate

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

def form (D : Datum H) : D.La →+ D.La →+ ℤ :=
  AddMonoidHom.mk' (fun x => (D.EF x).toAddMonoidHom) fun a b => by rw [map_add]; rfl

theorem form_apply (x y : D.La) : form D x y = D.EF x y := rfl

theorem form_isUnimod (D : Datum H) : IsUnimod H.bar (form D) := by
  refine ⟨fun x y => ?_, D.adj, fun x y h => D.unimod.1 (LinearMap.ext fun a => DFunLike.congr_fun h a),
    fun f => ?_⟩
  · exact (LinearMap.IsAlt.neg (B := D.EF) D.alt y x).symm
  · obtain ⟨x, hx⟩ := D.unimod.2 f.toIntLinearMap
    exact ⟨x, AddMonoidHom.ext fun a => LinearMap.congr_fun hx a⟩

variable {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

def evHom (I : TateIso D k Q act e) (n : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev n a)) fun a b => by rw [I.add]; rfl

theorem ev_zero (I : TateIso D k Q act e) (n : ℕ) : I.ev n 0 = 1 := (evHom I n).map_zero

theorem ev_nsmul (I : TateIso D k Q act e) (n m : ℕ) (a : D.La) : I.ev n (m • a) = I.ev n a ^ m :=
  (evHom I n).map_nsmul m a

theorem ev_sub (I : TateIso D k Q act e) (n : ℕ) (a b : D.La) : I.ev n (a - b) = I.ev n a / I.ev n b :=
  (evHom I n).map_sub a b

end

end GlobalTheory.HeckeTate

namespace GlobalTheory

open HeckeTate

theorem exists_tateIso_heckeQuotient :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (k : Type) [Field k] (Q Q' : Type) [CommGroup Q] [CommGroup Q'] (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → kˣ → Prop) (I : TateIso D k Q act e) (ψ : Q →* Q'), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → Function.Surjective ψ → (∀ a x, ψ (act a x) = act' a (ψ x)) → (∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, x ^ p = 1 → (∀ a ∈ J, act a x = 1) → ψ x = 1) → (∀ x, ψ x = 1 → x ^ p ^ 2 = 1 ∧ ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), act a x = 1) → (∀ x y, ψ x = 1 → ψ y = 1 → e (p ^ 2) x y 1) → Nat.card ψ.ker = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → (∀ n x y c, 0 < n → ψ x ^ n = 1 → ψ y ^ n = 1 → e (n * p ^ 2) x y c → e' n (ψ x) (ψ y) c) → ∃ I' : TateIso D k Q' act' e', I'.ζ = I.ζ ∧ ∀ n p' : ℕ, 0 < n → p * p' ≡ 1 [MOD n] → ∀ a, I'.ev n a = ψ (I.ev n (p' • a)) := by
  intro h₀ E _ _ _ H D P p k _ Q Q' _ _ act act' e e' I ψ hP hPP hp hpP hψ hact hlow hup hiso hcard huniq he'
  clear h₀
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq : 0 < p ^ 2 := pow_pos hp.pos 2
  have := D.fin
  have := D.proj
  have := datum_free_int D
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  let C : Submodule (𝓞 E) D.La :=
    { carrier := {a | ψ (I.ev (p ^ 2) a) = 1}
      add_mem' := fun {a b} ha hb => by
        change ψ _ = 1 at ha hb ⊢
        rw [I.add, map_mul, ha, hb, _root_.one_mul]
      zero_mem' := by
        change ψ _ = 1
        rw [ev_zero, map_one]
      smul_mem' := fun c a ha => by
        change ψ _ = 1 at ha ⊢
        have h0 := hact c (I.ev (p ^ 2) 0)
        rw [← I.lin, smul_zero, ev_zero, map_one] at h0
        rw [I.lin, hact, ha, ← h0] }
  have hC : ∀ a, a ∈ C ↔ ψ (I.ev (p ^ 2) a) = 1 := fun _ => Iff.rfl
  have hsq : ∀ a, (p ^ 2) • a ∈ C := fun a => by
    rw [hC, (I.ker _ hq _).2 ⟨a, rfl⟩, map_one]
  have hCiso : ∀ x ∈ C, ∀ y ∈ C, ((p ^ 2 : ℕ) : ℤ) ∣ form D x y := fun x hx y hy => by
    have := huniq _ _ _ _ _ hq ((I.onto _ hq _).2 ⟨x, rfl⟩) ((I.onto _ hq _).2 ⟨y, rfl⟩)
      (I.isom _ hq x y) (hiso _ _ hx hy)
    exact ((I.ζ_prim _ hq).zpow_eq_one_iff_dvd _).1 this
  have hidx : (nsmulAddMonoidHom (α := D.La) (p ^ 2)).range.relIndex C.toAddSubgroup = Nat.card ψ.ker := by
    let f : C.toAddSubgroup →+ Additive ψ.ker := AddMonoidHom.mk'
      (fun a => Additive.ofMul ⟨I.ev (p ^ 2) a, a.2⟩) fun a b => by
        rw [← ofMul_mul]
        exact congrArg _ (Subtype.ext (I.add _ _ _))
    have hf : Function.Surjective f := fun x => by
      obtain ⟨a, ha⟩ := (I.onto _ hq _).1 (hup _ x.toMul.2).1
      exact ⟨⟨a, (hC a).2 (ha ▸ x.toMul.2)⟩, Additive.toMul.injective (Subtype.ext ha)⟩
    have hker : f.ker = (nsmulAddMonoidHom (α := D.La) (p ^ 2)).range.addSubgroupOf C.toAddSubgroup := by
      ext a
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
      constructor
      · intro h
        obtain ⟨b, hb⟩ := (I.ker _ hq a).1 (congrArg (fun z => (z.toMul : Q)) h)
        exact ⟨b, hb.symm⟩
      · rintro ⟨b, hb⟩
        exact Additive.toMul.injective (Subtype.ext ((I.ker _ hq a).2 ⟨b, hb.symm⟩))
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
      AddSubgroup.card_top]
    rfl
  have horth := mem_of_orth (form D) (form_isUnimod D).bij (m := p ^ 2) (c := Nat.card ψ.ker) hq.ne'
    (by rw [hcard, datum_finrank_int]; ring) C.toAddSubgroup (by rintro _ ⟨a, rfl⟩; exact hsq a) hidx hCiso
  obtain ⟨B', hB', hBB⟩ := exists_unimod_div (form_isUnimod D) hq.ne' C hsq hCiso horth
  have hsq' : ∀ a, ∃ y : C, C.subtype y = (p : 𝓞 E) ^ 2 • a := fun a =>
    ⟨⟨_, hsq a⟩, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl⟩
  have hlow' : ∀ g ∈ P, ∀ a, ∃ y : C, C.subtype y = (g * p) • a := fun g hg a => by
    obtain ⟨J, hJ⟩ : P ∣ Ideal.span {(p : 𝓞 E)} := Ideal.dvd_iff_le.2 (by simpa using hpP)
    refine ⟨⟨(g * p) • a, hlow J (by rw [hJ, _root_.mul_comm]) (I.ev (p ^ 2) ((g * p) • a)) ?_ fun c hc => ?_⟩, rfl⟩
    · rw [← ev_nsmul, I.ker _ hq]
      refine ⟨g • a, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hJ ▸ Ideal.mul_mem_mul hg hc)
      rw [← I.lin, I.ker _ hq]
      refine ⟨d • a, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, smul_smul]
      congr 1
      push_cast
      linear_combination (p : 𝓞 E) * hd
  have hrank : Module.finrank (𝓞 E) D.La = Module.finrank (𝓞 E) C := by
    refine le_antisymm ?_ C.finrank_le
    let u : D.La →ₗ[𝓞 E] C := LinearMap.codRestrict C ((p ^ 2) • LinearMap.id) hsq
    refine LinearMap.finrank_le_finrank_of_injective (f := u) fun x y h => ?_
    refine (form_isUnimod D).smul_cancel hq.ne' ?_
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact congrArg Subtype.val h
  have := hP.isPrime
  obtain ⟨φ, φ', s, hs, hφ, hφ'⟩ := exists_local_iso hrank P
  obtain ⟨G, G1, G2, G3, G4, G5⟩ := exists_glued (form_isUnimod D) hB' (bar_bar H) hP hPP hp0 hpP C.subtype
    C.injective_subtype (fun x y => by simpa using hBB x y) hsq' hlow' φ φ' hs hφ hφ'
  have hpos : ∀ n : ℕ, 0 < n → 0 < n * p ^ 2 := fun n hn => Nat.mul_pos hn hq
  have hdown : ∀ n : ℕ, 0 < n → ∀ a, I.ev (n * p ^ 2) a ^ n = I.ev (p ^ 2) a := fun n hn a => by
    rw [_root_.mul_comm, I.tower _ _ hq hn]
  have hkey : ∀ n : ℕ, 0 < n → ∀ y : C, ψ (I.ev (n * p ^ 2) y) = 1 ↔ y ∈ mults C (n : 𝓞 E) := by
    intro n hn y
    rw [mem_mults]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := (I.onto _ hq _).1 (hup _ h).1
      have hcC : c ∈ C := (hC c).2 (hc ▸ h)
      have : I.ev (n * p ^ 2) (y - n • c) = 1 := by
        rw [ev_sub, ev_nsmul, hdown n hn, hc, div_self']
      obtain ⟨b, hb⟩ := (I.ker _ (hpos n hn) _).1 this
      refine ⟨⟨c, hcC⟩ + ⟨_, hsq b⟩, Subtype.ext ?_⟩
      rw [Nat.cast_smul_eq_nsmul]
      change (y : D.La) = n • (c + (p ^ 2) • b)
      rw [smul_add, ← mul_smul, ← hb]
      abel
    · rintro ⟨z, rfl⟩
      rw [Nat.cast_smul_eq_nsmul]
      change ψ (I.ev _ (n • (z : D.La))) = 1
      rw [ev_nsmul, hdown n hn]
      exact z.2
  have hkey' : ∀ n : ℕ, 0 < n → ∀ y y' : C, y - y' ∈ mults C (n : 𝓞 E) →
      ψ (I.ev (n * p ^ 2) y) = ψ (I.ev (n * p ^ 2) y') := fun n hn y y' h => by
    have := (hkey n hn _).2 h
    rwa [Submodule.coe_sub, ev_sub, map_div, div_eq_one] at this
  have htor : ∀ n : ℕ, 0 < n → ∀ y : C, ψ (I.ev (n * p ^ 2) y) ^ n = 1 := fun n hn y => by
    rw [← map_pow, hdown n hn]
    exact y.2
  refine ⟨⟨I.ζ, I.ζ_prim, I.ζ_pow, fun n a => ψ (I.ev (n * p ^ 2) (G n a)), fun n a b => ?_, fun n c a => ?_,
    fun n hn a => ?_, fun n hn x => ⟨fun hx => ?_, ?_⟩, fun n m hn hm a => ?_, fun n hn a b => ?_⟩, rfl,
    fun n p' hn hpp a => ?_⟩
  · rw [map_add, Submodule.coe_add, I.add, map_mul]
  · rw [map_smul, Submodule.coe_smul, I.lin, hact]
  · rw [hkey n hn]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := mem_mults.1 (G1 n hn a h)
      exact ⟨b, by rw [hb, Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨b, rfl⟩
      exact map_mem_mults _ (mem_mults.2 ⟨b, (Nat.cast_smul_eq_nsmul _ _ _).symm⟩)
  · obtain ⟨x, rfl⟩ := hψ x
    have h1 := (hup _ ((map_pow ψ x n).trans hx)).1
    rw [← pow_mul] at h1
    obtain ⟨b, rfl⟩ := (I.onto _ (hpos n hn) _).1 h1
    have hb : b ∈ C := by rw [hC, ← hdown n hn, map_pow, hx]
    obtain ⟨a, ha⟩ := G2 n hn ⟨b, hb⟩
    exact ⟨a, hkey' n hn _ _ ha⟩
  · rintro ⟨a, rfl⟩
    exact htor n hn _
  · rw [← map_pow, mul_right_comm, I.tower _ _ (hpos n hn) hm]
    exact hkey' n hn _ _ (G3 n m hn hm a)
  · refine he' n _ _ _ hn (htor n hn _) (htor n hn _) ?_
    have h1 := I.isom _ (hpos n hn) (G n a) (G n b)
    obtain ⟨t, ht⟩ := G4 n hn a b
    have h2 : D.EF (G n a) (G n b) = (p ^ 2 : ℕ) * (D.EF a b + n * t) := by
      rw [← ht, ← form_apply, hBB, form_apply]
      ring
    rw [h2, zpow_mul, zpow_natCast, I.ζ_pow _ _ hn hq, zpow_add, zpow_mul, zpow_natCast,
      (I.ζ_prim n hn).pow_eq_one, one_zpow, _root_.mul_one] at h1
    exact h1
  · have hcop : n.Coprime p := (Nat.coprime_of_mul_modEq_one p' hpp).symm
    change ψ (I.ev (n * p ^ 2) (G n a)) = _
    rw [← I.tower n _ hn hq, ← ev_nsmul]
    refine hkey' n hn _ ⟨_, hsq _⟩ ?_
    obtain ⟨b, hb⟩ := mem_mults.1 (G5 n hn hcop a)
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd.1 hpp)
    have ht' := congrArg (Int.castRingHom (𝓞 E)) ht
    simp only [eq_intCast] at ht'
    push_cast at ht'
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 (hcop.pow_right 2)).map (Int.castRingHom (𝓞 E))
    simp only [eq_intCast, Int.cast_natCast] at huv
    set y : C := G n a - ⟨_, hsq (p' • a)⟩ with hy
    have h1 : (y : D.La) = (n : 𝓞 E) • (b + ((p : 𝓞 E) * t) • a) := by
      rw [smul_add, ← hb, hy, Submodule.coe_sub, Submodule.subtype_apply]
      simp only [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul]
      rw [sub_add, ← sub_smul]
      congr 2
      push_cast
      linear_combination (-(p : 𝓞 E)) * ht'
    generalize b + ((p : 𝓞 E) * t) • a = z at h1
    refine mem_mults.2 ⟨u • y + v • ⟨_, hsq z⟩, Subtype.ext ?_⟩
    simp only [Submodule.coe_smul, Submodule.coe_add, h1, ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul]
    rw [← add_smul, huv, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.LieEtale

theorem existsUnique_dual_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {k : Type} [Field k]
    (s : Sp (DualNumber k) ⟶ Y) (x₀ : Sp k ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber k) ⟶ X,
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber k, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  have hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥ := fun a ha =>
    Ideal.mem_sInf.mpr fun {J} hJ => hJ.2.isPrime.mem_of_pow_mem 2 (by
      rw [pow_two, hsq a a ha ha]; exact J.zero_mem)
  refine existsUnique_of_exists_of_unique ?_ fun x₁ x₂ h₁ h₂ =>
    lift_ext_of_unramified f π hπ hj (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  have : IsLocalHom π.hom := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint k)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (range_subset_opens_of_isLocalRing s ?_) (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint k)) = s (Spec.map π (IsLocalRing.closedPoint k)) :=
      congr($h (IsLocalRing.closedPoint k))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R A _ _ _ _ _ _ π' hπ' φ
    have hs : Function.Surjective π' := fun c => (hπ c).imp fun b hb => (hπ' b).trans hb
    have hk : IsNilpotent (RingHom.ker (π' : CommRingCat.of (DualNumber k) →+* CommRingCat.of k)) := by
      convert hnil using 2
      exact RingHom.ext hπ'
    exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hs hk⟩

section Formal

variable {S : Scheme.{0}} {O k : Type} {P E : Over S}

def Eig {G : Over S} [GrpObj G] (z : P ⟶ E) (sc : k → (E ⟶ E)) (act : O → (G ⟶ G)) (τ : O → k)
    (v : E ⟶ G) : Prop :=
  z ≫ v = 1 ∧ ∀ a, v ≫ act a = sc (τ a) ≫ v

theorem comp_listProd {G : Over S} [GrpObj G] (z : P ⟶ E) (l : List (E ⟶ G))
    (h : ∀ u ∈ l, z ≫ u = 1) : z ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one z
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, h u (by simp), ih fun w hw => h w (by simp [hw]),
      _root_.mul_one]

theorem ofFn_prod_comp {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] {n : ℕ}
    (u : Fin n → (E ⟶ A)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod :=
  (map_list_prod (IsMonHom.monoidHom ψ E) _).trans (by rw [List.map_ofFn]; rfl)

theorem mult_iff {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    (z : P ⟶ E) (sc : k → (E ⟶ E)) (hz : ∀ c, z ≫ sc c = z)
    (a : O → (A ⟶ A)) (b : O → (B ⟶ B)) (ha : ∀ c, IsMonHom (a c))
    (hab : ∀ c, a c ≫ ψ = ψ ≫ b c) (τ : O → k)
    (H : ∀ w : E ⟶ B, z ≫ w = 1 → ∃! v : E ⟶ A, z ≫ v = 1 ∧ v ≫ ψ = w) (n : ℕ) :
    (∃ v : Fin n → (E ⟶ A), (∀ i, Eig z sc a τ (v i)) ∧ ∀ w, Eig z sc a τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) ↔
    (∃ v : Fin n → (E ⟶ B), (∀ i, Eig z sc b τ (v i)) ∧ ∀ w, Eig z sc b τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) := by
  have htan : ∀ v : E ⟶ A, z ≫ v = 1 → z ≫ v ≫ ψ = 1 := fun v hv => by
    rw [← Category.assoc, hv, MonObj.one_comp]
  have hinj : ∀ v v' : E ⟶ A, z ≫ v = 1 → z ≫ v' = 1 → v ≫ ψ = v' ≫ ψ → v = v' :=
    fun v v' hv hv' e => (H _ (htan v' hv')).unique ⟨hv, e⟩ ⟨hv', rfl⟩
  have hsc : ∀ (c : k) (v : E ⟶ A), z ≫ v = 1 → z ≫ sc c ≫ v = 1 := fun c v hv => by
    rw [← Category.assoc, hz, hv]
  have heig : ∀ v : E ⟶ A, z ≫ v = 1 → (Eig z sc a τ v ↔ Eig z sc b τ (v ≫ ψ)) := fun v hv => by
    refine ⟨fun h => ⟨htan v hv, fun c => ?_⟩, fun h => ⟨hv, fun c => hinj _ _ ?_ (hsc _ _ hv) ?_⟩⟩
    · rw [Category.assoc, ← hab, ← Category.assoc, h.2, Category.assoc]
    · have := ha c
      rw [← Category.assoc, hv, MonObj.one_comp]
    · rw [Category.assoc, hab, ← Category.assoc, h.2, Category.assoc]
  have hcomb : ∀ (v : Fin n → (E ⟶ A)) (w : E ⟶ A), (∀ i, z ≫ v i = 1) → z ≫ w = 1 →
      ∀ c : Fin n → k, (w = (List.ofFn fun i => sc (c i) ≫ v i).prod ↔
        w ≫ ψ = (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod) := fun v w hv hw c => by
    have e : (List.ofFn fun i => sc (c i) ≫ v i).prod ≫ ψ =
        (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod := by
      simp only [ofFn_prod_comp, Category.assoc]
    rw [← e]
    refine ⟨fun h => by rw [← h], hinj _ _ hw (comp_listProd z _ fun u hu => ?_)⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hsc _ _ (hv i)
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨fun i => v i ≫ ψ, fun i => (heig _ (hv i).1).mp (hv i), fun w hw => ?_⟩
    obtain ⟨w', ⟨hw', rfl⟩, -⟩ := H w hw.1
    exact (existsUnique_congr (hcomb v w' (fun i => (hv i).1) hw')).mp (h w' ((heig _ hw').mpr hw))
  · rintro ⟨v, hv, h⟩
    choose v' hv' using fun i => (H (v i) (hv i).1).exists
    obtain rfl : v = fun i => v' i ≫ ψ := funext fun i => (hv' i).2.symm
    refine ⟨v', fun i => (heig _ (hv' i).1).mpr (hv i), fun w hw => ?_⟩
    exact (existsUnique_congr (hcomb v' w (fun i => (hv' i).1) hw.1)).mpr
      (h _ ((heig _ hw.1).mp hw))

end Formal

section Dual

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)

def epsPtZero : Over.mk x ⟶ epsPt x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) =
      RingHom.id k := RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

def epsPtScale (c : k) : epsPt x ⟶ epsPt x :=
  Over.homMk (spMap (epsScale c)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).commutes r)

theorem epsPtZero_epsPtScale (c : k) : epsPtZero x ≫ epsPtScale x c = epsPtZero x := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r

variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)

theorem isLieEigen_iff (v : epsPt x ⟶ G) :
    IsLieEigen act x τ v ↔ Eig (epsPtZero x) (epsPtScale x) act.act τ v :=
  ⟨fun h => ⟨Over.OverMorphism.ext h.1, fun a => Over.OverMorphism.ext (h.2 a)⟩,
    fun h => ⟨congrArg (·.left) h.1, fun a => congrArg (·.left) (h.2 a)⟩⟩

theorem lieMult_iff (n : ℕ) : LieMult act x τ n ↔
    ∃ v : Fin n → (epsPt x ⟶ G), (∀ i, Eig (epsPtZero x) (epsPtScale x) act.act τ (v i)) ∧
      ∀ w, Eig (epsPtZero x) (epsPtScale x) act.act τ w →
        ∃! c : Fin n → k, w = (List.ofFn fun i => epsPtScale x (c i) ≫ v i).prod := by
  simp only [LieMult, isLieEigen_iff]
  refine exists_congr fun v => and_congr_right fun _ => forall_congr' fun w =>
    imp_congr_right fun _ => existsUnique_congr fun c => ⟨?_, fun h => ⟨_, fun _ => rfl, h⟩⟩
  rintro ⟨u, hu, rfl⟩
  obtain rfl : u = fun i => epsPtScale x (c i) ≫ v i :=
    funext fun i => Over.OverMorphism.ext (hu i)
  rfl

theorem existsUnique_tangent_lift {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    [Etale ψ.left] (w : epsPt x ⟶ B) (hw : epsPtZero x ≫ w = 1) :
    ∃! v : epsPt x ⟶ A, epsPtZero x ≫ v = 1 ∧ v ≫ ψ = w := by
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift ψ.left w.left (1 : Over.mk x ⟶ A).left
    (congrArg (·.left) ((MonObj.one_comp ψ).trans hw.symm))
  refine ⟨Over.homMk v ?_, ⟨Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩,
    fun v' hv' => Over.OverMorphism.ext
      (hu _ ⟨congrArg (·.left) hv'.1, congrArg (·.left) hv'.2⟩)⟩
  rw [← Over.w ψ, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h₂).trans (Over.w w)

end Dual

theorem lieMult_iff_of_etale :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult a x τ n ↔ LieMult b x τ n := by
  intro O _ S A B _ _ ψ a b _ _ hab k _ x τ n
  rw [lieMult_iff, lieMult_iff]
  exact mult_iff ψ _ _ (epsPtZero_epsPtScale x) a.act b.act a.hom hab τ
    (existsUnique_tangent_lift x ψ) n

end GlobalTheory.LieEtale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericFlatnessScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericFlatScheme

theorem affine (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : CommRingCat.{0})
    (s : Spec A ⟶ Sp R) [LocallyOfFiniteType s] :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd s (spMap φ)) := by
  obtain ⟨g, rfl⟩ : ∃ g : CommRingCat.of R ⟶ A, Spec.map g = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  have hg : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let : Algebra R A := g.hom.toAlgebra
  have : Algebra.FiniteType R A := hg
  obtain ⟨a, ha, hfree⟩ := (GlobalTheory.generic_freeness R).2.1 A A
  refine ⟨a, ha, fun R' _ φ hφ => ?_⟩
  let : Algebra R R' := φ.toAlgebra

  let : Algebra (Localization.Away a) R' := (IsLocalization.Away.lift a hφ).toAlgebra
  have : IsScalarTower R (Localization.Away a) R' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq a hφ x).symm
  have := hfree
  have hbc : IsBaseChange (Localization.Away a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) A) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) (Localization.Away a) _).mp
      inferInstance
  have : Module.Free (Localization.Away a) (Localization.Away a ⊗[R] A) :=
    Module.Free.of_equiv hbc.equiv.symm
  have hflat : Module.Flat R' (R' ⊗[R] A) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away a) R' R' A).symm

  have hA : g = CommRingCat.ofHom (algebraMap R A) := rfl
  have hF : Flat (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A)))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  rw [hA]
  change Flat (pullback.snd _ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  rw [← pullbackSymmetry_hom_comp_fst, ← pullbackSpecIso_hom_fst' R R' A]
  infer_instance

end GenericFlatScheme

theorem generic_flatness_scheme :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R),
      LocallyOfFiniteType s → QuasiCompact s → ∃ f : R, f ≠ 0 ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
          Flat (pullback.snd s (spMap φ)) := by
  intro R _ _ _ Z s hs hq
  have := hs
  have := hq
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  let 𝒰 := Z.affineCover.finiteSubcover
  have key : ∀ i, ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd (𝒰.f i ≫ s) (spMap φ)) :=
    fun i => by
      have : LocallyOfFiniteType (𝒰.f i ≫ s) := MorphismProperty.comp_mem _ _ _
        (inferInstance : LocallyOfFiniteType (𝒰.f i)) hs
      exact @GenericFlatScheme.affine R _ _ _ _ (𝒰.f i ≫ s) this
  choose e he0 heF using key
  refine ⟨∏ i, e i, Finset.prod_ne_zero_iff.mpr fun i _ => he0 i, fun R' _ φ hφ => ?_⟩

  have hloc : IsZariskiLocalAtSource @AlgebraicGeometry.Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat)
    (𝒰.pullback₁ (pullback.fst s (spMap φ)))).mpr fun i => ?_
  change Flat (pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ))
  have := heF i R' φ
    (isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem e (Finset.mem_univ _))) hφ)
  have h : pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ) =
      ((pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso s (spMap φ) (𝒰.f i)).hom) ≫
        pullback.snd (𝒰.f i ≫ s) (spMap φ) := by
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc]
  rw [h]
  infer_instance

end GlobalTheory
end

