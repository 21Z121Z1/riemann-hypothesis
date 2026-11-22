import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0650
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
section
noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LowFilt

open GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsOpp (D : Datum H) (Z Z' : Submodule (𝓞 E) D.La) : Prop :=
  Z ≤ perp D Z ∧ Z' ≤ perp D Z' ∧ (∀ φ : Z →+ ℤ, ∃! b : Z', ∀ a : Z, D.EF a b = φ a) ∧
    ∀ φ : Z' →+ ℤ, ∃! a : Z, ∀ b : Z', D.EF a b = φ b

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

def Cois (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) : Prop :=
  (∀ x, ∃ a e, y a = x + n • e) ∧
    ∀ a, (∀ b, (∃ e, y b = n • e) → (n : ℤ) ∣ D.EF a b) → ∃ e, y a = n • e

def KerIs (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (n : ℕ) : Prop :=
  ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e

abbrev img (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (I : Ideal (𝓞 E)) : Submodule (𝓞 E) X :=
  Z.map y ⊔ I • (⊤ : Submodule (𝓞 E) X)

def Improves (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (𝔭 : Ideal (𝓞 E)) (Z Z' Z'' : Submodule (𝓞 E) D.La) : Prop :=
  IsOpp D Z Z'' ∧ (∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → img D y Z' 𝔮 ≤ img D y Z'' 𝔮) ∧
    ¬ img D y Z'' 𝔭 ≤ img D y Z' 𝔭

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := H.starRing.star_involutive a

theorem ef_swap (D : Datum H) (a b : D.La) : D.EF a b = -D.EF b a := by
  have h := D.alt (a + b)
  simp only [map_add, LinearMap.add_apply, D.alt] at h
  linear_combination h

theorem mem_perp {D : Datum H} {Z : Submodule (𝓞 E) D.La} {a : D.La} : a ∈ perp D Z ↔ ∀ z ∈ Z, D.EF a z = 0 := Iff.rfl

variable {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.symm (h : IsOpp D Z Z') : IsOpp D Z' Z := by
  refine ⟨h.2.1, h.1, fun φ => ?_, fun φ => ?_⟩
  · obtain ⟨a, ha, hu⟩ := h.2.2.2 (-φ)
    refine ⟨a, fun b => by rw [ef_swap, ha]; simp, fun a' ha' => hu a' fun b => ?_⟩
    rw [ef_swap, ha']; simp
  · obtain ⟨a, ha, hu⟩ := h.2.2.1 (-φ)
    refine ⟨a, fun b => by rw [ef_swap, ha]; simp, fun a' ha' => hu a' fun b => ?_⟩
    rw [ef_swap, ha']; simp

theorem IsOpp.eq_zero (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') (h0 : b ∈ perp D Z) : b = 0 := by
  obtain ⟨c, -, hu⟩ := h.2.2.1 0
  have h1 := hu ⟨b, hb⟩ fun a => by rw [ef_swap, h0 _ a.2]; simp
  have h2 := hu 0 fun a => by simp
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem IsOpp.exists_sub_mem_perp (h : IsOpp D Z Z') (a : D.La) : ∃ b ∈ Z', a - b ∈ perp D Z := by
  obtain ⟨b, hb, -⟩ := h.2.2.1 ((D.EF.flip a).toAddMonoidHom.comp Z.subtype.toAddMonoidHom)
  refine ⟨b, b.2, fun z hz => ?_⟩
  have := hb ⟨z, hz⟩
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply, LinearMap.flip_apply] at this
  rw [ef_swap, map_sub, this]
  exact neg_eq_zero.2 (sub_self _)

theorem IsOpp.exists_decomp (h : IsOpp D Z Z') (a : D.La) :
    ∃ z ∈ Z, ∃ m ∈ perp D Z ⊓ perp D Z', ∃ b ∈ Z', a = z + m + b := by
  obtain ⟨b, hb, h1⟩ := h.exists_sub_mem_perp a
  obtain ⟨z, hz, h2⟩ := h.symm.exists_sub_mem_perp a
  refine ⟨z, hz, a - b - z, ⟨sub_mem h1 (h.1 hz), ?_⟩, b, hb, by abel⟩
  rw [sub_right_comm]
  exact sub_mem h2 (h.2.1 hb)

theorem IsOpp.isIsoSat (h : IsOpp D Z Z') : IsIsoSat D Z := by
  refine ⟨h.1, fun n x hn hx => ?_⟩
  obtain ⟨z, hz, m, hm, b, hb, rfl⟩ := h.exists_decomp x
  have cancel : ∀ (W : Submodule (𝓞 E) D.La) (v : D.La), n • v ∈ perp D W → v ∈ perp D W := fun W v hv w hw => by
    have := hv w hw
    rw [map_nsmul, LinearMap.smul_apply, smul_eq_zero] at this
    exact this.resolve_left hn
  have hb0 : b = 0 := h.eq_zero hb (by
    have := sub_mem (cancel Z _ (h.1 hx)) (add_mem (h.1 hz) hm.1)
    rwa [add_sub_cancel_left] at this)
  subst hb0
  have hm0 : n • m = 0 := h.symm.eq_zero
    (by have := sub_mem hx (nsmul_mem hz n); rwa [add_zero, smul_add, add_sub_cancel_left] at this) (nsmul_mem hm.2 n)
  have : m = 0 := D.unimod.1 (LinearMap.ext fun w => by
    have := congrArg (fun v => D.EF v w) hm0
    simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_zero] at this
    simpa using this.resolve_left hn)
  simpa [this] using hz

theorem IsOpp.shear (h : IsOpp D Z Z') (t : Z' →ₗ[𝓞 E] D.La) (ht : ∀ b, t b - b ∈ perp D Z)
    (hiso : ∀ b b', D.EF (t b) (t b') = 0) : IsOpp D Z (LinearMap.range t) := by
  have key : ∀ (a : Z) (b : Z'), D.EF a (t b) = D.EF a b := fun a b => by
    have := ht b a a.2
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [ef_swap, this, ← ef_swap]
  refine ⟨h.1, ?_, fun φ => ?_, fun φ => ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    exact hiso b b'
  · obtain ⟨b, hb, hu⟩ := h.2.2.1 φ
    refine ⟨⟨t b, b, rfl⟩, fun a => (key a b).trans (hb a), ?_⟩
    rintro ⟨_, b', rfl⟩ hb'
    exact Subtype.ext (congrArg t (hu b' fun a => (key a b').symm.trans (hb' a)))
  · obtain ⟨a, ha, hu⟩ := h.2.2.2 (φ.comp t.rangeRestrict.toAddMonoidHom)
    refine ⟨a, ?_, fun a' ha' => hu a' fun b => (key a' b).symm.trans (ha' ⟨t b, b, rfl⟩)⟩
    rintro ⟨_, b, rfl⟩
    exact (key a b).trans (ha b)

theorem isOpp_bot (D : Datum H) : IsOpp D ⊥ ⊥ :=
  ⟨bot_le, bot_le, fun φ => ⟨0, fun a => by rw [Subsingleton.elim a 0]; simp, fun _ _ => Subsingleton.elim _ _⟩,
    fun φ => ⟨0, fun a => by rw [Subsingleton.elim a 0]; simp, fun _ _ => Subsingleton.elim _ _⟩⟩

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, GlobalTheory.CharRank.bar_rt_neg, map_ofNat] at h1
  have h2 := H.two_weight_eq_one_add_root
  exact mul_left_cancel₀ (two_ne_zero (α := 𝓞 E)) (by linear_combination h1 + h2)

theorem exists_skew_solve (hd : ∀ φ : Z →+ ℤ, ∃! b : Z', ∀ a : Z, D.EF a b = φ a) (β : LinearMap.BilinForm ℤ Z)
    (hβ : ∀ a b, β a b = -β b a) (hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b)) :
    ∃ c : Z →ₗ[𝓞 E] Z', ∀ a b : Z, D.EF a (c b) + D.EF (c a) b = β a b := by
  choose c hc hu using fun b : Z => hd (AddMonoidHom.mk' (fun a => β (H.w0 • a) b) fun a a' => by simp)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  refine ⟨{ toFun := c, map_add' := fun b b' => (hu _ _ fun a => ?_).symm,
            map_smul' := fun x b => (hu _ _ fun a => ?_).symm }, fun a b => ?_⟩
  · simp [hc]
  · have h1 := hc b (H.bar x • a)
    rw [Submodule.coe_smul, D.adj, bar_bar, smul_comm, hadj, bar_bar] at h1
    exact h1
  · show D.EF a (c b) + D.EF (c a) b = _
    rw [ef_swap D (c a), hc, hc, ← hβ]
    have h2 := hadj (H.bar H.w0) a b
    rw [bar_bar] at h2
    rw [← h2, ← LinearMap.add_apply, ← map_add, ← add_smul, cmHostUnit_add_conj_eq_one, one_smul]

theorem IsOpp.exists_rank_one (h : IsOpp D Z Z') {m : D.La} (hm : m ∈ perp D Z ⊓ perp D Z') (θ : 𝓞 E →+ ℤ)
    (hθ : ∀ t, θ t - θ (H.bar t) + D.EF (t • m) m = 0) :
    ∃ ζ : (Z' →ₗ[𝓞 E] 𝓞 E) →+ D.La, (∀ ℓ, ζ ℓ ∈ Z) ∧ (∀ ℓ (x : Z'), D.EF x (ζ ℓ) = θ (ℓ x)) ∧
      (∀ (c : 𝓞 E) ℓ, ζ (c • ℓ) = H.bar c • ζ ℓ) ∧
      ∀ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, IsOpp D Z (LinearMap.range (Z'.subtype + ℓ.smulRight (m + ζ ℓ))) := by
  choose z hz hu using fun ℓ : Z' →ₗ[𝓞 E] 𝓞 E => h.symm.2.2.1 (θ.comp ℓ.toAddMonoidHom)
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at hz hu
  refine ⟨AddMonoidHom.mk' (fun ℓ => (z ℓ : D.La)) fun ℓ ℓ' => congrArg Subtype.val (hu _ (z ℓ + z ℓ') fun x => ?_).symm,
    fun ℓ => (z ℓ).2, hz, fun c ℓ => congrArg Subtype.val (hu _ (H.bar c • z ℓ) fun x => ?_).symm, fun ℓ => ?_⟩
  · simp [hz]
  · have := hz ℓ (c • x)
    rw [Submodule.coe_smul, D.adj, ℓ.map_smul] at this
    exact this
  · refine h.shear _ (fun b => ?_) fun b b' => ?_
    · simpa using (perp D Z).smul_mem (ℓ b) (add_mem hm.1 (h.1 (z ℓ).2))
    · have e1 : D.EF b b' = 0 := h.2.1 b.2 _ b'.2
      have e2 : ∀ (c : 𝓞 E) (x : Z'), D.EF (c • m) x = 0 := fun c x => (perp D Z').smul_mem c hm.2 _ x.2
      have e3 : ∀ c c' : 𝓞 E, D.EF (c • m) (c' • z ℓ) = 0 := fun c c' =>
        (perp D Z).smul_mem c hm.1 _ (Z.smul_mem c' (z ℓ).2)
      have e4 : ∀ c c' : 𝓞 E, D.EF (c • z ℓ) (c' • z ℓ) = 0 := fun c c' =>
        h.1 (Z.smul_mem c (z ℓ).2) _ (Z.smul_mem c' (z ℓ).2)
      have e5 : ∀ (c : 𝓞 E) (x : Z'), D.EF x (c • z ℓ) = θ (H.bar c * ℓ x) := fun c x => by
        have := hz ℓ (H.bar c • x)
        rw [Submodule.coe_smul, D.adj, bar_bar, ℓ.map_smul] at this
        exact this
      have e6 : D.EF (ℓ b • m) (ℓ b' • m) = D.EF ((H.bar (ℓ b') * ℓ b) • m) m := by
        rw [mul_smul, D.adj (H.bar (ℓ b')), bar_bar]
      have e7 := hθ (H.bar (ℓ b') * ℓ b)
      rw [map_mul H.bar, bar_bar, mul_comm (ℓ b')] at e7
      simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.smulRight_apply, AddMonoidHom.mk'_apply,
        smul_add, map_add]
      rw [ef_swap D b (ℓ b' • m), ef_swap D (ℓ b • (z ℓ : D.La)) b', ef_swap D (ℓ b • (z ℓ : D.La)) (ℓ b' • m),
        e1, e2, e2, e3, e3, e4, e5, e5, e6]
      linear_combination e7

theorem exists_theta_vec (D : Datum H) (m : D.La) :
    ∃ θ : 𝓞 E →+ ℤ, ∀ t, θ t - θ (H.bar t) + D.EF (t • m) m = 0 := by
  refine ⟨AddMonoidHom.mk' (fun t => -D.EF ((H.w0 * t) • m) m) fun a b => by simp [mul_add, add_smul, add_comm],
    fun t => ?_⟩
  have h1 : D.EF ((H.w0 * H.bar t) • m) m = -D.EF ((H.bar H.w0 * t) • m) m := by
    rw [D.adj, map_mul, bar_bar, ef_swap]
  have h2 : D.EF (t • m) m = D.EF ((H.w0 * t) • m) m + D.EF ((H.bar H.w0 * t) • m) m := by
    rw [← LinearMap.add_apply, ← map_add, ← add_smul, ← add_mul, cmHostUnit_add_conj_eq_one, one_mul]
  simp only [AddMonoidHom.mk'_apply]
  linear_combination h1 + h2

theorem range_le_of_mem {O P X : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup X] [Module O X]
    (f : P →ₗ[O] X) (ℓ : P →ₗ[O] O) (u : X) (I : Ideal O) (h : ∀ x, ℓ x ∈ I) :
    LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≤ LinearMap.range (f + ℓ.smulRight u) ⊔ I • ⊤ := by
  refine sup_le ?_ le_sup_right
  rintro _ ⟨x, rfl⟩
  have : f x = (f + ℓ.smulRight u) x - ℓ x • u := by simp
  rw [this]
  exact sub_mem (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem_smul (h x) trivial))

theorem range_le_of_ker {O P X : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup X] [Module O X]
    (f : P →ₗ[O] X) (ℓ : P →ₗ[O] O) (u : X) (I : Ideal O) (hI : I.IsMaximal) {v : P}
    (hv : f v ∈ I • (⊤ : Submodule O X)) (hl : ℓ v ∉ I) :
    u ∈ LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) ∧
      LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≤ LinearMap.range (f + ℓ.smulRight u) ⊔ I • ⊤ := by
  have hu : u ∈ LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) := by
    obtain ⟨c, i, hi, hc⟩ := hI.exists_inv hl
    have : (f + ℓ.smulRight u) (c • v) - c • f v + i • u = u := by
      simp only [LinearMap.add_apply, map_smul, LinearMap.smulRight_apply, smul_add, add_sub_cancel_left, smul_smul]
      rw [← add_smul, hc, one_smul]
    have h2 : (f + ℓ.smulRight u) (c • v) - c • f v + i • u ∈
        LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) :=
      add_mem (sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hv)))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul hi trivial))
    rwa [this] at h2
  refine ⟨hu, sup_le ?_ le_sup_right⟩
  rintro _ ⟨x, rfl⟩
  have : f x = (f + ℓ.smulRight u) x - ℓ x • u := by simp
  rw [this]
  exact sub_mem (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.smul_mem _ _ hu)

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfMkEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalLab

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem three_le_level (X₁ : Setup F W i) : 3 ≤ X₁.S.r * X₁.S.N := by
  have hN := X₁.ρ.N_eq
  have hn := X₁.ρ.n_prime.two_le
  have hk := X₁.ρ.two_le
  have hr := X₁.S.r_pos
  have h4 : 4 ≤ X₁.S.N := by
    rw [hN]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (X₁.ρ.n ^ X₁.ρ.k) ^ 2 :=
        Nat.pow_le_pow_left (le_trans hn (Nat.le_self_pow (by omega) _)) 2
  nlinarith

theorem isLab_onto (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X))
    (h : IsLab X ε c yy) (μ : Fin 8 → c.T.D.toPre.X) : ∃ a, yy a = QuotientAddGroup.mk μ := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm μ))
  exact ⟨a, by rw [hyy a _ ha, AddEquiv.apply_symm_apply]⟩

theorem congMod_of_mk_eq {X : Type} [AddCommGroup X] [Module.Free ℤ X] (κ : X ≃+ X) (m d L₁ : ℕ) (hm : m = d * L₁)
    (hd : d ≠ 0) (x : X)
    (h : (QuotientAddGroup.mk (d • (Pi.single (0 : Fin 8) x : Fin 8 → X)) : ModN m (Fin 8 → X)) =
      QuotientAddGroup.mk (fun b => κ ((d • (Pi.single (0 : Fin 8) x : Fin 8 → X)) b))) : CongMod L₁ (κ x) x := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.1 h
  have hw0 := congrFun hw 0
  simp only [nsmulAddMonoidHom_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.single_eq_same,
    map_nsmul] at hw0
  refine ⟨w 0, ?_⟩
  have key : (d : ℤ) • ((L₁ : ℤ) • w 0) = (d : ℤ) • (κ x - x) := by
    rw [← mul_smul, ← Nat.cast_mul, ← hm, natCast_zsmul, hw0, smul_sub, natCast_zsmul, natCast_zsmul]; abel
  have := smul_right_injective X (show (d : ℤ) ≠ 0 by exact_mod_cast hd) key
  rw [← natCast_zsmul, this]; abel

theorem rigid {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (D : Deep X₁ ε₁)
    {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁)
    (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (h₁ : IsLab X₁ ε₁ c yy₁)
    (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
    (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X))
    (hl : IsLab D.X D.ε (D.lift c y h) yy) (hc : D.Compat yy₁ yy)
    (hl' : IsLab D.X D.ε (D.lift c y h) yy') (hc' : D.Compat yy₁ yy') : yy' = yy := by
  obtain ⟨κ, hκβ, hκ⟩ := LabUniq.main g n F W Z i D.X D.ε D.diag p (y (cPt p)) (D.lift c y h) yy yy' hl hl'
  have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    rw [D.sq]
    exact D.dvd.trans ((dvd_pow_self D.m two_ne_zero).mul_left _)
  have hdL : D.X.S.r * D.X.S.N = D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) :=
    (Nat.div_mul_cancel hdvd).symm
  have hd0 : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) ≠ 0 := by
    intro h0
    have h3 := three_le_level D.X
    rw [hdL, h0, zero_mul] at h3
    omega
  have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (κ x) x := by
    intro x
    obtain ⟨a, ha⟩ := isLab_onto X₁ ε₁ c yy₁ h₁ (Pi.single 0 x)
    have e1 := hc a _ ha
    have e2 := hc' a _ ha
    have e3 := hκ (D.lab a) _ e1
    rw [e2] at e3
    exact congMod_of_mk_eq κ _ _ _ hdL hd0 x e3
  let e : c.T.D.toPre.X ≃ₗ[ℤ] c.T.D.toPre.X := κ.toIntLinearEquiv
  have he : e = LinearEquiv.refl ℤ _ :=
    eq_refl_of_isometry_congMod _ c.T.β (fun x hx => Trait.beta_pos g n _ _ F c.T x hx) e hκβ _
      (three_le_level X₁) hcong
  have hκ1 : ∀ x, κ x = x := fun x => by
    have := congrArg (fun f : c.T.D.toPre.X ≃ₗ[ℤ] c.T.D.toPre.X => f x) he
    simpa [e] using this
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy x)
  rw [hκ x μ hμ.symm, ← hμ]
  simp [hκ1]

end GlobalTheory.Poinc.GalLab

theorem GlobalTheory.Poinc.GalLab.main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') yy' → D.Compat yy₁ yy' → ∀ x, yy' x = yy (a x) := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D σ s hs
  obtain ⟨a, hfix, htr⟩ := GlobalTheory.T.galois_transport_torsion_labels_thetaSetup g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D σ s hs
  refine ⟨a, hfix, ?_⟩
  intro p _ z₁ c yy₁ h₁ y h h' yy yy' hl hc hl' hc' x
  have hl2 := htr p z₁ c y h h' yy hl
  have hc2 : D.Compat yy₁ (yy.comp a.toAddMonoidHom) := fun b μ hb => by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hfix]
    exact hc b μ hb
  have := GalLab.rigid D c yy₁ h₁ (y ≫ s) h' (yy.comp a.toAddMonoidHom) yy' hl2 hc2 hl' hc'
  exact (DFunLike.congr_fun this x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateLogDerivMinusPotentialsChartIndependen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem cancel_unit {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (δ : A → B) (u : Aˣ) (L Δ : B)
    (h₁ : δ u.val = π u.val * L) (h₂ : δ u.val = π u.val * Δ) : L = Δ :=
  ((Units.isUnit u).map π).mul_left_cancel (h₁.symm.trans h₂)

section ChartFreeProof

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} {h : Heat Y.H Y.q.left Q.P.L dd D}
  {K : Type} [Field K] {ν : R} {A₀ : Over (Sp K)} {m₀ : A₀.left ⟶ Q.P.A.left} {V : h.J → Q.P.A.left.Opens}
  {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}

theorem dE_trans_unit {D' : R → K} (hC : IsConnK Q.P.A Q.P.L A₀ m₀ D' V h.j ed pb) (hD : IsDesc Y h ν m₀ V ed pb)
    (hCo : Commutes Q m₀ ed) (α : Q.X) (j : Fin 4) (T : A₀.left ⟶ A₀.left) (h₁ : T ≫ m₀ = m₀ ≫ Q.famφB α j)
    (h₂ : T ≫ A₀.hom = A₀.hom) {Z : Scheme.{0}} {a : Z ⟶ Y.H.left} {b : Z ⟶ A₀.left} (w : a ≫ Y.q.left = b ≫ m₀)
    (z : Z) (i₀ : h.J) (hi₀ : (b ≫ m₀) z ∈ V i₀)
    (δ : Y.H.left.presheaf.stalk (a z) → Z.presheaf.stalk z)
    (hδ : ∀ W, W ≤ h.W i₀ → a z ∈ W → ∀ f, δ (gs (𝟙 _) (a z) W f) = gs a z W (dE h ν i₀ W f))
    (c c' : h.J) (hc : (b ≫ T ≫ m₀) z ∈ V c) (hc' : (b ≫ T ≫ m₀) z ∈ V c') :
    δ (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) (Q.P.L.g (h.j c) (h.j c')).val) =
      (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c'))
        (Q.P.L.g (h.j c) (h.j c')).val) *
        (gs (b ≫ T) z (m₀ ⁻¹ᵁ V c') (pb c') - gs (b ≫ T) z (m₀ ⁻¹ᵁ V c) (pb c)) := by
  have e : a ≫ Y.q.left ≫ Q.famφB α j = b ≫ T ≫ m₀ := by rw [h₁, reassoc_of% w]
  have hVL : V c ⊓ V c' ≤ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := inf_le_inf (hC.2.2.1 c) (hC.2.2.1 c')
  have hpV : (Q.famφB α j) (Y.q.left (a z)) ∈ V c ⊓ V c' := by
    show (a ≫ Y.q.left ≫ Q.famφB α j) z ∈ V c ⊓ V c'
    rw [e]; exact ⟨hc, hc'⟩
  have hq0 : Y.q.left (a z) ∈ V i₀ := by
    show (a ≫ Y.q.left) z ∈ V i₀
    rw [w]; exact hi₀
  have hqU : Y.q.left (a z) ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := ⟨hq0, hpV⟩
  have hbU : (b ≫ m₀) z ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := by
    show (b ≫ m₀) z ∈ _
    rw [← w]; exact hqU
  set g := (Q.P.L.g (h.j c) (h.j c')).val
  set F := ((Q.famφB α j).app (V c ⊓ V c')).hom (rsT g (V c ⊓ V c'))
  set f := resG Q.P.A.left (inf_le_right : V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') ≤ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) F
  have s₁ : gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) g =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c'))) ((Y.q.left.app _).hom f) := by
    rw [gs_pull (𝟙 _) Y.q.left (a z) _ hqU f, Category.id_comp, gs_res Y.q.left (a z) inf_le_right hqU F,
      gs_pull Y.q.left (Q.famφB α j) (a z) _ hpV _, gs_rsT (Y.q.left ≫ Q.famφB α j) (a z) hVL hpV]
  have hle : Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ h.W i₀ := by
    rw [hD.1 i₀]; exact fun _ hx ↦ hx.1
  have hbT : (b ≫ T) z ∈ m₀ ⁻¹ᵁ (V c ⊓ V c') := ⟨hc, hc'⟩
  have m : (Y.q.left ≫ Q.famφB α j) (a z) ∈ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := hVL hpV
  have hπ : (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) _ g) = gs (b ≫ T ≫ m₀) z _ g := by
    rw [← e, ← gs_pull a (Y.q.left ≫ Q.famφB α j) z _ m g, gs_stalkMap a z _ m, gs_pull (𝟙 _) _ (a z) _ m g,
      Category.id_comp]
  rw [hπ, s₁, hδ _ hle hqU, ← hD.2.1 Z a b w z i₀ _ inf_le_left hbU f,
    hC.1.res _ _ inf_le_right le_top F, gs_rsT b z (show m₀ ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ m₀ ⁻¹ᵁ (Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) from fun _ hx ↦ hx.2) hbU,
    hCo α j T h₁ h₂ (V c ⊓ V c') (rsT g (V c ⊓ V c')) Z b z ⟨hc, hc'⟩, hC.2.2.2 c c',
    gs_mul _ z _ hbT, gs_sub _ z _ hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c' from fun _ hx ↦ hx.2) hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c from fun _ hx ↦ hx.1) hbT,
    gs_pbT (b ≫ T) m₀ z (fun _ hx ↦ hVL hx) hbT, Category.assoc]

end ChartFreeProof

theorem chartFree : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCo α T h₁ h₂ Z a b hw z i i' hi hi' w H
  unfold CoordAt at H ⊢
  have hV : ∀ c, V c ≤ Q.P.L.U (h.j c) := hC.2.2.1
  have hm := hF.mem_chart hD hV h₁ hw hi
  have hm' := hF.mem_chart hD hV h₁ hw hi'
  have hT0 := hF.T_zero (h₁ 0) (h₂ 0)
  have hi₀ : (b ≫ m₀) z ∈ V (i 0) := by
    have := hi 0
    rwa [hT0, Category.id_comp] at this
  obtain ⟨δ, -, hδm, hδ⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z hm.1
  obtain ⟨l, hl⟩ := exists_dlog (a.stalkMap z).hom δ hδm
  have hx : gs a z (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j))
      (dE h ν (i 0) _ (rsT (xc Y α fun j ↦ h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i j)) (xc Y α fun j ↦ h.j (i j))).val := by
    rw [← hδ _ inf_le_left hm, gs_rsT (𝟙 _) (a z) inf_le_right hm, gs_unit (𝟙 _) (a z) _ hm.2]
  have hx' : gs a z (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j))
      (dE h ν (i' 0) _ (rsT (xc Y α fun j ↦ h.j (i' j)).val (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i' j)) (xc Y α fun j ↦ h.j (i' j))).val := by
    have hU : a z ∈ h.W (i 0) ⊓ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) := ⟨⟨hm.1, hm'.1⟩, hm'.2⟩
    have hle : h.W (i 0) ⊓ h.W (i' 0) ⊓ (xU Y α fun j ↦ h.j (i' j)) ≤ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) :=
      fun _ hy ↦ ⟨hy.1.2, hy.2⟩
    rw [← gs_res a z hle hU, ← (isField_dE h ν hF.field (i' 0)).2.2 _ _ hle inf_le_left,
      ← hF.dE_agree hw z (i 0) (i' 0) _ inf_le_left hU, ← hδ _ (inf_le_left.trans inf_le_left) hU, gs_res (𝟙 _) (a z) hle hU,
      gs_rsT (𝟙 _) (a z) inf_le_right hm', gs_unit (𝟙 _) (a z) _ hm'.2]
  have ht := gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 Y.H.left) (a z) hm.2 hm'.2
  have hu : ∀ k, (l (gm (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z)
      (Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))))
      (Q.P.L.g (h.j (i (![1, 2, 0, 3] k))) (h.j (i' (![1, 2, 0, 3] k)))))).toAdd =
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i' (![1, 2, 0, 3] k))) (pb (i' (![1, 2, 0, 3] k))) -
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i (![1, 2, 0, 3] k))) (pb (i (![1, 2, 0, 3] k))) := by
    intro k
    have mem : (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z) ∈
        Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))) :=
      ⟨Set.mem_iInter.1 hm.2 k, Set.mem_iInter.1 hm'.2 k⟩
    refine cancel_unit _ δ _ _ _ (hl _) ?_
    rw [← gs_unit _ _ _ mem, Category.id_comp, gtφT_eq]
    exact dE_trans_unit hC hD hCo α _ (T _) (h₁ _) (h₂ _) hw z (i 0) hi₀ δ hδ _ _ (hi _) (hi' _)
  have e2 := congrArg (fun u ↦ (l u).toAdd) ht
  simp only [map_mul, toAdd_mul, trF, map_prod, map_zpow, toAdd_prod, toAdd_zpow, Fin.sum_univ_four] at e2
  rw [hu 0, hu 1, hu 2, hu 3] at e2
  simp only [DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at e2
  rw [hx, gs_stalkMap a z _ hm.2, gs_unit (𝟙 _) (a z) _ hm.2] at H
  have eH := cancel_unit _ δ _ _ _ (hl _) H
  rw [hx', hl, gs_stalkMap a z _ hm'.2, gs_unit (𝟙 _) (a z) _ hm'.2]
  congr 1
  linear_combination eH - e2

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalarsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverTrait_expansion_scale_both_scalars : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  first | exact @GlobalTheory.Mum.Trait.exp_mul_left | exact GlobalTheory.Mum.Trait.exp_mul_left | (intros; apply GlobalTheory.Mum.Trait.exp_mul_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelStaysDividingDeeperModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividingLabel_stays_dividing_deeper_model : (∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  first | exact @GlobalTheory.Poinc.Sep.DeepDiv.div_lam | exact GlobalTheory.Poinc.Sep.DeepDiv.div_lam | (intros; apply GlobalTheory.Poinc.Sep.DeepDiv.div_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsPartCocycleCoboundaryOfHodgeDeRhamStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eps_part_cocycle_coboundary_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ u : Fn1 (A ⊗ B), IsCoc P.U u → Cohom (chartsA P) (sndPull u v) (Fn1.zero A) := by
  first | exact @GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham | exact GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham | (intros; apply GlobalTheory.PtExt.sndPull_cohom_zero_of_hodgeDeRham <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryDivisibleOfQuasiLogDefecStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_coboundary_divisible_of_quasiLog_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f → map (algebraMap O E) s = defect c.μ p f → c.ev 1 s = (p : O) • y → ∃ t : MvPowerSeries (Fin d) O, constantCoeff t = 0 ∧ In (Ideal.span {(p : O)}) (cob1 (up E c.μ) (f - map (algebraMap O E) t)) := by
  first | exact @GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev | exact GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev | (intros; apply GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev <;> assumption)
end

