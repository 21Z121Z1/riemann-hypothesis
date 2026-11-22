import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassIsSymmOfLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

abbrev Mc (l : Level H) : Ideal (𝓞 E) := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)

theorem exists_idem (l : Level H) : ∃ e ∈ Mc l, 1 - e ∈ l.Mb := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  exact ⟨y, hy, by rw [← hxy, add_sub_cancel_right]; exact hx⟩

theorem M_pos (l : Level H) : 0 < l.M := by
  have := l.three_le
  omega

theorem modN_of_mem_span {n : ℕ} {a : D.La}
    (h : a ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN n a := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨b, -, hb⟩ := h
  exact ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩

theorem modN_smul_Mb (l : Level H) {c : 𝓞 E} (hc : c ∈ Mc l) {a : D.La}
    (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • l.Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, mul_comm, l.prod] at h1

theorem modN_smul_Mc (l : Level H) {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb • l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, l.prod] at h1

theorem modN_of_mem_both (l : Level H) {a : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (ha' : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M a := by
  obtain ⟨e, he, he'⟩ := exists_idem l
  obtain ⟨b₁, hb₁⟩ := modN_smul_Mb l he ha
  obtain ⟨b₂, hb₂⟩ := modN_smul_Mc l he' ha'
  refine ⟨b₁ + b₂, ?_⟩
  rw [smul_add, ← hb₁, ← hb₂, ← add_smul]
  simp

theorem nsmul_M_mem (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem add_map_zero {M Q : Type} [AddCommGroup M] [Group Q] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c) :
    f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)

theorem add_map_nsmul {M Q : Type} [AddCommGroup M] [Group Q] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : M) : f (n • a) = f a ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; exact add_map_zero hf
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_pow_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) (a : D.La) :
    I.ev N a ^ (N / n) = I.ev n a := by
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hN
  have hq : 0 < N / n := Nat.div_pos (Nat.le_of_dvd hN h) hn
  have := I.tower n (N / n) hn hq a
  rwa [Nat.mul_div_cancel' h] at this

theorem zeta_pow_div (I : TateIso D k Q act e) {n N : ℕ} (hN : 0 < N) (h : n ∣ N) :
    I.ζ N ^ (N / n) = I.ζ n := by
  have hn : 0 < n := Nat.pos_of_dvd_of_pos h hN
  have hq : 0 < N / n := Nat.div_pos (Nat.le_of_dvd hN h) hn
  have := I.ζ_pow n (N / n) hn hq
  rwa [Nat.mul_div_cancel' h] at this

theorem exists_coprime_zpow {N : ℕ} (hN : 0 < N) {ζ ξ : kˣ} (hζ : IsPrimitiveRoot ζ N) (hξ : IsPrimitiveRoot ξ N) :
    ∃ ν : ℤ, IsCoprime ν (N : ℤ) ∧ ξ = ζ ^ ν := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one (ξ := (ξ : k))
    (by rw [← Units.val_pow_eq_pow_val, hξ.pow_eq_one, Units.val_one])
  have hξi : ξ = ζ ^ i := Units.ext (by rw [Units.val_pow_eq_pow_val, hi])
  have hcop : i.Coprime N := (hζ.pow_iff_coprime hN i).1 (by rw [← hξi]; exact hξ)
  exact ⟨i, Nat.isCoprime_iff_coprime.2 hcop, by rw [hξi, zpow_natCast]⟩

theorem exists_adjust
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (l : Level H) (N : ℕ)
    (hM : ∀ ν : ℤ, 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 → ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν ∧
      (l.A : ℤ) ∣ g.ν l.A - 1 ∧ (∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) ∧
      ∀ a, D.ModN l.A (g.f l.A a - a))
    (I : TateIso D k Q act e) (hN : 0 < N) (hA : l.A ∣ N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N)
    (h : ξ ^ (N / l.A) = I.ζ l.A) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La), I'.ev l.M a = I.ev l.M a := by
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hA0 := l.A_pos
  have h1 : I.ζ l.A ^ ν = I.ζ l.A := by
    calc I.ζ l.A ^ ν = ((I.ζ N) ^ (N / l.A)) ^ ν := by rw [zeta_pow_div I hN hA]
      _ = ((I.ζ N) ^ ν) ^ (N / l.A) := by simp only [← zpow_natCast, ← zpow_mul, mul_comm]
      _ = I.ζ l.A := by rw [← hξν, h]
  have hA1 : (l.A : ℤ) ∣ ν - 1 := by
    refine ((I.ζ_prim l.A hA0).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, zpow_one, h1, mul_inv_cancel]
  obtain ⟨g, hgN, -, hgM, hgA⟩ := hM ν hN hνc hA1
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgN
  · rw [LevelTwist.twist_ev]
    exact LevelTwist.ev_congr I hA0 (hgA a)
  · rw [LevelTwist.twist_ev]
    refine LevelTwist.ev_congr I (M_pos l) (modN_of_mem_both l (hgM a) ?_)
    exact Submodule.sub_mem _ (LevelTwist.map_mem_smul_top _ _ ha) ha

theorem exists_of_level
    (hν : ∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ))
    (N : ℕ)
    (hL : ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
      (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
      ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν)
    (he : ∀ x y c c', e N x y c → e N x y c' → c = c')
    (I : TateIso D k Q act e) (hN : 0 < N) {ξ : kˣ} (hξ : IsPrimitiveRoot ξ N) (α : D.La → Q)
    (hadd : ∀ a c, α (a + c) = α a * α c) (hpow : ∀ a, α a ^ N = 1) (hlin : ∀ c a, α (c • a) = act c (α a))
    (hiso : ∀ a b, e N (α a) (α b) (ξ ^ D.EF a b)) :
    ∃ I' : TateIso D k Q act e, I'.ζ N = ξ ∧ ∀ a, I'.ev N a = α a := by
  classical
  choose b hb using fun a => (I.onto N hN (α a)).1 (hpow a)
  let K : Submodule (𝓞 E) D.La := LinearMap.range ((N : 𝓞 E) • LinearMap.id)
  have memK : ∀ x y, I.ev N x = I.ev N y → x - y ∈ K := by
    intro x y hxy
    obtain ⟨z, hz⟩ := (tateIso_ev_eq_iff I hN x y).1 hxy
    exact LinearMap.mem_range.2
      ⟨z, by rw [hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  let β : D.La →ₗ[𝓞 E] D.La ⧸ K :=
    { toFun := fun a => Submodule.Quotient.mk (b a)
      map_add' := fun a c => by
        rw [← Submodule.Quotient.mk_add]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.add, hb, hb, hadd]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        refine (Submodule.Quotient.eq K).2 (memK _ _ ?_)
        rw [hb, I.lin, hb, hlin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property K.mkQ β K.mkQ_surjective
  have hfα : ∀ a, I.ev N (f a) = α a := by
    intro a
    have h1 : (Submodule.Quotient.mk (f a) : D.La ⧸ K) = Submodule.Quotient.mk (b a) :=
      LinearMap.congr_fun hf a
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq K).1 h1)
    rw [← hb a]
    exact (tateIso_ev_eq_iff I hN _ _).2
      ⟨z, by rw [← hz, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨ν, hνc, hξν⟩ := exists_coprime_zpow hN (I.ζ_prim N hN) hξ
  have hEF : ∀ a c, (N : ℤ) ∣ D.EF (f a) (f c) - ν * D.EF a c := by
    intro a c
    have h1 := I.isom N hN (f a) (f c)
    rw [hfα, hfα] at h1
    have h2 := he _ _ _ _ (hiso a c) h1
    rw [hξν, ← zpow_mul] at h2
    refine ((I.ζ_prim N hN).zpow_eq_one_iff_dvd _).1 ?_
    rw [zpow_sub, ← h2, mul_inv_cancel]
  obtain ⟨g, hgf, hgν⟩ := hL f ν hN hνc hEF
  refine ⟨LevelTwist.twist I g (hν g), ?_, fun a => ?_⟩
  · rw [LevelTwist.twist_ζ, hξν]
    exact LevelTwist.zeta_zpow_congr I hN hgν
  · rw [LevelTwist.twist_ev, ← hfα a]
    exact LevelTwist.ev_congr I hN (hgf a)

theorem exists_root_ext (B : Type) [Field B] [CharZero B] {A N : ℕ} (hN : 0 < N) (hA : A ∣ N) {ζ : B}
    (hζ : IsPrimitiveRoot ζ A) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra B L) (ξ : Lˣ), FiniteDimensional B L ∧ IsPrimitiveRoot ξ N ∧
      (ξ : L) ^ (N / A) = algebraMap B L ζ := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  have hA0 : 0 < A := Nat.pos_of_dvd_of_pos hA hN
  have : NeZero A := ⟨hA0.ne'⟩
  have hω := IsCyclotomicExtension.zeta_spec N B (CyclotomicField N B)
  set ω := IsCyclotomicExtension.zeta N B (CyclotomicField N B)
  have hq : 0 < N / A := Nat.div_pos (Nat.le_of_dvd hN hA) hA0
  have hω' : IsPrimitiveRoot (ω ^ (N / A)) A := by
    have := hω.pow_of_dvd hq.ne' (Nat.div_dvd_of_dvd hA)
    rwa [Nat.div_div_self hA hN.ne'] at this
  have hη : IsPrimitiveRoot (algebraMap B (CyclotomicField N B) ζ) A :=
    hζ.map_of_injective (algebraMap B (CyclotomicField N B)).injective
  obtain ⟨i, hiA, hi⟩ := hω'.eq_pow_of_pow_eq_one hη.pow_eq_one
  have hic : i.Coprime A := (hω'.pow_iff_coprime hA0 i).1 (by rw [hi]; exact hη)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hA (ZMod.unitOfCoprime i hic)
  have hji : (v : ZMod N).val % A = i % A := by
    have h1 := congrArg (fun u : (ZMod A)ˣ => (u : ZMod A)) hv
    simp only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at h1
    rw [← ZMod.natCast_val] at h1
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h1
  have hξ : IsPrimitiveRoot (ω ^ (v : ZMod N).val) N := hω.pow_of_coprime _ (ZMod.val_coe_unit_coprime v)
  refine ⟨CyclotomicField N B, inferInstance, inferInstance, (hξ.isUnit hN.ne').unit, ?_, ?_, ?_⟩
  · exact IsCyclotomicExtension.finiteDimensional {N} B (CyclotomicField N B)
  · exact IsPrimitiveRoot.coe_units_iff.1 (by rw [IsUnit.unit_spec]; exact hξ)
  · rw [IsUnit.unit_spec, ← pow_mul, mul_comm, pow_mul, pow_eq_pow_mod _ hω'.pow_eq_one, hji,
      Nat.mod_eq_of_lt hiA, hi]

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleCocycleOneAddEps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsCocycle

noncomputable section

lemma res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma cocycle_on {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    res h₁ (L.g i j) * res h₂ (L.g j k) = res h₃ (L.g i k) := by
  have := congrArg (res (le_inf h₁ (h₂.trans inf_le_right) : W ≤ L.U i ⊓ L.U j ⊓ L.U k))
    (hL.cocycle i j k)
  simpa only [map_mul, res_res] using this

def regauge {X : Scheme.{0}} (L : LB X) (u : ∀ i, Γ(X, L.U i)ˣ) : LB X :=
  ⟨L.ι, L.U, fun i i' => (res inf_le_left (u i))⁻¹ * L.g i i' * res inf_le_right (u i')⟩

lemma regauge_isLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    (regauge L u).IsLB where
  cover := hL.cover
  g_self := fun i => by
    have := hL.g_self i
    change res (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i)
      ((res inf_le_left (u i))⁻¹ * L.g i i * res inf_le_right (u i)) = 1
    simp only [map_mul, map_inv, res_res, this, _root_.mul_one, inv_mul_cancel]
  cocycle := fun i j k => by
    have := hL.cocycle i j k
    change res (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j)
        ((res inf_le_left (u i))⁻¹ * L.g i j * res inf_le_right (u j)) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k)
        ((res inf_le_left (u j))⁻¹ * L.g j k * res inf_le_right (u k)) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k)
        ((res inf_le_left (u i))⁻¹ * L.g i k * res inf_le_right (u k))
    simp only [map_mul, map_inv, res_res, ← this]
    group

lemma regauge_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (u : ∀ i, Γ(X, L.U i)ˣ) :
    LBIso L (regauge L u) := by
  refine ⟨⟨fun p : L.ι × L.ι => ((res inf_le_left (u p.1))⁻¹ * L.g p.1 p.2 :
    Γ(X, L.U p.1 ⊓ L.U p.2)ˣ)⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩
  let W : X.Opens := L.U a ⊓ L.U b ⊓ (L.U a' ⊓ L.U b')
  have ha : W ≤ L.U a := inf_le_left.trans inf_le_left
  have hb : W ≤ L.U b := inf_le_left.trans inf_le_right
  have ha' : W ≤ L.U a' := inf_le_right.trans inf_le_left
  have hb' : W ≤ L.U b' := inf_le_right.trans inf_le_right
  change res (le_inf ha hb) ((res inf_le_left (u a))⁻¹ * L.g a b) =
    (res (le_inf ha ha') ((res inf_le_left (u a))⁻¹ * L.g a a' * res inf_le_right (u a')) *
      (res (le_inf hb hb') (L.g b b'))⁻¹) *
      res (le_inf ha' hb') ((res inf_le_left (u a'))⁻¹ * L.g a' b')
  have e₁ := cocycle_on hL a a' b' (le_inf ha ha') (le_inf ha' hb') (le_inf ha hb')
  have e₂ := cocycle_on hL a b b' (le_inf ha hb) (le_inf hb hb') (le_inf ha hb')
  have e₃ : res (le_inf ha hb) (L.g a b) = res (le_inf ha ha') (L.g a a') *
      res (le_inf ha' hb') (L.g a' b') * (res (le_inf hb hb') (L.g b b'))⁻¹ := by
    rw [e₁, ← e₂, mul_inv_cancel_right]
  simp only [map_mul, map_inv, res_res, e₃]
  generalize res ha (u a) = x
  generalize res ha' (u a') = y
  generalize res (le_inf ha ha') (L.g a a') = z
  generalize res (le_inf ha' hb') (L.g a' b') = w
  generalize res (le_inf hb hb') (L.g b b') = v
  rw [mul_mul_mul_comm _ v⁻¹, mul_inv_cancel_right]
  ac_rfl

lemma appLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)) :
    (j.appLE O' O₂ h').hom ((ρ.appLE O O' h).hom a) = resG Y h'' a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Y) (_ : f = 𝟙 Y) (e : O₂ ≤ f ⁻¹ᵁ O), (f.appLE O O₂ e).hom a = resG Y h'' a := by
    intro f hf e
    subst hf
    simp [Scheme.Hom.appLE]
    rfl
  exact key _ hj _

lemma appLE_constFn_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)}
    {j : Y ⟶ Y'} (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    {O : Y.Opens} {O' : Y'.Opens} (h : O ≤ j ⁻¹ᵁ O') :
    (j.appLE O' O h).hom (constFn π O' DualNumber.eps) = 0 := by
  have h0 : O' ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  change (j.appLE O' O h).hom ((π.appLE ⊤ O' h0).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps)) = 0
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Sp (DualNumber ℂ))
      (_ : f = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (e : O ≤ f ⁻¹ᵁ ⊤),
      (f.appLE ⊤ O e).hom ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).inv.hom DualNumber.eps) = 0 := by
    intro f hf e
    subst hf
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have e2 := congrArg (fun φ => φ.hom DualNumber.eps) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    have e3 : (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom DualNumber.eps = 0 := by
      simp
    rw [e3, map_zero] at e2
    exact (congrArg _ e2.symm).trans (map_zero _)
  exact key _ hq _

lemma eq_one_add_eps {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}
    {j : Y ⟶ Y'} (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (O' : Y'.Opens)
    (F : Γ(Y', O')) (hF : (j.appLE O' _ le_rfl).hom F = 1) :
    ∃ k : Γ(Y, j ⁻¹ᵁ O'), ∀ h : O' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ O'),
      F = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom k := by
  obtain ⟨h₁, -, h₃⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have key : ∀ (O : Y.Opens) (O' : Y'.Opens) (_ : ρ ⁻¹ᵁ O = O') (F : Γ(Y', O')), ∃ a b : Γ(Y, O),
      ∀ h : O' ≤ ρ ⁻¹ᵁ O,
        F = (ρ.appLE _ _ h).hom a + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom b := by
    intro O O' e F
    subst e
    obtain ⟨ab, hab, -⟩ := h₃ O F
    refine ⟨ab.1, ab.2, fun h => ?_⟩
    rw [Scheme.Hom.appLE_eq_app]
    exact hab
  obtain ⟨a, b, hab⟩ := key _ O' (h₁ O') F
  refine ⟨b, fun h => ?_⟩
  have ha : a = 1 := by
    rw [hab h, map_add, map_mul, appLE_constFn_eps hq, zero_mul, add_zero,
      appLE_section hj h le_rfl le_rfl] at hF
    have e : resG Y (le_refl (j ⁻¹ᵁ O')) a = a := by
      change (Y.presheaf.map (𝟙 _)).hom a = a
      rw [Y.presheaf.map_id]
      rfl
    exact e.symm.trans hF
  rw [hab h, ha, map_one]

def pullLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, V)ˣ := Units.map (f.appLE U V h).hom

lemma pullLE_eq {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) : pullLE f h x = res h (pullU f U x) := by
  ext
  rfl

lemma pullLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U')
    (h' : U' ≤ U) (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullLE f h (res h' x) = pullLE f h'' x := by
  ext
  simp only [pullLE, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma pullLE_section {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)ˣ) : pullLE j h' (pullLE ρ h a) = res h'' a := by
  ext
  exact appLE_section hj h h' h'' a.val

theorem exists_cocycle_one_add_eps : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ Q : LB Y', Q.IsLB → (∃ t : (Q.pull j).Gen, t.IsGen) → ∃ (Q' : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), Q'.IsLB ∧ LBIso Q Q' ∧ (∀ i i' (h : Q'.U i ⊓ Q'.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), (Q'.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) := by
  intro Y Y' q π ρ j hp hj hq Q hQ ⟨t, ht⟩
  obtain ⟨h₁, -, -⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have hw : ∀ i : Q.ι, j ⁻¹ᵁ Q.U i ≤ (Q.pull j).U (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let s : ∀ i : Q.ι, Γ(Y, j ⁻¹ᵁ Q.U i)ˣ := fun i => res (hw i) (t.s fun _ => i)
  let u : ∀ i, Γ(Y', Q.U i)ˣ := fun i => pullLE ρ (h₁ (Q.U i)).ge (s i)
  have main : ∀ i i' : Q.ι, (j.appLE (Q.U i ⊓ Q.U i') _ le_rfl).hom ((regauge Q u).g i i').val = 1 := by
    intro i i'
    have hl : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have hr : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have e := congrArg (res (le_inf (hl.trans (hw i)) (hr.trans (hw i'))))
      (ht (fun _ => i) (fun _ => i'))
    have eg : res (le_inf (hl.trans (hw i)) (hr.trans (hw i')))
        ((Q.pull j).g (fun _ => i) (fun _ => i')) =
        pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (Q.g i i') := by
      rw [pullLE_eq]
      change res _ (∏ _k : PUnit.{1}, (res _ (pullU j _ (Q.g i i'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact res_res _ _ _
    rw [map_mul, res_res, res_res, eg] at e
    have : pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i')))
        ((res inf_le_left (u i))⁻¹ * Q.g i i' * res inf_le_right (u i')) = 1 := by
      rw [map_mul, map_mul, map_inv, pullLE_res j _ _ hl, pullLE_res j _ _ hr,
        pullLE_section hj _ _ hl, pullLE_section hj _ _ hr, res_res, res_res, _root_.mul_assoc, ← e,
        inv_mul_cancel]
    exact congrArg Units.val this
  choose k hk using fun i i' : Q.ι => eq_one_add_eps hp hj hq _ _ (main i i')
  exact ⟨regauge Q u, k, regauge_isLB hQ u, regauge_iso hQ u, hk⟩

end

end GlobalTheory.EpsCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoThickeningMapOfModEpsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_thickening_map_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  first | exact @GlobalTheory.ThickeningIso.isIso_of_mod_eps | exact GlobalTheory.ThickeningIso.isIso_of_mod_eps | (intros; apply GlobalTheory.ThickeningIso.isIso_of_mod_eps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassIsSymmOfLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_class_isSymm_of_lift : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ s, KSRel u p m D Θ s → ∀ L : LB X, L.IsLB → LBIso P₀.L (L.pull m) → IsSymm Hm Θ := by
  first | exact @GlobalTheory.KS.isSymm_of_lift | exact GlobalTheory.KS.isSymm_of_lift | (intros; apply GlobalTheory.KS.isSymm_of_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A), IsMonHom α → IsFinite α.left → Finite {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1} ∧ ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1}) := by
  first | exact @GlobalTheory.mapDeg_eq_pow_mul_card_ker | exact GlobalTheory.mapDeg_eq_pow_mul_card_ker | (intros; apply GlobalTheory.mapDeg_eq_pow_mul_card_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.primeToPart_level_exists_unique_mono : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p : ℕ), p.Prime → (∀ l : Level H, l.GoodAt p → ∃ l₀ : Level H, IsPrimeToPart l₀ l p) ∧ (∀ l l₀ : Level H, IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧ ∀ l₀' : Level H, IsPrimeToPart l₀' l p → l₀' = l₀) ∧ ∀ l l' l₀ l₀' : Level H, IsPrimeToPart l₀ l p → IsPrimeToPart l₀' l' p → l.Dvd l' → l₀.Dvd l₀' := by
  first | exact @GlobalTheory.Models.primeToPart_spec | exact GlobalTheory.Models.primeToPart_spec | (intros; apply GlobalTheory.Models.primeToPart_spec <;> assumption)
end

