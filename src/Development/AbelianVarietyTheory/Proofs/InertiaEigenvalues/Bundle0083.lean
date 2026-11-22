import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultTransport
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.SenAdd

section
variable {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]

theorem pow_mem (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (m : ℕ) :
    ∀ y ∈ Q, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    apply ih
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Q.sub_mem (hQ y hy) (Q.smul_mem _ hy)

theorem mem_gen (T : Module.End k A) (Q : Submodule k A) (hQ : ∀ y ∈ Q, T y ∈ Q) (x : k) (y : A) :
    y ∈ (⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m)) ↔
      ∃ m : ℕ, ((T - algebraMap k (Module.End k A) x) ^ m) y ∈ Q := by
  have hm : Monotone fun m : ℕ => Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) := by
    refine monotone_nat_of_le_succ fun m z hz => ?_
    rw [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]
    simpa using pow_mem T Q hQ x 1 _ hz
  exact Submodule.mem_iSup_of_directed _ hm.directed_le

theorem pow_comm (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B) (hT : ∀ y, h (T y) = T' (h y))
    (x : k) (m : ℕ) (y : A) :
    h (((T - algebraMap k (Module.End k A) x) ^ m) y) = ((T' - algebraMap k (Module.End k B) x) ^ m) (h y) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    congr 1
    simp [Module.algebraMap_end_apply, hT]

theorem gmult_transport (T : Module.End k A) (T' : Module.End k B) (h : A →ₗ[k] B)
    (hT : ∀ y, h (T y) = T' (h y)) (P Q : Submodule k A) (P' Q' : Submodule k B)
    (hP : ∀ y ∈ P, T y ∈ P) (hQP : Q ≤ P) (hQ' : ∀ y ∈ Q', T' y ∈ Q')
    (hmap : ∀ y ∈ P, h y ∈ P') (hker : ∀ y ∈ P, h y ∈ Q' ↔ y ∈ Q)
    (hsur : ∀ z ∈ P', ∃ y ∈ P, z - h y ∈ Q') (x : k) : gmult T P Q x = gmult T' P' Q' x := by
  have hQ : ∀ y ∈ Q, T y ∈ Q := fun y hy =>
    (hker _ (hP y (hQP hy))).1 (by rw [hT]; exact hQ' _ ((hker y (hQP hy)).2 hy))
  unfold gmult
  set G := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k A) x) ^ m) with hG
  set G' := P' ⊓ ⨆ m : ℕ, Q'.comap ((T' - algebraMap k (Module.End k B) x) ^ m) with hG'
  have hGG : ∀ y ∈ G, h y ∈ G' := by
    rintro y ⟨hy, hy2⟩
    obtain ⟨m, hm⟩ := (mem_gen T Q hQ x y).1 hy2
    refine ⟨hmap y hy, (mem_gen T' Q' hQ' x _).2 ⟨m, ?_⟩⟩
    rw [← pow_comm T T' h hT]
    exact (hker _ (hQP hm)).2 hm
  let φ : G →ₗ[k] (G' ⧸ Q'.submoduleOf G') := (Q'.submoduleOf G').mkQ ∘ₗ h.restrict hGG
  have hk : Q.submoduleOf G = LinearMap.ker φ := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    change y ∈ Q ↔ Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hker y hy.1).symm
  have hs : Function.Surjective φ := by
    intro w
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨y, hy, hzy⟩ := hsur z hz.1
    obtain ⟨m, hm⟩ := (mem_gen T' Q' hQ' x z).1 hz.2
    have hyG : y ∈ G := by
      refine ⟨hy, (mem_gen T Q hQ x y).2 ⟨m, (hker _ (pow_mem T P hP x m y hy)).1 ?_⟩⟩
      rw [pow_comm T T' h hT]
      have := Q'.sub_mem hm (pow_mem T' Q' hQ' x m _ hzy)
      rwa [map_sub, sub_sub_cancel] at this
    refine ⟨⟨y, hyG⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [eq_comm, Submodule.Quotient.eq]
    exact hzy
  rw [hk]
  exact (φ.quotKerEquivOfSurjective hs).finrank_eq

end

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

omit [Module k V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in

theorem sh_one_le (N : Submodule k⟦X⟧ V) : sh 1 N ≤ N := by
  have := sh_le_sh_of_le (zero_le_one' ℤ) N
  rwa [sh_zero_eq] at this

theorem nab_mem_sh_one {l : ℕ} (R : RingPG k l) (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V)
    (hN : CondC g N) : ∀ y ∈ sh 1 N, nab g y ∈ sh 1 N := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
  obtain ⟨κ, -, hκ⟩ := R.γ_v
  have hv := vv_ne_zero k
  have h1 := hN z hz
  have h2 : g z ∈ N := by simpa using N.add_mem (sh_one_le N h1) hz
  have h3 : vv k ^ (1 : ℤ) • (κ • g z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem κ h2, rfl⟩
  have h4 : nab g (vv k ^ (1 : ℤ) • z) = (g z - z) - vv k ^ (1 : ℤ) • (κ • g z) := by
    rw [nab_apply_eq, zpow_one, hg, hκ, ← algebraMap_smul k⸨X⸩ κ, mul_smul, ← smul_sub, inv_smul_smul₀ hv,
      sub_smul, one_smul, smul_smul, mul_comm (vv k)]
    change g z - ((κ : k⸨X⸩) * vv k) • g z - z = g z - z - ((κ : k⸨X⸩) * vv k) • g z
    abel
  rw [h4]
  exact Submodule.sub_mem _ h1 h3

omit [IsScalarTower k k⸨X⸩ V] in

theorem finite_quot (N : Submodule k⟦X⟧ V) (hN : N.FG) :
    FiniteDimensional k (↥(N.restrictScalars k) ⧸
      ((sh 1 N).restrictScalars k).submoduleOf (N.restrictScalars k)) := by
  obtain ⟨s, hs⟩ := hN
  have hle : Submodule.span k (s : Set V) ≤ N.restrictScalars k :=
    Submodule.span_le.2 fun y hy => hs ▸ Submodule.subset_span hy
  have key : ∀ y ∈ N, ∃ z ∈ Submodule.span k (s : Set V), y - z ∈ sh 1 N := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨z, hz, h⟩ := hy
      obtain ⟨z', hz', h'⟩ := hy'
      refine ⟨z + z', Submodule.add_mem _ hz hz', ?_⟩
      have := Submodule.add_mem _ h h'
      rwa [sub_add_sub_comm] at this
    | smul a y _ hy =>
      obtain ⟨z, hz, h⟩ := hy
      refine ⟨PowerSeries.constantCoeff a • z, Submodule.smul_mem _ _ hz, ?_⟩
      set t : k⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) a
      have ha : a = PowerSeries.X * t + algebraMap k k⟦X⟧ (PowerSeries.constantCoeff a) :=
        PowerSeries.eq_X_mul_shift_add_const a
      have h3 : vv k ^ (1 : ℤ) • (t • z) ∈ sh 1 N := mem_sh_iff_exists.2 ⟨_, N.smul_mem t (hle hz), rfl⟩
      have h4 : vv k ^ (1 : ℤ) • (t • z) = (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [zpow_one, mul_smul, vv_eq_coe_X]
        exact algebraMap_smul k⸨X⸩ (PowerSeries.X : k⟦X⟧) (t • z)
      have h5 : a • y - PowerSeries.constantCoeff a • z = a • (y - z) + (PowerSeries.X * t : k⟦X⟧) • z := by
        rw [← algebraMap_smul k⟦X⟧ (PowerSeries.constantCoeff a) z, eq_sub_of_add_eq ha.symm, smul_sub, sub_smul]
        abel
      rw [h5]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h) (h4 ▸ h3)
  haveI : FiniteDimensional k (Submodule.span k (s : Set V)) := FiniteDimensional.span_finset k s
  refine Module.Finite.of_surjective (Submodule.mkQ _ ∘ₗ Submodule.inclusion hle) fun w => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨z, hz, h⟩ := key y hy
  refine ⟨⟨z, hz⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [eq_comm, Submodule.Quotient.eq]
  exact h

end

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W] [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W] [FiniteDimensional k⸨X⸩ W] {U : Type} [AddCommGroup U] [Module k⸨X⸩ U] [Module k⟦X⟧ U] [Module k U] [IsScalarTower k⟦X⟧ k⸨X⸩ U] [IsScalarTower k k⸨X⸩ U] [IsScalarTower k k⟦X⟧ U] [FiniteDimensional k⸨X⸩ U] (gV : V →ₗ[k] V) (gW : W →ₗ[k] W) (gU : U →ₗ[k] U) (f : W →ₗ[k⸨X⸩] V) (p : V →ₗ[k⸨X⸩] U), Semi R.γ gV → Function.Injective f → Function.Surjective p → Function.Exact f p → (∀ x, f (gW x) = gV (f x)) → (∀ x, p (gV x) = gU (p x)) → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC gV N → ∀ x : k, sen gV N x = sen gW (N.comap (f.restrictScalars k⟦X⟧)) x + sen gU (N.map (p.restrictScalars k⟦X⟧)) x := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ U _ _ _ _ _ _ _ _ gV gW gU f p hg _ _ hex hf hp N hN hC x
  have hN1 := (condC_iff_nab_mem gV N).1 hC
  have hN2 := nab_mem_sh_one R gV hg N hC
  have nf : ∀ y, f (nab gW y) = nab gV (f y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hf]
  have np : ∀ y, p (nab gV y) = nab gU (p y) := fun y => by
    rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, hp]
  set N' := N.map (p.restrictScalars k⟦X⟧) with hN'
  have hsh : ∀ u, u ∈ sh 1 N' ↔ ∃ y ∈ sh 1 N, p y = u := by
    intro u
    constructor
    · intro hu
      obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hu
      exact ⟨_, mem_sh_iff_exists.2 ⟨z, hz, rfl⟩, map_smul p _ _⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := mem_sh_iff_exists.1 hy
      exact mem_sh_iff_exists.2 ⟨p z, ⟨z, hz, rfl⟩, (map_smul p _ _).symm⟩
  have hU : ∀ u ∈ sh 1 N', nab gU u ∈ sh 1 N' := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := (hsh u).1 hu
    exact (hsh _).2 ⟨_, hN2 y hy, np y⟩
  let Q : Submodule k V := N.restrictScalars k ⊓ ((sh 1 N').restrictScalars k).comap (p.restrictScalars k)
  have hQ : ∀ y, y ∈ Q ↔ y ∈ N ∧ p y ∈ sh 1 N' := fun _ => Iff.rfl
  have hadd := GlobalTheory.PhiGam.GmultAdd.main (nab gV) (N.restrictScalars k) Q ((sh 1 N).restrictScalars k)
    (fun y hy => (hQ y).2 ⟨sh_one_le N hy, (hsh _).2 ⟨y, hy, rfl⟩⟩) inf_le_left hN1
    (fun y hy => (hQ _).2 ⟨hN1 y hy.1, by rw [np]; exact hU _ hy.2⟩) hN2 (finite_quot N hN.1) x
  have e1 : gmult (nab gV) (N.restrictScalars k) Q x = sen gU N' x :=
    gmult_transport (nab gV) (nab gU) (p.restrictScalars k) np _ _ (N'.restrictScalars k)
      ((sh 1 N').restrictScalars k) hN1 inf_le_left hU
      (fun y hy => ⟨y, hy, rfl⟩) (fun y hy => ⟨fun h => ⟨hy, h⟩, fun h => h.2⟩)
      (by rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hy, by simp⟩) x
  have e2 : sen gW (N.comap (f.restrictScalars k⟦X⟧)) x = gmult (nab gV) Q ((sh 1 N).restrictScalars k) x := by
    refine gmult_transport (nab gW) (nab gV) (f.restrictScalars k) nf _ _ _ _ ?_ (sh_one_le _) hN2 ?_ ?_ ?_ x
    · intro y hy
      change f (nab gW y) ∈ N
      rw [nf]
      exact hN1 _ hy
    · intro y hy
      refine (hQ _).2 ⟨hy, ?_⟩
      change p (f y) ∈ _
      rw [hex.apply_apply_eq_zero]
      exact Submodule.zero_mem _
    · intro y _
      change f y ∈ sh 1 N ↔ y ∈ sh 1 _
      rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]
      rfl
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := (hsh _).1 hz.2
      obtain ⟨w, hw⟩ := (hex (z - y)).1 (by rw [map_sub, hyz]; exact sub_self _)
      refine ⟨w, ?_, ?_⟩
      · change f w ∈ N
        rw [hw]
        exact N.sub_mem hz.1 (sh_one_le N hy)
      · change z - f w ∈ sh 1 N
        rwa [hw, sub_sub_cancel]
  rw [e2, ← e1, add_comm]
  exact hadd

end GlobalTheory.PhiGam.SenAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermBasisOrthonormal
section
noncomputable section

namespace GlobalTheory.UnitLemma.OrthBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem herm_add_right (x y z₁ z₂ : B.A) : B.herm x y (z₁ + z₂) = B.herm x y z₁ + B.herm x y z₂ := by
  unfold InvAlg.herm
  rw [map_add, mul_add, map_add]

theorem herm_zero_right (x y : B.A) : B.herm x y 0 = 0 := by
  unfold InvAlg.herm
  simp

theorem herm_smul_right' (x y z : B.A) (a : K.E) : B.herm x y (a • z) = K.c a * B.herm x y z := by
  unfold InvAlg.herm
  rw [Algebra.smul_def, map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem herm_sum_smul_left {n : ℕ} (x z : B.A) (a : Fin n → K.E) (v : Fin n → B.A) :
    B.herm x (∑ j, a j • v j) z = ∑ j, a j * B.herm x (v j) z := by
  unfold InvAlg.herm
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]

theorem herm_mul_left_of_fixed (x g y z : B.A) (hg : B.σ g = g) :
    B.herm x (g * y) z = B.herm x y (g * z) := by
  unfold InvAlg.herm
  rw [map_mul B.σ, hg]; congr 1; ring

theorem repr_mul {n : ℕ} (e : Module.Basis (Fin n) K.E B.A) (g z : B.A) (i : Fin n) :
    e.repr (g * z) i = ∑ j, e.repr z j * e.repr (g * e j) i := by
  conv_lhs => rw [← e.sum_repr z]
  rw [Finset.mul_sum, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

end GlobalTheory.UnitLemma.OrthBasis

namespace GlobalTheory.UnitLemma

open GlobalTheory.UnitLemma.OrthBasis

theorem herm_basis_orthonormal : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), B.σ B.g = B.g → IsUnit w →
    Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l) = ⊤ → ∀ (n : ℕ) (e : Module.Basis (Fin n) K.E B.A),
    (∀ i j, K.c (e.repr (B.g * e j) i) = e.repr (B.g * e i) j) → (∀ j, B.herm x (e j) w = K.c (e.repr w j)) →
    ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0 := by
  intro K B x w hg hw hspan n e hM hwj

  let P : B.A → Prop := fun z => ∀ i, B.herm x (e i) z = K.c (e.repr z i)
  have hstep : ∀ z, P z → P (B.g * z) := by
    intro z hz i
    rw [← herm_mul_left_of_fixed B x B.g (e i) z hg]
    conv_lhs => rw [← e.sum_repr (B.g * e i)]
    rw [herm_sum_smul_left, repr_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j, RingEquiv.map_mul K.c, hM, mul_comm]
  have hpow : ∀ l : ℕ, P (B.g ^ l * w) := by
    intro l
    induction l with
    | zero => simpa [P] using hwj
    | succ l ih => rw [pow_succ', mul_assoc]; exact hstep _ ih
  have hspanP : ∀ a ∈ Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l), P (a * w) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨l, rfl⟩ := hy; exact hpow l
    | zero => intro i; simp [herm_zero_right]
    | add y z _ _ hy hz =>
      intro i; rw [add_mul, herm_add_right, hy i, hz i, map_add, Finsupp.add_apply, map_add]
    | smul a y _ hy =>
      intro i; rw [smul_mul_assoc, herm_smul_right', hy i, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul,
        RingEquiv.map_mul K.c]
  have hall : ∀ z, P z := by
    intro z
    obtain ⟨u, rfl⟩ := hw
    have := hspanP (z * ((u⁻¹ : B.Aˣ) : B.A)) (by rw [hspan]; exact Submodule.mem_top)
    rwa [mul_assoc, Units.inv_mul, mul_one] at this
  intro i j
  rw [hall (e j) i, e.repr_self, Finsupp.single_apply]
  split_ifs with h1 h2 h2
  · exact map_one _
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero _

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeIsOpenIsCompactTest
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LatTop

theorem isLocallyConstant_indicator_one' {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem lattice_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)),
    IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧
      IsTest (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} (1 : A.L → ℂ)) := by
  intro F E _ _ _ _ hU A r j
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  set B : Set E := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set V : Set (Fin r → E) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hS : {y : A.L | ∀ i, ‖j y i‖ ≤ 1} = jF ⁻¹' V := by
    ext y
    simp [hV, hB, jF]
  have hS' : jF ⁻¹' V = jF.symm '' V := (jF.toEquiv.image_symm_eq_preimage V).symm
  have hSo : IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVo.preimage hc
  have hSc : IsClosed {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVc.preimage hc
  have hSk : IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := by
    rw [hS, hS']; exact hVk.image hcs
  exact ⟨hSo, hSk, isLocallyConstant_indicator_one' ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LatTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralRightCosetFunEqFinsum
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory

theorem integral_rightCoset_fun_eq_finsum (G Λ : Type) [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (H : Set G)
    (hH : IsOpen H) (hμ : μ H = 1) (π : G → Λ) (hπ : ∀ g g', π g' = π g ↔ g' * g⁻¹ ∈ H)
    (s : Λ → ℂ) (hs : ∀ l, s l = 0 ∨ ‖s l‖ = 1) :
    ∫ g, s (π g) ∂μ = ∑ᶠ l ∈ Set.range π, s l := by
  classical

  have hfib : ∀ g, π ⁻¹' {π g} = (fun x => x * g⁻¹) ⁻¹' H := by
    intro g; ext x; simp [hπ g x]
  have hfibO : ∀ g, IsOpen (π ⁻¹' {π g}) := by
    intro g; rw [hfib g]; exact hH.preimage (continuous_mul_right _)
  have hfibM : ∀ l, MeasurableSet (π ⁻¹' {l}) := by
    intro l
    by_cases hl : l ∈ Set.range π
    · obtain ⟨g, rfl⟩ := hl; exact (hfibO g).measurableSet
    · have : π ⁻¹' {l} = ∅ := by
        ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h => hl ⟨x, h⟩
      rw [this]; exact MeasurableSet.empty
  have hfib1 : ∀ g, μ (π ⁻¹' {π g}) = 1 := by
    intro g; rw [hfib g, measure_preimage_mul_right, hμ]
  set S := Set.range π ∩ Function.support s with hSdef
  by_cases hS : S.Finite
  · set T := hS.toFinset with hT
    have hfun : (fun g => s (π g)) = fun g => ∑ l ∈ T, (π ⁻¹' {l}).indicator (fun _ => s l) g := by
      funext g
      have : ∀ l, (π ⁻¹' {l}).indicator (fun _ => s l) g = if π g = l then s (π g) else 0 := by
        intro l
        by_cases h : π g = l
        · subst h; simp
        · simp [Set.indicator_apply, h]
      simp only [this, Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · have : π g ∉ S := by rw [hT, Set.Finite.mem_toFinset] at *; exact h
        by_contra hne
        exact this ⟨⟨g, rfl⟩, Ne.symm hne |>.symm⟩
    rw [hfun, integral_finset_sum]
    · rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hS]
      refine Finset.sum_congr rfl ?_
      intro l hl
      rw [integral_indicator_const _ (hfibM l)]
      have hl' : l ∈ Set.range π := ((Set.Finite.mem_toFinset hS).1 hl).1
      obtain ⟨g, rfl⟩ := hl'
      simp [Measure.real, hfib1 g]
    · intro l _
      exact (integrable_indicator_iff (hfibM l)).2 (by
        by_cases hl : l ∈ Set.range π
        · obtain ⟨g, rfl⟩ := hl
          haveI : IsFiniteMeasure (μ.restrict (π ⁻¹' {π g})) := ⟨by simp [hfib1 g]⟩
          exact integrable_const _
        · have : π ⁻¹' {l} = ∅ := by
            ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
            exact fun h => hl ⟨x, h⟩
          rw [this]; exact integrableOn_empty)
  · rw [finsum_mem_eq_zero_of_infinite hS]
    apply integral_undef
    intro hint
    have hfin := hint.2

    have hbound : ∀ F : Finset Λ, (↑F : Set Λ) ⊆ S → (F.card : ENNReal) ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
      intro F hF
      calc (F.card : ENNReal) = ∑ l ∈ F, μ (π ⁻¹' {l}) := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum]
            refine Finset.sum_congr rfl ?_
            intro l hl
            obtain ⟨⟨g, rfl⟩, _⟩ := hF hl
            simp [hfib1 g]
        _ = ∫⁻ g, ∑ l ∈ F, (π ⁻¹' {l}).indicator 1 g ∂μ := by
            rw [lintegral_finset_sum]
            · refine Finset.sum_congr rfl ?_
              intro l _
              rw [lintegral_indicator_one (hfibM l)]
            · intro l _
              exact (measurable_one.indicator (hfibM l))
        _ ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
            apply lintegral_mono
            intro g
            have : ∀ l, (π ⁻¹' {l}).indicator (1 : G → ENNReal) g = if π g = l then 1 else 0 := by
              intro l; simp [Set.indicator_apply]
            simp only [this, Finset.sum_ite_eq]
            split_ifs with h
            · obtain ⟨_, hsupp⟩ := hF h
              rcases hs (π g) with h0 | h1
              · exact absurd h0 hsupp
              · rw [← ofReal_norm_eq_enorm, h1]; simp
            · exact bot_le
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin.ne
    obtain ⟨F, hFS, hFc⟩ := Set.Infinite.exists_subset_card_eq (hS : S.Infinite) n
    have := hbound F hFS
    rw [hFc] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants : ∀ (k : Type) [Field k] (r : ℕ), (∀ (g : GL (Fin r) k) (Y : Gl r k), inv (act g Y) = inv Y) ∧ (∀ a : Inv r k, inv (sec a) = a) ∧ (∀ Y : Gl r k, Cm Y * Bm Y = hankel (inv Y)) ∧ (∀ (g h : GL (Fin r) k) (Y : Gl r k), act (g * h) Y = act g (act h Y)) ∧ ∀ Y Y₁ : Gl r k, Delta (inv Y) ≠ 0 → inv Y₁ = inv Y → ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  first | exact @GlobalTheory.JR.normalForm_invariants | exact GlobalTheory.JR.normalForm_invariants | (intros; apply GlobalTheory.JR.normalForm_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitInvariantMapProperStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) ∧ Continuous (fun Y : Gl r F => inv Y) ∧ Continuous (fun a : Inv r F => Delta a) ∧ ∀ (C : Set (Gl r F)) (Ω : Set (Inv r F)), IsCompact C → IsCompact Ω → (∀ a ∈ Ω, Delta a ≠ 0) → IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  first | exact @GlobalTheory.JR.OrbitProper.main | exact GlobalTheory.JR.OrbitProper.main | (intros; apply GlobalTheory.JR.OrbitProper.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDetStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det : ∀ (k : Type) [CommRing k] (r : ℕ), (∀ Y : Gl r k, lastDet Y = (-1) ^ r * (Cm Y).det) ∧ ∀ (g : GL (Fin r) k) (Y : Gl r k), Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  first | exact @GlobalTheory.JR.transfer_factor_lemma | exact GlobalTheory.JR.transfer_factor_lemma | (intros; apply GlobalTheory.JR.transfer_factor_lemma <;> assumption)
end

