import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct

namespace GlobalTheory.PMon

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def FilA (a : ℤ) : AddSubgroup P.R.BdR := ((P.PD (botExt l)).Fil a).toAddSubgroup

theorem mem_Fil_iff (K : FinExt l) {a : ℤ} {x : P.R.BdR} : x ∈ Fil P a ↔ x ∈ (P.PD K).Fil a := by
  have := P.PD_Fil (botExt l) K a
  change x ∈ ((P.PD (botExt l)).Fil a : Set P.R.BdR) ↔ x ∈ ((P.PD K).Fil a : Set P.R.BdR)
  rw [this]

variable {P}

theorem Fil_zero_mem (a : ℤ) : (0 : P.R.BdR) ∈ Fil P a := (FilA P a).zero_mem
theorem Fil_add {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P a) : x + y ∈ Fil P a := (FilA P a).add_mem hx hy
theorem Fil_neg {a : ℤ} {x : P.R.BdR} (hx : x ∈ Fil P a) : -x ∈ Fil P a := (FilA P a).neg_mem hx
theorem Fil_sum {a : ℤ} {ι : Type*} {s : Finset ι} {f : ι → P.R.BdR} (h : ∀ i ∈ s, f i ∈ Fil P a) :
    ∑ i ∈ s, f i ∈ Fil P a := (FilA P a).sum_mem h
theorem Fil_mul {a b : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy
theorem Fil_mul_left {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P 0) (hy : y ∈ Fil P a) : x * y ∈ Fil P a := by
  simpa using Fil_mul hx hy
theorem Fil_mul_right {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P 0) : x * y ∈ Fil P a := by
  simpa using Fil_mul hx hy
theorem one_mem_Fil : (1 : P.R.BdR) ∈ Fil P 0 := (P.PD (botExt l)).one_mem
theorem Fil_act (g : GQ l) {a : ℤ} {x : P.R.BdR} (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at this

variable (P)

def S0 : Subring P.R.BdR where
  carrier := Fil P 0
  zero_mem' := Fil_zero_mem 0
  one_mem' := one_mem_Fil
  add_mem' := Fil_add
  neg_mem' := Fil_neg
  mul_mem' := Fil_mul_left

theorem mem_S0_of_sum_eq {x : P.R.BdR} : x ∈ S0 P ↔ x ∈ Fil P 0 := Iff.rfl

theorem om_mem_Fil (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  rw [mem_Fil_iff P (adjExt x)]
  have h := ((P.PD (adjExt x)).Fil 0).smul_mem ⟨x, mem_adjExt x⟩ (P.PD (adjExt x)).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact h

theorem kd_mem_Fil (c : ↥(MaximalUnramifiedExtension l)) : kd P c ∈ Fil P 0 := om_mem_Fil P _

theorem q_mem_Fil (q : ℚ_[l]) : algebraMap ℚ_[l] P.R.BdR q ∈ Fil P 0 := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
  exact om_mem_Fil P _

theorem iota_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem iota_act (g : GQ l) (b : P.R.B) : P.ιB (P.actQ g b) = P.actQdR g (P.ιB b) := by
  have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rwa [P.PD_actB, P.PD_ι, P.PD_ι, P.PD_actdR] at this

theorem iota_kur (c : ↥(MaximalUnramifiedExtension l)) : P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = kd P c := by
  have := (P.PD (adjExt (c : Om l))).ι.commutes ⟨c, mem_adjExt _, c.2⟩
  rw [P.PD_ι] at this
  exact this

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := rfl
theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  simp [fr, pow_add, AlgHom.mul_apply]
theorem fr_one (c : ↥(MaximalUnramifiedExtension l)) : fr l 1 c = frobUr l c := by simp [fr]
theorem fr_q (m : ℕ) (q : ℚ_[l]) : fr l m (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q :=
  (frobUr l ^ m).commutes q
theorem fr_comm {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (m : ℕ) : fr l r (fr l m c) = fr l m c := by
  rw [← fr_add, add_comm, fr_add, h]
theorem fr_mul {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (k : ℕ) : fr l (r * k) c = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, fr_add, h, ih]
theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (h : fr l r c = c) (m : ℕ) : fr l (m % r) c = fr l m c := by
  conv_rhs => rw [← Nat.mod_add_div m r, fr_add, fr_mul h]

theorem phi_iter_kur (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m c) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, phiB_algebraMap, add_comm, fr_add, fr_one]

def evHom (m : ℕ) : P.R.B →+* P.R.BdR :=
  (P.ιB : P.R.B →+* P.R.BdR).comp ((P.φB ^ m : P.R.B →ₐ[ℚ_[l]] P.R.B) : P.R.B →+* P.R.B)

theorem evHom_apply (m : ℕ) (b : P.R.B) : evHom P m b = ev P m b := by
  simp [evHom, ev, AlgHom.coe_pow]

theorem ev_kur (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = kd P (fr l m c) := by
  rw [ev, phi_iter_kur, iota_kur]

theorem ev_act (m : ℕ) (g : GQ l) (b : P.R.B) : ev P m (P.actQ g b) = P.actQdR g (ev P m b) := by
  rw [ev, ev, ← iota_act]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]

theorem act_kd {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    P.actQdR (g : GQ l) (kd P c) = kd P c := by
  change P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR (c : Om l)) = algebraMap (Om l) P.R.BdR (c : Om l)
  rw [P.actQdR_Om, mem_GK.1 g.2 _ hc]

theorem act_kur {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c :=
  P.actQ_Kur _ c c (mem_GK.1 g.2 _ hc)

theorem act_ks {K : FinExt l} (g : ↥(GK K)) {c : ↥(MaximalUnramifiedExtension l)} (hc : (c : Om l) ∈ K.1) :
    actSt P (g : GQ l) (ks P c) = ks P c := by
  change actSt P (g : GQ l) (Polynomial.C _) = Polynomial.C _
  rw [actSt_C, act_kur P g hc]

theorem tz_add (a b : ℤ) : tz P (a + b) = tz P a * tz P b := by simp [tz, zpow_add]
theorem tz_zero : tz P 0 = 1 := by simp [tz]
theorem tz_one : tz P 1 = P.ιB P.tB := by simp [tz]

theorem fund {b : P.R.B} (h : P.φB b = b) (h0 : P.ιB b ∈ Fil P 0) : ∃ c : ℚ_[l], algebraMap ℚ_[l] P.R.B c = b :=
  (P.PD (botExt l)).fund b (by rw [P.PD_φ, h]) (by rw [P.PD_ι]; exact h0)

def resK {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) :
    ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l) := ρ.comp (Subgroup.inclusion (GK_le hK))

theorem IsRat.resK {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1) {r : ℕ}
    {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : IsRat r ρ) : IsRat r (resK hK ρ) where
  pos := h.pos
  le := fun c hc => hK (h.le c hc)
  rat := fun g => h.rat _
  cont := fun i j => (h.cont i j).comp (continuous_induced_rng.2 continuous_subtype_val)

theorem AdmDR.resK {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : AdmDR P ρ) : AdmDR P (resK hK ρ) := fun m =>
  (h m).imp fun _ hQ g => hQ ⟨g, GK_le hK g.2⟩

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.ResSel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

variable (X) in

def IsCj (g g' : GE N) : Prop := ∀ x, g' x = X.cc (g (X.cc.symm x))

def IsDual (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) : Prop :=
  ∀ g, (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = Tdual i s g

def ResTriv (g : GE N) : Prop :=
  (Tmat i s g).map (IsLocalRing.residue (X.O0 i)) = 1 ∧ IsLocalRing.residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1

def Small (L : Subgroup (GE N)) (z : GE N) : Prop :=
  IsOpen (L : Set (GE N)) ∧ L.Normal ∧ (∀ g g', IsCj X g g' → (g ∈ L ↔ g' ∈ L)) ∧ (∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ g ∈ L, ResTriv i s g

section Field

variable (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]

def IsRes : Prop := ∀ x ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) K x = 0

def ResIso : Prop :=
  ∃ A : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A ∧
    ∀ g g', IsCj X g g' → (Tdual i s g').map (algebraMap (X.O0 i) K) * A = A * (Tmat i s g).map (algebraMap (X.O0 i) K)

abbrev red (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) : Representation K (GE N) (Fin D.R.r → K) := repOn ρ (1 : GE N →* Kˣ) K

variable {i K}

abbrev cl {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) : H1 (red i K ρ) := Submodule.Quotient.mk x

def form {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) (y : Z1 (red i K ρ')) (g h g' h' : GE N) : K :=
  x.1 g ⬝ᵥ y.1 h - x.1 g' ⬝ᵥ y.1 h'

end Field

def SpanOdd : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ¬ ResIso i s K →
    ∀ ρ, IsDual i s ρ → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z →
    ∀ (n n' : ℕ) (x : Fin n → Z1 (red i K (Tgl i s))) (y : Fin n' → Z1 (red i K ρ)),
      LinearIndependent K (fun a => cl (x a)) → LinearIndependent K (fun b => cl (y b)) → ∀ c : Fin n → Fin n' → K,
      (∀ h ∈ L, ∀ h', IsCj X h h' → ∑ a, ∑ b, c a b * form (x a) (y b) h h h' h' = 0) → c = 0

def SpanTwo : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K →
    ∀ ρ, IsDual i s ρ → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z →
    ∀ A : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A →
      (∀ g g', IsCj X g g' → (Tdual i s g').map (algebraMap (X.O0 i) K) * A = A * (Tmat i s g).map (algebraMap (X.O0 i) K)) →
    ∀ (n : ℕ) (x : Fin n → Z1 (red i K (Tgl i s))) (y : Fin n → Z1 (red i K ρ)),
      LinearIndependent K (fun a => cl (x a)) → (∀ a g g', IsCj X g g' → (y a).1 g' = A.mulVec ((x a).1 g)) →
      ∀ c : Fin n → Fin n → K,
      (∀ h ∈ L, ∀ h', IsCj X h h' → ∑ a, ∑ b, c a b * form (x a) (y b) h h h' h' = 0) → ∀ a b, c a b = c b a

def EqDim : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ →
    Module.Finite K (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) ∧ Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅) ∧
      Module.finrank K (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) = Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅)

def Position (M : ℕ) {R : ℕ} (P : Fin R ⊕ Fin R → PlE D.host)
    (d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (φ φ' : Fin R → GE N) : Prop :=
  SlopeTestRemainingChoices X i M ∅ P d ∧ (∃ z L, IsTameInertiaElementAtTwistPrime X i z ∧ Small i s L z ∧ Steps X i M L z P d) ∧
    ∀ a, (∀ g ∈ DecV N (P (.inr a)), ResTriv i s g) ∧ IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧
      IsCj X (φ a) (φ' a)

def FirstHalf : Prop :=
  ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ', 1 ≤ M → Position i s M P d φ φ' →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ),
    IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) →
    ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ ρ, (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ a v, Over (P (.inl a)) v →
      H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧
        Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype))

def FirstPlace : Prop :=
  ∀ (P : PlE D.host) (z : GE N) (L : Subgroup (GE N)), IsTameInertiaElementAtTwistPrime X i z → Small i s L z →
    (∀ v, Over P v → v ∉ X.S0 i ∧ normV v % X.l i = 1) →
    (∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ),
    IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) →
    ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ ρ, (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ v, Over P v →
      H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧
        Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype))

theorem mod_l_eq_one {M n : ℕ} (hM : 1 ≤ M) (hn : n % (2 * X.l i ^ M) = 1) : n % X.l i = 1 := by
  have hd : X.l i ∣ 2 * X.l i ^ M := Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  rw [← Nat.mod_mod_of_dvd _ hd, hn, Nat.mod_eq_of_lt (Fact.out : (X.l i).Prime).one_lt]

theorem FirstPlace.firstHalf (h : FirstPlace i s) : FirstHalf i s := by
  intro M R P d φ φ' hM hP Λ _ _ _ _ κ hκ hκ' B _ _ _ _ hB ρ hρ a v hv
  obtain ⟨hA, ⟨z, L, hz, hL, hS⟩, -⟩ := hP
  refine h (P (.inl a)) z L hz hL (fun w hw => ?_) (hS.1 a) Λ κ hκ hκ' B hB ρ hρ v hv
  obtain ⟨-, -, -, h0, -, hn⟩ := hA.1 _ w hw
  exact ⟨h0, mod_l_eq_one i hM hn⟩

def Recip : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ →
    ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q →
    ∀ γ γ' : Fin R → GE N, (∀ a, γ a ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))) ∧
      d (.inr a) (γ a) = Multiplicative.ofAdd 1 ∧ IsCj X (γ a) (γ' a)) →
    ∃ c : Fin R → Kˣ, ∀ (x : Z1 (red i K (Tgl i s))) (y : Z1 (red i K ρ)),
      cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → cl y ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K ∅ →
      ∑ a, (c a : K) * form x y (γ a) (φ a) (γ' a) (φ' a) = 0

variable (X) in

def StepAB : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z →
    ∀ U : Subgroup (GE N), IsOpen (U : Set (GE N)) → U.Normal → ∀ (A : Finset (PlE D.host)) (R : ℕ) (h : Fin R → GE N),
    (∀ a, h a ∈ H ∧ ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → h a ζ = ζ) →
    ∃ P : Fin R ⊕ Fin R → PlE D.host, SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M U z P (fun q => d (P q)) ∧
      (∀ q v, Over (P q) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧
      ∀ a, ∃ σ g : GE N, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ ∧ g * σ * g⁻¹ * (h a)⁻¹ ∈ U

def Corank {R : ℕ} (φ φ' : Fin R → GE N) (e : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K →
    Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∃ c : Fin R → K,
    ∀ x : Fin (e + 1) → Z1 (red i K (Tgl i s)), (∀ a, cl (x a) ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) →
      (∀ a (y : Z1 (red i K ρ)), cl y ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K ∅ →
        ∑ b, c b * form (x a) y (φ b) (φ b) (φ' b) (φ' b) = 0) → ¬ LinearIndependent K (fun a => cl (x a))

def ResBound : Prop :=
  ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 4 * D.R.r * R + 2 < X.l i ^ M →
    Position i s M P d φ φ' → IsQ P Q →
    ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))), Computes bkP i s M d Q Φ →
      (Corank bkP i s φ φ' 0 → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ 4 * D.R.r * R ∧ IsUnit (F.coeff m)) ∧
      (Corank bkP i s φ φ' 1 → a = 0 ∨ ∃ b c, ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.adjugate b c →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ 4 * D.R.r * R ∧ IsUnit (F.coeff m))

def ChooseH : Prop :=
  ∀ T : Set (X.Sig i), (∀ s ∈ T, GalHyp bkP i s) → ∃ R : ℕ, ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L : Subgroup (GE N), IsOpen (L : Set (GE N)) → L.Normal → (∀ s ∈ T, Small i s L z) →
    ∃ (h : Fin R → GE N) (U : Subgroup (GE N)), (∀ a, h a ∈ L) ∧ IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧
      ∀ φ φ' : Fin R → GE N, (∀ a, IsCj X (φ a) (φ' a) ∧ ∃ g, g * φ a * g⁻¹ * (h a)⁻¹ ∈ U) →
        ∀ s ∈ T, Corank bkP i s φ φ' (if nu X i = 0 then 0 else 1)

theorem IsCj.unique {g g' g'' : GE N} (h : IsCj X g g') (h' : IsCj X g g'') : g' = g'' :=
  AlgEquiv.ext fun x => (h x).trans (h' x).symm

theorem isCj_one : IsCj X (1 : GE N) 1 := fun x => by simp

theorem IsCj.mul {g g' h h' : GE N} (hg : IsCj X g g') (hh : IsCj X h h') : IsCj X (g * h) (g' * h') := fun x => by
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh x, hg]
  simp

theorem IsDual.unique {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (h : IsDual i s ρ) (h' : IsDual i s ρ') : ρ = ρ' :=
  MonoidHom.ext fun g => Units.ext ((h g).trans (h' g).symm)

example : IsRes i (IsLocalRing.ResidueField (X.O0 i)) := fun x hx =>
  (IsLocalRing.residue_eq_zero_iff x).2 hx

theorem form_swap {K : Type} [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
    {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) (y : Z1 (red i K ρ')) (g h g' h' : GE N) :
    form x y g' h' g h = -form x y g h g' h' := by
  simp [form]

def dualRep : GE N →* GL (Fin D.R.r) (X.O0 i) :=
  MonoidHom.toHomUnits
    { toFun := Tdual i s
      map_one' := by
        rw [Tdual, ← Tgl_coe, map_one, map_one]
        simp
      map_mul' := fun g h => by
        simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul]
        rw [smul_mul_smul_comm] }

theorem isDual_dualRep : IsDual i s (dualRep i s) := fun _ => rfl

end GlobalTheory.ResSel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

def MatThm : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ

def FrameEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (AdmDR P ρ ↔ ∃ w : Fin r → n → ℤ, Framed P ρ w)

def TwistStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ), IsRat r ρ → Framed P ρ w →
    ∃ (K' : FinExt l) (r' : ℕ) (ρ' : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (w' : Fin r' → n → ℤ),
      IsRat r' ρ' ∧ Framed P ρ' w' ∧ ∑ m, ∑ j, w' m j = 0 ∧ (AdmSt P ρ' → AdmSt P ρ)

def SenFinite : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]),
    (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) →
    ∀ M : GL n ℂ_[l], (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) *
      (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) →
    (ρ '' (IK K : Set ↥(GK K))).Finite

def UnrStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (ρ '' (IK K : Set ↥(GK K))).Finite → AdmSt P ρ

def SenStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → Framed P ρ (0 : Fin r → n → ℤ) → AdmSt P ρ

def Hyodo : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v : V, Continuous fun g => ρ g v) → IsSst P ρ →
    ∀ c : ↥(GK K) → V, Continuous c → (∀ g h, c (g * h) = c g + ρ g (c h)) →
    (∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) →
    ∃ b : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g b - b

def ExtStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) →
    AdmDR P ρ → AdmSt P ρ₁ → AdmSt P ρ₂ → AdmSt P ρ

def SubQuot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI)
    (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) →
    AdmDR P ρ → AdmDR P ρ₁ ∧ AdmDR P ρ₂

def RedStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → Splits r ρ →
    (∀ (a : Type) [Fintype a] [DecidableEq a], Fintype.card a < Fintype.card n →
      ∀ ρ' : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l), IsRat r ρ' → AdmDR P ρ' → AdmSt P ρ') → AdmSt P ρ

def ModStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (x y : Fin r × n), x ≠ y →
    IsRat r ρ → Framed P ρ w → ¬ Splits r ρ →
    ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + eps x y (m, j)) ∧
      (AdmSt P ρ' → AdmSt P ρ)

def FLAt (r : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n]
    (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), x ≠ y → (∀ m, UnitM P (U m)) →
    (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) →
      ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) →
    ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧
      ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) =
        (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR)

def Ratio : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h s : ℕ), s < h →
    ∀ ω ω' : P.R.B, Plus T ω → Plus T ω' → P.φB^[h] ω = (l : P.R.B) ^ s * ω → P.φB^[h] ω' = (l : P.R.B) ^ s * ω' →
    ω' ≠ 0 → P.φB ω * ω' = ω * P.φB ω' → ∃ c : ℚ_[l], ω = c • ω'

def Moore : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h k : ℕ), k ≤ h →
    ∀ a : Fin k → P.R.B, (∀ j, Plus T (a j)) → (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) →
    LinearIndependent ℚ_[l] a → (Matrix.of fun i j : Fin k => P.φB^[i] (a j)).det ≠ 0

def ExI : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h →
    ∀ μ : Fin h → P.R.BdR, (∀ i, μ i ∈ Fil P 0) → (∃ i, μ i ∉ Fil P 1) →
    ∃ b : Fin h → P.R.B, (∀ j, Plus T (b j)) ∧ (∀ j, P.φB^[h] (b j) = (l : P.R.B) * b j) ∧
      LinearIndependent ℚ_[l] b ∧ ∀ j, ∑ i, μ i * ev P i (b j) ∈ Fil P 1

def ExII : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 2 ≤ h →
    ∀ lam : Fin h → P.R.BdR, (∀ j, lam j ∈ Fil P 0) →
    (∀ c : Fin h → ℚ_[l], ∑ j, c j • lam j ∈ Fil P 1 → c = 0) →
    ∃ a : Fin h → P.R.B, a ≠ 0 ∧ (∀ j, Plus T (a j)) ∧ (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) ∧
      ∀ i : Fin h, ∑ j, lam j * ev P i (a j) ∈ Fil P 1

def WeilRes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n]
    (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, fr l r ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) ∧
      ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))

end GlobalTheory.PMon

end
end

