import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

structure WSeed (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) where

  N : ℕ

  c₁ : ℕ

  c₂ : ℕ

  c₃ : ℕ

  F : Matrix (Fin d) (Fin d) (Wq l bk.a)

  F' : Matrix (Fin d) (Fin d) (Wq l bk.a)
  F_mul : F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))

  X : Matrix (Fin d) (Fin d) bk.S

  X' : Matrix (Fin d) (Fin d) bk.S
  X_mul : X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) bk.S)

  W : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)

  W' : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)
  W_mul : W * W' = bk.iA τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
  φ : ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ →
    ((l : bk.DA bk.ρ₀) ^ c₁) • (W * X'.map bk.iS).map Φ =
      bk.iS (frobS l bk.a bk.E) ^ N • (W * X'.map bk.iS * F.map (bk.iS.comp C))

  κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)
  gal : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G →
    bk.iA (bk.ev bk.E * τ) ^ N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (W * X'.map bk.iS).map G) =
      bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) ^ N • (W * X'.map bk.iS * κ g)
  fix : ∀ g : ↥(GK K), bk.FixFlat g → κ g = 1
  nopole : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → ∀ i j,
    bk.iS bk.E ^ (2 * N) ∣ (X'.map bk.iS * κ g * (X.map bk.iS).map G) i j
  log : ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) ∧
    ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → ∀ i j,
      bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) i j

structure Pre (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) where

  T : Matrix (Fin d) (Fin d) (WCb l)
  unit : IsUnit T

  A : Matrix (Fin d) (Fin d) bk.S

  A' : Matrix (Fin d) (Fin d) bk.S
  A_mul : A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S)
  φ : bk.evW bk.E ^ N • T.map (frobW l) = T * A.map bk.evW
  fix : ∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T

structure Frame (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) extends Pre bk N d ρ where

  ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)
  gal : ∀ g : ↥(GK K), zW (ρ g) * T.map (galW l (g : GQ l)) = T * (ε g).map (inclW l)

variable {bk : BK K} {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}

def Frame.IsBeta (F : Frame bk N d ρ) (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) : Prop :=
  (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) ∧ ∀ (g : ↥(GK K)) i j,
    bk.ev bk.E ^ m ∣ ((F.ε g).map WittVector.frobenius * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) i j

def Frame.IsDR (F : Frame bk N d ρ) : Prop := ∀ m : ℕ, ∃ k β, F.IsBeta m k β

def Frame.IsCr (F : Frame bk N d ρ) : Prop :=
  ∀ (g : ↥(GK K)) i j, bk.ev X ∣ (F.ε g - (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j

def Link (bk : BK K) {d' : ℕ} (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l))
    (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (n r : ℕ) : Prop :=
  ∃ (R : Matrix (Fin d) (Fin d') bk.S) (G : Matrix (Fin d') (Fin d) bk.S),
    (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * T' - T * R.map bk.evW) i j) ∧
    ∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j

structure Onto {Γ : Type} {d d' : ℕ} (ρ : Γ → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : Γ → Matrix (Fin d') (Fin d') ℤ_[l])
    (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) : Prop where
  equi : ∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j
  surj : ∃ S : Matrix (Fin d') (Fin d) ℤ_[l], ∀ i j, (l : ℤ_[l]) ^ n ∣ (Pi * S - (1 : Matrix (Fin d) (Fin d) ℤ_[l])) i j

structure Tower {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) where

  d' : ℕ → ℕ

  ρ' : ∀ n, Γ →* GL (Fin (d' n)) ℤ_[l]

  Pi : ∀ n, Matrix (Fin d) (Fin (d' n)) ℤ_[l]
  onto : ∀ n, Onto (fun g => (ρ g).val) (fun g => (ρ' n g).val) (Pi n) n

  f : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l]
  f_equi : ∀ n g, f n * (ρ' (n + 1) g).val = (ρ' n g).val * f n
  f_Pi : ∀ n i j, (l : ℤ_[l]) ^ n ∣ (Pi n * f n - Pi (n + 1)) i j

def zOm (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* Om l := (algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])

def qRep {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) : Representation ℚ_[l] Γ (Fin d → ℚ_[l]) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
    (((algebraMap ℤ_[l] ℚ_[l]).mapMatrix : Matrix (Fin d) (Fin d) ℤ_[l] →+* _).toMonoidHom.comp ((Units.coeHom _).comp ρ))

structure Reads {Γ : Type} [Group Γ] {a d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (r : Γ →* GL (Fin a) (Om l))
    (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]) : Prop where
  equi : ∀ g j, (r g).val * b j = ∑ i, zOm l ((ρ g).val i j) • b i
  one : ∑ i, zOm l (e i) • b i = 1

structure Layer {Γ : Type} [Group Γ] {a d' : ℕ} (L₀ : FinExt l) (Cl : Set (Γ →* GL (Fin a) (Om l))) (ρ' : Γ →* GL (Fin d') ℤ_[l]) where

  m : ℕ

  rep : Fin m → (Γ →* GL (Fin a) (Om l))
  mem : ∀ k, rep k ∈ Cl

  L : Fin m → FinExt l
  le : ∀ k, L₀.1 ≤ (L k).1
  rep_mem : ∀ k g i j, (rep k g).val i j ∈ (L k).1

  b : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)
  b_mem : ∀ s k i j, b s k i j ∈ (L k).1
  indep : LinearIndependent ℚ_[l] b
  span : ∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (Set.range b)

  e : Fin d' → ℤ_[l]
  reads : ∀ k, Reads ρ' (rep k) (fun s => b s k) e

  c : Fin m → Om l

structure Cover {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ} (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l))
    (Cl : Set (Γ →* GL (Fin a) (Om l))) where

  d : ℕ

  ρ : Γ →* GL (Fin d) ℤ_[l]
  cont : Continuous ρ

  b : Fin d → Matrix (Fin a) (Fin a) (Om l)

  e : Fin d → ℤ_[l]
  reads : Reads ρ r b e

  tw : Tower ρ
  cont' : ∀ n, Continuous (tw.ρ' n)

  lay : ∀ n, Layer L₀ Cl (tw.ρ' n)
  unit : ∀ n i, (l : ℤ_[l]) ^ n ∣ (tw.Pi n *ᵥ (lay n).e - e) i
  trace : ∀ n s, ‖(∑ i, zOm l (tw.Pi n i s) • b i).trace - ∑ k, (lay n).c k * ((lay n).b s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹

def IsHT (C : Core l) (ξ : Ainf l) {a : ℕ} (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (z : ℂ_[l])
    (u : Matrix (Fin a) (Fin a) ℂ_[l]) : Prop :=
  ∀ (K' : FinExt l) (p q : ℕ) (x : Fin a → Per.BdR l) (y : Fin a → Per.BdRp l),
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
      (ρ g).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) *ᵥ (fun i => Per.σD (g : GQ l) (x i)) = x) →
    (∀ i, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * x i = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p * y i)) →
    u *ᵥ (fun i => Per.θD l (y i)) = z ^ ((p : ℤ) - q) • fun i => Per.θD l (y i)

structure Hodge (C : Core l) (ξ : Ainf l) {a : ℕ} (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (K' : FinExt l) where

  V : Matrix (Fin a) (Fin a) (Per.BdRp l)
  unit : IsUnit V

  p : Fin a → ℕ

  q : ℕ

  Q : Matrix (Fin a) (Fin a) (Per.BdR l)
  Q_eq : ∀ i j, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * Q i j =
    algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p j * V i j)
  inv : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
    (ρ g).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) * Q.map (Per.σD (g : GQ l)) = Q

def IsZ (bk : BK K) (g : ↥(GK K)) (z : ℂ_[l]) : Prop :=
  ∃ w : Ainf l, Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w ∧ z * Per.θD l (aDp l w) = 1

def Frame.triv (bk : BK K) (d : ℕ) : Frame bk 0 d (fun _ => 1) where
  T := 1
  unit := isUnit_one
  A := 1
  A' := 1
  A_mul := by simp
  φ := by simp [Matrix.map_one]
  fix g _ := by simp [zW, Matrix.map_one]
  ε _ := 1
  gal g := by simp [zW, Matrix.map_one]

theorem Frame.triv_isCr (bk : BK K) (d : ℕ) : (Frame.triv bk d).IsCr := fun _ i j => by simp [Frame.triv]

end GlobalTheory.BKLim

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TypePreservedOfAdmissibleIntegral
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll.Model

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X}

theorem zpow_apply' (i : X.Tw) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : X.RCG i Q →* (X.Ok i k)ˣ) (a : ℤ)
    (g : X.RCG i Q) : (ψ ^ a) g = (ψ g) ^ a := rfl

theorem not_coprime_mul (i : X.Tw) (n : ℤ) : ¬ IsCoprime (n * (X.l i : ℤ)) (X.l i : ℤ) := by
  intro h
  have h1 : IsUnit (X.l i : ℤ) := isCoprime_self.1 h.of_mul_left_right
  have h2 := (X.lPrime i).out.one_lt
  rw [Int.isUnit_iff] at h1
  omega

theorem admissibleBounds_of_all {N0 : X.Tw → ℕ} (h : admissibleIndexBoundAllPowers Y bkP N0) : TwistingCharacterExistence Y bkP N0 := by
  intro i hi hs e he F hF A0
  obtain ⟨Q, k', ψ', h1⟩ := h i hi hs e he F hF A0
  exact ⟨Q, k', ψ', by simpa using h1 1 isCoprime_one_left⟩

theorem provedGalois_of_all {E : ExpDat Y} {N0 : X.Tw → ℕ} {i : X.Tw} (h : goodTwistExistsAllCoprimePowers Y bkP E N0 i) : TwistTheoremAtIndex Y bkP E N0 i := by
  intro hs e he hF S hS A
  obtain ⟨Q, k', ψ', h1⟩ := h hs e he hF S hS A
  exact ⟨Q, k', ψ', by simpa using h1 1 isCoprime_one_left⟩

theorem provedGaloisAll_iff {E : ExpDat Y} {N0 : X.Tw → ℕ} {i : X.Tw} :
    goodTwistExistsAllCoprimePowers Y bkP E N0 i ↔ GlobalTheory.IndefiniteRowSideFullHecke.LemmaAtAllGoodPlaces.LemmaAllAt Y bkP E N0 i := Iff.rfl

theorem twGoodAt_of_all {D : D7} {C : NChoice D} {I : TwIn D} (h : TwGoodAtAll D C I) : TwGoodAt D C I :=
  fun w hw => ⟨(h w hw).1, by simpa using (h w hw).2 1 isCoprime_one_left⟩

theorem psiAt_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (a : ℤ) :
    BlochKatoReduction.Gen.psiAt b (ψ ^ a) = BlochKatoReduction.Gen.psiAt b ψ ^ a := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

theorem twGoodAll_side {D : D7} {C : NChoice D} {I : TwIn D} (h : TwGoodAtAll D C I) (w)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) (b : Bool) (a : ℤ) (ha : IsCoprime a (D.ntw.l (C.twI w) : ℤ)) :
    TwGoodOne D I (C.twI w) b (C.Q w) (C.k' w) (C.psi' w ^ a) := by
  have h1 := (h w hw).2 a ha
  have h2 := (h w hw).2 (-a) ha.neg_left
  unfold TwGoodOne at *
  revert h1 h2
  cases b <;> cases C.sd w <;> simp [BlochKatoReduction.Gen.psiAt] <;> tauto

variable (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

theorem zero_mem_ball (i : X.Tw) (j : ℕ) (b : Bool) {B : ℝ} (hB : 0 ≤ B) : (0 : Y.Fm i j b) ∈ Ball T i j b B :=
  ⟨zero_mem _, fun y => by simpa using hB⟩

theorem bsup_eq (i : X.Tw) (j : ℕ) (b : Bool) : Y.Bsup i j b = Submodule.span (X.O i) (Ball T i j b 1) :=
  T.Bsup_def i j b

theorem norm_l (i : X.Tw) : ‖((X.l i : ℕ) : ℂ_[X.l i])‖ = ((X.l i : ℝ))⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[X.l i] (PadicComplex (X.l i))), norm_algebraMap', Padic.norm_p]

theorem smul_l_pow (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b) :
    ((X.l i : X.O i) ^ c) • f = ((X.l i : FractionRing (X.O i)) ^ c) • f := by
  rw [← algebraMap_smul (FractionRing (X.O i))]
  simp

theorem l_pow_smul_mem (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (B : ℝ) (f : Y.Fm i j b)
    (hf : f ∈ Ball T i j b ((X.l i : ℝ) ^ c * B)) : ((X.l i : X.O i) ^ c) • f ∈ Ball T i j b B := by
  have hl : (0 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.pos
  rw [smul_l_pow]
  refine ⟨T.FmUr_smul i j b _ _ (pow_mem (natCast_mem _ _) _) hf.1, fun y => ?_⟩
  rw [T.ev_smul, norm_mul, map_pow, map_natCast, norm_pow, norm_l, inv_pow]
  rw [inv_mul_le_iff₀ (by positivity)]
  exact hf.2 y

theorem l_pow_smul_span (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b)
    (hf : f ∈ Submodule.span (X.O i) (Ball T i j b ((X.l i : ℝ) ^ c))) :
    ((X.l i : X.O i) ^ c) • f ∈ Y.Bsup i j b := by
  rw [bsup_eq T]
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (l_pow_smul_mem T i j b c 1 x (by simpa using hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem bsup_stable_of_gKeeps (h : GKeeps T) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (g) :
    (Y.Bsup i j b).map ((Y.actG i j b g).toLinearMap.restrictScalars (X.O i)) ≤ Y.Bsup i j b := by
  rw [bsup_eq T, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact Submodule.subset_span (h i hi j hj b g f hf)

theorem bsup_stable_of_hkKeeps (h : HkKeeps T) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (k P) (hk : HkIdx i k P) :
    (Y.Bsup i j b).map (hkO Y i j b k P) ≤ Y.Bsup i j b := by
  rw [bsup_eq T, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact Submodule.subset_span (h i hi j hj b k P hk f hf)

theorem integral_of_univBdd {E : ExpDat Y} (h : UnivBdd T E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    ∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q →
      Disjoint Q (X.S0 i) → Disjoint Q (Y.lev i j b a) →
      ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a ∈ LinearMap.range ((Mall Y i j b).subtype.rTensor _) := by
  intro a ha
  obtain ⟨c, hc⟩ := h i hi j hj b a ha
  refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
  obtain ⟨Xi, hXi, hδ⟩ := hc Q M h1 h2 h3 h4
  rw [hXi, Finsupp.sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun δ _ => ?_
  have hm : ((X.l i : X.O i) ^ c) • Xi δ ∈ Mall Y i j b :=
    ⟨l_pow_smul_span T i j b c _ (hδ δ).2,
      ((Fm0 Y i j b).restrictScalars (X.O i)).smul_mem _ (hδ δ).1⟩
  exact ⟨(⟨_, hm⟩ : Mall Y i j b) ⊗ₜ AddMonoidAlgebra.single δ (1 : X.O i), by
    simp [TensorProduct.smul_tmul']⟩

theorem span_bsup_of_supBdd (h : SupBdd T) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) : Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b)) = ⊤ := by
  rw [eq_top_iff, ← T.FmUr_span i j b, Submodule.span_le]
  intro f hf
  obtain ⟨B, hB⟩ := h i hi j hj b f hf
  have hl : (1 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.one_lt
  obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt B hl
  have h1 : f ∈ Ball T i j b ((X.l i : ℝ) ^ c) := ⟨hB.1, fun y => (hB.2 y).trans hc.le⟩
  have h2 := l_pow_smul_span T i j b c f (Submodule.subset_span h1)
  rw [smul_l_pow] at h2
  have hne : ((X.l i : FractionRing (X.O i))) ≠ 0 := by
    intro h0
    have := congrArg (T.iC i) h0
    rw [map_natCast, map_zero] at this
    exact (X.lPrime i).out.ne_zero (by exact_mod_cast this)
  have h3 := (Submodule.span (FractionRing (X.O i)) (Y.Bsup i j b : Set (Y.Fm i j b))).smul_mem
    (((X.l i : FractionRing (X.O i)) ^ c)⁻¹) (Submodule.subset_span h2)
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hne), one_smul] at h3

theorem typePreserved_of_admissibleIntegral {E : ExpDat Y} (h : IsotypicPartsInternalDirectSum Y E) : TypeKept E :=
  fun i hi j hj b => (h i hi j hj b).2.2.2.2.2

theorem coeffs_of_range {O V Δ : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommMonoid Δ]
    (S : Submodule O V) (t : S ⊗[O] AddMonoidAlgebra O Δ) :
    ∃ Xi : Δ →₀ V, S.subtype.rTensor _ t = Xi.sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) ∧
      ∀ δ, Xi δ ∈ S := by
  classical
  have hadd : ∀ A B : Δ →₀ V, (A + B).sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) =
      A.sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) +
        B.sum (fun δ f => f ⊗ₜ[O] AddMonoidAlgebra.single δ (1 : O)) := fun A B =>
    Finsupp.sum_add_index' (fun _ => TensorProduct.zero_tmul _ _) (fun _ _ _ => TensorProduct.add_tmul _ _ _)
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y hx hy =>
    obtain ⟨A, hA, hA'⟩ := hx
    obtain ⟨B, hB, hB'⟩ := hy
    exact ⟨A + B, by rw [map_add, hA, hB, hadd], fun δ => add_mem (hA' δ) (hB' δ)⟩
  | tmul m p =>
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y hx hy =>
      obtain ⟨A, hA, hA'⟩ := hx
      obtain ⟨B, hB, hB'⟩ := hy
      exact ⟨A + B, by rw [TensorProduct.tmul_add, map_add, hA, hB, hadd], fun δ => add_mem (hA' δ) (hB' δ)⟩
    | single δ r =>
      refine ⟨Finsupp.single δ (r • (m : V)), ?_, fun δ' => ?_⟩
      · rw [Finsupp.sum_single_index (by simp), TensorProduct.smul_tmul]
        simp
      · rw [Finsupp.single_apply]
        split_ifs
        · exact S.smul_mem _ m.2
        · exact zero_mem _

theorem l_ne_zero (T : NTh D.R D.host D.what₂ D.LL0 N X Y) (i : X.Tw) : ((X.l i : FractionRing (X.O i))) ≠ 0 := by
  intro h0
  have := congrArg (T.iC i) h0
  rw [map_natCast, map_zero] at this
  exact (X.lPrime i).out.ne_zero (by exact_mod_cast this)

theorem inv_smul_span (i : X.Tw) (j : ℕ) (b : Bool) (c : ℕ) (f : Y.Fm i j b) (hf : f ∈ Y.Bsup i j b) :
    ((X.l i : FractionRing (X.O i)) ^ c)⁻¹ • f ∈ Submodule.span (X.O i) (Ball T i j b ((X.l i : ℝ) ^ c)) := by
  have hl : (0 : ℝ) < X.l i := by exact_mod_cast (X.lPrime i).out.pos
  rw [bsup_eq T] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    refine Submodule.subset_span ⟨T.FmUr_smul i j b _ _ (inv_mem (pow_mem (natCast_mem _ _) _)) hx.1, fun y => ?_⟩
    rw [T.ev_smul, norm_mul, map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, norm_l, inv_pow, inv_inv]
    exact mul_le_of_le_one_right (by positivity) (hx.2 y)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem uniformBound_of_admissibleIntegral {E : ExpDat Y} (h : IsotypicPartsInternalDirectSum Y E) : UnivBdd T E := by
  intro i hi j hj b a ha
  obtain ⟨c, hc⟩ := (h i hi j hj b).2.2.2.2.1 a ha
  refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
  obtain ⟨t, ht⟩ := hc Q M h1 h2 h3 h4
  obtain ⟨Xi, hXi, hδ⟩ := coeffs_of_range (Mall Y i j b) t
  have hne := pow_ne_zero c (l_ne_zero T i)
  refine ⟨((X.l i : FractionRing (X.O i)) ^ c)⁻¹ • Xi, ?_, fun δ => ⟨?_, inv_smul_span T i j b c _ (hδ δ).1⟩⟩
  · have e1 : ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a =
        ((X.l i : FractionRing (X.O i)) ^ c) • Y.thU i j b Q M a := by
      rw [← algebraMap_smul (FractionRing (X.O i))]
      simp
    have e2 : Y.thU i j b Q M a = ((X.l i : FractionRing (X.O i)) ^ c)⁻¹ •
        Xi.sum (fun δ f => f ⊗ₜ[X.O i] AddMonoidAlgebra.single δ (1 : X.O i)) := by
      rw [← hXi, ht, e1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e2, Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
    simp [TensorProduct.smul_tmul']
  · exact (Fm0 Y i j b).smul_mem _ (hδ δ).2

end GlobalTheory.TwAll.Model

end
end

