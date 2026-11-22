import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ApolarMonomial
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Alg

variable {S : Type} [CommRing S] {ρ V : Type}

def apolar (P : MvPolynomial V S) (f : MvPowerSeries V S) : S :=
  ∑ m ∈ P.support, P.coeff m * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f)

theorem apolar_monomial (m : V →₀ ℕ) (c : S) (f : MvPowerSeries V S) :
    apolar (MvPolynomial.monomial m c) f = c * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f) := by
  classical
  rw [apolar, Finset.sum_subset (MvPolynomial.support_monomial_subset) fun x _ hx => by
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul], Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

example : apolar (MvPolynomial.monomial (Finsupp.single () 2) (1 : ℚ))
    (MvPowerSeries.monomial (Finsupp.single () 2) 1) = 2 := by
  rw [apolar_monomial, MvPowerSeries.coeff_monomial_same, Finsupp.prod_single_index (by simp)]
  norm_num [Nat.factorial]

def jetAt (c : ρ → V) (m : ℕ) : Jet S ρ m →ₐ[S] Jet S V m :=
  jetMap (fun r => MvPolynomial.X (c r)) fun r => X_mem_orig (c r)

def serAt (c : ρ → V) (g : MvPowerSeries ρ S) : MvPowerSeries V S :=
  MvPowerSeries.subst (fun r => (MvPowerSeries.X (c r) : MvPowerSeries V S)) g

end Alg

section Exp

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

structure IsExp (u : ρ → (Sp (DualNumber S) ⟶ G.left)) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) : Prop where
  zero : ∀ m, homAt x0 (jetAug : Jet S ρ m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ≫ x (m + 1) = x m
  law : ∀ m, homAt x0 (jetSum (Finset.univ : Finset (Fin 2))) ≫ x m =
    (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) * (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)
  act : ∀ m (c : O), x m ≫ a.act c = homAt x0 (jetScale fun r => ch r c) ≫ x m
  tan : ∀ r, (homAt x0 (jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left = u r

variable (bar : O → O) (L : LB G.left) (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => eSec G) fun _ => 1))

abbrev Fr (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) : Type :=
  ∀ m, LB.Gen (LB.LinComb L (K := PUnit) (fun _ => (x m).left) fun _ => 1)

structure IsHoriz (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m y J, Good L y J →
    val (e (m + 1)) (homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m)).left y J = val (e m) (𝟙 _) y J
  zero : ∀ y J, Good L y J → val (e 0) (homAt x0 (jetAug : Jet S ρ 0 →ₐ[S] S)).left y J = val rig x0 y J
  coc : ∀ c : O, ∃ β : LB.Gen (LB.LinComb L (K := Fin 4)
      ![(a.act (1 + c * bar c)).left, (a.act c).left, 𝟙 _, (a.act (c * bar c)).left] ![1, -2, -1, -1]), β.IsGen ∧
    (∀ y J, Good L y J → val β (eSec G) y J = (val rig (𝟙 _) y J ^ 3)⁻¹) ∧
    ∀ m y J, Good L y J → val (e m) (homAt x0 (jetScale fun r => ch r (1 + c * bar c))).left y J =
      val β (x m).left y J * val (e m) (homAt x0 (jetScale fun r => ch r c)).left y J ^ 2 * val (e m) (𝟙 _) y J *
        val (e m) (homAt x0 (jetScale fun r => ch r (c * bar c))).left y J

variable (G) in

abbrev Pw (n : ℕ) : Over X := Over.mk x0 ⊗ powObj G n

variable (G) in

abbrev pr {n : ℕ} (b : Fin n) : (Pw G x0 n).left ⟶ G.left := (snd _ _ ≫ powPr G b).left

abbrev SecPw (n k : ℕ) : Type := LB.Sec (LB.LinComb L (pr G x0 (n := n)) fun _ => (k : ℤ))

def pwPt {n : ℕ} (col : Fin n → ρ → V) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (m : ℕ) :
    overAt x0 (Jet S V m) ⟶ Pw G x0 n :=
  lift (Over.homMk (spMap (algebraMap S (Jet S V m))) rfl)
    ((powIsLimit G n).lift (Fan.mk _ fun b => homAt x0 (jetAt (col b) m) ≫ x m))

def IsGermPw {n k : ℕ} (col : Fin n → ρ → V) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x)
    (s : SecPw x0 L n k) (f : MvPowerSeries V S) : Prop :=
  ∀ m y J, Good L y J → sval s (pwPt x0 col x m).left y J =
    gs (𝟙 _) y ⊤ (toΓ _ (psJet m f)) * ∏ b, (val (e m) (homAt x0 (jetAt (col b) m)).left y J ^ k).val

def IsVal (u : ρ → (Sp (DualNumber S) ⟶ G.left)) {n k : ℕ} (col : Fin n → ρ → V) (P : MvPolynomial V S)
    (s : SecPw x0 L n k) (v : S) : Prop :=
  ∃ (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) (f : MvPowerSeries V S),
    IsExp a x0 ch u x ∧ IsHoriz a x0 ch bar L rig x e ∧ IsGermPw x0 L col x e s f ∧ v = apolar P f

def IsBoxSum {n k N : ℕ} (s : SecPw x0 L n k) (c : Fin N → S) (σ : Fin N → Fin n → H0 L k) : Prop :=
  ∀ y J, Good L y J → sval s (𝟙 _) y J =
    ∑ i, gs (fst (Over.mk x0) (powObj G n)).left y ⊤ (toΓ S (c i)) * ∏ b, sval (σ i b) (pr G x0 b) y J

end Exp

section Gt

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} (Y : Ray oa)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ Sp R) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

def IsTermGerm {k : ℕ} (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ Y.H) (e : Fr x0 D.toPre.P.L fun m => x m ≫ Y.q)
    {α : D.toPre.X} (σ : D.toPre.SecB k α) (g : MvPowerSeries ρ S) : Prop :=
  ∀ m y J, Good D.toPre.P.L y J → sval σ (x m ≫ Y.q).left y J * (val ((Y.Φ _ (x m)).s α) (𝟙 _) y J).val =
    gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (e m) (𝟙 _) y J ^ k).val

def IsValGt [TopologicalSpace S] (u : ρ → (Sp (DualNumber S) ⟶ Y.H.left)) {n k : ℕ} (col : Fin n → ρ → V)
    (P : MvPolynomial V S) (s : SecPw x0 U.LG.L n k) (v : S) : Prop :=
  ∃ (N : ℕ) (c : Fin N → S) (σ : Fin N → Fin n → H0 U.LG.L k) (F : Fin N → Fin n → ∀ α, D.toPre.SecB k α)
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ Y.H) (e : Fr x0 D.toPre.P.L fun m => x m ≫ Y.q)
    (g : Fin N → Fin n → D.toPre.X → MvPowerSeries ρ S),
    IsBoxSum x0 U.LG.L s c σ ∧ (∀ i b l, U.ExpandsAt l k (σ i b) (F i b)) ∧ IsExp Y.act x0 ch u x ∧
    IsHoriz (Ray.actB oa) x0 ch star D.toPre.P.L D.toPre.rig (fun m => x m ≫ Y.q) e ∧
    (∀ i b α, IsTermGerm Y x0 x e (F i b α) (g i b α)) ∧
    HasSum (fun χ : Fin n → D.toPre.X =>
      apolar P (∑ i, MvPowerSeries.C (c i) * ∏ b, serAt (col b) (g i b (χ b)))) v

end Gt

end GlobalTheory.RayEv
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqZeroOfApplySelf
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.LocM.TorCheck

theorem ordGe_pow_iff {R : Type} [CommRing R] [IsDomain R] {u : R} (h0 : u ≠ 0) (hu : ¬ IsUnit u) (e a b n : ℕ) (i : ℚ) :
    OrdGe (u ^ e) i n (Ideal.span {u ^ a}) (Ideal.span {u ^ b}) ↔ i * ((a : ℚ) - b) ≤ e * n := by
  rw [ordGe_span_iff]
  simp only [← pow_mul, ← pow_add]
  rw [pow_dvd_pow_iff h0 hu]
  have hd : (0 : ℚ) < i.den := by exact_mod_cast i.den_pos
  have hi : i * i.den = i.num := Rat.mul_den_eq_num i
  have hn : ((i.num.toNat : ℤ) : ℚ) - (((-i.num).toNat : ℤ) : ℚ) = i.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg i.num
  simp only [Int.cast_natCast] at hn
  rw [← Nat.cast_le (α := ℚ), ← mul_le_mul_iff_of_pos_right (b := i * ((a : ℚ) - b)) hd]
  push_cast
  have : i * ((a : ℚ) - b) * i.den = ((i.num.toNat : ℚ) - ((-i.num).toNat : ℚ)) * ((a : ℚ) - b) := by
    rw [hn, ← hi]; ring
  rw [this]
  constructor <;> intro h <;> linarith

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

theorem minVal_eval (B : X → X → ℝ) : (InvFun.minVal O).eval X B = sInf {x | (∃ y, B y y = x) ∧ x ≠ B 0 0} := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  change sInf _ = _
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, map_zero]
  exact and_congr_left' ⟨fun ⟨y, h⟩ => ⟨r y, h⟩, fun ⟨y, h⟩ => (hr y).elim fun z e => ⟨z, e ▸ h⟩⟩

theorem minVal_linearOn (γ : LinearMap.BilinForm ℤ X) : (InvFun.minVal O).LinearOn ![γ] := by
  intro c hc
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, InvFun.evalZ, minVal_eval, map_zero, Int.cast_zero, mul_zero,
    LinearMap.zero_apply]
  rcases (hc 0).eq_or_lt with h | h
  · rw [← h]
    simp only [zero_mul]
    convert Real.sInf_empty
    exact Set.eq_empty_of_forall_notMem fun x ⟨⟨_, h⟩, h'⟩ => h' h.symm
  · rw [← smul_eq_mul (c 0) (sInf _), ← Real.sInf_smul_of_nonneg (hc 0)]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨⟨y, rfl⟩, hx⟩
      exact ⟨_, ⟨⟨y, rfl⟩, fun e => hx (by rw [e, mul_zero])⟩, rfl⟩
    · rintro ⟨_, ⟨⟨y, rfl⟩, hx⟩, rfl⟩
      exact ⟨⟨y, rfl⟩, mul_ne_zero h.ne' hx⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem eq_zero_of_apply_self {β : LinearMap.BilinForm ℤ (𝓞 E)} (hβ : β ∈ levelForms H 1 (𝓞 E))
    (hp : ∀ y, 0 ≤ β y y) {y₀ : 𝓞 E} (hy : y₀ ≠ 0) (h : β y₀ y₀ = 0) (y : 𝓞 E) : β y y = 0 := by
  have h1 : ∀ z, β y₀ z = 0 := fun z => by
    by_contra hz
    have k := hp ((-(β z z + 1) * β y₀ z) • y₀ + z)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h, hβ.1 z y₀] at k
    have : 1 ≤ β y₀ z * β y₀ z := mul_self_pos.2 hz
    have := hp z
    nlinarith
  obtain ⟨N, hN, c, hc⟩ : ∃ N : ℤ, N ≠ 0 ∧ ∃ c : 𝓞 E, c * y₀ = N := by
    have hI : Ideal.span {y₀} ≠ ⊥ := by simpa using hy
    refine ⟨(Ideal.absNorm (Ideal.span {y₀}) : ℕ), ?_, ?_⟩
    · exact_mod_cast fun e => hI (Ideal.absNorm_eq_zero_iff.1 e)
    · have := Ideal.absNorm_mem (Ideal.span {y₀})
      simpa using Ideal.mem_span_singleton'.1 this
  have h2 : β ((y * c) • y₀) y = 0 := by rw [hβ.2.1, h1]
  have e : (y * c) • y₀ = N • y := by rw [smul_eq_mul, mul_assoc, hc, zsmul_eq_mul, mul_comm]
  rw [e, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left hN

theorem exists_isPiece (M : ℕ) (hM : M ≠ 0) :
    0 < (InvFun.minVal (𝓞 E)).evalZ ((M : ℤ) • HostModel.trForm H) ∧
    (InvFun.minVal (𝓞 E)).LinearOn ![(M : ℤ) • HostModel.trForm H] ∧
    ∃ ℓ, IsPiece H (InvFun.minVal (𝓞 E)) 1 ![(M : ℤ) • HostModel.trForm H] ℓ := by
  set γ := (M : ℤ) • HostModel.trForm H with hγ
  have pos : ∀ y : 𝓞 E, y ≠ 0 → 0 < γ y y := fun y hy =>
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hM) (HostModel.trForm_pos H hy)
  obtain ⟨y₀, hy₀, hmin⟩ : ∃ y₀ : 𝓞 E, y₀ ≠ 0 ∧ ∀ y, y ≠ 0 → γ y₀ y₀ ≤ γ y y := by
    obtain ⟨y₀, h0, h⟩ := (measure fun y : 𝓞 E => (γ y y).toNat).wf.has_min {y | y ≠ 0} ⟨1, one_ne_zero⟩
    refine ⟨y₀, h0, fun y hy => ?_⟩
    have h1 : ¬ (γ y y).toNat < (γ y₀ y₀).toNat := h y hy
    have := pos y hy
    have := pos y₀ h0
    omega
  have hv : (InvFun.minVal (𝓞 E)).evalZ γ = γ y₀ y₀ := by
    rw [InvFun.evalZ, minVal_eval]
    refine IsLeast.csInf_eq ⟨⟨⟨y₀, rfl⟩, ?_⟩, ?_⟩
    · simpa using (pos y₀ hy₀).ne'
    · rintro _ ⟨⟨y, rfl⟩, h⟩
      exact_mod_cast hmin y fun e => h (by rw [e])
  refine ⟨hv ▸ by exact_mod_cast pos y₀ hy₀, minVal_linearOn γ,
    (LinearMap.applyₗ y₀) ∘ₗ (LinearMap.applyₗ y₀), fun i => ?_, fun β hβ hp => ?_⟩
  · fin_cases i
    simp [hv]
  · simp only [Nat.cast_one, one_mul, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, InvFun.evalZ, minVal_eval]
    by_cases h : β y₀ y₀ = 0
    · rw [h]
      refine le_of_eq ?_
      rw [Int.cast_zero]
      convert Real.sInf_empty
      exact Set.eq_empty_of_forall_notMem fun x ⟨⟨y, e⟩, h'⟩ => h' (by
        rw [← e, eq_zero_of_apply_self H hβ hp hy₀ h y]; simp)
    · refine csInf_le ⟨0, ?_⟩ ⟨⟨y₀, rfl⟩, by simpa using h⟩
      rintro _ ⟨⟨y, rfl⟩, -⟩
      exact_mod_cast hp y

end GlobalTheory.LocM.TorCheck
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueIsVal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.Points
open GlobalTheory.GradedPieces IsLocalRing

namespace GlobalTheory.LocM.FJ

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Value

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure GrTriv (Z : Mdl Y i₀) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) (F : Z.X.Modules) : Type 1 where

  L : LB Z.X

  isLB : L.IsLB

  hU : ∀ i, IsAffineOpen (L.U i)

  w : ∀ i, Vecs Dw (Y Z.i).t Γ(Z.X, L.U i)

  int : ∀ i, IntFrame Z (hU i) (w i)

  trans : ∀ (i i' : L.ι) (k : Type) [Field k] (φ : Γ(Z.X, L.U i) →+* k) (φ' : Γ(Z.X, L.U i') →+* k)
    (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ (hU i).fromSpec = spMap φ' ≫ (hU i').fromSpec → Set.range (spMap φ ≫ (hU i).fromSpec) ⊆ Z.opn →
    (∀ σ, DiagAt (Y Z.i).t (spMap φ ≫ (hU i).fromSpec ≫ Z.π) ((w i').bc φ' σ) ((w i).bc φ σ) (d σ)) →
    valR (spMap φ ≫ (hU i).fromSpec) _ (L.g i i').val = ∏ σ, ∏ a, d σ a ^ e σ a

  iso : F ≅ GlobalTheory.LB.toMod L

variable {Z : Mdl Y i₀} {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ}

theorem nonempty_grTriv (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {L : LB Z.X} (h : IsGrLB Z e L) :
    Nonempty (GrTriv Z e (Z.ofMod (GlobalTheory.LB.toMod L)).toMod) := by
  obtain ⟨hL, hU, w, hw, ht⟩ := h
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod L) := (GlobalTheory.VB.isVB_toMod hL).isFiniteQC
  obtain ⟨i⟩ := GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso E H Dw Xo p W hp hW Y i₀ Z (GlobalTheory.LB.toMod L)
  exact ⟨⟨L, hL, hU, w, hw, ht, i⟩⟩

variable {F : Z.X.Modules} (T : GrTriv Z e F) {V : Z.X.Opens} {k : Type} [Field k]

def GrTriv.IsVal (f : Γ(F, V)) (x : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) (r : k) : Prop :=
  ⊤ ≤ x ⁻¹ᵁ V ∧ ∃ (i : T.L.ι) (φ : Γ(Z.X, T.L.U i) →+* k) (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k),
    spMap φ ≫ (T.hU i).fromSpec = x ∧ (∀ σ, DiagAt (Y Z.i).t (x ≫ Z.π) ((T.w i).bc φ σ) (u σ) (d σ)) ∧
    r = valR x (V ⊓ T.L.U i) (GlobalTheory.LB.coord (T.iso.hom.app V f) i) * ∏ σ, ∏ a, d σ a ^ e σ a

theorem range_subset_opn {x : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) : Set.range x ⊆ Z.opn := by
  obtain ⟨a, φ, rfl, -⟩ := h
  rintro _ ⟨z, rfl⟩
  rw [← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, le_preimage_specMap_fromSpec (Z.U a).2 (CommRingCat.ofHom φ) (Set.mem_univ z)⟩

theorem GrTriv.existsUnique_isVal (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) (f : Γ(F, V)) {x : Sp k ⟶ Z.X}
    (hx : ⊤ ≤ x ⁻¹ᵁ V) {u : Vecs Dw (Y Z.i).t k} (hu : Z.FlagAt x u) : ∃! r, T.IsVal f x u r := by
  have ho := range_subset_opn hu
  have tu : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i) := fun σ i => by
    obtain ⟨_, _, -, h, -⟩ := hu
    exact (h.1 σ i).1
  have fl : ∀ i (φ : Γ(Z.X, T.L.U i) →+* k), spMap φ ≫ (T.hU i).fromSpec = x → Z.FlagAt x ((T.w i).bc φ) :=
    fun i φ h => h ▸ (T.int i).2 k φ (h ▸ ho)
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (T.isLB.cover.ge (Set.mem_univ (x (closedPoint k))))
    have h : ⊤ ≤ x ⁻¹ᵁ T.L.U i := fun z _ => by
      obtain rfl : z = closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
      exact hi
    have e₁ := specMap_valMap_fromSpec (T.hU i) x h
    choose d hd using fun σ => exists_diag_of_flagAt Z hty hu (fl i _ e₁) σ (tu σ) (tan_bc (T.int i) _ e₁ σ)
      (linInd_bc (T.int i) _ e₁ σ)
    exact ⟨_, hx, i, _, d, e₁, fun σ => (diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) (d σ)).2 (hd σ), rfl⟩
  · rintro _ _ ⟨-, i, φ, d, e₁, hd, rfl⟩ ⟨-, i', φ', d', e₂, hd', rfl⟩
    choose D hD using fun σ => exists_diag_of_flagAt Z hty (fl i _ e₁) (fl i' _ e₂) σ (tan_bc (T.int i) _ e₁ σ)
      (tan_bc (T.int i') _ e₂ σ) (linInd_bc (T.int i') _ e₂ σ)
    have hg := T.trans i i' k φ φ' D (e₁.trans e₂.symm) (e₁ ▸ ho) fun σ => by
      rw [← Category.assoc, e₁]
      exact (diagAt_iff (tan_bc (T.int i') _ e₂ σ) (tan_bc (T.int i) _ e₁ σ) (D σ)).2 (hD σ)
    have hd'' : ∀ σ, d' σ = fun a => d σ a * D σ a := fun σ =>
      ((diagAt_iff (tan_bc (T.int i') _ e₂ σ) (tu σ) _).1 (hd' σ)).unique (linInd_bc (T.int i') _ e₂ σ)
        ((hD σ).trans ((diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) _).1 (hd σ)))
    have h₁ : ⊤ ≤ x ⁻¹ᵁ T.L.U i := e₁ ▸ le_preimage_specMap_fromSpec (T.hU i) (CommRingCat.ofHom φ)
    have h₂ : ⊤ ≤ x ⁻¹ᵁ T.L.U i' := e₂ ▸ le_preimage_specMap_fromSpec (T.hU i') (CommRingCat.ofHom φ')
    have h₃ : ⊤ ≤ x ⁻¹ᵁ (V ⊓ T.L.U i ⊓ T.L.U i') := fun z hz => ⟨⟨hx hz, h₁ hz⟩, h₂ hz⟩
    have hc := congrArg (valR x _) (GlobalTheory.LB.coord_mem (T.iso.hom.app V f) i i')
    rw [valR_mul x _ h₃] at hc
    erw [valR_res x _ h₃, valR_res x _ h₃, valR_res x _ h₃] at hc
    rw [e₁] at hg
    rw [hc, hg]
    simp only [hd'', mul_zpow, Finset.prod_mul_distrib]
    ring

theorem GrTriv.IsVal.change {T : GrTriv Z e F} {f : Γ(F, V)} {x : Sp k ⟶ Z.X} {u u' : Vecs Dw (Y Z.i).t k} {r : k}
    (h : T.IsVal f x u r) (tu : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i))
    (tu' : ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u' σ i)) {d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k}
    (hd : ∀ σ, DiagAt (Y Z.i).t (x ≫ Z.π) (u σ) (u' σ) (d σ)) : T.IsVal f x u' (r * ∏ σ, ∏ a, d σ a ^ e σ a) := by
  obtain ⟨hx, i, φ, D, e₁, hD, rfl⟩ := h
  refine ⟨hx, i, φ, fun σ a => d σ a * D σ a, e₁, fun σ => (diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu' σ) _).2
    (((diagAt_iff (tan_bc (T.int i) _ e₁ σ) (tu σ) _).1 (hD σ)).trans ((diagAt_iff (tu σ) (tu' σ) _).1 (hd σ))), ?_⟩
  simp only [mul_zpow, Finset.prod_mul_distrib]
  ring

theorem GrTriv.isVal_chart (f : Γ(F, V)) {x : Sp k ⟶ Z.X} (hx : ⊤ ≤ x ⁻¹ᵁ V) (i : T.L.ι) (φ : Γ(Z.X, T.L.U i) →+* k)
    (h : spMap φ ≫ (T.hU i).fromSpec = x) :
    T.IsVal f x ((T.w i).bc φ) (valR x (V ⊓ T.L.U i) (GlobalTheory.LB.coord (T.iso.hom.app V f) i)) :=
  ⟨hx, i, φ, fun _ _ => 1, h, fun σ => (diagAt_iff (tan_bc (T.int i) _ h σ) (tan_bc (T.int i) _ h σ) _).2 (Diag.refl _),
    by simp⟩

end Value

end GlobalTheory.LocM.FJ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSMulRegularNatCast
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem eq_zero_of_flat {R T : Type} [CommRing R] [IsDomain R] [CharZero R] [CommRing T] (φ : R →+* T) (hφ : φ.Flat)
    {c : ℕ} (hc : c ≠ 0) {a : T} (h : (c : T) * a = 0) : a = 0 := by
  let := φ.toAlgebra
  have : Module.Flat R T := hφ
  have hr :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (R := R) (M := T) (r := (c : R)) (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hc))
  refine hr (a₁ := a) (a₂ := 0) ?_
  simp only [Nat.cast_smul_eq_nsmul, smul_zero, nsmul_eq_mul, h]

def Lat.mulIncl {B : Mdl Y i₀} (L : Lat B) (c : ℕ) : L.N.toMod ⟶ B.om :=
  LB.homOfLinear (fun V => c • QCoh.appLinear L.N.incl V) fun h s =>
    (congrArg (c • ·) (Twist.app_resM L.N.incl h s)).trans (map_nsmul (Twist.resM B.om h) c _).symm

theorem Mdl.isSMulRegular_natCast (B : Mdl Y i₀) {U : B.X.Opens} (hU : IsAffineOpen U) {c : ℕ} (hc : c ≠ 0)
    {a : Γ(B.X, U)} (h : (c : Γ(B.X, U)) * a = 0) : a = 0 := by
  have := B.flat
  have hf := Flat.flat_appLE B.s (isAffineOpen_top _) hU le_top
  let φ : B.i.c.V W →+* Γ(B.X, U) := (B.s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of (B.i.c.V W))).inv.hom
  have hφ : φ.Flat := (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (B.i.c.V W))).inv)).comp hf
  exact eq_zero_of_flat φ hφ hc h

def Lat.powSMul {B : Mdl Y i₀} (hp : p ≠ 0) (L : Lat B) (c : ℕ) : Lat B :=
  have : Mono (L.mulIncl (p ^ c)) := QCoh.mono_of_locally_app_injective _ fun V x hx => by
    obtain ⟨V', n, m, hx', hm⟩ := L.free x
    obtain ⟨U, hU, hxU, hle⟩ := QCoh.exists_affine_mem_le (U := V ⊓ V') x ⟨hx, hx'⟩
    refine ⟨U, hxU, hle.trans inf_le_left, (injective_iff_map_eq_zero _).2 fun s hs => ?_⟩
    have h₁ : ((p ^ c : ℕ) : Γ(B.X, U)) • s = 0 := L.N.incl_app_injective U (by
      rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_zero]
      exact hs)
    let b := hm.basis (hle.trans inf_le_right)
    refine b.ext_elem fun i => B.isSMulRegular_natCast hU (pow_ne_zero c hp) ?_ |>.trans (by simp)
    simpa using congrArg (fun z => b.repr z i) h₁
  Lat.ofBundle (L.mulIncl (p ^ c)) L.free fun V hV s => by
    have hu : IsUnit ((p : ℕ) : Γ(B.X, V)) := by
      have := (B.X.toRingedSpace.isUnit_res_basicOpen ((p : ℕ) : Γ(B.X, ⊤))).map
        (B.X.presheaf.map (homOfLE hV).op).hom
      exact (map_natCast ((B.X.presheaf.map (homOfLE hV).op).hom.comp
        (B.X.presheaf.map (homOfLE (B.X.basicOpen_le _)).op).hom) p) ▸ this
    obtain ⟨u, hu⟩ := hu.pow c
    obtain ⟨r, hr⟩ := L.N.mem_sec_iff.1 ((L.gen V hV).ge (Submodule.mem_top (x := (↑u⁻¹ : Γ(B.X, V)) • s)))
    refine ⟨r, ?_⟩
    change p ^ c • L.N.incl.app V r = s
    rw [hr, ← Nat.cast_smul_eq_nsmul Γ(B.X, V), Nat.cast_pow, ← hu, smul_smul, Units.mul_inv, one_smul]

end GlobalTheory.LocM
end
end

