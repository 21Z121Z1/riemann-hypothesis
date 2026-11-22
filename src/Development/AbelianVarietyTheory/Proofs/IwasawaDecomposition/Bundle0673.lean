import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRigFr
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayHoriz

section Jet

variable {S : Type} [CommRing S] {ρ : Type}

def jetW {K : Type} [Fintype K] (w : K → ρ → S) (m : ℕ) : Jet S ρ m →ₐ[S] Jet S (K × ρ) m :=
  jetMap (fun r => ∑ i, MvPolynomial.C (w i r) * MvPolynomial.X (i, r)) fun r =>
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (X_mem_orig (i, r))

end Jet

section Frames

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left)
  (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => eSec G) fun _ => 1))

structure IsRigFr (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m y J, Good L y J →
    val (e (m + 1)) (homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m)).left y J = val (e m) (𝟙 _) y J
  zero : ∀ y J, Good L y J → val (e 0) (homAt x0 (jetAug : Jet S ρ 0 →ₐ[S] S)).left y J = val rig x0 y J

def ev {K : Type} [Fintype K] {x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G} (e : Fr x0 L x) (w : K → ρ → S) (m : ℕ)
    (y : (overAt x0 (Jet S (K × ρ) m)).left) (J : ((overAt x0 (Jet S (K × ρ) m)).left ⟶ G.left) → L.ι) :
    ((overAt x0 (Jet S (K × ρ) m)).left.presheaf.stalk y)ˣ :=
  val (e m) (homAt x0 (jetW w m)).left y J

def pt2 (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (m : ℕ) : overAt x0 (Jet S (Fin 2 × ρ) m) ⟶ G ⊗ G :=
  lift (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)

def pt3 (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (m : ℕ) : overAt x0 (Jet S (Fin 3 × ρ) m) ⟶ G3 G :=
  lift (homAt x0 (jetIn (0 : Fin 3)) ≫ x m)
    (lift (homAt x0 (jetIn (1 : Fin 3)) ≫ x m) (homAt x0 (jetIn (2 : Fin 3)) ≫ x m))

def ThetaIs (t : LB.Gen (Theta G L)) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop :=
  ∀ m y J, Good L y J → val t (pt3 x0 x m).left y J =
    ∏ I : Finset (Fin 3), val (e m) (homAt x0 (jetSum I : Jet S ρ m →ₐ[S] Jet S (Fin 3 × ρ) m)).left y J ^
      ((-1 : ℤ) ^ (3 - I.card))

def SymIs (σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]))
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop :=
  ∀ m y J, Good L y J → val σ (x m).left y J =
    val (e m) (homAt x0 (jetScale (fun _ => (-1 : S)) : Jet S ρ m →ₐ[S] Jet S ρ m)).left y J *
      (val (e m) (𝟙 _) y J)⁻¹

def LamBal {O : Type} [CommRing O] (a : OAct O G) (bar : O → O) (ch : ρ → O →+* S)
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop :=
  ∀ c : O, ∃ w : LB.Gen (LB.LinComb L (rosatiφ G (a.act c) (a.act (bar c))) rosatiε), w.IsGen ∧
    (∀ y J, Good L y J → val w (zero2 G) y J = 1) ∧
    ∀ m y J, Good L y J → val w (pt2 x0 x m).left y J =
      ev x0 L e ![fun r => ch r c, fun _ => 1] m y J * (ev x0 L e ![fun r => ch r c, fun _ => 0] m y J)⁻¹ *
        (ev x0 L e ![fun _ => 0, fun _ => 1] m y J)⁻¹ * (ev x0 L e ![fun _ => 1, fun r => ch r (bar c)] m y J)⁻¹ *
        ev x0 L e ![fun _ => 1, fun _ => 0] m y J * ev x0 L e ![fun _ => 0, fun r => ch r (bar c)] m y J

end Frames

end GlobalTheory.RayHoriz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X] {m : ℕ}

def linW (w : (X × X) →₀ ℤ) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := w.sum fun p k => k * β p.1 p.2
  map_add' β γ := by
    simp only [LinearMap.add_apply, mul_add]
    exact Finsupp.sum_add
  map_smul' c β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finsupp.mul_sum]
    exact Finsupp.sum_congr fun _ _ => by ring

def evalW (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : ℝ := w.sum fun p k => (k : ℝ) * B p.1 p.2

theorem linW_apply (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : linW w β = w.sum fun p k => k * β p.1 p.2 := rfl

theorem evalW_toReal (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : evalW w (toReal β) = linW w β := by
  simp [evalW, linW_apply, Finsupp.sum]

theorem evalW_add (w : (X × X) →₀ ℤ) (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (B + B') = evalW w B + evalW w B' := by
  simp only [evalW, LinearMap.add_apply, mul_add]
  exact Finsupp.sum_add

theorem evalW_smul (w : (X × X) →₀ ℤ) (t : ℝ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (t • B) = t * evalW w B := by
  simp only [evalW, LinearMap.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

def evalWL (w : (X × X) →₀ ℤ) : (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) →ₗ[ℝ] ℝ where
  toFun := evalW w
  map_add' := evalW_add w
  map_smul' t B := evalW_smul w t B

theorem evalW_sum (w : (X × X) →₀ ℤ) (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    evalW w (∑ i, t i • toReal (u i)) = ∑ i, t i * linW w (u i) := by
  have := map_sum (evalWL w) (fun i => t i • toReal (u i)) Finset.univ
  simp only [evalWL, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by rw [evalW_smul, evalW_toReal]

def rcone (u : Fin m → LinearMap.BilinForm ℤ X) : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ B = ∑ i, t i • toReal (u i)}

def StrictWith {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) [Module O X] [Module.Finite O X] (N : ℕ)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (u : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ i, (ℓ (u i) : ℝ) = N * φ.evalZ (u i)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i

theorem isStrict_iff {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} [Module O X] [Module.Finite O X]
    {u : Fin m → LinearMap.BilinForm ℤ X} : IsStrict bar φ u ↔ ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧
      StrictWith bar φ N ℓ u := Iff.rfl

def kDen (N n : ℕ) (𝓜 : Finset ℕ) : ℕ := N * ∏ M ∈ 𝓜, (M + 1) ^ n

def lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) : (X × X) →₀ ℤ :=
  (D : ℤ) • ((∏ M ∈ 𝓜, ((M : ℤ) + 1) ^ n) • w +
    ∑ M ∈ 𝓜, ((N : ℤ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℤ) + 1) ^ n) • ∑ y, Finsupp.single (r (a M y), r (a M y)) 1)

example : linW (Finsupp.single ((1 : ℤ), (1 : ℤ)) 1) mulForm = 1 := by simp [linW_apply]

example : toReal mulForm ∈ rcone ![mulForm] := ⟨![1], fun i => by fin_cases i; simp, by simp⟩

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.familyIsotropicDual_linearIndependent_and_card : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  intro r d M e f hiso hdual hspan
  have hli : LinearIndependent ℝ (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have hb : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (fun v => v ⬝ᵥ M *ᵥ e k) hg
      simpa [add_dotProduct, sum_dotProduct, smul_dotProduct, hiso, hdual] using h
    have ha : ∀ k, g (Sum.inl k) = 0 := by
      intro k
      have hg' : ∑ i, g (Sum.inl i) • e i = 0 := by simpa [hb] using hg
      have h := congrArg (fun v => f k ⬝ᵥ M *ᵥ v) hg'
      simpa [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, hdual] using h
    rintro (k | k)
    · exact ha k
    · exact hb k
  refine ⟨hli, ?_⟩
  have h1 := finrank_span_eq_card hli
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
  omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetEvaluationPowerSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AdicConverge

open MvPolynomial Formalism.L2.Pj

section Coef

variable {K : Type} [CommRing K] {ρ : Type} {m : ℕ}

def jetCoef (n : ρ →₀ ℕ) (j : Jet K ρ m) : K := (Ideal.Quotient.mk_surjective j).choose.coeff n

theorem jetCoef_mk {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (p : MvPolynomial ρ K) :
    jetCoef (m := m) n (Ideal.Quotient.mk _ p) = p.coeff n := by
  have hs := Ideal.Quotient.mk_surjective (I := orig K ρ ^ (m + 1)) (Ideal.Quotient.mk (orig K ρ ^ (m + 1)) p)
  show hs.choose.coeff n = _
  have h2 : (Ideal.Quotient.mk (orig K ρ ^ (m + 1)) (hs.choose - p) : Jet K ρ m) = 0 := by
    rw [map_sub, hs.choose_spec, sub_self]
  have := (GlobalTheory.JetTest.mk_eq_zero_iff _).1 h2 n hn
  rwa [coeff_sub, sub_eq_zero] at this

theorem jetCoef_add {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (a b : Jet K ρ m) :
    jetCoef n (a + b) = jetCoef n a + jetCoef n b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_add, jetCoef_mk hn, jetCoef_mk hn, jetCoef_mk hn, coeff_add]

theorem jetCoef_smul {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (c : K) (a : Jet K ρ m) :
    jetCoef n (algebraMap K (Jet K ρ m) c * a) = c * jetCoef n a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have : algebraMap K (Jet K ρ m) c * Ideal.Quotient.mk _ p = Ideal.Quotient.mk _ (MvPolynomial.C c * p) := by
    rw [map_mul, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  rw [this, jetCoef_mk hn, jetCoef_mk hn, coeff_C_mul]

theorem jetCoef_psJet [Fintype ρ] [DecidableEq ρ] {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (h : MvPowerSeries ρ K) :
    jetCoef n (psJet m h) = MvPowerSeries.coeff n h := by
  rw [psJet, jetCoef_mk hn, GlobalTheory.JetTest.coeff_psTrunc, if_pos hn]

theorem jet_ext (a b : Jet K ρ m) (h : ∀ n : ρ →₀ ℕ, n.degree ≤ m → jetCoef n a = jetCoef n b) : a = b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← sub_eq_zero, ← map_sub, GlobalTheory.JetTest.mk_eq_zero_iff]
  intro e he
  rw [coeff_sub, ← jetCoef_mk he, ← jetCoef_mk he, h e he, sub_self]

end Coef

theorem exists_bound {α : Type} (S : Finset α) (φ : α → ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ (∀ x ∈ S, φ x ≤ q) ∧ (q = 0 ∨ ∃ x ∈ S, q = φ x) := by
  classical
  have hne : (insert 0 (S.image φ)).Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨(insert 0 (S.image φ)).max' hne, Finset.le_max' _ 0 (Finset.mem_insert_self _ _),
    fun x hx => Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem φ hx)), ?_⟩
  rcases Finset.mem_insert.1 (Finset.max'_mem _ hne) with h | h
  · exact Or.inl h
  · obtain ⟨x, hx, hq⟩ := Finset.mem_image.1 h
    exact Or.inr ⟨x, hx, hq.symm⟩

section Norms

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {R : Type} [CommRing R] (f : R →+* C)

def normIdeal (hf : ∀ r, ‖f r‖ ≤ 1) (c : ℝ) (hc : 0 ≤ c) : Ideal R where
  carrier := {a | ‖f a‖ ≤ c}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp [hc]
  smul_mem' := fun r a ha => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖f r‖ * ‖f a‖ ≤ 1 * c := mul_le_mul (hf r) ha (norm_nonneg _) zero_le_one
      _ = c := one_mul c

theorem norm_le_of_mem_pow {I : Ideal R} (hI : I.FG) (hf1 : ∀ r, ‖f r‖ ≤ 1) (hfI : ∀ r ∈ I, ‖f r‖ < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ k : ℕ, ∀ a ∈ I ^ k, ‖f a‖ ≤ q ^ k := by
  classical
  obtain ⟨G, hG⟩ := hI
  obtain ⟨q, hq0, hqG, hq⟩ := exists_bound G (fun x => ‖f x‖)
  have hq1 : q < 1 := by
    rcases hq with h | ⟨x, hx, h⟩
    · rw [h]; exact one_pos
    · rw [h]; exact hfI x (hG ▸ Ideal.subset_span hx)
  refine ⟨q, hq0, hq1, fun k => ?_⟩
  suffices h : I ^ k ≤ normIdeal f hf1 (q ^ k) (pow_nonneg hq0 k) from fun a ha => h ha
  induction k with
  | zero => intro a _; show ‖f a‖ ≤ q ^ 0; rw [pow_zero]; exact hf1 a
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    have ha' : ‖f a‖ ≤ q ^ k := ih ha
    have hspan : Ideal.span (G : Set R) ≤ normIdeal f hf1 (q ^ 1) (pow_nonneg hq0 1) :=
      Ideal.span_le.2 fun x hx => by show ‖f x‖ ≤ q ^ 1; rw [pow_one]; exact hqG x hx
    have hb' : ‖f b‖ ≤ q ^ 1 := hspan (hG.symm ▸ hb)
    show ‖f (a * b)‖ ≤ q ^ (k + 1)
    rw [map_mul, norm_mul, pow_succ]
    exact mul_le_mul ha' (by simpa using hb') (norm_nonneg _) (pow_nonneg hq0 k)

variable {W : Type} [CommRing W] [Algebra R W]

def normSub (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C) (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w) (c : ℝ)
    (hc : 0 ≤ c) : Submodule R W where
  carrier := {w | ‖Λ w‖ ≤ c}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp [hc]
  smul_mem' := fun r a ha => by
    simp only [Set.mem_setOf_eq] at *
    rw [hΛ, norm_mul]
    calc ‖f r‖ * ‖Λ a‖ ≤ 1 * c := mul_le_mul (hf r) ha (norm_nonneg _) zero_le_one
      _ = c := one_mul c

theorem bound_of_finite [Module.Finite R W] (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C)
    (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w) : ∃ B : ℝ, 0 ≤ B ∧ ∀ w, ‖Λ w‖ ≤ B := by
  classical
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := W)
  obtain ⟨B, hB0, hBT, -⟩ := exists_bound T (fun w => ‖Λ w‖)
  refine ⟨B, hB0, fun w => ?_⟩
  have h : (⊤ : Submodule R W) ≤ normSub f hf Λ hΛ B hB0 := hT ▸ Submodule.span_le.2 (fun x hx => hBT x hx)
  exact h Submodule.mem_top

theorem bound_pow (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C) (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w)
    {I : Ideal R} {q B : ℝ} (hq0 : 0 ≤ q) (hq : ∀ k : ℕ, ∀ a ∈ I ^ k, ‖f a‖ ≤ q ^ k) (hB : ∀ w, ‖Λ w‖ ≤ B)
    (e : ℕ) (x : W) (hx : x ∈ I.map (algebraMap R W) ^ e) : ‖Λ x‖ ≤ q ^ e * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [← Ideal.map_pow] at hx
  have hx' : x ∈ (I ^ e) • (⊤ : Submodule R W) := by
    rw [Ideal.smul_top_eq_map]; exact hx
  have hle : (I ^ e) • (⊤ : Submodule R W) ≤ normSub f hf Λ hΛ (q ^ e * B) (mul_nonneg (pow_nonneg hq0 e) hB0) :=
    Submodule.smul_le.2 fun a ha w _ => by
      show ‖Λ (a • w)‖ ≤ q ^ e * B
      rw [hΛ, norm_mul]
      exact mul_le_mul (hq e a ha) (hB w) (norm_nonneg _) (pow_nonneg hq0 e)
  exact hle hx'

theorem hasSum_of_adic (Λ : W →+ C) (J : Ideal W)
    (hbound : ∀ ε > 0, ∃ e : ℕ, ∀ x ∈ J ^ (e + 1), ‖Λ x‖ < ε) {X : Type} (s : W) (t : X → W)
    (hst : ∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ J ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ J ^ (e + 1)) :
    HasSum (fun α => Λ (t α)) (Λ s) := by
  classical
  change Filter.Tendsto (fun S : Finset X => ∑ b ∈ S, Λ (t b)) Filter.atTop (nhds (Λ s))
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨e, he⟩ := hbound ε hε
  obtain ⟨S, hS1, hS2⟩ := hst e
  refine ⟨S, fun S' hS' => ?_⟩
  have hmem : s - ∑ α ∈ S', t α ∈ J ^ (e + 1) := by
    have h : s - ∑ α ∈ S', t α = (s - ∑ α ∈ S, t α) - ∑ α ∈ S' \ S, t α := by
      rw [← Finset.sum_sdiff hS']; abel
    rw [h]
    exact sub_mem hS2 (sum_mem fun α hα => hS1 α (Finset.mem_sdiff.1 hα).2)
  rw [dist_eq_norm, ← map_sum, ← map_sub, ← norm_neg, ← map_neg, neg_sub]
  exact he _ hmem

end Norms

theorem converge : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (R : Type) [CommRing R] (I : Ideal R), I.FG → ∀ f : R →+* C, (∀ r, ‖f r‖ ≤ 1) → (∀ r ∈ I, ‖f r‖ < 1) → ∀ (W : Type) [CommRing W] [Algebra R W] [Module.Finite R W] (ρ : Type) [Fintype ρ] [DecidableEq ρ] (m : ℕ) (κ : W →+* Jet C ρ m), (∀ r, κ (algebraMap R W r) = algebraMap C (Jet C ρ m) (f r)) → ∀ (X : Type) (s : W) (t : X → W), (∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) → ∀ (u : Jet C ρ m) (g : X → MvPowerSeries ρ C), (∀ α, psJet m (g α) = u * κ (t α)) → (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → Summable fun α => MvPowerSeries.coeff n (g α)) ∧ ∀ g₀ : MvPowerSeries ρ C, (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → HasSum (fun α => MvPowerSeries.coeff n (g α)) (MvPowerSeries.coeff n g₀)) → psJet m g₀ = u * κ s := by
  intro C _ _ _ R _ I hI f hf1 hfI W _ _ _ ρ _ _ m κ hκ X s t hst u g hg
  obtain ⟨q, hq0, hq1, hq⟩ := norm_le_of_mem_pow f hI hf1 hfI
  have key : ∀ n : ρ →₀ ℕ, n.degree ≤ m →
      HasSum (fun α => MvPowerSeries.coeff n (g α)) (jetCoef n (u * κ s)) := by
    intro n hn
    let Λ : W →+ C := AddMonoidHom.mk' (fun w => jetCoef n (u * κ w)) (fun a b => by
      simp only [map_add, mul_add]; exact jetCoef_add hn _ _)
    have hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w := by
      intro r w
      show jetCoef n (u * κ (r • w)) = f r * jetCoef n (u * κ w)
      rw [Algebra.smul_def, map_mul, hκ, mul_left_comm, jetCoef_smul hn]
    obtain ⟨B, hB0, hB⟩ := bound_of_finite f hf1 Λ hΛ
    have hcoef : ∀ α, MvPowerSeries.coeff n (g α) = Λ (t α) := fun α => by
      rw [← jetCoef_psJet hn, hg α]; rfl
    have hbound : ∀ ε > 0, ∃ e : ℕ, ∀ x ∈ I.map (algebraMap R W) ^ (e + 1), ‖Λ x‖ < ε := by
      intro ε hε
      have hB1 : (0 : ℝ) < B + 1 := by linarith
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hB1) hq1
      refine ⟨k, fun x hx => ?_⟩
      calc ‖Λ x‖ ≤ q ^ (k + 1) * B := bound_pow f hf1 Λ hΛ hq0 hq hB (k + 1) x hx
        _ ≤ q ^ k * (B + 1) :=
          mul_le_mul (pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ k)) (by linarith) hB0 (pow_nonneg hq0 k)
        _ < ε / (B + 1) * (B + 1) := mul_lt_mul_of_pos_right hk hB1
        _ = ε := div_mul_cancel₀ _ (ne_of_gt hB1)
    have h := hasSum_of_adic Λ (I.map (algebraMap R W)) hbound s t hst
    simp only [← hcoef] at h
    exact h
  refine ⟨fun n hn => (key n hn).summable, fun g₀ hg₀ => jet_ext _ _ fun n hn => ?_⟩
  rw [jetCoef_psJet hn]
  exact (hg₀ n hn).unique (key n hn)

end GlobalTheory.AdicConverge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepAtlasPullback
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan ev_appLE ev_spMap_tau tau tau_le le_preimage_comp le_preimage_map le_preimage_mono)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
open GlobalTheory.LocM.MapComp GlobalTheory.LocM.CommonMod GlobalTheory.LocM.StepMono

namespace GlobalTheory.GrCl.RowCombination

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_comb {Z₁ Z B : Mdl Y i₀} {g : Z.X ⟶ B.X} (hg : IsMap Z B g) {X' : Scheme.{0}} {f : X' ⟶ Z.X}
    {ty' : (E →+* ℂ) → Finset ℕ} {A' : Atlas (Y Z.i) (f ≫ Z.π) ty'} {h : Z₁.X ⟶ X'} (hm : MapsTo Z₁ A' h)
    (hf : IsMap Z₁ Z (h ≫ f)) {σ : E →+* ℂ} {r : ℕ} (hr : r ∈ Z₁.ty σ) {K : Type} [Field K] {w : Sp K ⟶ Z₁.X}
    {v : Sp (DualNumber K) ⟶ B.t.G.left} (hs : InStep Z₁ B σ r w v) :
    ∃ (τ : (Y Z.i).X ⟶ (Y B.i).X) (mu : SABMap (Y Z.i).t (Y B.i).t τ)
      (u : TVecs Dw (Y Z.i).t (((w ≫ h) ≫ f) ≫ Z.π)) (cf : Fin (Dw.mult σ) → K),
      LocM.IsTrans B.i Z.i τ mu ∧ Set.range ((w ≫ h) ≫ f) ⊆ Z.opn ∧ A'.FlagAt (w ≫ h) (up u) ∧
        (∀ j : Fin (Dw.mult σ), r ≤ (j : ℕ) → cf j = 0) ∧
        v ≫ B.tMap.φ = (tv (∑ j, cf j • u σ j)).left ≫ mu.φ := by
  obtain ⟨τ₁, mu₁, u₁, i, t₁, fu₁, hi, hv⟩ := hs
  have hw := range_subset_opn Z₁ fu₁
  obtain ⟨τ, mu, u, t, e, fu, fu'⟩ := hm K w hw
  have hz : Set.range ((w ≫ h) ≫ f) ⊆ Z.opn := by
    rintro _ ⟨x, rfl⟩
    have := map_mem_opn hf (hw ⟨x, rfl⟩)
    simpa only [Scheme.Hom.comp_apply] using this
  obtain ⟨τ₀, mu₀, -, t₀, -⟩ := hg.2 K _ hz
  obtain ⟨mu', hmu'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₀ mu
  have t' := isTrans_comp hg.1.1 hf.1.1 t₀ t mu' hmu'
  obtain ⟨-, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ _ _ mu₁ mu' (hg.1.2.1.trans hf.1.2.1) t₁ t'
  obtain ⟨c, gu, gu₁, hsf⟩ := flagAt_two Z₁ fu fu₁
  obtain ⟨cf, hcf, hc⟩ := hsf σ r hr i hi
  have e' : (w ≫ Z₁.π) ≫ τ = ((w ≫ h) ≫ f) ≫ Z.π := by
    rw [Category.assoc, ← e]; simp only [Category.assoc]
  have hc' := comb_push mu hc
  rw [e'] at hc'
  obtain ⟨U, hU⟩ := exists_up (Dw := Dw) (u := fun σ j => u σ j ≫ mu.φ)
    fun σ j => isTan_push mu _ e' (gu.1 σ j).1
  have hcomb : tanOf (isTan_push mu _ e' (gu₁.1 σ i).1) = ∑ j, cf j • U σ j := by
    refine (isComb_iff (U σ) cf _).1 ?_
    have : (fun j => (tv (U σ j)).left) = fun j => u σ j ≫ mu.φ := congrFun hU σ
    rw [this]
    exact hc'
  obtain ⟨a, φ, ha, -⟩ := fu₁
  obtain ⟨y, hy, -⟩ := exists_lift_chart Z₁ ha
  refine ⟨τ₀, mu₀, U, cf, t₀, hz, hU ▸ fu', hcf, hv.trans ?_⟩
  rw [← hcomb, left_tanOf, hmu K y _ _ _ (by rw [hy]; exact (gu₁.1 σ i).1.1), hmu', Category.assoc]

theorem row_comb {K N : Type} [Field K] [AddCommGroup N] [Module K N] {m n r : ℕ} (hr : r ≤ m) (L : N →ₗ[K] (Fin n → K))
    (a : Fin n → K) (u : Fin m → N) (cf : Fin m → K) (hcf : ∀ j : Fin m, r ≤ (j : ℕ) → cf j = 0)
    (ha : ∀ l : Fin r, ∑ i, a i * L (u (Fin.castLE hr l)) i = 0) : ∑ i, a i * L (∑ j, cf j • u j) i = 0 := by
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ (j : ℕ)
  · simp [hcf j hj]
  · have := ha ⟨j, by omega⟩
    simp only [mul_left_comm _ (cf j), ← Finset.mul_sum]
    exact mul_eq_zero_of_right _ this

theorem holds_of_planar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → Planar D.Em f q → ∀ (Z₁ : Mdl Y i₀) (h : Z₁.X ⟶ X'), MapsTo Z₁ A' h → IsMap Z₁ Z (h ≫ f) → t.k ∈ Z₁.ty t.σ → t.Holds Z₁ := by
  intro E _ _ _ H Dw Xo p W Y i₀ _ _ t Z g D hg hL A X' f q ty' A' _ hG hP Z₁ h hm hf hk
  refine ⟨hk, (h ≫ f) ≫ g, isMap_comp hf hg, fun x => ?_⟩
  obtain ⟨U, -, α, a, hx, hUα, H₁⟩ := hP (h x)
  obtain ⟨V, m, hαV, hfr, H₂⟩ := hL α
  obtain ⟨_, ⟨U', hU', rfl⟩, hx', hle⟩ := Z₁.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((h ⁻¹ᵁ U : Z₁.X.Opens) : Set Z₁.X) from hx) (h ⁻¹ᵁ U).2
  have e : U' ≤ h ⁻¹ᵁ U := hle
  refine ⟨U', hU', V, _, m, Matrix.GeneralLinearGroup.map (h.appLE U U' e).hom a, hx',
    fun y hy => hαV (hUα (e hy)), hfr, fun K _ φ v hv hh hs j hj => ?_⟩
  have h₀ : ⊤ ≤ (spMap φ ≫ tau hU') ⁻¹ᵁ U' := le_preimage_comp _ (tau_le hU' le_rfl)
  have eφ := ev_spMap_tau hU' φ h₀
  change IsTanAtG t.B.t ((spMap φ ≫ tau hU') ≫ _) v at hv
  change InStep Z₁ t.B t.σ t.k (spMap φ ≫ tau hU') v at hs
  change ⊤ ≤ ((spMap φ ≫ tau hU') ≫ _) ⁻¹ᵁ V at hh
  change ∑ l, φ ((h.appLE U U' e).hom (a j l)) * tanEv t.B.t hv hh _ = 0
  generalize spMap φ ≫ tau hU' = w at h₀ eφ hv hs hh
  subst eφ
  have h₁ : ⊤ ≤ (w ≫ h) ⁻¹ᵁ U := le_preimage_map h e h₀
  have h₂ : ⊤ ≤ ((w ≫ h) ≫ f) ⁻¹ᵁ D.C.B α := le_preimage_map f hUα h₁
  obtain ⟨τ, mu, u, cf, tr, hz, fu, hcf, hvv⟩ := exists_comb hg hm hf hk hs
  have eq : w ≫ (h ≫ f) ≫ g = ((w ≫ h) ≫ f) ≫ g := by simp only [Category.assoc]
  obtain ⟨hv', hh', he⟩ := tanEv_congr t.B.t eq hv hh
  have key := row_comb t.le (D.crd α K _ h₂) (fun i => ev (w ≫ h) U h₁ (a j i)) (u t.σ) cf hcf
    fun l => H₁ K _ h₁ h₂ _ (((hG K _ u).1 fu).2 α h₂) l j hj
  refine (Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (ev_appLE w h e h₀ h₁ _) ?_).trans key
  exact (he _).trans (H₂ τ mu tr K _ h₂ hz _ v hv' hh' hvv l).symm

end GlobalTheory.GrCl.RowCombination
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_family_chart_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → ∃ Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ, (∀ b ∈ B, IsRiem Fu i (P b) (Hm b)) ∧ ∀ p q, ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  first | exact @GlobalTheory.RiemSmooth.exists_riem_contDiffOn | exact GlobalTheory.RiemSmooth.exists_riem_contDiffOn | (intros; apply GlobalTheory.RiemSmooth.exists_riem_contDiffOn <;> assumption)
end

