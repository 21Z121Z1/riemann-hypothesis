import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.appellHumbert_uniformisation_riemannForm : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ (∀ l, χ l = 1 ∨ χ l = -1) ∧ (∀ l m, χ (l + m) = χ l * χ m * (-1) ^ Ef l m) ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧ ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) := by
  first | exact @GlobalTheory.AnyAppellHumbert.isAH_properties | exact GlobalTheory.AnyAppellHumbert.isAH_properties | (intros; apply GlobalTheory.AnyAppellHumbert.isAH_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionOfDiagonalCMActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.determinantCondition_of_diagonalCMAction : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → (∀ (a : 𝓞 E) z, u.ex (fun i => ty i (a : E) * z i) = u.ex z ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), DetCond D act (spMap β) (β H.rt0) := by
  first | exact @GlobalTheory.detCond_of_diagonal_action | exact GlobalTheory.detCond_of_diagonal_action | (intros; apply GlobalTheory.detCond_of_diagonal_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PowerAdjoint

open GlobalTheory.CechPic

section Algebra

variable {M : Type} {V : Type 1} [AddCommGroup M] [AddCommGroup V] {n : Type} [Fintype n]

def form (B : M →+ M →+ V) (W : Matrix n n ℤ) (x y : n → M) : V := ∑ u, ∑ v, W u v • B (x u) (y v)

theorem form_left (B : M →+ M →+ V) (W m : Matrix n n ℤ) (x y : n → M) :
    form B W (fun u => ∑ v, m u v • x v) y = form B (m.transpose * W) x y := by
  have hL : form B W (fun u => ∑ v, m u v • x v) y = ∑ u, ∑ v, ∑ w, (W u v * m u w) • B (x w) (y v) := by
    simp [form, Finset.smul_sum, smul_smul, map_sum]
  have hR : form B (m.transpose * W) x y = ∑ w, ∑ v, ∑ u, (m u w * W u v) • B (x w) (y v) := by
    simp [form, Matrix.mul_apply, Finset.sum_smul]
  rw [hL, hR]
  calc ∑ u, ∑ v, ∑ w, (W u v * m u w) • B (x w) (y v)
      = ∑ u, ∑ w, ∑ v, (W u v * m u w) • B (x w) (y v) := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ w, ∑ u, ∑ v, (W u v * m u w) • B (x w) (y v) := Finset.sum_comm
    _ = ∑ w, ∑ v, ∑ u, (m u w * W u v) • B (x w) (y v) := Finset.sum_congr rfl fun _ _ => by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem form_right (B : M →+ M →+ V) (W m : Matrix n n ℤ) (x y : n → M) :
    form B W x (fun u => ∑ v, m u v • y v) = form B (W * m) x y := by
  have hL : form B W x (fun u => ∑ v, m u v • y v) = ∑ u, ∑ v, ∑ w, (W u v * m v w) • B (x u) (y w) := by
    simp [form, Finset.smul_sum, smul_smul, map_sum]
  have hR : form B (W * m) x y = ∑ u, ∑ w, ∑ v, (W u v * m v w) • B (x u) (y w) := by
    simp [form, Matrix.mul_apply, Finset.sum_smul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem form_polar (B : M →+ M →+ V) (hB : ∀ a b, B a b = B b a) (W : Matrix n n ℤ) (x y : n → M) :
    form B W (x + y) (x + y) - form B W x x - form B W y y + form B W 0 0 = form B (W + W.transpose) x y := by
  have hyx : ∑ u, ∑ v, W u v • B (y u) (x v) = ∑ u, ∑ v, W v u • B (x u) (y v) := by
    rw [Finset.sum_comm]
    simp only [hB (y _) (x _)]
  simp only [form, Pi.add_apply, Pi.zero_apply, map_add, map_zero, AddMonoidHom.add_apply,
    smul_add, smul_zero, Finset.sum_add_distrib, Finset.sum_const_zero, Matrix.add_apply, Matrix.transpose_apply, add_smul]
  rw [hyx]
  abel

end Algebra

section Square

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

omit [IsCommMonObj B] in

theorem exists_biadditive {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (T : Over S) (hb : ∀ x x' y : T ⟶ B, ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen) :
    ∃ β : Additive (T ⟶ B) →+ Additive (T ⟶ B) →+ Pic T.left, (∀ a b, β a b = β b a) ∧
      ∀ x y : T ⟶ B, β (.ofMul x) (.ofMul y) = pull (lift x y).left (cls P hP) := by
  have add1 : ∀ x x' y : T ⟶ B, pull (lift (x * x') y).left (cls P hP) =
      pull (lift x y).left (cls P hP) + pull (lift x' y).left (cls P hP) := by
    intro x x' y
    have h0 := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hb x x' y)
    rw [cls_linComb hP] at h0
    simp [Fin.sum_univ_three] at h0
    rw [← sub_eq_zero, ← h0]
    abel
  have e1 : cls P hP = pull (lift (snd B B) (fst B B)).left (cls P hP) := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP _).2 hs
  have hsym : ∀ x y : T ⟶ B, pull (lift y x).left (cls P hP) = pull (lift x y).left (cls P hP) := by
    intro x y
    have e2 : (lift y x).left ≫ (lift (snd B B) (fst B B)).left = (lift x y).left := by
      rw [← Over.comp_left]
      congr 1
      ext <;> simp
    calc pull (lift y x).left (cls P hP)
        = pull (lift y x).left (pull (lift (snd B B) (fst B B)).left (cls P hP)) := by rw [← e1]
      _ = pull (lift x y).left (cls P hP) := by rw [← pull_comp, e2]
  have add2 : ∀ x y y' : T ⟶ B, pull (lift x (y * y')).left (cls P hP) =
      pull (lift x y).left (cls P hP) + pull (lift x y').left (cls P hP) := by
    intro x y y'
    rw [hsym (y * y') x, add1, ← hsym y x, ← hsym y' x]
  refine ⟨AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => pull (lift a.toMul b.toMul).left (cls P hP))
    fun b b' => ?_) fun a a' => ?_, fun a b => ?_, fun x y => rfl⟩
  · rw [toMul_add]
    exact add2 _ _ _
  · ext b
    simp only [toMul_add]
    exact add1 _ _ _
  · exact (hsym a.toMul b.toMul).symm

theorem comp_prod_zpow {T T' : Over S} (ρ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) (k : Fin n → ℤ) :
    ρ ≫ (List.ofFn fun v => x v ^ k v).prod = (List.ofFn fun v => (ρ ≫ x v) ^ k v).prod := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => simp [List.ofFn_succ, MonObj.comp_mul, GrpObj.comp_zpow, ih]

theorem ofMul_comp_matrix {Q T : Over S} {n : ℕ} (pr : Fin n → (Q ⟶ B)) (m : Matrix (Fin n) (Fin n) ℤ) (α : Q ⟶ Q)
    (hα : ∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) (x : T ⟶ Q) :
    (fun u => Additive.ofMul ((x ≫ α) ≫ pr u)) = fun u => ∑ v, m u v • Additive.ofMul (x ≫ pr v) := by
  funext u
  rw [Category.assoc, hα u, comp_prod_zpow]
  simp [ofMul_list_prod, List.sum_ofFn, ofMul_zpow]

theorem exists_form {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (T : Over S) (hb : ∀ x x' y : T ⟶ B, ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen)
    {Q : Over S} [GrpObj Q] [IsCommMonObj Q] {n : Type} [Fintype n] (pr : n → (Q ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    {L : LB Q.left} (hL : L.IsLB) (W : Matrix n n ℤ)
    (hW : LBIso L (LB.LinComb P (K := n × n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2))) :
    ∃ β : Additive (T ⟶ B) →+ Additive (T ⟶ B) →+ Pic T.left,
      (∀ x : T ⟶ Q, pull x.left (cls L hL) =
        form β W (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (x ≫ pr u))) ∧
      ∀ (x y : T ⟶ Q) hh, cls (cubeLB Q ![x, y] L) hh =
        form β (W + W.transpose) (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (y ≫ pr u)) := by
  obtain ⟨β, hβs, hβ⟩ := exists_biadditive hP hs T hb
  have hpt : ∀ x : T ⟶ Q, pull x.left (cls L hL) =
      form β W (fun u => .ofMul (x ≫ pr u)) (fun u => .ofMul (x ≫ pr u)) := by
    intro x
    rw [(cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hW, cls_linComb hP, map_sum, Fintype.sum_prod_type]
    simp only [form]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hβ]
  refine ⟨β, hpt, fun x y hh => ?_⟩
  have hxy : (fun u => Additive.ofMul ((x * y) ≫ pr u)) =
      (fun u => Additive.ofMul (x ≫ pr u)) + fun u => Additive.ofMul (y ≫ pr u) := by
    funext u
    have := hpr u
    simp [MonObj.mul_comp]
  have h1 : (fun u => Additive.ofMul ((1 : T ⟶ Q) ≫ pr u)) = 0 := by
    funext u
    have := hpr u
    simp [MonObj.one_comp]
  rw [cls_cube_two hL x y hh, lam, hpt, hpt, hpt, hpt, hxy, h1]
  exact form_polar β hβs W _ _

theorem primitive_adjoint {P : LB (G2 B).left} (hP : P.IsLB) (hs : LBIso P (P.pull (lift (snd B B) (fst B B)).left))
    (hb : ∀ (T : Over S) (x x' y : T ⟶ B), ∃ t : LB.Gen (LB.LinComb P (K := Fin 3)
      ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen)
    {Q : Over S} [GrpObj Q] [IsCommMonObj Q] {n : ℕ} (pr : Fin n → (Q ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    {L : LB Q.left} (hL : L.IsLB) (W : Matrix (Fin n) (Fin n) ℤ)
    (hW : LBIso L (LB.LinComb P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W uv.1 uv.2)))
    (m : Matrix (Fin n) (Fin n) ℤ) (α : Q ⟶ Q) (hα : ∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) :
    ((W + W.transpose) * m = W → LBIso L (cubeLB Q ![𝟙 Q, α] L)) ∧
      ∀ (m' : Matrix (Fin n) (Fin n) ℤ) (α' : Q ⟶ Q), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) →
        m.transpose * (W + W.transpose) = (W + W.transpose) * m' →
        LBIso (cubeLB Q ![fst Q Q ≫ α, snd Q Q] L) (cubeLB Q ![fst Q Q, snd Q Q ≫ α'] L) := by
  refine ⟨fun hm => ?_, fun m' α' hα' hm' => ?_⟩
  · obtain ⟨β, hpt, hcube⟩ := exists_form hP hs Q (hb Q) pr hpr hL W hW
    have hc : (cubeLB Q ![𝟙 Q, α] L).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL hc).1 ?_
    have e0 := hpt (𝟙 Q)
    rw [Over.id_left, pull_id] at e0
    have hY := ofMul_comp_matrix pr m α hα (𝟙 Q)
    have hR := form_right β (W + W.transpose) m (fun u => Additive.ofMul (pr u)) (fun u => Additive.ofMul (pr u))
    simp only [Category.id_comp] at e0 hY
    rw [e0, hcube (𝟙 Q) α hc]
    simp only [Category.id_comp]
    rw [hY, hR, hm]
  · obtain ⟨β, -, hcube⟩ := exists_form hP hs (Q ⊗ Q) (hb (Q ⊗ Q)) pr hpr hL W hW
    have h1 : (cubeLB Q ![fst Q Q ≫ α, snd Q Q] L).IsLB := LB.isLB_linComb hL _ _
    have h2 : (cubeLB Q ![fst Q Q, snd Q Q ≫ α'] L).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff h1 h2).1 ?_
    have hl := form_left β (W + W.transpose) m (fun u => Additive.ofMul (fst Q Q ≫ pr u))
      (fun u => Additive.ofMul (snd Q Q ≫ pr u))
    have hr := form_right β (W + W.transpose) m' (fun u => Additive.ofMul (fst Q Q ≫ pr u))
      (fun u => Additive.ofMul (snd Q Q ≫ pr u))
    rw [hcube _ _ h1, hcube _ _ h2, ofMul_comp_matrix pr m α hα (fst Q Q), ofMul_comp_matrix pr m' α' hα' (snd Q Q), hl, hr, hm']

end Square

theorem matrix_primitive_adjoint : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → ∀ (m : Matrix (Fin 8) (Fin 8) ℤ) (α : P.A ⟶ P.A), (∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → ((W + W.transpose) * m = W → LBIso P.L (cubeLB P.A ![𝟙 P.A, α] P.L)) ∧ ∀ (m' : Matrix (Fin 8) (Fin 8) ℤ) (α' : P.A ⟶ P.A), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) → m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB P.A ![fst P.A P.A ≫ α, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ α'] P.L) := by
  intro hΘ W K _ o _ s h k ζ c P pr hpr huniv hW m α hα
  have : IsCommMonObj P.A := P.isAb.comm
  exact primitive_adjoint c.isLB c.symm
    (fun T x x' y => siegPre_bundle_mul_left hΘ K o s h k ζ c P pr hpr huniv T x x' y) pr hpr P.isLB W hW m α hα

end GlobalTheory.PowerAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam

theorem lbIso_pow_pull_square {B B' G G' : Scheme.{0}} {β : B' ⟶ B} {π : G' ⟶ G} {φ : B ⟶ G} {φ' : B' ⟶ G'}
    (h : φ' ≫ π = β ≫ φ) {P : LB G} {P' : LB G'} {M : LB B} {M' : LB B'} (hP : P.IsLB) (hP' : P'.IsLB)
    (hM : M.IsLB) (hM' : M'.IsLB) (eP : LBIso P' (P.pull π)) (eM : LBIso M' (M.pull β)) {n : ℕ}
    (hI : LBIso (lbPow M n) (P.pull φ)) : LBIso (lbPow M' n) (P'.pull φ') := by
  obtain ⟨w, hw⟩ := eP
  have e₁ : LBIso (P'.pull φ') (P.pull (φ' ≫ π)) :=
    iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => φ') (fun _ => 1)
  have e₂ : LBIso (P.pull (φ' ≫ π)) ((P.pull φ).pull β) :=
    LBIso.chartPull (chartPullSame P _ _ _ β fun _ => h) (chartPullPull _ β) (lbIso_refl (pull_isLB hP φ))
  have e₃ := LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂
  refine LBIso.trans (isLB_lbPow hM' _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP' _) ?_ e₃.symm
  exact LBIso.trans (isLB_lbPow hM' _) (isLB_lbPow (pull_isLB hM _) _) (pull_isLB (pull_isLB hP _) _)
    (lbIso_lbPow eM _) (LBIso.chartPull (chartPullPowPull M β _) (chartPullPull _ β) hI)

theorem KerSet.pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'} [GrpObj G] [GrpObj G']
    {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} (hβ : β ≫ B.hom = B'.hom ≫ f) (hπ : IsGrpPullback G' G f π)
    {ψ : B ⟶ G} {ψ' : B' ⟶ G'} (h : ψ'.left ≫ π = β ≫ ψ.left) {K : Set B.left} (hK : KerSet ψ K) :
    KerSet ψ' (β ⁻¹' K) := by
  intro k _ _ x z
  have e : pushHom hπ (Over.mk x) (z ≫ ψ') = pushPt hβ z ≫ ψ := Over.OverMorphism.ext (by
    show (z.left ≫ ψ'.left) ≫ π = (z.left ≫ β) ≫ ψ.left
    rw [Category.assoc, Category.assoc, h])
  have e₁ : z ≫ ψ' = 1 ↔ pushPt hβ z ≫ ψ = 1 := by
    rw [← e]
    refine ⟨fun q => by rw [q, map_one], fun q => PureType.eq_of_comp_eq hπ.1 ?_⟩
    exact congrArg (fun u => u.left) (q.trans (map_one (pushHom hπ (Over.mk x))).symm)
  refine e₁.trans ((hK k (x ≫ f) (pushPt hβ z)).trans ?_)
  show Set.range (z.left ≫ β) ⊆ K ↔ _
  simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]

theorem isog_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l p S S' s s' f o₁ o₂ o₁' o₂' n₁ n₂ ψ
  have c₁ := n₁.toSABMap.cart
  have c₂ := n₂.toSABMap.cart
  refine ⟨?_, fun ψ' h => ⟨?_, fun K _ hK => KerSet.pull c₁.1.w c₂ h hK⟩⟩
  · obtain ⟨ψ', h⟩ := PureType.exists_hom_over c₁.1.w c₂.1 ψ
    exact ⟨ψ', h, fun χ hχ => PureType.eq_of_comp_eq c₂.1 (hχ.trans h.symm)⟩
  rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩
  have sq : IsPullback n₁.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact c₁.1) h.symm c₂.1
  have lev : ∀ {u : 𝟙_ (Over S) ⟶ o₁.t.G} {v : 𝟙_ (Over S) ⟶ o₂.t.G} {u' : 𝟙_ (Over S') ⟶ o₁'.t.G}
      {v' : 𝟙_ (Over S') ⟶ o₂'.t.G}, u'.left ≫ n₁.toSABMap.φ = f ≫ u.left → v'.left ≫ n₂.toSABMap.φ = f ≫ v.left →
      u ≫ ψ = v → u' ≫ ψ' = v' := fun {u v u' v'} hu hv e => PureType.eq_of_comp_eq c₂.1 (by
    refine Eq.trans ?_ hv.symm
    rw [← e, Over.comp_left, Over.comp_left, Category.assoc]
    exact (congrArg (u'.left ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ψ.left) hu).trans (Category.assoc _ _ _))))
  refine ⟨⟨PureType.isMonHom_over c₁ c₂ h, MorphismProperty.of_isPullback (P := @IsFinite) sq h₂,
    MorphismProperty.of_isPullback (P := @Etale) sq h₃, MorphismProperty.of_isPullback (P := @Surjective) sq h₄,
    fun a => PureType.eq_of_comp_eq c₂.1 ?_, ?_⟩, fun p' hp a =>
    ⟨lev (n₁.eta _) (n₂.eta _) (h₇ p' hp a).1, lev (n₁.etaA _) (n₂.etaA _) (h₇ p' hp a).2⟩⟩
  · have e : (o₁.t.act.act a).left ≫ ψ.left = ψ.left ≫ (o₂.t.act.act a).left := congrArg (fun u => u.left) (h₅ a)
    have h' : ψ'.left ≫ n₂.cm.F = n₁.cm.F ≫ ψ.left := h
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, n₂.act, h', reassoc_of% h',
      reassoc_of% (n₁.act a), e]
  · exact lbIso_pow_pull_square h o₂.t.PP.isLB o₂'.t.PP.isLB o₁.t.PP.isLB o₁'.t.PP.isLB
      (n₂.lin.imp fun _ q => q.1) (n₁.lin.imp fun _ q => q.1) h₆

end GlobalTheory.HkFam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsKsMatrixOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KSField

section Linear
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} {g : ℕ}

theorem isCob_const_mul (q : Y ⟶ Sp K) (a : K) {c : C1 U} (h : IsCob U c) :
    IsCob U (fun i j => constFn q (U i ⊓ U j) a * c i j) := by
  have := isCob_lc q (g := 1) (fun _ => a) (fun _ => c) fun _ => h
  convert this using 1
  funext i j
  simp [lc]

theorem matrix_comb (q : Y ⟶ Sp K) {φ θ θ' θ'' : Fin g → C1 U} (hφ : ∀ c, IsCob U (lc q c φ) → c = 0)
    {Θ Θ' Θ'' : Matrix (Fin g) (Fin g) K} (c : K) (h : ∀ b, IsCob U (θ b - lc q (Θ b) φ))
    (h' : ∀ b, IsCob U (θ' b - lc q (Θ' b) φ)) (h'' : ∀ b, IsCob U (θ'' b - lc q (Θ'' b) φ))
    (e : ∀ a, IsCob U (fun i j => θ'' a i j - constFn q _ c * θ a i j - θ' a i j)) : Θ'' = c • Θ + Θ' := by
  rw [← sub_eq_zero]
  funext b
  refine hφ _ ?_
  convert (((e b).sub (h'' b)).add (isCob_const_mul q c (h b))).add (h' b) using 1
  funext i j
  have : ∀ a, constFn q (U i ⊓ U j) ((Θ'' - (c • Θ + Θ')) b a) = constFn q (U i ⊓ U j) (Θ'' b a) -
      (constFn q (U i ⊓ U j) c * constFn q (U i ⊓ U j) (Θ b a) + constFn q (U i ⊓ U j) (Θ' b a)) := fun a => by
    simp [constFn]
  simp only [lc, Pi.add_apply, Pi.sub_apply, this, sub_mul, add_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum, _root_.mul_assoc]
  ring

end Linear

def linearOfComb {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V → W)
    (h : ∀ (c : K) x y, f (c • x + y) = c • f x + f y) : V →ₗ[K] W where
  toFun := f
  map_add' x y := by simpa using h 1 x y
  map_smul' c x := by
    have h0 : f 0 = 0 := by simpa using h 1 0 0
    simpa [h0] using h c x 0

theorem lbIso_cube_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {s : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) {f f' : G ⟶ G} {f₀ f₀' : G' ⟶ G'}
    (hf : f₀.left ≫ φ = φ ≫ f.left) (hf' : f₀'.left ≫ φ = φ ≫ f'.left)
    (H : LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ f'] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ f₀, snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ f₀'] L') := by
  obtain ⟨w, hw⟩ := e
  have pa : ∀ {a : G ⟶ G} {a₀ : G' ⟶ G'}, a₀.left ≫ φ = φ ≫ a.left → ∀ {T : Over S'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ a₀) = pushPt h.1.w x ≫ a := fun ha _ x => Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have M : LBIso (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G' ≫ f₀, snd G' G'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card))
      (L.LinComb (fun I : ULift (Finset (Fin 2)) => (psum G' ![fst G' G', snd G' G' ≫ f₀'] I.down).left ≫ φ)
        fun I => (-1) ^ (2 - I.down.card)) := by
    refine LBIso.chartPull (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullSame L _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    · fin_cases i
      · exact (pa hf _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa hf' _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
    (iso_linComb ((isGen_iff w).1 hw) _ _)
    (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) M
      (iso_linComb ((isGen_iff w).1 hw) _ _).symm)

theorem isDerK_snd {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    IsDerK (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom (fun x => lam x.snd) := by
  refine ⟨fun a b => by simp, fun a b => ?_⟩
  simp [TrivSqZeroExt.snd_mul]

theorem spMap_fst_dirMap {K : Type} [Field K] {r : ℕ} (lam : (Fin r → K) →ₗ[K] K) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap lam) =
      spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dirMap]

theorem exists_ksMatrix_of
    (href : ∀ (X : Scheme.{0}) (L : LB X), CompactSpace X → L.IsLB → ∃ L' : LB X, Finite L'.ι ∧ L'.IsLB ∧ (∀ i, IsAffineOpen (L'.U i)) ∧ LBIso L L')
    (hinv : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd)
    (hphi : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (X : Scheme.{0}) (m : P₀.A.left ⟶ X) (L : LB X), L.IsLB → LBIso P₀.L (L.pull m) → (∃ φ, IsDlog m L dd φ) ∧ ∀ φ, IsDlog m L dd φ → (∀ a, IsCoc _ (φ a)) ∧ ∀ c, IsCob _ (lc P₀.A.hom c φ) → c = 0)
    (hcoc : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → Smooth p → ∀ (D : R → K) (I : Type) (W : I → X.Opens), IsDerK x₀ D → (∀ i, IsAffineOpen (W i)) → ∃ d θ, KSCoc A₀.hom p m D W dd d θ ∧ ∀ a, IsCoc _ (θ a))
    (hlin : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j))
    (hsym : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ))
    (hend : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose)
    (hzero : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁)
    (htriv : Out.Laws → ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (R : Type) [CommRing R] (xD : R →+* DualNumber K) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (ψ : A'.left ⟶ A.left) (j : A₀.left ⟶ A'.left) (d : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, (j ≫ ψ) ⁻¹ᵁ W)), IsAbelianScheme A₀ → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) ψ → IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j → LocDerK A₀.hom A.hom (j ≫ ψ) (fun r => (xD r).snd) ⊤ d → ∃ ρ, IsConstK A' A₀ ρ j) :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (P : Out.PolAV (Sp (TrivSqZeroExt K (Fin r → K)))) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ P.A.left) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom) φ₀ → LBIso P₀.L (P.L.pull φ₀) → IsLieBasis v → ∃ Θ : ((Fin r → K) →ₗ[K] K) →ₗ[K] Matrix (Fin g) (Fin g) K, (∀ lam, (Θ lam).IsSymm) ∧ (∀ (f f' : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), IsMonHom f → IsMonHom f' → f₀.left ≫ φ₀ = φ₀ ≫ f.left → f₀'.left ≫ φ₀ = φ₀ ≫ f'.left → LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → ∀ lam, F * Θ lam = Θ lam * F'.transpose) ∧ ∀ lam, Θ lam = 0 → ∀ (G : Over (Sp (DualNumber K))) [GrpObj G] (ψ : G.left ⟶ P.A.left), IsGrpPullback G P.A (spMap (dirMap lam)) ψ → ∃ ψ₀ : G.left ⟶ P₀.A.left, IsGrpPullback G P₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ ∧ ∀ io : P₀.A.left ⟶ G.left, io ≫ ψ = φ₀ → io ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom → io ≫ ψ₀ = 𝟙 _ := by
  intro hL hL2 hC K _ _ r P P₀ φ₀ g v hp hI hv
  have hc : CompactSpace P.A.left := by
    have := P.isAb.proper
    exact QuasiCompact.compactSpace_of_compactSpace P.A.hom
  obtain ⟨L, hfin, hLB, haff, hiso⟩ := href _ P.L hc P.isLB
  have hI' : LBIso P₀.L (L.pull φ₀) := LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB hLB _) hI
    (hiso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl))
  choose dd hdd using fun a => (hinv K P₀.A (v a) (hv.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := hphi K P₀ g v dd hv hdd _ φ₀ L hLB hI'
  have hind := (hφ' φ hφ).2
  choose d θ hks _ using fun lam : (Fin r → K) →ₗ[K] K =>
    hcoc K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 P.isAb.smooth _ L.ι L.U (isDerK_snd lam) haff
  choose Θ hΘ hΘ' using fun lam : (Fin r → K) →ₗ[K] K =>
    hsym hL hL2 hC K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ
  refine ⟨linearOfComb Θ fun c x y => matrix_comb P₀.A.hom hind c (hΘ' x) (hΘ' y) (hΘ' _)
    (hlin K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ c _ _ _ _ _ _ (hks x) (hks y)
      (hks (c • x + y))), hΘ, fun f f' f₀ f₀' F F' hf hf' e e' H hF hF' lam => ?_, fun lam h0 G _ ψ hψ => ?_⟩
  · exact hend K P₀ g v dd hv hdd _ _ P φ₀ L _ (d lam) (θ lam) φ hp hLB haff hI' (hks lam) hφ (Θ lam) f f₀ f₀' F F'
      (hΘ' lam) (PureType.isMonHom_over hp hp e) (PureType.isMonHom_over hp hp e') e
      (lbIso_cube_pull hp P.isLB P₀.isLB hI e e' H) hF hF'
  · have h0' : Θ lam = 0 := h0
    have hcob : ∀ a, IsCob _ (θ lam a) := fun a => by
      convert hΘ' lam a using 1
      funext i j
      simp [h0', lc, constFn]
    obtain ⟨d₁, hd₁⟩ := hzero K P₀.A g v dd P₀.isAb.smooth hv hdd _ _ _ P.A.hom φ₀ hp.1 L.ι L.U _ _ _ hLB.cover
      (hks lam) hcob
    have w : φ₀ ≫ P.A.hom = (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap (dirMap lam) := by
      rw [Category.assoc, spMap_fst_dirMap, hp.1.w]
    obtain ⟨j, hj, hj'⟩ : ∃ j : P₀.A.left ⟶ G.left, j ≫ ψ = φ₀ ∧
        j ≫ G.hom = P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom :=
      ⟨hψ.1.lift _ _ w, hψ.1.lift_fst _ _ w, hψ.1.lift_snd _ _ w⟩
    have hD : (fun x : TrivSqZeroExt K (Fin r → K) => (dirMap lam x).snd) = fun x => lam x.snd :=
      funext fun x => TrivSqZeroExt.snd_map lam x
    obtain ⟨d₂, hd₂⟩ : ∃ d₂, LocDerK P₀.A.hom P.A.hom (j ≫ ψ) (fun x => (dirMap lam x).snd) ⊤ d₂ := by
      rw [hj, hD]
      exact ⟨d₁, hd₁⟩
    obtain ⟨ρ, hρ, -, hρ'⟩ := htriv hL K P₀.A _ (dirMap lam) P.A G ψ j d₂ P₀.isAb
      (PolPull.isAbelianScheme_of_isGrpPullback P.isAb hψ) hψ
      (hψ.cancel (hp.congr (spMap_fst_dirMap lam).symm hj.symm) hj') hd₂
    refine ⟨ρ, hρ, fun io h₁ h₂ => ?_⟩
    rw [hψ.1.hom_ext (h₁.trans hj.symm) (h₂.trans hj'.symm), hρ']

end GlobalTheory.KSField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalPeriodLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_local_period_lift :
    ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g → ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range) ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀ a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a))) :=
  fun hT hL => GlobalTheory.T.holomorphic_map_moduli_lifts_locally_to_periods hT hL isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
    obj_isAbelianScheme_dim_rigidified_sym obj_pull RelExp.exists_relative_exp latContinuation
    holomorphic_diagonalisation (torsion_eq_and_weilIs_of_isHolTo hL)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOActOfMapLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_oAct_of_endo_preserving_lattice : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (O : Type) [CommRing O] (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (r : O →+* Module.End ℂ (Fin P.g → ℂ)), (∀ a, ∀ z ∈ u.Λ, r a z ∈ u.Λ) → ∃ act : OAct O P.A, ∀ a z, u.ex (r a z) = u.ex z ≫ act.act a := by
  first | exact @GlobalTheory.exists_oAct_of_map_lattice | exact GlobalTheory.exists_oAct_of_map_lattice | (intros; apply GlobalTheory.exists_oAct_of_map_lattice <;> assumption)
end

