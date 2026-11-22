import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0115
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitiveOfLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBaseStatement

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOActOfMapLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem isMonHom_mul_of_isCommMonObj {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) where
  one_hom := by
    rw [Hom.mul_def]
    exact IsMonHom.one_hom _
  mul_hom := by
    rw [Hom.mul_def]
    exact IsMonHom.mul_hom _

theorem exists_oAct_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (O : Type) [CommRing O] (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (r : O →+* Module.End ℂ (Fin P.g → ℂ)), (∀ a, ∀ z ∈ u.Λ, r a z ∈ u.Λ) → ∃ act : OAct O P.A, ∀ a z, u.ex (r a z) = u.ex z ≫ act.act a := by
  intro hL hL2 hGen hTh O _ P u r hr

  have key : ∀ a, ∃! f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (r a z) = u.ex z ≫ f := fun a =>
    existsUnique_isMonHom_of_map_lattice hL hL2 hGen hTh P P P.L P.L u u (r a) (hr a)
  choose act hact huniq using key
  have eq_of : ∀ a (h : P.A ⟶ P.A), IsMonHom h → (∀ z, u.ex (r a z) = u.ex z ≫ h) → h = act a :=
    fun a h h1 h2 => huniq a h ⟨h1, h2⟩
  have hom : ∀ a, IsMonHom (act a) := fun a => (hact a).1
  refine ⟨⟨act, hom, ?_, ?_, ?_⟩, fun a z => (hact a).2 z⟩
  · refine (eq_of 1 (𝟙 _) inferInstance ?_).symm
    intro z
    simp
  · intro a b
    refine (eq_of (a * b) (act a ≫ act b) inferInstance ?_).symm
    intro z
    rw [mul_comm a b, map_mul, Module.End.mul_apply, (hact b).2, (hact a).2, Category.assoc]
  · intro a b
    have := hom a
    have := hom b
    refine (eq_of (a + b) (act a * act b) (isMonHom_mul_of_isCommMonObj _ _) ?_).symm
    intro z

    rw [map_add, LinearMap.add_apply, u.2, (hact a).2, (hact b).2, MonObj.comp_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_of_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₀)) ⟶ A₀)), s = spMap i ≫ s₀ → IsGrpPullback c.A A₀ (spMap i) φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∀ u, (c.lev (Pi.single u 1)).left ≫ φ = spMap i ≫ (lev₀ u).left) → ∃ c₀ : SiegPre h M ζ s₀, SiegPB c c₀ (spMap i) := by
  first | exact @GlobalTheory.exists_siegPre_of_descended_data | exact GlobalTheory.exists_siegPre_of_descended_data | (intros; apply GlobalTheory.exists_siegPre_of_descended_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmetricBiadditiveBundleEighthPower
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EighthPower

open GlobalTheory.CechPic Matrix

theorem map_prod_add {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) : f (∏ i, x i) = ∑ i, f (x i) := by
  simpa only [zpow_one, one_smul] using GlobalTheory.BilinCalc.map_prod_zpow f hf x fun _ => 1

theorem map_zpow_add {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    (x : G) (c : ℤ) : f (x ^ c) = c • f x := by
  simpa only [Fin.prod_univ_one, Fin.sum_univ_one] using
    GlobalTheory.BilinCalc.map_prod_zpow f hf (n := 1) (fun _ => x) fun _ => c

section Points

variable {S : Scheme.{0}} {G A T T' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem comp_prod_zpow (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A)) (c : Fin n → ℤ) :
    h ≫ (∏ i, x i ^ c i) = ∏ i, (h ≫ x i) ^ c i := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (fun z => h ≫ z) fun a b => MonObj.comp_mul _ _ _
  have e : F (∏ i, x i ^ c i) = ∏ i, F (x i) ^ c i := by simp only [map_prod, map_zpow]
  exact e

theorem prod_comp_hom (f : G ⟶ A) [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ G)) :
    (∏ i, x i) ≫ f = ∏ i, x i ≫ f := by
  let F : (T ⟶ G) →* (T ⟶ A) := MonoidHom.mk' (fun z => z ≫ f) fun a b => MonObj.mul_comp _ _ _
  exact map_prod F x _

omit [IsCommMonObj A] in
theorem comp_id_zpow (x : T ⟶ A) (c : ℤ) : x ≫ (𝟙 A ^ c) = x ^ c := by
  let F : (A ⟶ A) →* (T ⟶ A) := MonoidHom.mk' (fun z => x ≫ z) fun a b => MonObj.comp_mul _ _ _
  have e : F (𝟙 A ^ c) = F (𝟙 A) ^ c := map_zpow F _ _
  exact e.trans (congrArg (· ^ c) (Category.comp_id x))

end Points

theorem prod_zpow_eq {H : Type*} [CommGroup H] (x : H) {n : ℕ} (c : Fin n → ℤ) : ∏ i, x ^ c i = x ^ ∑ i, c i := by
  have h := map_prod (zpowersHom H x) (fun i => Multiplicative.ofAdd (c i)) Finset.univ
  simp only [zpowersHom_apply, toAdd_prod, toAdd_ofAdd] at h
  exact h.symm

theorem main : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsE8 W → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → (∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB G ![fst G G ≫ ρ m, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ ρ m'] L)) → (∀ m, (W + W.transpose) * m = W → LBIso L (cubeLB G ![𝟙 G, ρ m] L)) → ∃ P : LB (G2 A).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) ∧ LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro W S G A _ _ _ _ pr L ρ hE hpr huniv hL hΘ hρ hadj hprim
  obtain ⟨B, hB⟩ : ∃ B, B = W + W.transpose := ⟨_, rfl⟩
  have hdet : IsUnit B.det := by rw [hB, hE.2]; exact isUnit_one
  have hBs : B.transpose = B := by rw [hB, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  rw [← hB] at hadj hprim
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Fin 8 → ℤ, u₀ = Pi.single 0 1 := ⟨_, rfl⟩
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Fin 8 → ℤ, B *ᵥ u₁ = u₀ := ⟨B⁻¹ *ᵥ u₀, by rw [Matrix.mulVec_mulVec, hBi, Matrix.one_mulVec]⟩
  have h00 : u₀ ⬝ᵥ u₀ = 1 := by rw [hu₀]; simp
  have hsymB : ∀ v v' : Fin 8 → ℤ, v ⬝ᵥ B *ᵥ v' = v' ⬝ᵥ B *ᵥ v := fun v v' => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBs, dotProduct_comm]
  have ext : ∀ {T : Over S} (x x' : T ⟶ G), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' := fun {T} x x' h =>
    (huniv T fun u => x' ≫ pr u).unique h fun _ => rfl
  choose ψ hψ using fun v : Fin 8 → ℤ => (huniv A fun u => 𝟙 A ^ v u).exists
  have hψ' : ∀ {T : Over S} (x : T ⟶ A) v u, (x ≫ ψ v) ≫ pr u = x ^ v u := fun x v u => by
    rw [Category.assoc, hψ, comp_id_zpow]
  have ψmul : ∀ {T : Over S} (x y : T ⟶ A) v, (x * y) ≫ ψ v = (x ≫ ψ v) * (y ≫ ψ v) := fun x y v =>
    ext _ _ fun u => by rw [hψ', MonObj.mul_comp, hψ', hψ', _root_.mul_zpow]
  have ψone : ∀ {T : Over S} v, (1 : T ⟶ A) ≫ ψ v = 1 := fun v =>
    ext _ _ fun u => by rw [hψ', MonObj.one_comp, _root_.one_zpow]
  have ψsmul : ∀ {T : Over S} (x : T ⟶ A) (c : ℤ) v, x ≫ ψ (c • v) = (x ^ c) ≫ ψ v := fun x c v =>
    ext _ _ fun u => by rw [hψ', hψ', ← _root_.zpow_mul, Pi.smul_apply, smul_eq_mul]
  have ψρ : ∀ {T : Over S} (x : T ⟶ A) v m, (x ≫ ψ v) ≫ ρ m = x ≫ ψ (m *ᵥ v) := fun x v m =>
    ext _ _ fun u => by
      rw [hψ', Category.assoc, hρ, List.prod_ofFn, comp_prod_zpow]
      simp only [hψ', ← _root_.zpow_mul, prod_zpow_eq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have ρdec : ∀ m, ρ m = ∏ v, pr v ≫ ψ (m *ᵥ Pi.single v 1) := fun m =>
    ext _ _ fun u => by
      rw [hρ, List.prod_ofFn, prod_comp_hom]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hψ']
      simp
  have iddec : 𝟙 G = ∏ v, pr v ≫ ψ (Pi.single v 1) :=
    ext _ _ fun u => by
      rw [Category.id_comp, prod_comp_hom, Finset.prod_eq_single u (fun b _ hb => by
        rw [hψ', Pi.single_eq_of_ne' hb, zpow_zero]) (by simp), hψ', Pi.single_eq_same, zpow_one]
  have lamL := fun {T : Over S} (x y z : T ⟶ G) => lam_mul_left hL hΘ x y z
  obtain ⟨l, hl⟩ : ∃ l, l = cls L hL := ⟨_, rfl⟩
  rw [← hl] at lamL
  have lamR : ∀ {T : Over S} (x y z : T ⟶ G), lam l z (x * y) = lam l z x + lam l z y := fun x y z => by
    rw [lam_comm, lamL, lam_comm l x, lam_comm l y]
  have adj : ∀ {T : Over S} (x y : T ⟶ G) m m', m.transpose * B = B * m' →
      lam l (x ≫ ρ m) y = lam l x (y ≫ ρ m') := by
    intro T x y m m' hm
    have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj m m' hm)
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, ← hl] using h'
  obtain ⟨p, hp⟩ : ∃ p : ∀ {T : Over S}, (T ⟶ A) → (T ⟶ A) → Pic T.left,
      ∀ {T : Over S} (x y : T ⟶ A), p x y = lam l (x ≫ ψ u₀) (y ≫ ψ u₁) := ⟨_, fun _ _ => rfl⟩
  have pL : ∀ {T : Over S} (x x' y : T ⟶ A), p (x * x') y = p x y + p x' y := fun x x' y => by
    rw [hp, hp, hp, ψmul, lamL]
  have pR : ∀ {T : Over S} (x x' y : T ⟶ A), p y (x * x') = p y x + p y x' := fun x x' y => by
    rw [hp, hp, hp, ψmul, lamR]
  have key : ∀ {T : Over S} (x y : T ⟶ A) v v', lam l (x ≫ ψ v) (y ≫ ψ v') = (v ⬝ᵥ B *ᵥ v') • p x y := by
    intro T x y v v'
    have h := adj (x ≫ ψ u₀) (y ≫ ψ v') (vecMulVec v u₀) (vecMulVec u₁ (B *ᵥ v)) (by
      rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, hu₁, ← Matrix.mulVec_transpose, hBs])
    have e₁ : vecMulVec v u₀ *ᵥ u₀ = v := by
      rw [Matrix.vecMulVec_mulVec, h00]; simp
    have e₂ : vecMulVec u₁ (B *ᵥ v) *ᵥ v' = (v ⬝ᵥ B *ᵥ v') • u₁ := by
      rw [Matrix.vecMulVec_mulVec, dotProduct_comm, hsymB v' v]; simp
    rw [ψρ, ψρ, e₁, e₂, ψsmul, ← hp] at h
    rw [h]
    exact map_zpow_add (fun z => p x z) (fun a b => pR a b x) y _
  have pS : ∀ {T : Over S} (x y : T ⟶ A), p y x = p x y := fun x y => by
    rw [hp, lam_comm, key, hsymB, hu₁, h00, one_smul]
  have hP : (cubeLB G ![fst A A ≫ ψ u₀, snd A A ≫ ψ u₁] L).IsLB := LB.isLB_linComb hL _ _
  have hc : cls _ hP = p (fst A A) (snd A A) := by rw [cls_cube_two hL, hp, hl]
  have hpull : ∀ {T : Over S} (x y : T ⟶ A), pull (lift x y).left (cls _ hP) = p x y := fun x y => by
    rw [hc, hp, hp, pull_lam, lift_fst_assoc, lift_snd_assoc]
  refine ⟨cubeLB G ![fst A A ≫ ψ u₀, snd A A ≫ ψ u₁] L, hP, ?_, ?_, ?_, fun T x x' y => ⟨?_, ?_⟩, ?_⟩
  · refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hp, ψone, lam_one_left]
  · refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hp, ψone, lam_one_right]
  · refine (cls_eq_iff hP (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hc, pS]
  · refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, hpull, pL]
    abel
  · refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, hpull, pR]
    abel
  · refine (cls_eq_iff hL (LB.isLB_linComb hP _ _)).1 ?_
    have hw : B * (B⁻¹ * W) = W := by rw [← Matrix.mul_assoc, hBi, Matrix.one_mul]
    have h := ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 (hprim _ hw)).trans (cls_cube_two hL _ _ _)
    rw [cls_linComb hP, h, ← hl, Fintype.sum_prod_type, iddec, ρdec,
      map_prod_add (fun z => lam l z _) (fun a b => lamL a b _)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_prod_add (fun z => lam l _ z) (fun a b => lamR a b _)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [key, hpull, Matrix.mulVec_mulVec, hw]
    congr 1
    simp

end GlobalTheory.EighthPower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueIsMonHomOfLinearMapLatticeAnyDimStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)), (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃! f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  first | exact @GlobalTheory.existsUnique_isMonHom_of_map_lattice | exact GlobalTheory.existsUnique_isMonHom_of_map_lattice | (intros; apply GlobalTheory.existsUnique_isMonHom_of_map_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isThetaPtOver_pull_of_gen {n : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P n x v) (h : T' ⟶ T)
    (hg : ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 h th)) :
    IsThetaPtOver P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    hL hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨τ', hτ', k₂⟩ := exists_gen_pullTo (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) τ hτ h.left
    (fun _ => by rw [← Over.comp_left, MonObj.comp_one])
  choose U' hU' k₃ using fun a => exists_symLift_act_pull hL h (hU a)
  refine ⟨_, _, α', τ', U', fun a => pullS P.A _ h (s₂ a), fun a => h.left.appTop.hom (w a),
    Units.map h.left.appTop.hom.toMonoidHom u, hg _ hth, hα', hτ', k₁ _ _ hs₁, hU',
    fun a => k₃ a _ _ (hs₂ a), fun a => isValueAt_of_sv hL hτ' fun z J hJ => ?_, fun a => ?_⟩
  · have q := sv_of_isValueAt (hw a) h hJ
    rw [MonObj.comp_one] at q
    rw [sv_pullS _ _ _ _ _ z hJ, ← Over.comp_left, lift_whiskerRight, Category.id_comp, q, k₂ _ _ z J hJ,
      Category.id_comp]
    exact congrArg (· * _) ((gs_pull (𝟙 _) h.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  · exact (congrArg h.left.appTop.hom (hv a)).trans (map_mul _ _ _)

theorem exists_basicOpen_isGenSec (hS : SecBaseChangeAnySt) [IsAffine T.left] (V : T.left.Opens) (p : T.left)
    (hp : p ∈ V) : ∃ f : Γ(T.left, ⊤), p ∈ T.left.basicOpen f ∧
      ∃ j : overRes (T.left.basicOpen f) ⟶ overRes V, j ≫ overResι V = overResι _ ∧
        ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 j th) := by
  obtain ⟨V₀, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := V ⊓ T.hom ⁻¹ᵁ V₀) ⟨p, hp, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V₀ := Over.homMk
    (IsOpenImmersion.lift V₀.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact (hf y.2).2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hle : W ≤ V := hf.trans inf_le_left
  let j : overRes W ⟶ overRes V := Over.homMk (T.left.homOfLE hle) (by
    change T.left.homOfLE hle ≫ V.ι ≫ T.hom = W.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hj : j ≫ overResι V = overResι W := Over.OverMorphism.ext (T.left.homOfLE_ι hle)
  refine ⟨f, hpf, j, hj, fun th H s => ?_⟩
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := EmbPull.exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (pullS P.A 1 (overResι V) (SecM.toSec P.A u))
  have hr' : pullM P.A P.L 1 (overResι V) u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have e₁ := congrArg (pullM P.A P.L 1 j) hr'
  rw [pullM_comp _ P.isLB, hj, hu, LinearMap.map_smulₛₗ] at e₁
  obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W).left, ⊤), SecM.ofSec P.A s =
      d • pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)) := by
    have := c.sum_repr (SecM.ofSec P.A s)
    rw [Fintype.sum_unique, hc] at this
    exact ⟨_, this.symm⟩
  have hf₁ : IsUnit (W.ι.appTop.hom f) := by
    refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ => ?_
    refine (Scheme.mem_basicOpen_top _ _ y).1 ?_
    rw [← Scheme.preimage_basicOpen_top]
    exact y.2
  obtain ⟨a, ha⟩ : IsUnit ((overResι W).left.appTop.hom (f ^ n)) := by
    rw [map_pow]
    exact hf₁.pow n
  have key : SecM.ofSec P.A s = (d * (a⁻¹ : Γ((overRes W).left, ⊤)ˣ) * j.left.appTop.hom r) •
      pullM P.A P.L 1 j (SecM.ofSec P.A th) := by
    rw [mul_smul, ← e₁, ← ha, ← mul_smul, Units.inv_mul_cancel_right, hd]
  exact ⟨_, fun i => congrArg (fun q => q.1 i) key⟩

theorem isThetaPt_pull (hS : SecBaseChangeAnySt) [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T) {n : ℕ} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P n x v) :
    IsThetaPt P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  obtain ⟨h₁, h₂, H⟩ := H
  refine ⟨h₁, by simpa using h₂.map h.left.appTop.hom, fun p => ?_⟩
  obtain ⟨V, hV, H⟩ := H (h.left p)
  obtain ⟨f, hf, j, hj, hg⟩ := exists_basicOpen_isGenSec P hS V _ hV
  let f' := h.left.appTop.hom f
  have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
  let W := T.left.basicOpen f
  let W' := T'.left.basicOpen f'
  let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf'.ge y.2)
  have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
  let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
    change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
    rw [← Category.assoc, hk₀, Category.assoc, Over.w])
  have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
  have : IsAffine (overRes W).left := hW
  have : IsAffine (overRes W').left := hW'
  have Q := isThetaPtOver_pull_of_gen P (isThetaPtOver_pull_of_gen P H j hg) k
    fun _ => EmbPull.isGenSec_pullS P hS k
  have e : k ≫ j ≫ overResι V = overResι W' ≫ h := by rw [hj]; exact hk
  refine ⟨W', hf'.le hf, ?_⟩
  convert Q using 2 with a a
  · rw [← Category.assoc, ← e]
    simp only [Category.assoc]
  · exact (congrArg (fun q => q.left.appTop.hom (v a)) e).symm

end GlobalTheory.ThetaBaseChange

theorem GlobalTheory.hasTh_baseChange : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh (spMap φ ≫ x) (fun a => φ (v a)) := by
  intro hl o _ g N' J b S s t R R' _ _ φ x v H
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap φ ≫ x)).left := inferInstanceAs (IsAffine (Spec _))
  have Q := GlobalTheory.ThetaBaseChange.isThetaPt_pull t.pol hl.secBaseChangeAny
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) H
  unfold TObj.HasTh
  convert Q using 2 with a a
  · exact Over.OverMorphism.ext (Category.assoc (spMap φ) x (t.lab a).left)
  · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckePointsOfParts
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_transfer
    (hW : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c))
    {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} (u : Obj D l b sX) {k : Type} [Field k]
    {s : Sp k ⟶ Sp B} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c => hW _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, m.cart.1.isoPullback_hom_snd, fun x => ?_, fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

theorem fibPt_injective {X : Scheme.{0}} (G : Over X) {k : Type} [Field k] {y : Sp k ⟶ X} :
    Function.Injective (fibPt G (y := y)) := fun a b h => Over.OverMorphism.ext (by
  have := congrArg (· ≫ pullback.fst G.hom y) h
  simpa only [fibPt, pullback.lift_fst] using this)

end GlobalTheory.HeckePoint

namespace GlobalTheory

open HeckePoint

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitutionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.lineBundleIso_linComb_symm_biadditive_substitution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.BilinCalc.main | exact GlobalTheory.BilinCalc.main | (intros; apply GlobalTheory.BilinCalc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_pull :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) :=
  ObjPull.objPull_of_lie_of_ample LiePull.lieMult_pull
    (PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem pol_pull :
    ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L') :=
  PolPull.pol_pull_of_relAmple_local GlobalTheory.T.relAmple_of_locally_on_base

end GlobalTheory
end
end

