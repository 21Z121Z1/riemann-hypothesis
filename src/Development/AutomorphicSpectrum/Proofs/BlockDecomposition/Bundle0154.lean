import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0145
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0072
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0144
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0147

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoordsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraically_independent_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), IsIntegral X → 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → (AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) → (V : Set X).Nonempty → letI := (strV q V).toAlgebra; AlgebraicIndependent K (tV i y hy V hV) := by
  first | exact @GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV | exact GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV | (intros; apply GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveOfSurjectiveSameRankStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_of_surjective_same_rank : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (n : ℕ), VB R A n → VB R B n → ∀ f : A →ₗ[R] B, Function.Surjective f → Function.Bijective f := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB | exact GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialValueOfFactorPullbacksStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bisimplicial_value_of_factor_pullbacks : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {N p q : ℕ} (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1)) (x : Cn F N), (bv F ρ₁ ρ₂ (pulln (boxL F) N x) = fun a _ ↦ pr F ρ₁ x a ⊗ₜ[R] 1) ∧ (bv F ρ₁ ρ₂ (pulln (boxR F) N x) = fun _ b ↦ 1 ⊗ₜ[R] pr F ρ₂ x b) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.bv_pulln_box | exact GlobalTheory.CompanionTheory.HopfC.bv_pulln_box | (intros; apply GlobalTheory.CompanionTheory.HopfC.bv_pulln_box <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxEvaluationPullbackLeftRightStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_evaluation_pullback_left_right : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1) (_ : dn F 1 x = 0), pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 ∧ pulln (boxE F T₀ ε) 1 (pulln (boxR F) 1 x) = x := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR | exact GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR | (intros; apply GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOne
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem red_cT_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) :
    red ϖ 1 (cT σ x) = cT (barσ σ ϖ h 1) (red ϖ 1 x) := by
  ext i j
  simp only [red, cT, Matrix.map_apply, Matrix.transpose_apply, barσ_mk]

theorem red_mul_one {R : Type} [CommRing R] (ϖ : R) {a b c : ℕ}
    (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ 1 (x * y) = red ϖ 1 x * red ϖ 1 y := by
  simp only [red]
  exact Matrix.map_mul

theorem red_surj_one {R : Type} [CommRing R] (ϖ : R) {a b : ℕ}
    (y : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ 1)) : ∃ x, red ϖ 1 x = y := by
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  simp only [red, Matrix.map_apply, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec

theorem isUnit_det_red_one {R : Type} [CommRing R] (ϖ : R) {a : ℕ}
    (x : Matrix (Fin a) (Fin a) R) (hx : IsUnit x.det) : IsUnit (red ϖ 1 x).det := by
  have e : (red ϖ 1 x).det = Ideal.Quotient.mk (lev ϖ 1) x.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact hx.map _

theorem red_image_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ 1 '' {x : Matrix (Fin m) (Fin n) R | red ϖ 1 (cT σ x * S * x) = red ϖ 1 T} =
      {y | cT (barσ σ ϖ h 1) y * red ϖ 1 S * y = red ϖ 1 T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [red_mul_one, red_mul_one, red_cT_one σ ϖ h] at hx
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj_one ϖ y
    simp only [Set.mem_setOf_eq] at hy
    refine ⟨x, ?_, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [red_mul_one, red_mul_one, red_cT_one σ ϖ h]
    exact hy

theorem solCount_one : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → (solCount σ ϖ S T 1 : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hS' : cT σ S = S ∧ IsUnit S.det := hS
  have hT' : cT σ T = T ∧ IsUnit T.det := hT
  have h1 : cT (barσ σ ϖ hR.fix_ϖ 1) (red ϖ 1 S) = red ϖ 1 S := by
    rw [← red_cT_one σ ϖ hR.fix_ϖ, hS'.1]
  have h2 : cT (barσ σ ϖ hR.fix_ϖ 1) (red ϖ 1 T) = red ϖ 1 T := by
    rw [← red_cT_one σ ϖ hR.fix_ϖ, hT'.1]
  unfold solCount
  rw [red_image_one σ ϖ hR.fix_ϖ S T]
  exact GlobalTheory.T.card_hermitian_representations_residue (R ⧸ lev ϖ 1) (barσ σ ϖ hR.fix_ϖ 1) q ε
    (resAlg_of_isUnrQuad R σ ϖ q ε hR) m n hnm (red ϖ 1 S) (red ϖ 1 T) h1
    (isUnit_det_red_one ϖ S hS'.2) h2 (isUnit_det_red_one ϖ T hT'.2)

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDApply
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w w'

namespace GlobalTheory.CompanionTheory.CechOne

variable {R : Type} [CommRing R]

theorem mem_B_of_cls {K : Cx.{w} R} {n : ℕ} {x : K.X n} (hx : K.d n x = 0) (h : K.cls x hx = 0) : x ∈ K.B n :=
  (Submodule.Quotient.mk_eq_zero ((K.B n).submoduleOf (K.Z n))).1 h

theorem d_of_mem_B (K : Cx.{w} R) (n : ℕ) (x : K.X n) (h : x ∈ K.B n) : K.d n x = 0 := by
  cases n with
  | zero =>
    have h0 : x = 0 := h
    rw [h0, map_zero]
  | succ n =>
    obtain ⟨g, rfl⟩ := h
    exact K.dd n g

section Tic

variable {K : DCx.{w} R} {E : Cx.{w'} R} (e : DCx.AugRow E K) {a : ℕ}

def LowB (q : ℕ) : Prop :=
  (∀ p (b : K.X (p + 1) q), b ∈ (K.col (p + 1)).B q → K.dh (p + 1) q b = 0 →
    ∃ b' ∈ (K.col p).B q, K.dh p q b' = b) ∧
  (∀ b : K.X 0 q, b ∈ (K.col 0).B q → K.dh 0 q b = 0 → ∃ z ∈ E.B q, e.ε q z = b)

theorem lowB (hr0 : ∀ q x, K.dh 0 q x = 0 → ∃ y, e.ε q y = x)
    (hr : ∀ p q x, K.dh (p + 1) q x = 0 → ∃ y, K.dh p q y = x)
    (hc : ∀ p q, q ≠ a → ∀ x, K.dv p q x = 0 → x ∈ (K.col p).B q) : ∀ q, q ≤ a → LowB e q := by
  intro q
  induction q with
  | zero =>
    intro _
    constructor
    · intro p b hb _
      have h0 : b = 0 := hb
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
    · intro b hb _
      have h0 : b = 0 := hb
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
  | succ q ih =>
    intro hq
    obtain ⟨i1, -⟩ := ih (by omega)
    have L1 : ∀ p (x : K.X (p + 1) q), K.dv (p + 1) q x = 0 → K.dh (p + 1) q x = 0 →
        ∃ y, K.dh p q y = x ∧ K.dv p q y = 0 := by
      intro p x hv hh
      obtain ⟨b', hb', e'⟩ := i1 p x (hc _ _ (by omega) x hv) hh
      exact ⟨b', e', d_of_mem_B (K.col p) q b' hb'⟩
    constructor
    · rintro p b ⟨c, rfl⟩ hb
      change K.dh (p + 1) (q + 1) (K.dv (p + 1) q c) = 0 at hb
      rw [K.hv] at hb
      obtain ⟨y, hy, hyv⟩ := L1 (p + 1) (K.dh (p + 1) q c) hb (K.hh _ _ _)
      obtain ⟨v, hv⟩ := hr p q (c - y) (by rw [map_sub, hy, sub_self])
      refine ⟨K.dv p q v, ⟨v, rfl⟩, ?_⟩
      change K.dh p (q + 1) (K.dv p q v) = K.dv (p + 1) q c
      rw [K.hv, hv, map_sub, hyv, sub_zero]
    · rintro b ⟨c, rfl⟩ hb
      change K.dh 0 (q + 1) (K.dv 0 q c) = 0 at hb
      rw [K.hv] at hb
      obtain ⟨y, hy, hyv⟩ := L1 0 (K.dh 0 q c) hb (K.hh _ _ _)
      obtain ⟨z, hz⟩ := hr0 q (c - y) (by rw [map_sub, hy, sub_self])
      refine ⟨E.d q z, ⟨z, rfl⟩, ?_⟩
      change e.ε (q + 1) (E.d q z) = K.dv 0 q c
      rw [← e.comm, hz, map_sub, hyv, sub_zero]

theorem mem_B_of_eps (hinj : ∀ q, Function.Injective (e.ε q)) (h : ∀ q, q ≤ a → LowB e q) {q : ℕ} (hq : q ≤ a)
    (z : E.X q) (hz : e.ε q z ∈ (K.col 0).B q) : z ∈ E.B q := by
  obtain ⟨z', hz', h'⟩ := (h q hq).2 _ hz (e.hε q z)
  rwa [← hinj q h']

theorem exists_lift (hinj : ∀ q, Function.Injective (e.ε q)) (hr0 : ∀ q x, K.dh 0 q x = 0 → ∃ y, e.ε q y = x)
    (h : ∀ q, q ≤ a → LowB e q) (u : K.X 0 a) (hu : K.dv 0 a u = 0) (hd : K.dh 0 a u ∈ (K.col 1).B a) :
    ∃ z b, E.d a z = 0 ∧ b ∈ (K.col 0).B a ∧ e.ε a z + b = u := by
  obtain ⟨b, hb, eb⟩ := (h a le_rfl).1 0 _ hd (K.hh _ _ _)
  obtain ⟨z, hz⟩ := hr0 a (u - b) (by rw [map_sub, eb, sub_self])
  refine ⟨z, b, hinj (a + 1) ?_, hb, by rw [hz, sub_add_cancel]⟩
  rw [← e.comm, hz, map_zero, map_sub, hu, d_of_mem_B (K.col 0) a b hb, sub_zero]

end Tic

variable {ι : Type} [DecidableEq ι]

theorem cech_d_apply (P : PM.{w} R ι) (p : ℕ) (x : P.cech.X p) (t : Fin (p + 2) → ι) :
    P.cech.d p x t = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • P.res (ent_comp t k.succAbove) (x (t ∘ k.succAbove)) := by
  rw [Cos.d_apply, Finset.sum_apply]
  rfl

theorem d_aug (P : PM.{w} R ι) (x : P.M ∅) : P.cech.d 0 (P.aug x) = 0 := by
  funext t
  rw [cech_d_apply, Fin.sum_univ_two]
  change (-1 : ℤ) ^ 0 • P.res _ (P.res _ x) + (-1 : ℤ) ^ 1 • P.res _ (P.res _ x) = 0
  rw [P.res_comp, P.res_comp]
  simp

theorem ent_nonempty {n : ℕ} (i : Fin (n + 1) → ι) : (ent i).Nonempty :=
  Finset.univ_nonempty.image i

variable (A : Sy.{w} R ι)

abbrev dcx : DCx.{w} R where
  X p q := (A.term q).cech.X p
  dh p q := (A.term q).cech.d p
  dv p q := LinearMap.pi fun i => ((A.K (ent i)).d q).comp (LinearMap.proj i)
  hh p q := (A.term q).cech.dd p
  vv p q x := by
    funext i
    exact (A.K (ent i)).dd q (x i)
  hv p q x := by
    funext t
    rw [cech_d_apply]
    change _ = (A.K (ent t)).d q ((A.term q).cech.d p x t)
    rw [cech_d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    exact congrArg _ ((A.res _).comm q _).symm

def aug : DCx.AugRow (A.K ∅) (dcx A) where
  ε q := (A.term q).aug
  hε q x := d_aug (A.term q) x
  comm q x := by
    funext i
    exact (A.res _).comm q x

theorem mem_col_B {p q : ℕ} (x : (dcx A).X p q) (h : ∀ i, x i ∈ (A.K (ent i)).B q) : x ∈ ((dcx A).col p).B q := by
  cases q with
  | zero =>
    have h0 : x = 0 := funext h
    exact h0
  | succ q =>
    choose c hc using h
    exact ⟨c, funext hc⟩

theorem col_B_mem {p q : ℕ} (x : (dcx A).X p q) (h : x ∈ ((dcx A).col p).B q) (i) : x i ∈ (A.K (ent i)).B q := by
  cases q with
  | zero =>
    have h0 : x = 0 := h
    rw [h0]
    exact Submodule.zero_mem _
  | succ q =>
    obtain ⟨c, rfl⟩ := h
    exact ⟨c i, rfl⟩

theorem oneLow : OneLow := by
  intro R _ ι _ A a hD hO
  have hinj : ∀ q, Function.Injective ((aug A).ε q) := fun q =>
    (injective_iff_map_eq_zero _).2 fun x hx => by simpa using (hD q).2.1 x hx
  have hr0 : ∀ q x, (dcx A).dh 0 q x = 0 → ∃ y, (aug A).ε q y = x := fun q x hx => by
    obtain ⟨y, hy⟩ := (hD q).2.2.1 x hx
    exact ⟨y, hy.trans (one_smul _ _)⟩
  have hr : ∀ p q x, (dcx A).dh (p + 1) q x = 0 → ∃ y, (dcx A).dh p q y = x := fun p q x hx => by
    obtain ⟨y, hy⟩ := (hD q).2.2.2 p x hx
    exact ⟨y, hy.trans (one_smul _ _)⟩
  have hc : ∀ p q, q ≠ a → ∀ x, (dcx A).dv p q x = 0 → x ∈ ((dcx A).col p).B q := by
    intro p q hq x hx
    refine mem_col_B A x fun i => ?_
    have hi : (A.K (ent i)).d q (x i) = 0 := congrFun hx i
    have := hO (ent i) (ent_nonempty i) q hq
    exact mem_B_of_cls hi (Subsingleton.elim _ _)
  have hL := lowB (aug A) hr0 hr hc
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine mem_B_of_eps (aug A) hinj hL hj.le z.1 (hc 0 j hj.ne _ ?_)
    rw [(aug A).comm, show (A.K ∅).d j z.1 = 0 from z.2, map_zero]
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine mem_B_of_eps (aug A) hinj hL le_rfl z.1 (mem_col_B A _ fun i => ?_)
    have hz : (A.K (ent i)).d a ((A.res (Finset.empty_subset _)).f a z.1) = 0 := by
      rw [(A.res _).comm, show (A.K ∅).d a z.1 = 0 from z.2, map_zero]
    exact mem_B_of_cls hz (congrFun hx i)
  · intro y
    constructor
    · intro hy
      have hs : ∀ i, ∃ u : (A.K (ent i)).Z a, Submodule.Quotient.mk u = y i := fun i =>
        Submodule.Quotient.mk_surjective _ (y i)
      choose u hu using hs
      let u' : (dcx A).X 0 a := fun i => (u i).1
      have hv : (dcx A).dv 0 a u' = 0 := funext fun i => (u i).2
      have hd : (dcx A).dh 0 a u' ∈ ((dcx A).col 1).B a := by
        refine mem_col_B A _ fun t => ?_
        have h := congrFun hy t
        rw [cech_d_apply, Fin.sum_univ_two, ← hu, ← hu] at h
        have hz : (A.K (ent t)).d a ((dcx A).dh 0 a u' t) = 0 := congrFun ((dcx A).hv 0 a u' ▸ (by rw [hv, map_zero] : (dcx A).dh 0 (a + 1) ((dcx A).dv 0 a u') = 0)) t
        refine mem_B_of_cls hz ?_
        simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h
        have e : (⟨(dcx A).dh 0 a u' t, hz⟩ : (A.K (ent t)).Z a) =
            (A.res (ent_comp t (Fin.succAbove 0))).mapZ a (u (t ∘ Fin.succAbove 0)) -
              (A.res (ent_comp t (Fin.succAbove 1))).mapZ a (u (t ∘ Fin.succAbove 1)) := by
          refine Subtype.ext ?_
          change (A.term a).cech.d 0 u' t = _
          rw [cech_d_apply, Fin.sum_univ_two]
          simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
          exact (sub_eq_add_neg _ _).symm
        change Submodule.Quotient.mk (⟨(dcx A).dh 0 a u' t, hz⟩ : (A.K (ent t)).Z a) = 0
        rw [e, Submodule.Quotient.mk_sub, sub_eq_add_neg]
        exact h
      obtain ⟨z, b, hz, hb, e⟩ := exists_lift (aug A) hinj hr0 hL u' hv hd
      refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
      funext i
      rw [← hu]
      change Submodule.Quotient.mk ((A.res (Finset.empty_subset _)).mapZ a ⟨z, hz⟩) = Submodule.Quotient.mk (u i)
      refine (Submodule.Quotient.eq _).2 ?_
      have hbi := col_B_mem A b hb i
      have e' : (A.term a).aug z i + b i = (u i).1 := congrFun e i
      have e2 : (A.term a).aug z i - (u i).1 = -(b i) := by
        rw [← e']
        abel
      change (A.term a).aug z i - (u i).1 ∈ (A.K (ent i)).B a
      rw [e2]
      exact neg_mem hbi
    · rintro ⟨x, rfl⟩
      exact d_aug _ x

end GlobalTheory.CompanionTheory.CechOne

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechStructureSheafComparisonStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_structure_sheaf_comparison : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.cech_OSys_homology_equiv | exact GlobalTheory.CompanionTheory.Hodge.Nerve.cech_OSys_homology_equiv | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.cech_OSys_homology_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_divided_powers_graded_constant : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  first | exact @GlobalTheory.CompanionTheory.ChartFil.chart_grConst | exact GlobalTheory.CompanionTheory.ChartFil.chart_grConst | (intros; apply GlobalTheory.CompanionTheory.ChartFil.chart_grConst <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassZeroCocycleTensorCoboundary
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.Axis

theorem rTensor_cocycle_eq_coboundary_of_class_eq_zero :
    ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] (t : Z1 F ⊗[R] N), (H1.mk F).rTensor N t = 0 →
    ∃ g : ∀ T : C, F.obj T ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T) := by
  intro R _ C _ F N _ _ t ht
  have hex : Function.Exact ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) (H1.mk F) :=
    LinearMap.exact_map_mkQ_range _
  obtain ⟨u, rfl⟩ := (rTensor_exact N hex (H1.mk_surjective F) t).1 ht
  refine ⟨fun T => (LinearMap.proj T : C0 F →ₗ[R] F.obj T).rTensor N u, fun T T' φ => ?_⟩
  have key : evZ F φ ∘ₗ (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F) =
      (LinearMap.proj T' : C0 F →ₗ[R] F.obj T') -
        (mp F φ).toLinearMap ∘ₗ (LinearMap.proj T : C0 F →ₗ[R] F.obj T) := by
    ext g
    rfl
  rw [← LinearMap.rTensor_comp_apply, key, LinearMap.rTensor_sub, LinearMap.sub_apply,
    LinearMap.rTensor_comp_apply]

end GlobalTheory.CompanionTheory.Axis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainBaseChangeEquivalencesStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_base_change_equivalences : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F'), ∃ (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F') (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F'), (∀ c, E₀ (1 ⊗ₜ c) = fun T ↦ m.α T (c T)) ∧ (∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ)) ∧ (∀ c, E₂ (1 ⊗ₜ c) = fun T T' T'' φ ψ ↦ m.α T'' (c T T' T'' φ ψ)) ∧ (∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x)) ∧ ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x) := by
  first | exact @GlobalTheory.CompanionTheory.CochainBC.main | exact GlobalTheory.CompanionTheory.CochainBC.main | (intros; apply GlobalTheory.CompanionTheory.CochainBC.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_cohomology_nerve_homology_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveCx.obj (toMod F)).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveCx.obj (toMod F)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx | exact GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleTensorCoboundaryClassZero
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis.KFlat

section Pi

variable {R : Type} [CommRing R] {J : Type} [Finite J] {M : J → Type} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {N : Type} [AddCommGroup N] [Module R N]

theorem piLeft_apply_eq [Fintype J] [DecidableEq J] (u : (∀ i, M i) ⊗[R] N) (i : J) :
    TensorProduct.piLeft R N M u i = (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem pi_rTensor_eq_zero (w : (∀ i, M i) ⊗[R] N)
    (h : ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N w = 0) : w = 0 := by
  classical
  have := Fintype.ofFinite J
  apply (TensorProduct.piLeft R N M).injective
  funext i
  rw [piLeft_apply_eq, h, map_zero]
  rfl

theorem pi_rTensor_exists (g : ∀ i, M i ⊗[R] N) :
    ∃ u : (∀ i, M i) ⊗[R] N, ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N u = g i := by
  classical
  have := Fintype.ofFinite J
  refine ⟨(TensorProduct.piLeft R N M).symm g, fun i ↦ ?_⟩
  rw [← piLeft_apply_eq, LinearEquiv.apply_symm_apply]

end Pi

theorem class_eq_zero_of_coboundary (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (t : Z1 F ⊗[R] N)
    (g : ∀ T : C, F.obj T ⊗[R] N)
    (h : ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T)) :
    (H1.mk F).rTensor N t = 0 := by
  classical
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun T T' ↦ by
    haveI : Subsingleton (T ⟶ T') := inferInstance
    exact Finite.of_subsingleton
  let κ : Z1 F →ₗ[R] ∀ x : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj x.2.1 :=
    LinearMap.pi fun x ↦ evZ F x.2.2
  have hκ : Function.Injective κ := fun a b hab ↦ Subtype.ext (by
    funext T T' φ
    exact congrFun hab ⟨T, T', φ⟩)
  let δ : C0 F →ₗ[R] Z1 F := (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)
  obtain ⟨u, hu⟩ := pi_rTensor_exists (R := R) (M := fun T : C ↦ F.obj T) (N := N) g
  have hδ : ∀ {T T' : C} (φ : T ⟶ T'), evZ F φ ∘ₗ δ =
      (LinearMap.proj T' : C0 F →ₗ[R] F.obj T') -
        (mp F φ).toLinearMap ∘ₗ (LinearMap.proj T : C0 F →ₗ[R] F.obj T) := fun φ ↦ by
    refine LinearMap.ext fun c ↦ ?_
    rfl
  have key : t = δ.rTensor N u := by
    apply Module.Flat.rTensor_preserves_injective_linearMap κ hκ
    rw [← sub_eq_zero, ← map_sub]
    apply pi_rTensor_eq_zero
    rintro ⟨T, T', φ⟩
    rw [← LinearMap.rTensor_comp_apply]
    have e : (LinearMap.proj (⟨T, T', φ⟩ : Σ T : C, Σ T' : C, (T ⟶ T')) :
        (∀ x : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj x.2.1) →ₗ[R] F.obj T') ∘ₗ κ = evZ F φ := rfl
    rw [e, map_sub, h, ← LinearMap.rTensor_comp_apply, hδ, LinearMap.rTensor_sub, LinearMap.sub_apply,
      LinearMap.rTensor_comp_apply, hu, hu, sub_self]
  have hz : H1.mk F ∘ₗ δ = 0 := by
    refine LinearMap.ext fun c ↦ ?_
    exact (H1.mk_eq_zero (F := F) (f := δ c)).2 ⟨c, rfl⟩
  rw [key, ← LinearMap.rTensor_comp_apply, hz, LinearMap.rTensor_zero, LinearMap.zero_apply]

end GlobalTheory.CompanionTheory.Axis.KFlat
end
end

