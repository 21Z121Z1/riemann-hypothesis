import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointWithZeroSecondCoordLeftCompSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedDieudonneFunctorQuasiLogarithms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernRepresentativeContractionOfOrthogonal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ChernRep

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem isContr_add {z z' : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B} {κ κ' : Fn1 A}
    (h : IsContr z v κ) (h' : IsContr z' v κ') : IsContr (z + z') v (κ.add κ') := by
  unfold IsContr at h h' ⊢
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  simp only [Fn1.add, Pi.add_apply, h D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ,
    h' D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ, ← TrivSqZeroExt.snd_add]
  congr 1
  abel

theorem isContr_sum {n : ℕ} {z : Fin n → C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B}
    {κ : Fin n → Fn1 A} (h : ∀ k, IsContr (z k) v (κ k)) :
    IsContr (∑ k, z k) v (fun D _ _ D' _ _ φ x ↦ ∑ k, κ k D D' φ x) := by
  unfold IsContr at h ⊢
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun k _ ↦ h k D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have key : ∀ g : Fin n → TrivSqZeroExt D' D', ∑ k, (g k).snd = (∑ k, g k).snd := fun g ↦
    (map_sum (TrivSqZeroExt.sndHom D' D') g Finset.univ).symm
  exact key fun k ↦ z k _ _ _ s τ - z k _ _ _ a s' - z k _ _ _ i τ + z k _ _ _ b i'

theorem isContr_eq {z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B} (hv : IsTangent v)
    {κ κ' : Fn1 A} (h : IsContr z v κ) (h' : IsContr z v κ') (D : Type) [CommRing D] [Algebra R D]
    (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    κ D D' φ x = κ' D D' φ x := by
  obtain ⟨s, i, s', i', a, b, τ, hs, hi, hs', hi', ha, hb, hτ⟩ :=
    (GlobalTheory.PtExt.ContrMor.exists_contr R A B v hv).1 D D' φ x
  rw [h D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ, h' D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ]

theorem sum_split {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (Φ : M →ₗ[R] N →ₗ[R] P) {n : ℕ} (a a₁ : Fin n → M) (b b₁ : Fin n → N)
    (h : ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0) :
    ∑ k, Φ (a k) (b k) = ∑ k, Φ (a₁ k) (b k) + ∑ k, Φ (a k - a₁ k) (b₁ k) := by
  have h0 : ∑ k, Φ (a k - a₁ k) (b k - b₁ k) = 0 := by
    have := congrArg (TensorProduct.lift Φ) h
    simpa only [map_sum, TensorProduct.lift.tmul, map_zero] using this
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [map_sub, LinearMap.sub_apply]
  abel

theorem fv_sub_sum {X : Over (Sp R)} {n : ℕ} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (t : Fin n → R)
    (u : Fin n → Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type)
    [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (f - ∑ k, t k • u k) D D' φ x = fv f D D' φ x - ∑ k, algebraMap R D' (t k) * fv (u k) D D' φ x := by
  simp only [fv, ev, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
  rfl

theorem fv_smul {X : Over (Sp R)} (t : R) (u : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D]
    [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (t • u) D D' φ x = algebraMap R D' t * fv u D D' φ x := by
  simp only [fv, ev, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]

section Rep

variable (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
  (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)

omit [GrpObj A] [GrpObj B] in

def cupPr (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)

omit [GrpObj A] [GrpObj B] in

theorem mk_cupPr (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    CatCoh.H2.mk _ (cupPr m₁ m₂ a b) = cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ a))
      (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ b)) := rfl

def cupPrim (A B : Over (Sp R)) [GrpObj A] [GrpObj B] :
    primDR A →ₗ[R] primDR B →ₗ[R] CatCoh.H2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  (cup _).compl₁₂ (pullOver (dp0 R) (𝟙 _) (fst A B) ∘ₗ (primDR A).subtype)
    (pullOver (dp0 R) (𝟙 _) (snd A B) ∘ₗ (primDR B).subtype)

theorem cupPrim_apply (a : primDR A) (b : primDR B) : cupPrim A B a b =
    cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) a.1) (pullOver (dp0 R) (𝟙 _) (snd A B) b.1) := rfl

theorem mk_cupPr_prim {a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))} {x : primDR A}
    {y : primDR B} (ha : CatCoh.H1.mk _ a = x.1) (hb : CatCoh.H1.mk _ b = y.1) :
    CatCoh.H2.mk _ (cupPr m₁ m₂ a b) = cupPrim A B x y := by
  rw [mk_cupPr, cupPrim_apply, ha, hb]

variable {n : ℕ} (α : Fin n → Form (A.hom ≫ 𝟙 _)) (β : Fin n → Form (B.hom ≫ 𝟙 _))
  (a' : Fin n → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b' : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))

omit [GrpObj A] [GrpObj B] in

def rep : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  ∑ k, cupPr m₁ m₂ (α k).1 (b' k) + ∑ k, cupPr m₁ m₂ (a' k) (β k).1

omit [GrpObj A] [GrpObj B] in

theorem rep_val : (rep m₁ m₂ α β a' b').1 =
    ∑ k, (cupPr m₁ m₂ (α k).1 (b' k)).1 + ∑ k, (cupPr m₁ m₂ (a' k) (β k).1).1 := by
  rw [rep, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]

omit [GrpObj A] [GrpObj B] in

theorem mk_rep : CatCoh.H2.mk _ (rep m₁ m₂ α β a' b') =
    ∑ k, CatCoh.H2.mk _ (cupPr m₁ m₂ (α k).1 (b' k)) + ∑ k, CatCoh.H2.mk _ (cupPr m₁ m₂ (a' k) (β k).1) :=
  ((CatCoh.H2.mk _).map_add _ _).trans (congrArg₂ (· + ·) (map_sum _ _ _) (map_sum _ _ _))

omit [GrpObj A] [GrpObj B] in

theorem rep_triv (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (p : T ⟶ T') (q : T' ⟶ T'') (hT : T.J = ⊥)
    (hT' : T'.J = ⊥) (hT'' : T''.J = ⊥) : (rep m₁ m₂ α β a' b').1 T T' T'' p q = 0 := by
  have h1 : ∀ k, (cupPr m₁ m₂ (α k).1 (b' k)).1 T T' T'' p q = 0 := fun k ↦ by
    rw [cupPr, cupZ_apply,
      show (m₁.coef.pullbackOneCocycle (α k).1).1 T T' p = 0 from (α k).2 (m₁.functor.map p) hT hT', map_zero, zero_mul]
  have h2 : ∀ k, (cupPr m₁ m₂ (a' k) (β k).1).1 T T' T'' p q = 0 := fun k ↦ by
    rw [cupPr, cupZ_apply,
      show (m₂.coef.pullbackOneCocycle (β k).1).1 T' T'' q = 0 from (β k).2 (m₂.functor.map q) hT' hT'', mul_zero]
  rw [rep_val]
  simp only [Pi.add_apply, Finset.sum_apply, h1, h2, Finset.sum_const_zero, add_zero]

theorem rep_contr {v : epsR R ⟶ B} (hv : IsTangent v) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)))
    (hcl : CatCoh.H1.mk _ (f - ∑ k, tanVal v (β k) • a' k) ∈ F1 (A.hom ≫ 𝟙 _)) (κ : Fn1 A)
    (hκ : IsContr (rep m₁ m₂ α β a' b').1 v κ) : Cohom (whole A) κ (fv f).neg := by
  obtain ⟨-, hex⟩ := GlobalTheory.PtExt.ContrMor.exists_contr R A B v hv
  choose κX hκX using fun k ↦ hex (cupPr m₁ m₂ (α k).1 (b' k)).1
  choose κY hκY using fun k ↦ hex (cupPr m₁ m₂ (a' k) (β k).1).1
  rw [rep_val] at hκ
  have hsC := isContr_add (isContr_sum hκX) (isContr_sum hκY)
  have hX0 := fun k ↦ GlobalTheory.PtExt.contr_cup_form_eq_zero R A B m₁ m₂ v hv (α k) (b' k) (κX k) (hκX k)
  have hYc := fun k ↦ GlobalTheory.PtExt.cohom_contr_cupA R A B m₁ m₂ v hv (a' k) (β k) (κY k) (hκY k)
  unfold Cohom at hYc
  choose cY hcY using hYc
  obtain ⟨k₀, hk₀⟩ := (GlobalTheory.PtExt.mem_hodgeFiltration_iff_pointwiseCoboundary R A _).1 hcl
  refine ⟨fun D _ _ x ↦ k₀ D x + ∑ k, cY k D x, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := isContr_eq hv hκ hsC D D' φ x
  have e2 := hk₀ D D' φ x (sm_whole x)
  have e3 : ∀ k, κY k D D' φ x = cY k D' (spOver φ ≫ x) - φ (cY k D x) -
      algebraMap R D' (tanVal v (β k)) * fv (a' k) D D' φ x := fun k ↦ by
    have h3 := hcY k D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg, fv_smul, map_neg] at h3
    linear_combination h3
  rw [fv_sub_sum] at e2
  simp only [Fn1.add, Fn1.neg, hX0, Finset.sum_const_zero, zero_add] at e1 ⊢
  rw [e1, map_add, map_sum]
  simp only [e3, Finset.sum_sub_distrib]
  linear_combination e2

end Rep

theorem apply_sub_sum {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {n : ℕ}
    (a a₁ : Fin n → M) (b b₁ : Fin n → N) (h : ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0) (x : M →ₗ[R] R)
    (y : N →ₗ[R] R) (hx : ∀ k, x (a₁ k) = 0) (c : M) (hc : x c = ∑ k, x (a k) * y (b k)) :
    x (c - ∑ k, y (b₁ k) • (a k - a₁ k)) = 0 := by
  have e := sum_split ((LinearMap.mul R R).compl₁₂ x y) a a₁ b b₁ h
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at e
  simp only [map_sub, hx, sub_zero, zero_mul, Finset.sum_const_zero, zero_add] at e
  rw [map_sub, map_sum, hc, e]
  simp only [map_smul, map_sub, hx, sub_zero, smul_eq_mul, mul_comm, sub_self]

theorem mk_sub_sum {n : ℕ} {f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {c : primDR A} (hf : CatCoh.H1.mk _ f = c.1)
    {a' : Fin n → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {a : Fin n → primDR A} (ha : ∀ k, CatCoh.H1.mk _ (a' k) = (a k).1)
    (t : Fin n → R) : CatCoh.H1.mk _ (f - ∑ k, t k • a' k) = (c - ∑ k, t k • a k : primDR A).1 := by
  rw [map_sub, map_sum, hf, Submodule.coe_sub, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, ha k, Submodule.coe_smul]

end GlobalTheory.PtExt.ChernRep

open GlobalTheory.PtExt.ChernRep in

theorem GlobalTheory.PtExt.exists_chernRep_contr_of_orth : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∃ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) ∧ (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) ∧ ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (whole A) κ (fv f).neg := by
  intro hHDR R _ A B _ _ g hA hB hgA hgB P hP pf hpf horth h' v hv c hc f hf
  obtain ⟨hFree, hHodge, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hHDR
  obtain ⟨-, hprA, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hFree hA hgA
  obtain ⟨-, hprB, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hFree hB hgB
  obtain ⟨-, hCA, -⟩ := hHodge R A g hA hgA
  obtain ⟨-, hCB, -⟩ := hHodge R B g hB hgB
  obtain ⟨n, a, b, hch, hab⟩ := hpf
  have L := GlobalTheory.tensor_mem_of_dualAnnihilator R (primDR A) (primDR B) (PrimitiveSubmodule A) (PrimitiveSubmodule B) hCA hCB
  obtain ⟨a₁, b₁, ha₁, hb₁, hsum⟩ := L.2 n a b fun x hx y hy ↦ (hab x y).symm.trans (horth x hx y hy)
  have eα : ∀ k, ∃ α : Form (A.hom ≫ 𝟙 _), Form.cl _ α = (a₁ k).1 := fun k ↦ by
    have h := ha₁ k
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at h
    exact h
  choose α hα using eα
  have eβ : ∀ k, ∃ β : Form (B.hom ≫ 𝟙 _), Form.cl _ β = (b₁ k).1 := fun k ↦ by
    have h := hb₁ k
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at h
    exact h
  choose β hβ using eβ
  choose b' hb' using fun k ↦ CatCoh.H1.mk_surjective (O (dp0 R) (B.hom ≫ 𝟙 _)) (b k).1
  choose a' ha' using fun k ↦ CatCoh.H1.mk_surjective (O (dp0 R) (A.hom ≫ 𝟙 _)) (a k - a₁ k).1
  have m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  refine ⟨rep m₁ m₂ α β a' b', ?_, rep_triv m₁ m₂ α β a' b', rep_contr m₁ m₂ α β a' b' hv.1 f ?_⟩
  · have hz : CatCoh.H2.mk _ (rep m₁ m₂ α β a' b') = ∑ k, cupPrim A B (a k) (b k) :=
      ((mk_rep m₁ m₂ α β a' b').trans (congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun k _ ↦ mk_cupPr_prim m₁ m₂ (hα k) (hb' k))
        (Finset.sum_congr rfl fun k _ ↦ mk_cupPr_prim m₁ m₂ (ha' k) (hβ k)))).trans
        (sum_split (cupPrim A B) a a₁ b b₁ hsum).symm
    exact hz ▸ hch
  · have ht : (fun k ↦ tanVal v (β k)) = fun k ↦ h' (b₁ k) := funext fun k ↦ by
      have hm : Form.cl _ (β k) ∈ primDR B := (hβ k).symm ▸ (b₁ k).2
      exact (hv.2 (β k) hm).symm.trans (congrArg h' (Subtype.ext (hβ k)))
    have hd : c - ∑ k, h' (b₁ k) • (a k - a₁ k) ∈ PrimitiveSubmodule A := L.1 _ fun x hx ↦
      apply_sub_sum a a₁ b b₁ hsum x h' (fun k ↦ (Submodule.mem_dualAnnihilator _).1 hx _ (ha₁ k)) c
        ((hc x hx).symm.trans (hab x h'))
    rw [mk_sub_sum hf ha' fun k ↦ tanVal v (β k)]
    simp only [fun k ↦ congrFun ht k]
    exact hd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalTraitSystemAtClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem rank_le (hn : 3 ≤ n) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := GlobalTheory.T.siegelTrait_characterGroup_finrank_le_genus_of_three_le g n F hn T

theorem lam (hE : IsE8 W) (hT : ThetaInt F W i) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) : ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ :=
  GlobalTheory.T.thetaSetup_classicalTraitPeriods_bounded_below_maxIdeal _ n F W Z i X₁ X₁.one_le X₁.three_le X₁.odd X₁.imm hE hT X₁.projM p z₁ hz

variable {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (c : CTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ c.y) z₁ (RatModel.gPt_specializes c.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC c a = c.val a := rfl

theorem norm_evC_le (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC c a‖ ≤ 1 :=
  RatModel.norm_val_le_one c.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC c a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff c.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem beta_pos (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X) (hx : x ≠ 0) : 0 < c.T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal c.T.V).ne_top c.T.mono hx
  fin_cases j
  simpa using hj

end GlobalTheory.Poinc.PreSys

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

variable (X₁ p) in

abbrev Key : Type := (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (Fin k → ℤ) → (Fin k → ℤ) → ℝ)

def Rep (c : CTrait X₁ p z₁) (q : Key X₁ p) : Prop :=
  c.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X, ∀ u v, q.2.2 u v = c.sc * c.T.β (e u) (e v)

def coord (c : CTrait X₁ p z₁) : (Fin (Module.finrank ℤ c.T.D.toPre.X) → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X :=
  (Module.finBasis ℤ c.T.D.toPre.X).equivFun.symm

def keyOf (c : CTrait X₁ p z₁) : Key X₁ p :=
  (c.y, ⟨Module.finrank ℤ c.T.D.toPre.X, fun u v => c.sc * c.T.β (coord c u) (coord c v)⟩)

theorem rep_keyOf (c : CTrait X₁ p z₁) : Rep c (keyOf c) := ⟨rfl, coord c, fun _ _ => rfl⟩

variable (X₁ p z₁) in

def Pts : Type := {q : Key X₁ p // ∃ c : CTrait X₁ p z₁, Rep c q}

noncomputable def pick (y : Pts X₁ p z₁) : CTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2

variable (X₁ p z₁) in

noncomputable def sys : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.D.toPre.X
  rank_le y := rank_le X₁.three_le _
  β y := (pick y).T.β
  bal y := ⟨(pick y).T.symm, fun a u v => by simp⟩
  pos y x hx := beta_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : (sys X₁ p z₁ (g := g)).Matches := by
  intro c
  refine ⟨⟨keyOf c, c, rep_keyOf c⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    show evC _ a = c.val a
    rw [evC_apply]
    unfold CTrait.val
    rw [hy]
    rfl
  · obtain ⟨-, e', he'⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    have key : ∀ a b : (pick ⟨keyOf c, c, rep_keyOf c⟩).T.D.toPre.X,
        (pick ⟨keyOf c, c, rep_keyOf c⟩).sc * (pick ⟨keyOf c, c, rep_keyOf c⟩).T.β a b =
          c.sc * c.T.β (coord c (e'.symm a)) (coord c (e'.symm b)) := by
      intro a b
      have h := he' (e'.symm a) (e'.symm b)
      rw [e'.apply_symm_apply, e'.apply_symm_apply] at h
      exact h.symm
    exact ⟨e'.symm.trans (coord c), key⟩

theorem sys_lam (hE : IsE8 W) (hT : ThetaInt F W i) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    (sys X₁ p z₁ (g := g)).abelian₂ := by
  obtain ⟨C, hC⟩ := lam hE hT X₁ p z₁ hz
  exact ⟨C, fun y x hx => by
    obtain ⟨h, hm, hle⟩ := hC (pick y) x hx
    exact ⟨h, hm, hle⟩⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z),
    IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) →
      ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧
        (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X,
          ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  intro g n F W Z i hE hT X₁ p _ z₁ hz
  exact ⟨sys X₁ p z₁, sys_matches, sys_lam hE hT hz, fun y => ⟨pick y, fun a => rfl, LinearEquiv.refl ℤ _,
    fun a b => rfl⟩⟩

end GlobalTheory.Poinc.PreSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedBoundaryPointMaximalIdealStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedBoundaryPoint_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U : Y.X.affineOpens) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∃ x' : gen Y, genι Y x' = x ∧ x' ∈ genBd Y ∧ IsClosed ({x'} : Set (gen Y)) := by
  first | exact @GlobalTheory.BoundaryPoint.exists_closed_boundary_point | exact GlobalTheory.BoundaryPoint.exists_closed_boundary_point | (intros; apply GlobalTheory.BoundaryPoint.exists_closed_boundary_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffsTangentVectorTranslatedBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffs_tangentVector_translatedBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ → w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom → ∃ c : Fin n → S, ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = ∑ a, ρ (c a) * (valR (wt a) O f).snd := by
  first | exact @GlobalTheory.VertSpan.exists_coeffs_translate | exact GlobalTheory.VertSpan.exists_coeffs_translate | (intros; apply GlobalTheory.VertSpan.exists_coeffs_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedDieudonneFunctorQuasiLogarithmsStatement
section
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms : ∀ (p : ℕ) [Fact p.Prime], ∃ B : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn), B.Katz := by
  first | (exact @GlobalTheory.exists_base_isConn_katz) | (exact GlobalTheory.exists_base_isConn_katz) | (intros; apply GlobalTheory.exists_base_isConn_katz  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVarietyStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_of_regular_on_cover_abelianVariety : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  first | exact @GlobalTheory.HeatConst.const_of_regular_on_cover | exact GlobalTheory.HeatConst.const_of_regular_on_cover | (intros; apply GlobalTheory.HeatConst.const_of_regular_on_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverMemberContainingFractionFieldPointStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_member_containing_fractionField_point : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R), φ c ≠ 0 → ∀ (J : Type) (W : J → G.left.Opens), ⨆ i, W i = G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → ∃ i, ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ W i := by
  first | exact @GlobalTheory.genPt_mem_cover | exact GlobalTheory.genPt_mem_cover | (intros; apply GlobalTheory.genPt_mem_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFractionRingOfVectorFieldStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_fractionRing_of_vectorField : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] [CharZero Ω] (x : Sp Ω ⟶ X), (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) → ∀ (W : X.Opens) (d : Fld X), IsField W d → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ W → ∃ dt0 : Derivation ℤ (FractionRing Ω) (FractionRing Ω), ∀ (O : X.Opens) (f : Γ(X, O)), O ≤ W → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (d O f) = dt0 (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  first | exact @GlobalTheory.GenDer.exists_derivation_fractionRing | exact GlobalTheory.GenDer.exists_derivation_fractionRing | (intros; apply GlobalTheory.GenDer.exists_derivation_fractionRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberPointOfVectorFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumberPoint_of_vectorField : ∀ (Z : Scheme.{0}) (W : Z.Opens) (e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W e → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ Z), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ w : Sp (DualNumber S) ⟶ Z, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ ∧ ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (O : Z.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(Z, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := by
  first | exact @GlobalTheory.EpsPoint.exists_epsPoint | exact GlobalTheory.EpsPoint.exists_epsPoint | (intros; apply GlobalTheory.EpsPoint.exists_epsPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericEndomorphismMumfordRingActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericEndomorphism_mumford_ringAction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
  first | exact @GlobalTheory.Mum.GenericEnd.main | exact GlobalTheory.Mum.GenericEnd.main | (intros; apply GlobalTheory.Mum.GenericEnd.main <;> assumption)
end

