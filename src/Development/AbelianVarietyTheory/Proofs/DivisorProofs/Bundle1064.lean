import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeTheoremPicardGroup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section
namespace GlobalTheory.CubeThm

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem comp_psum {T T' : Over S} {n : ℕ} (f : T' ⟶ T) (v : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    f ≫ psum B v I = psum B (fun i => f ≫ v i) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

theorem lift_comp_cubeCoordinates (x y z : B ⟶ B) :
    (fun i => lift x (lift y z) ≫ x3 B i) = ![x, y, z] := by
  funext i
  fin_cases i <;> simp [x3]

theorem cube_pic (M : GlobalTheory.UU.CP B) (x y z : B ⟶ B) :
    GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) =
      GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) := by
  set c := GlobalTheory.CechPic.cls M.L.L M.L.isLB
  have hT : (Theta B M.L.L).IsLB := LB.isLB_linComb M.L.isLB _ _
  have h0 : GlobalTheory.CechPic.cls (Theta B M.L.L) hT = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff hT).2 ⟨M.c.t, M.c.isGen⟩
  have h1 : (∑ I : ULift.{0} (Finset (Fin 3)),
      ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0 :=
    (GlobalTheory.CechPic.cls_linComb M.L.isLB (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left)
      (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0
  have h2 := congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1
  rw [map_sum, map_zero] at h2
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_psum, lift_comp_cubeCoordinates] at h2
  rw [← Equiv.ulift.symm.sum_comp] at h2
  simp only [Equiv.ulift_symm_down] at h2
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  have e0 : psum B ![x, y, z] ∅ = 1 := rfl
  have e1 : psum B ![x, y, z] {0} = x := (show _ = x * 1 from rfl).trans (mul_one x)
  have e2 : psum B ![x, y, z] {1} = y := (show _ = y * 1 from rfl).trans (mul_one y)
  have e3 : psum B ![x, y, z] {2} = z := (show _ = z * 1 from rfl).trans (mul_one z)
  have e4 : psum B ![x, y, z] {0, 1} = x * y :=
    (show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))
  have e5 : psum B ![x, y, z] {0, 2} = x * z :=
    (show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))
  have e6 : psum B ![x, y, z] {1, 2} = y * z :=
    (show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))
  have e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z :=
    (show _ = x * (y * (z * 1)) from rfl).trans
      ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at h2
  have c0 : (∅ : Finset (Fin 3)).card = 0 := rfl
  have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
  have c2 : ({1} : Finset (Fin 3)).card = 1 := rfl
  have c3 : ({2} : Finset (Fin 3)).card = 1 := rfl
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := rfl
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7] at h2
  norm_num at h2
  rw [← sub_eq_zero]
  rw [← h2]
  abel

end GlobalTheory.CubeThm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxRationalBasisCompatible
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RatDarboux

theorem exists_rat_matrix {F R V W ι : Type} [Field F] [CommRing R] [Nontrivial R] [Algebra F R] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    (j : V →+ W) (hj : ∀ (c : F) x, j (c • x) = algebraMap F R c • j x) (hinj : Function.Injective j)
    (hc : Module.finrank F V = Fintype.card ι) (e₀ e₂ : W ≃ₗ[R] (ι → R))
    (h₀ : ∀ x, ∃ u : ι → F, e₀ (j x) = fun i => algebraMap F R (u i))
    (h₂ : ∀ x, ∃ u : ι → F, e₂ (j x) = fun i => algebraMap F R (u i)) :
    ∃ g : Matrix ι ι F, ∀ w, e₂ w = g.map (algebraMap F R) *ᵥ e₀ w := by
  classical
  have hφ : Function.Injective (algebraMap F R) := (algebraMap F R).injective
  have hvec : ∀ a b : ι → F, (fun i => algebraMap F R (a i)) = (fun i => algebraMap F R (b i)) → a = b := by
    intro a b h
    funext i
    exact hφ (congrFun h i)

  have lin : ∀ (e : W ≃ₗ[R] (ι → R)) (u : V → ι → F), (∀ x, e (j x) = fun i => algebraMap F R (u x i)) →
      ∃ U : V →ₗ[F] (ι → F), ∀ x, U x = u x := by
    intro e u hu
    refine ⟨{ toFun := u, map_add' := ?_, map_smul' := ?_ }, fun x => rfl⟩
    · intro x y
      apply hvec
      rw [← hu, map_add, map_add, hu, hu]
      funext i
      simp
    · intro c x
      apply hvec
      rw [← hu, hj, map_smul, hu]
      funext i
      simp
  choose u₀ hu₀ using h₀
  choose u₂ hu₂ using h₂
  obtain ⟨U₀, hU₀⟩ := lin e₀ u₀ hu₀
  obtain ⟨U₂, hU₂⟩ := lin e₂ u₂ hu₂

  have inj : Function.Injective U₀ := by
    intro x y hxy
    apply hinj
    apply e₀.injective
    rw [hu₀, hu₀, ← hU₀, ← hU₀, hxy]
  have surj : Function.Surjective U₀ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [hc, Module.finrank_fintype_fun_eq_card]
  let E₀ : V ≃ₗ[F] (ι → F) := LinearEquiv.ofBijective U₀ ⟨inj, surj⟩
  refine ⟨LinearMap.toMatrix' (U₂ ∘ₗ E₀.symm.toLinearMap), ?_⟩
  set g := LinearMap.toMatrix' (U₂ ∘ₗ E₀.symm.toLinearMap) with hg

  have onForm : ∀ x, e₂ (j x) = g.map (algebraMap F R) *ᵥ e₀ (j x) := by
    intro x
    have h1 : g *ᵥ U₀ x = U₂ x := by
      rw [hg, LinearMap.toMatrix'_mulVec]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      congr 1
      exact E₀.symm_apply_apply x
    funext i
    rw [hu₂, hu₀, ← hU₂, ← h1, ← hU₀]
    exact RingHom.map_mulVec (algebraMap F R) g (U₀ x) i

  have onBasis : ∀ i, e₂ (e₀.symm (Pi.single i 1)) = g.map (algebraMap F R) *ᵥ Pi.single i 1 := by
    intro i
    obtain ⟨x, hx⟩ := surj (Pi.single i 1)
    have hs : e₀ (j x) = Pi.single i 1 := by
      rw [hu₀, ← hU₀, hx]
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [← hs, LinearEquiv.symm_apply_apply, onForm]
  have hL : (e₂.toLinearMap ∘ₗ e₀.symm.toLinearMap) = Matrix.mulVecLin (g.map (algebraMap F R)) := by
    apply (Pi.basisFun R ι).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Matrix.mulVecLin_apply]
    exact onBasis i
  intro w
  have := LinearMap.congr_fun hL (e₀ w)
  simpa using this

theorem std_form {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (a b : κ ⊕ κ → R) :
    a ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) *ᵥ b) =
      (a ∘ Sum.inl) ⬝ᵥ (b ∘ Sum.inr) - (b ∘ Sum.inl) ⬝ᵥ (a ∘ Sum.inr) := by
  rw [Matrix.fromBlocks_mulVec]
  conv_lhs => rw [← Sum.elim_comp_inl_inr a]
  rw [sumElim_dotProduct_sumElim]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero, Matrix.neg_mulVec,
    dotProduct_comm (a ∘ Sum.inr)]
  simp only [neg_dotProduct, sub_eq_add_neg]

theorem exists_rat_symplectic_gen {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R]
    [Nontrivial R] [Algebra F R] {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    {Bf : Matrix α β (R ⊗[F] E) → Matrix α β (R ⊗[F] E) → R} (d₀ d₂ : Darboux Bf κ)
    (inc : Matrix α β E → Matrix α β (R ⊗[F] E)) (hinc : ∀ x a b, inc x a b = (1 : R) ⊗ₜ[F] x a b)
    (hc : Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E)
    (h₀ : ∀ x : Matrix α β E, ∃ u v : κ → F,
      d₀.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i)))
    (h₂ : ∀ x : Matrix α β E, ∃ u v : κ → F,
      d₂.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i))) :
    ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
      ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  classical
  have hφ : Function.Injective (algebraMap F R) := (algebraMap F R).injective

  let j : Matrix α β E →+ Matrix α β (R ⊗[F] E) :=
    { toFun := inc
      map_zero' := by
        ext a b
        simp [hinc]
      map_add' := by
        intro x y
        ext a b
        simp [hinc, TensorProduct.tmul_add] }
  have hj : ∀ (c : F) x, j (c • x) = algebraMap F R c • j x := by
    intro c x
    ext a b
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinc, Matrix.smul_apply]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [Algebra.smul_def]
  have hinj : Function.Injective j := by
    intro x y hxy
    ext a b
    have h := congrFun (congrFun hxy a) b
    simp only [j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinc] at h
    apply Algebra.TensorProduct.includeRight_injective (A := R) (B := E) hφ
    simpa [Algebra.TensorProduct.includeRight_apply] using h

  let σ := (LinearEquiv.sumArrowLequivProdArrow κ κ R R).symm
  have hσ : ∀ p : (κ → R) × (κ → R), σ p = Sum.elim p.1 p.2 := fun p => rfl
  have hcard : Module.finrank F (Matrix α β E) = Fintype.card (κ ⊕ κ) := by
    rw [Module.finrank_matrix, Fintype.card_sum, ← hc]
    ring
  have rat : ∀ (d : Darboux Bf κ), (∀ x : Matrix α β E, ∃ u v : κ → F,
      d.e (inc x) = (fun i => algebraMap F R (u i), fun i => algebraMap F R (v i))) →
      ∀ x, ∃ u : κ ⊕ κ → F, (d.e.trans σ) (j x) = fun i => algebraMap F R (u i) := by
    intro d hd x
    obtain ⟨u, v, huv⟩ := hd x
    refine ⟨Sum.elim u v, ?_⟩
    simp only [LinearEquiv.trans_apply, j, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hσ, huv]
    funext i
    cases i <;> rfl
  obtain ⟨g, hg⟩ := GlobalTheory.RatDarboux.exists_rat_matrix j hj hinj hcard (d₀.e.trans σ) (d₂.e.trans σ)
    (rat d₀ h₀) (rat d₂ h₂)
  simp only [LinearEquiv.trans_apply, hσ] at hg
  set G := g.map (algebraMap F R) with hG
  set JR : Matrix (κ ⊕ κ) (κ ⊕ κ) R := Matrix.fromBlocks 0 1 (-1) 0 with hJR

  have form : ∀ (d : Darboux Bf κ) w w',
      Bf w w' = Sum.elim (d.e w).1 (d.e w).2 ⬝ᵥ (JR *ᵥ Sum.elim (d.e w').1 (d.e w').2) := by
    intro d w w'
    rw [hJR, GlobalTheory.RatDarboux.std_form, d.form]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  have pres : ∀ y y' : κ ⊕ κ → R, y ⬝ᵥ (JR *ᵥ y') = y ⬝ᵥ ((Gᵀ * JR * G) *ᵥ y') := by
    intro y y'
    obtain ⟨w, hw⟩ := (d₀.e.trans σ).surjective y
    obtain ⟨w', hw'⟩ := (d₀.e.trans σ).surjective y'
    simp only [LinearEquiv.trans_apply, hσ] at hw hw'
    have h := (form d₀ w w').symm.trans (form d₂ w w')
    rw [hg, hg, hw, hw'] at h
    rw [h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose G y, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
  refine ⟨g, ?_, ?_⟩
  ·
    have hJmap : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = JR := by
      ext i k
      rcases i with i | i <;> rcases k with k | k <;>
        simp [hJR, Matrix.one_apply, apply_ite (algebraMap F R)]
    have key : (gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g).map (algebraMap F R) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hJmap, ← hG]
      ext i k
      have h := pres (Pi.single i 1) (Pi.single k 1)
      simp only [single_dotProduct, one_mul, Matrix.mulVec_single_one] at h
      exact h.symm
    exact Matrix.map_injective hφ key
  · intro w
    unfold GlobalTheory.AdelicSvN.act
    rw [← hG, ← hg w]
    exact Prod.ext (Sum.elim_comp_inl (d₂.e w).1 (d₂.e w).2).symm (Sum.elim_comp_inr (d₂.e w).1 (d₂.e w).2).symm

theorem exists_rat_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β κ : Type) [Fintype α] [Fintype β]
  [Fintype κ] [DecidableEq κ] (Bf : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F) (d₀ d₂ : Darboux Bf κ),
  Fintype.card κ * 2 = Fintype.card α * Fintype.card β * Module.finrank F E →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₀.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  (∀ x : Matrix α β E, ∃ u v : κ → F, d₂.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
  ∃ g : Matrix (κ ⊕ κ) (κ ⊕ κ) F, gᵀ * Matrix.fromBlocks 0 1 (-1) 0 * g = Matrix.fromBlocks 0 1 (-1) 0 ∧
    ∀ w, d₂.e w = GlobalTheory.AdelicSvN.act g (d₀.e w) := by
  intro F E _ _ _ _ _ α β κ _ _ _ _ Bf d₀ d₂ hc h₀ h₂

  have : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  exact exists_rat_symplectic_gen (R := AF F) d₀ d₂ (incM F)
    (fun x a b => rfl) hc h₀ h₂

end GlobalTheory.RatDarboux
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointsTransferIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.Loc

theorem smul_conj_iff {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (f : A) {N N' : Matrix n n A}
    (h : N * N' = 1) (h' : N' * N = 1) (X : Matrix n n A) :
    f • (N * X * N' - 1) = N * X * N' - 1 ↔ f • (X - 1) = X - 1 := by
  have e : N * X * N' - 1 = N * (X - 1) * N' := by rw [mul_sub, sub_mul, mul_one, h]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul]
  refine ⟨fun k => ?_, fun k => by rw [k]⟩
  have := congrArg (fun Y => N' * Y * N) k
  simpa only [← mul_assoc, h', one_mul, mul_assoc _ N' N, mul_one] using this

variable {D : D7}

theorem parts_ext {a b : Formalism.L2.Theta.AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  apply e.injective
  exact Prod.ext (by rw [he1, he1, h1]) (by rw [he2, he2, h2])

theorem map_one_apply {A B n : Type} [CommRing A] [CommRing B] [DecidableEq n] (φ : A →+* B) (i j : n) :
    φ ((1 : Matrix n n A) i j) = (1 : Matrix n n B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem suppF_iff_fin (V : HSp D) (f : Formalism.L2.Theta.AE D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) :
    SuppF V f g ↔ finPart D f • (finMat D.sp.cm.sig V.gram g - 1) = finMat D.sp.cm.sig V.gram g - 1 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have e2 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = (finMat D.sp.cm.sig V.gram g - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, map_one_apply]
    rfl
  have e1 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_one_apply, sub_eq_zero]
    have : infHom V g = 1 := hg
    exact congrArg (fun m : GL (Fin V.rank) _ => m.1 i j) this
  rw [Matrix.smul_apply, smul_eq_mul, ← e2]
  refine ⟨fun h => by rw [← RingHom.map_mul, h], fun h => parts_ext ?_ ?_⟩
  · rw [RingHom.map_mul, e1, mul_zero]
  · rw [RingHom.map_mul, h]

theorem comp_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) → GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D f) Q = 1) ∧
    (Q.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D f) Q = 0) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, ⟨α, rfl, h1, h0⟩, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (finPart D (algebraMap _ (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α))) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α) := by
    rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
    change GlobalTheory.LFun.toCompl rfl ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α) ⊗ₜ[D.host.F]
      (1 : D.host.E)) = _
    rw [GlobalTheory.LFun.toCompl_tmul, map_one, mul_one]
    rfl
  rw [e]
  refine ⟨fun hQ => ?_, fun hQ => by rw [h0 _ hQ, map_zero]⟩
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α = 1 := by
    revert h1
    generalize P.under (𝓞 D.host.F) = v at hQ
    subst hQ
    exact id
  rw [h2, map_one]

theorem supp_iff_loc [IsCMField D.host.E] {n : ℕ} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) (x : UA D.host.E n) :
    finPart D f • (((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1) =
      ((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1 ↔
    ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → cLoc u x = 1 := by
  have key : ∀ i j (u : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      ((((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1) i j) u =
      (cLoc u x).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro i j u
    rw [Matrix.sub_apply, map_sub, Matrix.map_apply, RingEquiv.apply_symm_apply,
      ← map_one_apply ((pLoc D.host.E u).comp (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom)]
    rfl
  have ev : ∀ (a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (u : HeightOneSpectrum (𝓞 D.host.E)),
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (a * b) u =
        GlobalTheory.LFun.finAdEquiv D.host.F D.host.E a u * GlobalTheory.LFun.finAdEquiv D.host.F D.host.E b u := by
    intro a b u
    rw [map_mul]; rfl
  constructor
  · intro k u hu
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun m => GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (m i j) u) k
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [ev, (comp_of_isPrimeIdem h u).2 hu, zero_mul, key, eq_comm, sub_eq_zero] at this
    exact this
  · intro k
    refine Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      (FiniteAdeleRing.ext _ fun u => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, ev]
    by_cases hu : u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)
    · rw [(comp_of_isPrimeIdem h u).1 hu, one_mul]
    · rw [key, k u hu, Units.val_one, sub_self, mul_zero]

theorem finMat_mul (V : HSp D) (g h : Formalism.L2.Theta.GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h := by
  have := congrArg Units.val ((finHom V).map_mul g h)
  rw [Units.val_mul] at this
  exact this

theorem finMat_one (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : Formalism.L2.Theta.GA D V) = 1 :=
  congrArg Units.val (finHom V).map_one

theorem map_mul_inv {K A n : Type} [Field K] [CommRing A] [Fintype n] [DecidableEq n] {T : Type} [FunLike T K A]
    [RingHomClass T K A] (φ : T) {M : Matrix n n K} (hu : IsUnit M.det) : M.map φ * M⁻¹.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locU_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* Formalism.L2.Theta.GA D V) (h₀ : Formalism.L2.Theta.GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) := by
  intro D _ V j h₀ M hM hh hfin hmat _
  refine ⟨fun P => ?_, fun P e f h x => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    exact GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hu : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hM
  have hG : cj j h₀ x ∈ GfC V ↔ x ∈ finU D.host.E V.rank := by
    rw [hfin, cj_apply, Subgroup.mul_mem_cancel_right _ hh, Subgroup.mul_mem_cancel_left _ (inv_mem hh)]
  have hL : x ∈ locU V.rank P ↔ x ∈ finU D.host.E V.rank ∧ ∀ u : HeightOneSpectrum (𝓞 D.host.E),
      u.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → cLoc u x = 1 := by
    simp only [locU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rw [hL, ← hG]
  refine and_congr_right fun hx => ?_
  have m1 := map_mul_inv (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F]
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) hu
  have m2 := mul_eq_one_comm.1 m1
  have e1 : finMat D.sp.cm.sig V.gram (cj j h₀ x) =
      finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram (j x) * finMat D.sp.cm.sig V.gram h₀ := by
    rw [cj_apply, finMat_mul, finMat_mul]
  have k1 : finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram h₀ = 1 := by
    rw [← finMat_mul, inv_mul_cancel, finMat_one]
  refine ((suppF_iff_fin V f hx).trans ?_).symm
  rw [e1]
  refine (smul_conj_iff _ k1 (mul_eq_one_comm.1 k1) _).trans ?_
  rw [hmat]
  exact (smul_conj_iff _ m1 m2 _).trans (supp_iff_loc h x)

end GlobalTheory.DefTransfer.Loc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtaleStatement
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_le_of_pullback_le_pow_finiteEtale : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g := by
  first | exact @GlobalTheory.degree_le_of_pull_le_pow | exact GlobalTheory.degree_le_of_pull_le_pow | (intros; apply GlobalTheory.degree_le_of_pull_le_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetProductDepthInChartEqSumFactorDepthsStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), nuProdC Ch X cx = ∑ f : Lt1 Dw, nuFacC Ch X f (cx f) := by
  first | exact @GlobalTheory.FactorDepthProd.nuProdC_eq_sum | exact GlobalTheory.FactorDepthProd.nuProdC_eq_sum | (intros; apply GlobalTheory.FactorDepthProd.nuProdC_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositiveStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_sign_of_positive_eigenvector_one_positive : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  first | (exact @GlobalTheory.diag_sign_of_pos_eigenvector) | (exact GlobalTheory.diag_sign_of_pos_eigenvector) | (intros; apply GlobalTheory.diag_sign_of_pos_eigenvector  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorSupportTransferRankStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_support_transfer_rank : ∀ {D : D7} (V V' : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), V'.rank = V.rank → IsPrimeIdem P e f → SuppF V f α → DivAt V e ϖ d α → ∃ α' : GA D V', SuppF V' f α' ∧ DivAt V' e ϖ d α' := by
  first | exact @GlobalTheory.DivMove.exists_divAt_of_rank_eq | exact GlobalTheory.DivMove.exists_divAt_of_rank_eq | (intros; apply GlobalTheory.DivMove.exists_divAt_of_rank_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  first | exact @GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | exact GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | (intros; apply GlobalTheory.SchANonzero.exists_mem_schA_ne_zero <;> assumption)
end

