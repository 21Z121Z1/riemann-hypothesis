import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsLeMemPowOfMulMemPowOfNonZeroDivisor
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsCrOfFinset
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CrLocal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem qcont_map {X V W : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W]
    [Module ℚ_[l] W] (f : V →ₗ[ℚ_[l]] W) {c : X → V} (hc : QCont l c) : QCont l fun x => f (c x) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : ContinuousAdd W := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap f).comp hc

theorem qcont_add {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c d : X → V}
    (hc : QCont l c) (hd : QCont l d) : QCont l fun x => c x + d x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hc hd

theorem qcont_sum {X V ι : Type} [Fintype ι] [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c : ι → X → V}
    (hc : ∀ i, QCont l (c i)) : QCont l fun x => ∑ i, c i x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact continuous_finset_sum _ fun i _ => hc i

theorem contAction_of_qcont {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V)
    (h : ∀ v, QCont l fun g => ρ g v) : ContAction ρ := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  have h' : ∀ v, Continuous fun g => ρ g v := fun v => by
    have := h v
    unfold QCont at this
    rwa [← eq_moduleTopology ℚ_[l] V] at this
  let b := Module.finBasis ℚ_[l] V
  have e : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.coord i p.2 • ρ p.1 (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2, map_sum]
    simp only [map_smul, Basis.coord_apply]
  unfold ReciprocityTheory.Gal.ContAction
  rw [e]
  exact continuous_finset_sum _ fun i _ =>
    ((IsModuleTopology.continuous_of_linearMap (b.coord i)).comp continuous_snd).smul ((h' _).comp continuous_fst)

theorem qcont_colRep {B : Type} [CommRing B] [Algebra ℚ_[l] B] (ρ : G →* GL (Fin 3) B)
    (h : ∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) (v : Fin 3 → B) :
    QCont l fun g => resCoef ℚ_[l] (colRep ρ) g v := by
  have e : (fun g => resCoef ℚ_[l] (colRep ρ) g v) = fun g => ∑ i, ∑ j,
      ((LinearMap.single ℚ_[l] (fun _ : Fin 3 => B) i).comp (LinearMap.mulRight ℚ_[l] (v j)))
        ((ρ g : Matrix (Fin 3) (Fin 3) B) i j) := by
    funext g
    ext k
    change (ρ g : Matrix (Fin 3) (Fin 3) B).mulVec v k = _
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact qcont_sum fun i => qcont_sum fun j => qcont_map _ (h i j)

variable [IsTopologicalGroup G] {φ : G →* GQ l}

theorem cr_sub (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (f : V →ₗ[ℚ_[l]] W) (hf : ∀ g x, f (ρ g x) = σ g (f x)) (hi : Function.Injective f) (h : IsCr φ σ) :
    IsCr φ ρ := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact ((isCrys_isDR_sub_quot φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ) f hf).1 hi).1 h

theorem cr_prod (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (h : IsCr φ ρ) (h' : IsCr φ σ) : IsCr φ (ρ.prod σ) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact (isCrys_isDR_prod φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ)).1 h h'

theorem exists_cr_of_finset (hφ : IsOpenEmbedding φ) {V ι : Type} [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (N : ι → Set V)
    (h : ∀ i, ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → x ∈ N i) (S : Finset ι) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → ∀ i ∈ S, x ∈ N i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, 0, fun v => ?_, ?_,
      fun _ _ => Subsingleton.elim _ _, by simp⟩
    · exact @continuous_const _ _ _ (moduleTopology ℚ_[l] PUnit) v
    · unfold IsCr
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, mul_zero]
  | insert a S _ ih =>
    obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := ih
    obtain ⟨W', _, _, _, σ', f', h1', h2', h3', h4'⟩ := h a
    refine ⟨W × W', inferInstance, inferInstance, inferInstance, σ.prod σ', f.prod f', fun v => ?_,
      cr_prod hφ σ σ' h1 h1' h2 h2', fun g x => ?_, fun x hx i hi => ?_⟩
    · have := qcont_add (qcont_map (LinearMap.inl ℚ_[l] W W') (h1 v.1)) (qcont_map (LinearMap.inr ℚ_[l] W W') (h1' v.2))
      convert this using 2 with g
      ext <;> simp [Representation.prod]
    · ext <;> simp [Representation.prod, h3, h3']
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h4' x (congrArg Prod.snd hx)
      · exact h4 x (congrArg Prod.fst hx) i hi

theorem isCr_of_local : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (ρ : G →* GL (Fin 3) B), (∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) → (∀ (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra B B'] [IsScalarTower ℚ_[l] B B'], IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (algebraMap B B')).comp ρ))) → IsCr φ (colRep ρ) := by
  intro l _ G _ _ _ φ hφ B _ _ _ ρ hc h
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := exists_cr_of_finset hφ (resCoef ℚ_[l] (colRep ρ))
    (fun m : MaximalSpectrum B => {v | ∀ i, algebraMap B (Localization.AtPrime m.asIdeal) (v i) = 0})
    (fun m => by
      let a : B →ₗ[ℚ_[l]] Localization.AtPrime m.asIdeal :=
        (IsScalarTower.toAlgHom ℚ_[l] B (Localization.AtPrime m.asIdeal)).toLinearMap
      haveI : Module.Finite ℚ_[l] (Localization.AtPrime m.asIdeal) :=
        Module.Finite.of_surjective a (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
      refine ⟨Fin 3 → Localization.AtPrime m.asIdeal, inferInstance, inferInstance, inferInstance,
        resCoef ℚ_[l] (colRep ((Matrix.GeneralLinearGroup.map
          (algebraMap B (Localization.AtPrime m.asIdeal))).comp ρ)), a.compLeft (Fin 3),
        qcont_colRep _ fun i j => qcont_map a (hc i j), h _, fun g x => ?_, fun x hx i => congrFun hx i⟩
      ext k
      exact RingHom.map_mulVec (algebraMap B (Localization.AtPrime m.asIdeal)) _ x k) Finset.univ
  refine cr_sub hφ (resCoef ℚ_[l] (colRep ρ)) σ (qcont_colRep ρ hc) h1 f h3 ?_ h2
  rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  exact eq_zero_of_localization _ fun J hJ => h4 x hx ⟨J, hJ⟩ (Finset.mem_univ _) i

end GlobalTheory.CrLocal
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsGLConjEqDiagonalOfCharpolyEqProd
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem isUnit_det_sub_smul_one_of_forall_not_isUnit {C : Type} [CommRing C] [IsLocalRing C]
    {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n C) (hQ : ∀ i j, ¬ IsUnit (Q i j))
    (c : C) (hc : IsUnit c) : IsUnit (Q - c • (1 : Matrix n n C)).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue C).mapMatrix (Q - c • (1 : Matrix n n C)) =
      (-(IsLocalRing.residue C c)) • (1 : Matrix n n _) := by
    ext i j
    have hq : IsLocalRing.residue C (Q i j) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (hQ i j))
    by_cases h : i = j
    · subst h; simp [hq]
    · simp [hq, h]
  rw [hm, Matrix.det_smul, Matrix.det_one, mul_one]
  refine pow_ne_zero _ (neg_ne_zero.2 ?_)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hc

theorem exists_GL_conj_eq_diagonal_of_charpoly_eq_prod :
    ∀ {C : Type} [CommRing C] [IsLocalRing C] (A : Matrix (Fin 3) (Fin 3) C) (p : Fin 3 → C),
      (∀ a b, a ≠ b → IsUnit (p a - p b)) → A.charpoly = ∏ a, (X - Polynomial.C (p a)) →
      ∃ h : GL (Fin 3) C, (h : Matrix (Fin 3) (Fin 3) C) * A *
        ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal p := by
  intro C _ _ A p hp hchar
  classical
  set P : Fin 3 → C[X] := fun a => ∏ b ∈ Finset.univ.erase a, (X - Polynomial.C (p b)) with hPdef
  have hfull : ∀ a, (X - Polynomial.C (p a)) * P a = ∏ b, (X - Polynomial.C (p b)) := fun a =>
    Finset.mul_prod_erase _ (fun b => X - Polynomial.C (p b)) (Finset.mem_univ a)
  have hz : aeval A (∏ b, (X - Polynomial.C (p b))) = 0 := by
    rw [← hchar]; exact Matrix.aeval_self_charpoly A
  have hsplit : ∀ (f : C[X]) a, f = Polynomial.C (f.eval (p a)) +
      (X - Polynomial.C (p a)) * (f /ₘ (X - Polynomial.C (p a))) := by
    intro f a
    have h := modByMonic_add_div f (X - Polynomial.C (p a))
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact h.symm
  have key : ∀ (f : C[X]) a, aeval A (f * P a) = f.eval (p a) • aeval A (P a) := by
    intro f a
    conv_lhs => rw [hsplit f a]
    rw [add_mul, mul_comm (X - Polynomial.C (p a)), mul_assoc, hfull]
    simp only [map_add, map_mul, hz, mul_zero, add_zero, aeval_C, Algebra.smul_def]
  have hq : ∀ a, IsUnit ((P a).eval (p a)) := by
    intro a
    simp only [hPdef, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun b hb => hp a b (Finset.ne_of_mem_erase hb).symm)
  have hq0 : ∀ a b, a ≠ b → (P a).eval (p b) = 0 := by
    intro a b hab
    simp only [hPdef, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩) (sub_self _)
  have hBA : ∀ a, aeval A (P a) * A = p a • aeval A (P a) := by
    intro a
    have h := key X a
    rwa [mul_comm, map_mul, aeval_X, eval_X] at h
  have hBB : ∀ a b, aeval A (P a) * aeval A (P b) = (P a).eval (p b) • aeval A (P b) := by
    intro a b
    rw [← map_mul]
    exact key (P a) b
  have hex : ∀ a, ∃ i j, IsUnit (aeval A (P a) i j) := by
    intro a
    by_contra hne
    push_neg at hne
    obtain ⟨u, hu⟩ := hq a
    set E := ((u⁻¹ : Cˣ) : C) • aeval A (P a) with hE
    have hEn : ∀ i j, ¬ IsUnit (E i j) := by
      intro i j h
      apply hne i j
      have h' : aeval A (P a) i j = (u : C) * E i j := by
        rw [hE, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]
      rw [h']
      exact (Units.isUnit u).mul h
    have hEE : E * E = E := by
      rw [hE, Matrix.smul_mul, Matrix.mul_smul, hBB, ← hu, smul_smul, smul_smul,
        mul_assoc, Units.inv_mul, mul_one]
    have hdet := isUnit_det_sub_smul_one_of_forall_not_isUnit E hEn 1 isUnit_one
    rw [one_smul] at hdet
    have hE0 : E = 0 := by
      have h1 : (E - 1) * E = 0 := by rw [sub_mul, hEE, one_mul, sub_self]
      obtain ⟨w, hw⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
      calc E = ((w⁻¹ : (Matrix (Fin 3) (Fin 3) C)ˣ) : Matrix (Fin 3) (Fin 3) C) * ((E - 1) * E) := by
            rw [← mul_assoc, ← hw, Units.inv_mul, one_mul]
        _ = 0 := by rw [h1, mul_zero]
    have hB0 : aeval A (P a) = 0 := by
      have h' : aeval A (P a) = (u : C) • E := by rw [hE, smul_smul, Units.mul_inv, one_smul]
      rw [h', hE0, smul_zero]
    have hs := congrArg (aeval A) (hsplit (P a) a)
    rw [hB0, map_add, aeval_C, map_mul, ← hu] at hs
    have hinv : aeval A (X - Polynomial.C (p a)) *
        (-(((u⁻¹ : Cˣ) : C) • aeval A (P a /ₘ (X - Polynomial.C (p a))))) = 1 := by
      have h2 : aeval A (X - Polynomial.C (p a)) * aeval A (P a /ₘ (X - Polynomial.C (p a))) =
          -algebraMap C _ (u : C) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hs.symm
      rw [mul_neg, Matrix.mul_smul, h2, smul_neg, neg_neg, Algebra.smul_def, ← map_mul,
        Units.inv_mul, map_one]
    have hdx : IsUnit (aeval A (X - Polynomial.C (p a))).det :=
      IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hinv, Matrix.det_one])
    have hev : A.charpoly.eval (p a) = 0 := by
      rw [hchar, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
    rw [Matrix.eval_charpoly] at hev
    have hneg : Matrix.scalar (Fin 3) (p a) - A = -(aeval A (X - Polynomial.C (p a))) := by
      simp [Algebra.algebraMap_eq_smul_one, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hneg, Matrix.det_neg] at hev
    have hu2 : IsUnit ((-1 : C) ^ Fintype.card (Fin 3) * (aeval A (X - Polynomial.C (p a))).det) :=
      ((isUnit_neg_one).pow _).mul hdx
    rw [hev] at hu2
    exact not_isUnit_zero hu2
  choose i j hij using hex
  let H : Matrix (Fin 3) (Fin 3) C := Matrix.of fun a k => aeval A (P a) (i a) k
  let Q : Matrix (Fin 3) (Fin 3) C := Matrix.of fun k b => aeval A (P b) k (j b)
  have hHQ : H * Q = Matrix.diagonal fun a => (P a).eval (p a) * aeval A (P a) (i a) (j a) := by
    ext a b
    have h' : (H * Q) a b = (aeval A (P a) * aeval A (P b)) (i a) (j b) := by
      simp [H, Q, Matrix.mul_apply]
    rw [h', hBB, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp
    · rw [hq0 a b hab, zero_mul, Matrix.diagonal_apply_ne _ hab]
  have hdetH : IsUnit H.det := by
    have h2 : IsUnit (H * Q).det := by
      rw [hHQ, Matrix.det_diagonal]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun a _ => (hq a).mul (hij a))
    rw [Matrix.det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hHA : H * A = Matrix.diagonal p * H := by
    ext a k
    have h' : (H * A) a k = (aeval A (P a) * A) (i a) k := by simp [H, Matrix.mul_apply]
    rw [h', hBA, Matrix.diagonal_mul]
    simp [H]
  have hU := (Matrix.isUnit_iff_isUnit_det H).2 hdetH
  refine ⟨hU.unit, ?_⟩
  rw [IsUnit.unit_spec, hHA, mul_assoc, hU.mul_val_inv, mul_one]

end GlobalTheory
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsLeMemPowOfMulMemPowOfNonZeroDivisorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_mem_pow_of_mul_mem_pow_of_nonZeroDivisor : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A), (∀ a, δ * a = 0 → a = 0) → ∀ j : ℕ, ∃ k : ℕ, j ≤ k ∧ ∀ a, δ * a ∈ m ^ k → a ∈ m ^ j := by
  first | exact @GlobalTheory.exists_pow_mem_of_mul_mem_pow | exact GlobalTheory.exists_pow_mem_of_mul_mem_pow | (intros; apply GlobalTheory.exists_pow_mem_of_mul_mem_pow <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.FinrankDualInvariantsScalarRepEqFinrankKerSmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dualInvariants_scalarRep_eq_finrank_ker_smul : ∀ {G E B : Type} [Group G] [Field E] [CommRing B] [Algebra E B] [Module.Finite E B] {N : Type} [AddCommGroup N] [Module B N] [Module E N] [IsScalarTower E B N] [Module.Finite E N] (χ : G →* Bˣ) (ε : G →* Eˣ) (ρ : Representation E G N), (∀ g x, ρ g x = (χ g : B) • x) → ∀ δ : B, Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) = Ideal.span {δ} → finrank E ↥(H0dual ε ρ) = finrank E ↥(LinearMap.ker ((LinearMap.lsmul B N δ).restrictScalars E)) := by
  intro G E B _ _ _ _ _ N _ _ _ _ _ χ ε ρ hρ δ hδ
  set L := (LinearMap.lsmul B N δ).restrictScalars E with hL
  have key : H0dual ε ρ = (LinearMap.range L).dualAnnihilator := by
    ext f
    have hmem : f ∈ H0dual ε ρ ↔ ∀ (g : G) (x : N), f (ρ g x) = (ε g : E) * f x := by
      unfold H0dual
      exact Iff.rfl
    rw [hmem, Submodule.mem_dualAnnihilator]
    let S : Ideal B :=
      { carrier := {b | ∀ x : N, f (b • x) = 0}
        add_mem' := fun {a b} ha hb x => by
          simp only [Set.mem_setOf_eq] at ha hb
          rw [add_smul, map_add, ha x, hb x, add_zero]
        zero_mem' := fun x => by simp
        smul_mem' := fun c b hb x => by
          simp only [Set.mem_setOf_eq] at hb
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb _ }
    have hS : ∀ b, b ∈ S ↔ ∀ x : N, f (b • x) = 0 := fun b => Iff.rfl
    have hgen : ∀ g, (∀ x, f (ρ g x) = (ε g : E) * f x) ↔
        ((χ g : B) - algebraMap E B (ε g)) ∈ S := by
      intro g
      rw [hS]
      refine forall_congr' fun x => ?_
      rw [hρ, sub_smul, map_sub, algebraMap_smul, f.map_smul (ε g : E) x, smul_eq_mul, sub_eq_zero]
    constructor
    · intro h
      have hle : Ideal.span (Set.range fun g => (χ g : B) - algebraMap E B (ε g)) ≤ S := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        exact (hgen g).1 (h g)
      rw [hδ] at hle
      have hd : δ ∈ S := hle (Ideal.subset_span rfl)
      rintro _ ⟨x, rfl⟩
      exact hd x
    · intro h g
      rw [hgen]
      have hd : δ ∈ S := fun x => h _ ⟨x, rfl⟩
      have hle : Ideal.span {δ} ≤ S := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hd
      rw [← hδ] at hle
      exact hle (Ideal.subset_span ⟨g, rfl⟩)
  rw [key]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range L)
  have h2 := LinearMap.finrank_range_add_finrank_ker L
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ModuleFiniteQuotientMaximalPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_quotient_maximal_pow : ∀ {K A : Type} [Field K] [CommRing A] [Algebra K A] [IsNoetherianRing A] (m : Ideal A), Module.Finite K (A ⧸ m) → ∀ k : ℕ, Module.Finite K (A ⧸ m ^ k) := by
  intro K A _ _ _ _ m hm k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, Ideal.one_eq_top]
    infer_instance
  have hle : m ^ k ≤ m := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hk)
  let f : (A ⧸ m ^ k) →ₐ[K] A ⧸ m := Ideal.Quotient.factorₐ K hle
  have hsurj : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  refine Module.finite_of_surjective_of_ker_le_nilradical f hsurj ?_ ?_
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ m := by
      rw [RingHom.mem_ker] at hx
      have : Ideal.Quotient.mk m a = 0 := hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.zero_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow ha k
  · exact IsNoetherian.noetherian _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SpanCharacterSubCyclotomicEqOfPositiveWeight
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CharCycIdeal

theorem isClosed_ideal {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [TopologicalSpace B]
    [IsModuleTopology ℚ_[l] B] (J : Ideal B) : IsClosed (J : Set B) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨f, hf, hJ⟩ := Submodule.exists_le_ker_of_notMem (p := J.restrictScalars ℚ_[l]) (v := x) hx
  have hc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  refine Filter.mem_of_superset ((isOpen_ne.preimage hc).mem_nhds (x := x) hf) fun y hy h => hy ?_
  exact hJ (x := y) h

theorem span_range_sub_cyc : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (χ : G →* Bˣ), Continuous (fun g => (χ g : B)) → ∀ w : ℤ, 1 ≤ w → (∀ g, φ g ∈ Iq l → χ g = cycA l l B (φ g) ^ w) → ∀ σ : G, ((Iq l).comap φ ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ → Ideal.span (Set.range fun g => (χ g : B) - (cycA l l B (φ g) : B)) = (if w = 1 then Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} else ⊤) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ χ hχ w hw hI σ hσ
  have hA : ∀ g : GQ l, (cycA l l B g : B) = algebraMap ℚ_[l] B (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun g =>
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B _
  split_ifs with h1
  · subst h1
    refine le_antisymm ?_ (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨σ, rfl⟩))
    set J := Ideal.span {(χ σ : B) - (cycA l l B (φ σ) : B)} with hJ
    have hε : Continuous fun g => (cycA l l B (φ g) : B) := by
      simp only [hA]
      have h0 : Continuous (algebraMap ℚ_[l] B) :=
        IsModuleTopology.continuous_of_linearMap (Algebra.linearMap ℚ_[l] B)
      have h2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
      exact h0.comp (h2.comp (Units.continuous_val.comp
        ((UpperTheory.V.Loc.cycFacts l l).1.comp hφ.continuous)))
    let q : Bˣ →* (B ⧸ J)ˣ := Units.map (Ideal.Quotient.mk J : B →* B ⧸ J)
    let H : Subgroup G := (q.comp χ).eqLocus (q.comp ((cycA l l B).comp φ))
    have hH : ∀ g, g ∈ H ↔ (χ g : B) - (cycA l l B (φ g) : B) ∈ J := fun g => by
      rw [← Ideal.Quotient.eq]
      exact Units.ext_iff
    have hcl : IsClosed (H : Set G) := by
      have : (H : Set G) = (fun g => (χ g : B) - (cycA l l B (φ g) : B)) ⁻¹' (J : Set B) := Set.ext hH
      rw [this]
      exact (isClosed_ideal (l := l) J).preimage (hχ.sub hε)
    have hle : (Iq l).comap φ ⊔ Subgroup.zpowers σ ≤ H := by
      refine sup_le (fun g hg => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [hH, hI g hg, zpow_one, sub_self]
        exact J.zero_mem
      · rw [hH]
        exact Ideal.subset_span rfl
    have htop := Subgroup.topologicalClosure_minimal _ hle hcl
    rw [hσ] at htop
    rw [Ideal.span_le]
    rintro _ ⟨g, rfl⟩
    exact (hH g).1 (htop (Subgroup.mem_top g))
  · obtain ⟨s, ⟨⟨g, rfl⟩, hg⟩, hs⟩ := ((UpperTheory.V.Loc.cycInertia l).2 φ.range hφ.isOpen_range).2
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, w = ((n + 2 : ℕ) : ℤ) := ⟨(w - 2).toNat, by omega⟩
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨g, rfl⟩) ?_
    show IsUnit ((χ g : B) - (cycA l l B (φ g) : B))
    rw [hI g hg, zpow_natCast, Units.val_pow_eq_pow_val, hA, ← map_pow, ← map_sub]
    refine IsUnit.map _ (Ne.isUnit fun h => hs ?_)
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨n + 1, n.succ_pos, ?_⟩
    have h2 : cyc l l (φ g) ^ (n + 2) = cyc l l (φ g) := by
      apply Units.ext
      apply Subtype.ext
      rw [Units.val_pow_eq_pow_val]
      push_cast
      exact sub_eq_zero.1 h
    rw [pow_succ] at h2
    exact mul_eq_right.1 h2

end GlobalTheory.CharCycIdeal
end

