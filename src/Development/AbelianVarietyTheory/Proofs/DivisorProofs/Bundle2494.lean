import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2397
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MulEqOneOfComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrder
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CasimirOrder

open Matrix

variable {O : Type} [Ring O] {r : ℕ}

theorem exists_W_of_casimir (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ)
    (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a)
    (hp : ∀ a, a ≠ 0 → 0 < φ (s a * a))
    (hcen : ∀ a, a * casimir x s φ = casimir x s φ * a)
    (hpos : ∀ u, u ≠ 0 → 0 < φ (s (casimir x s φ * u) * u)) :
    ∃ (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), ((W + Wᵀ).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧
      ∑ i, ∑ j, W i j • (s (x i) * x j) = (d : O) := by
  classical
  set C := casimir x s φ with hC
  have sC : s C = C := casimir_star hs hss hφs
  set s' : O →+ O := s.comp (AddMonoidHom.mulLeft C) with hs'
  have hs'a : ∀ u, s' u = s u * C := fun u => by simp [hs', hs, sC]
  have b'symm : ∀ u v, form s' φ u v = form s' φ v u := by
    intro u v
    simp only [form_apply, hs'a]
    rw [← hφs (s u * C * v), hs, hs, hss, sC, ← _root_.mul_assoc]
  have bsymm := form_symm hs hss hφs
  set G := gram (⇑x) s φ with hG
  set G' := gram (⇑x) s' φ with hG'
  have hGpd : (G.map (Int.cast : ℤ → ℝ)).PosDef :=
    posDef_gram x (form s φ) bsymm fun w hw => by simpa using hp w hw
  have hG'pd : (G'.map (Int.cast : ℤ → ℝ)).PosDef := by
    refine posDef_gram x (form s' φ) b'symm fun w hw => ?_
    have h := hpos w hw
    simp only [form_apply, hs'a]
    rwa [hs, sC] at h
  have hδ : 0 < G.det := by
    have := hGpd.det_pos
    rw [← Int.cast_det] at this
    exact_mod_cast this
  have hδ' : 0 < G'.det := by
    have := hG'pd.det_pos
    rw [← Int.cast_det] at this
    exact_mod_cast this
  set A := G.adjugate with hA
  set A' := G'.adjugate with hA'
  have hAs : ∀ i j, A i j = A j i := adjugate_gram_symm hs hss hφs
  have hG't : G'ᵀ = G' := by
    ext i j
    simp only [transpose_apply, hG', gram_eq, of_apply]
    exact b'symm _ _
  have hA's : ∀ i j, A' i j = A' j i := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose G')
    rw [hG't] at h
    simpa using h.symm
  have L1' : ∀ v, G'.det • v = ∑ i, ∑ j, (A' i j * φ (s (x i) * C * v)) • x j := by
    intro v
    have h := det_smul_eq_sum x (form s' φ) b'symm v
    rw [← gram_eq] at h
    simpa only [form_apply, hs'a] using h
  have L1 : ∀ v, G.det • v = ∑ i, ∑ j, (A i j * φ (s (x i) * v)) • x j := by
    intro v
    have h := det_smul_eq_sum x (form s φ) bsymm v
    rw [← gram_eq] at h
    simpa only [form_apply] using h
  set C₁ : O := ∑ i, ∑ j, A' i j • (s (x i) * x j) with hC₁
  have lhs : G'.det • C = ∑ k, ∑ l, ∑ i, ∑ j,
      (A k l * (A' i j * φ (s (x i) * C * x l))) • (s (x k) * x j) := by
    conv_lhs => rw [hC, casimir]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm, ← mul_smul_comm, L1' (x l), Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_smul]
  have rhs : C * (G.det • C₁) = ∑ i, ∑ j, ∑ a, ∑ b,
      (A' i j * (A a b * φ (s (x a) * (C * x i)))) • (s (x b) * x j) := by
    rw [hC₁, Finset.smul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : C * (G.det • (A' i j • (s (x i) * x j))) = A' i j • (s (G.det • (C * x i)) * x j) := by
      rw [mul_smul_comm, mul_smul_comm, map_zsmul, smul_mul_assoc, hs, sC, smul_comm, ← _root_.mul_assoc,
        ← hcen]
    rw [e, L1 (C * x i)]
    simp only [map_sum, map_zsmul, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  have swap4 : ∀ f : Fin r → Fin r → Fin r → Fin r → O,
      ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ i, ∑ j, ∑ l, ∑ k, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ l, ∑ k, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have key : G'.det • C = C * (G.det • C₁) := by
    rw [lhs, rhs, swap4]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    have hb := b'symm (x i) (x l)
    simp only [form_apply, hs'a] at hb
    rw [hAs l k, ← _root_.mul_assoc (s (x l)), hb]
    ring_nf
  have hC1 : G.det • C₁ = ((G'.det : ℤ) : O) := by
    by_contra hne
    have hw : ((G'.det : ℤ) : O) - G.det • C₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have h := hpos _ hw
    have h0 : C * (((G'.det : ℤ) : O) - G.det • C₁) = 0 := by
      rw [mul_sub, ← key, ← Int.cast_comm, ← zsmul_eq_mul, sub_self]
    rw [h0, map_zero, zero_mul, map_zero] at h
    exact lt_irrefl _ h
  refine ⟨G.det • A', G'.det.toNat, ?_, by omega, ?_⟩
  · have hadj : (G'.map (Int.cast : ℤ → ℝ)).adjugate = A'.map Int.cast := by
      rw [hA']; exact ((Int.castRingHom ℝ).map_adjugate G').symm
    have e : ((G.det • A' + (G.det • A')ᵀ).map (Int.cast : ℤ → ℝ)) =
        ((2 * G.det : ℤ) : ℝ) • (G'.map (Int.cast : ℤ → ℝ)).adjugate := by
      rw [hadj]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
        hA's j i]
      push_cast; ring
    rw [e]
    exact (adjugate_posDef hG'pd).smul (by exact_mod_cast (by omega : (0 : ℤ) < 2 * G.det))
  · have e : ∑ i, ∑ j, (G.det • A') i j • (s (x i) * x j) = G.det • C₁ := by
      rw [hC₁, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_smul]
    rw [e, hC1, ← Int.cast_natCast, Int.toNat_of_nonneg hδ'.le]

end GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

variable {p : ℕ} [Fact p.Prime]

def htStar (D : Datum p) : D.O →+ D.O :=
  (MulOpposite.opAddEquiv.symm.toAddMonoidHom).comp D.star.toAddMonoidHom

@[simp] theorem htStar_apply (D : Datum p) (a : D.O) : htStar D a = (D.star a).unop := rfl

noncomputable def htTrace (D : Datum p) : D.O →+ ℤ where
  toFun a := LinearMap.trace ℤ D.La (DistribMulAction.toLinearMap ℤ D.La a)
  map_zero' := by
    have : DistribMulAction.toLinearMap ℤ D.La (0 : D.O) = 0 := by ext y; exact zero_smul _ _
    rw [this, map_zero]
  map_add' a b := by
    have : DistribMulAction.toLinearMap ℤ D.La (a + b) =
        DistribMulAction.toLinearMap ℤ D.La a + DistribMulAction.toLinearMap ℤ D.La b := by
      ext y; exact add_smul _ _ _
    rw [this, map_add]

theorem htTrace_mul_comm (D : Datum p) (a b : D.O) : htTrace D (a * b) = htTrace D (b * a) := by
  haveI := D.freeLa; haveI := D.finLa
  have hm : ∀ a b : D.O, DistribMulAction.toLinearMap ℤ D.La (a * b) =
      DistribMulAction.toLinearMap ℤ D.La a * DistribMulAction.toLinearMap ℤ D.La b := by
    intro a b; ext y; exact mul_smul _ _ _
  show LinearMap.trace ℤ D.La _ = LinearMap.trace ℤ D.La _
  rw [hm, hm, LinearMap.trace_mul_comm]

noncomputable def htForm (D : Datum p) : D.O →+ ℤ := htTrace D + (htTrace D).comp (htStar D)

theorem htStar_mul (D : Datum p) (a b : D.O) : htStar D (a * b) = htStar D b * htStar D a := by
  simp [map_mul]

theorem htStar_star (D : Datum p) (a : D.O) : htStar D (htStar D a) = a := by
  simpa using D.star_star a

theorem exists_W_datum (D : Datum p) : ∃ (r : ℕ) (x : Module.Basis (Fin r) ℤ D.O) (W : Matrix (Fin r) (Fin r) ℤ)
    (d : ℕ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧
      ∑ i, ∑ j, W i j • (htStar D (x i) * x j) = (d : D.O) := by
  haveI := D.freeO; haveI := D.finO
  have hs := htStar_mul D
  have hss := htStar_star D
  have hφs : ∀ a, htForm D (htStar D a) = htForm D a := by
    intro a; simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hss, add_comm]
  have hφc : ∀ a b, htForm D (a * b) = htForm D (b * a) := by
    intro a b
    simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hs]
    rw [htTrace_mul_comm D a b, htTrace_mul_comm D (htStar D b)]
  have hp : ∀ a, a ≠ 0 → 0 < htForm D (htStar D a * a) := by
    intro a ha
    simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hs, hss]
    have h : 0 < LinearMap.trace ℤ D.La (DistribMulAction.toLinearMap ℤ D.La (a * (D.star a).unop)) := by
      first
        | exact GlobalTheory.UPel.HT.trace_mul_star_pos p D a ha
        | exact GlobalTheory.UPel.HT.trace_mul_star_pos D a ha
        | exact GlobalTheory.UPel.HT.trace_mul_star_pos a ha
    have h' : htTrace D (htStar D a * a) = htTrace D (a * htStar D a) := htTrace_mul_comm D _ _
    have h'' : 0 < htTrace D (a * htStar D a) := h
    omega
  exact ⟨_, Module.finBasis ℤ D.O, exists_W_of_casimir (Module.finBasis ℤ D.O) (htStar D) (htForm D) hs hss hφs hp
    (GlobalTheory.T.integralCasimirElement_central _ _ _ hs hss hφc hφs hp) (GlobalTheory.T.integralCasimirElement_mul_pos _ _ _ hs hss hφc hφs hp)⟩

end GlobalTheory.CasimirOrder

theorem GlobalTheory.CasimirOrder.exists_posdef_relation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ (r : ℕ) (e : Fin r → D.Oᵐᵒᵖ) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), Submodule.span ℤ (Set.range e) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧ ∑ i, ∑ j, W i j • (e j * MulOpposite.op ((D.star (e i).unop).unop)) = (d : D.Oᵐᵒᵖ) := by
  intro p _ D
  obtain ⟨r, x, W, d, hW, hd, hsum⟩ := GlobalTheory.CasimirOrder.exists_W_datum D
  refine ⟨_, fun i => MulOpposite.op (x i), W, d, ?_, hW, hd, ?_⟩
  · have h := x.mulOpposite.span_eq
    convert h using 3
    all_goals first
      | exact Subsingleton.elim _ _
      | (funext i; simp)
  · rw [← MulOpposite.op_natCast, ← hsum, Finset.op_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.op_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulOpposite.op_smul, MulOpposite.op_mul]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricRigidifiedTranslateAmpleKTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_rigidified_translate_ample_K_trivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (b : 𝟙_ _ ⟶ B), IsAbelianScheme B → M.IsLB → RelAmple B M → KTriv B M → (∃ t : LB.Gen (Theta B M), t.IsGen) → LBIso (M.pull (ι[B]).left) (M.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left) → ∃ L : LB B.left, L.IsLB ∧ Rigidified B L ∧ Out.Sym B L ∧ RelAmple B L ∧ KTriv B L ∧ LBIso (abelian₂ B L) (abelian₂ B M) := by
  first | exact @GlobalTheory.SymTranslate.exists_sym_translate | exact GlobalTheory.SymTranslate.exists_sym_translate | (intros; apply GlobalTheory.SymTranslate.exists_sym_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticSimilitude_action_on_levelFamily : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∃ ρ : sympSimGrp h M → (X ⟶ X), ρ 1 = 𝟙 X ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ SympActs s s₁ u lev ρ := by
  first | exact @GlobalTheory.UPel.HT.SympAct.exists_sympActs | exact GlobalTheory.UPel.HT.SympAct.exists_sympActs | (intros; apply GlobalTheory.UPel.HT.SympAct.exists_sympActs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProduct
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ContrMor

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]
  {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D']

theorem specOverOfAlgHom_pointWithZeroSecondCoord (φ : D →ₐ[R] D') (x : Pt A D) : spOver φ ≫ pt0 B x = pt0 B (spOver φ ≫ x) := by
  simp [pt0, comp_lift, MonObj.comp_one]

theorem spOver_fst_ptV (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) :
    spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x = pt0 B x := by
  have k : spOver (TrivSqZeroExt.fstHom R D D) ≫ spOver (EpsWeil.epsMap R D) =
      toUnit _ ≫ GrpTangent.epsZero R := by
    refine Over.OverMorphism.ext ?_
    rw [spOver_comp, PDiv.spOver_left, Over.comp_left, Over.toUnit_left]
    refine Eq.trans (congrArg spMap (RingHom.ext fun a ↦ ?_)) (Cris.spMap_comp
      (TrivSqZeroExt.fstHom R R R).toRingHom (algebraMap R D))
    simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl']
  ext1
  · simp only [ptV, pt0, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    rw [show (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D from
      AlgHom.ext fun _ ↦ rfl, PDiv.spOver_id, Category.id_comp]
  · simp only [ptV, pt0, comp_lift, lift_snd]
    rw [← Category.assoc, k, Category.assoc, (GrpTangent.isTangent_iff v).1 hv, MonObj.comp_one]

theorem spOver_epsHom_ptV (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver (epsHom φ) ≫ ptV v x = ptV v (spOver φ ≫ x) := by
  ext1
  · simp only [ptV, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    congr 2
    ext c <;> simp [epsHom, DualNumber.lift_apply_apply]
  · simp only [ptV, comp_lift, lift_snd, ← Category.assoc, spOver_comp]
    congr 2
    ext <;> simp only [AlgHom.comp_apply, EpsWeil.epsMap, epsHom, DualNumber.lift_apply_eps]

def sHom (x : Pt A D) : trivAt (pt0 B x) ⟶ thickAt B x :=
  (epsExt R D).secHom (pt0 B x).w (epsExt R D).i (epsExt R D).π_i

def iHom (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) : trivAt (ptV v x) ⟶ thickAt B x :=
  Thick.trivHom (AlgHom.id R _) (by
    have := congrArg Over.Hom.left (spOver_fst_ptV v hv x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def aHom (φ : D →ₐ[R] D') (x : Pt A D) : trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x)) :=
  Thick.trivHom φ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def bHom (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x)) :=
  Thick.trivHom (epsHom φ) (by
    have := congrArg Over.Hom.left (spOver_epsHom_ptV v φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def τHom (φ : D →ₐ[R] D') (x : Pt A D) : thickAt B x ⟶ thickAt B (spOver φ ≫ x) :=
  (epsExt R D).thickHom (epsExt R D') (epsHom φ) φ
    (fun c ↦ by simp [epsHom, DualNumber.lift_apply_apply]) _ _ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

end GlobalTheory.PtExt.ContrMor

namespace GlobalTheory.PtExt.ContrMor

theorem exists_contr : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (v : epsR R ⟶ B), IsTangent v → (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x) (s' : trivAt (pt0 B (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x)) (i' : trivAt (ptV v (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x)) (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x))) (b : trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x))) (τ : thickAt B x ⟶ thickAt B (spOver φ ≫ x)), (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧ (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧ (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧ ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ := by
  intro R _ A B _ _ v hv
  refine ⟨fun D _ _ D' _ _ φ x ↦ ⟨sHom x, iHom v hv x, sHom _, iHom v hv _, aHom φ x, bHom v φ x, τHom φ x,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, fun z ↦ ?_⟩
  refine ⟨fun D _ _ D' _ _ φ x ↦ TrivSqZeroExt.snd (R := D')
    (z _ _ _ (sHom x) (τHom φ x) - z _ _ _ (aHom φ x) (sHom _) - z _ _ _ (iHom v hv x) (τHom φ x) +
      z _ _ _ (bHom v φ x) (iHom v hv _)), ?_⟩
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  obtain rfl : s = sHom x := Thick.hom_ext fun r ↦ (hs r).trans rfl
  obtain rfl : i = iHom v hv x := Thick.hom_ext fun r ↦ (hi r).trans rfl
  obtain rfl : s' = sHom _ := Thick.hom_ext fun r ↦ (hs' r).trans rfl
  obtain rfl : i' = iHom v hv _ := Thick.hom_ext fun r ↦ (hi' r).trans rfl
  obtain rfl : a = aHom φ x := Thick.hom_ext fun r ↦ (ha r).trans rfl
  obtain rfl : b = bHom v φ x := Thick.hom_ext fun r ↦ (hb r).trans rfl
  obtain rfl : τ = τHom φ x := Thick.hom_ext fun r ↦ (hτ r).trans rfl
  rfl

end GlobalTheory.PtExt.ContrMor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSquareEquivFibreSquareSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorSquare_equiv_fibreSquare_sections : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V₀ : Y.Opens), IsAffineOpen V₀ →
    ∀ (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∃ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      ∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b := by
  first | exact @GlobalTheory.LBDescent.exists_tensorSquare_equiv_sections | exact GlobalTheory.LBDescent.exists_tensorSquare_equiv_sections | (intros; apply GlobalTheory.LBDescent.exists_tensorSquare_equiv_sections <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_qkPt_of_utest : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : S.Gam), ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left := by
  intro o Ω _ _ _ S ρ p _ y₀ u a
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  obtain ⟨x, hx, hadd, -⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain ⟨f, f₁, f₂, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) _ (GlobalTheory.RealCompare.one_le_rN S)
  have hx1 : x a ^ (S.r * S.N) = 1 := by
    have := u.A.isAb.comm
    obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul x hadd
    rw [← hsm, ThetaReal.nsmul_self, h0]
  obtain ⟨q, hq⟩ := f₂ _ hx1
  exact ⟨q, x a, (f₁ _ _).2 hq.symm, hx a⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionBasisRealMultiplicationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_basis_real_multiplication : ∀ (F : Type) [Field F] [NumberField F] (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (rm : OAct (𝓞 F) A) (L : LB A.left) (u : HolUnif A L (Module.finrank ℚ F)) (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)), (∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ rm.act a) → ∀ N : ℕ, 1 ≤ N → ∃ pt : Fin 2 → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ i, pt i ^ N = 1) ∧ (∀ a b : 𝓞 F, (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧ ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) := by
  first | exact @GlobalTheory.TorsionPoints.exists_torsion_basis | exact GlobalTheory.TorsionPoints.exists_torsion_basis | (intros; apply GlobalTheory.TorsionPoints.exists_torsion_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusFactorBaseChangeField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isMonHom_of_comp_mono_torus {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N P : C}
    [MonObj M] [MonObj N] [MonObj P] (e : M ⟶ N) (i : N ⟶ P) [Mono i] [IsMonHom i] [IsMonHom (e ≫ i)] :
    IsMonHom e := by
  constructor
  · rw [← cancel_mono i, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom,
      ← Category.assoc, ← tensorHom_comp_tensorHom]

theorem exists_torus_factor : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] (β₀ : G'₀.left ⟶ G₀.left), IsGrpPullback G'₀ G₀ (spMap ρ) β₀ → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] (Q₀ : GlobalTheory.UU.TQ G₀ X) (Q'₀ : GlobalTheory.UU.TQ G'₀ X'), ∃ (i₁ : splitTorus (Sp k') X ⟶ G'₀) (e : splitTorus (Sp k') X ⟶ splitTorus (Sp k') X'), IsMonHom e ∧ e ≫ Q'₀.i = i₁ ∧ GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ Q₀.i := by
  intro k k' _ _ hk' ρ G₀ _ G'₀ _ β₀ hβ₀ X X' _ _ _ _ Q₀ Q'₀
  letI : Field k' := hk'.toField
  obtain ⟨i₁, h₁, -⟩ := GlobalTheory.UU.existsUnique_torusCompat hβ₀.1 Q₀.i
  haveI := Q₀.i_hom
  haveI := Q'₀.i_hom
  haveI := Q'₀.q_hom
  haveI hi₁ : IsMonHom i₁ := GlobalTheory.UU.TorusCompat.isMonHom hβ₀ h₁
  haveI : IsProper Q'₀.B.hom := Q'₀.isAb.proper
  have hc : i₁ ≫ Q'₀.q = toUnit _ ≫ η[Q'₀.B] := by
    have h := GlobalTheory.TorusConst.eq_const (K := k') X (i₁ ≫ Q'₀.q)
    rw [IsMonHom.one_hom] at h
    exact h
  let e := Q'₀.isKernel.lift i₁ (toUnit _) hc
  have he : e ≫ Q'₀.i = i₁ := Q'₀.isKernel.lift_fst _ _ hc
  haveI : Mono Q'₀.i := by
    haveI : Mono (η[Q'₀.B]) := ⟨fun a b _ => toUnit_unique a b⟩
    exact Q'₀.isKernel.mono_fst_of_mono
  haveI : IsMonHom (e ≫ Q'₀.i) := he ▸ hi₁
  exact ⟨i₁, e, isMonHom_of_comp_mono_torus e Q'₀.i, he, h₁⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateThetaPullbackNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translate_thetaPullback_ne_zero : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    ∃ i, (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)) ≠ 0 := by
  first | exact @GlobalTheory.TransNZ.exists_ne | exact GlobalTheory.TransNZ.exists_ne | (intros; apply GlobalTheory.TransNZ.exists_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqPositiveSquaresTimesSelfAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint : ∀ (n : ℕ) (Tm : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef → (B * Tm.map (Rat.cast : ℚ → ℝ)).PosDef → ∃ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧ (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tm + ∑ i, c i • ((Polynomial.aeval Tm (p i)) ^ 2 * Tm) := by
  first | exact @GlobalTheory.Desc.SqLin.main | exact GlobalTheory.Desc.SqLin.main | (intros; apply GlobalTheory.Desc.SqLin.main <;> assumption)
end

