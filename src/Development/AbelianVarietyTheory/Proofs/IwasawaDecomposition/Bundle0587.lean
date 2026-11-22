import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormOfParts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockSymm

section Split

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def chernRootsOver : MvPolynomial (ι × ℕ) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R x.2)

variable {m} [DecidableEq ι] (τ₀ : ι)

def rootSplit : Root m ≃ Fin (m τ₀) ⊕ Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) :=
  GlobalTheory.InnerAutomorphism.sigmaSplit (fun τ => Fin (m τ)) τ₀

def splitEquiv : MvPolynomial (Root m) R ≃ₐ[R]
    MvPolynomial (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :=
  (renameEquiv R (rootSplit τ₀)).trans (sumAlgEquiv R _ _)

theorem splitEquiv_X_self (i : Fin (m τ₀)) :
    splitEquiv R τ₀ (X (⟨τ₀, i⟩ : Root m)) = X i := by
  have e : rootSplit τ₀ (⟨τ₀, i⟩ : Root m) = Sum.inl i := GlobalTheory.InnerAutomorphism.sigmaSplit_self (fun τ => Fin (m τ)) τ₀ i
  simp [splitEquiv, e]

theorem splitEquiv_X_ne {τ : ι} (h : τ ≠ τ₀) (i : Fin (m τ)) :
    splitEquiv R τ₀ (X (⟨τ, i⟩ : Root m)) = C (X ⟨⟨τ, h⟩, i⟩) := by
  have e : rootSplit τ₀ (⟨τ, i⟩ : Root m) = Sum.inr ⟨⟨τ, h⟩, i⟩ := GlobalTheory.InnerAutomorphism.sigmaSplit_of_ne (fun τ => Fin (m τ)) h i
  simp [splitEquiv, e]

theorem splitEquiv_symm_X (i : Fin (m τ₀)) :
    (splitEquiv R τ₀).symm (X i) = X (⟨τ₀, i⟩ : Root m) := by
  rw [AlgEquiv.symm_apply_eq, splitEquiv_X_self]

theorem splitEquiv_symm_C (c : MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :
    (splitEquiv R τ₀).symm (C c) = rename (fun y => (⟨y.1.1, y.2⟩ : Root m)) c := by
  rw [AlgEquiv.symm_apply_eq]
  induction c using MvPolynomial.induction_on with
  | C r =>
    simp only [rename_C]
    change _ = splitEquiv R τ₀ (algebraMap R _ r)
    rw [AlgEquiv.commutes]; rfl
  | add p q hp hq => simp [map_add, ← hp, ← hq]
  | mul_X p y hp =>
    simp only [map_mul, rename_X]
    rw [← hp, splitEquiv_X_ne R τ₀ y.1.2]

theorem splitEquiv_symm_esymm (j : ℕ) :
    (splitEquiv R τ₀).symm (esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) j) =
      chernRootsOver R m (X (τ₀, j)) := by
  simp [chernRootsOver, esymm, map_sum, map_prod, splitEquiv_symm_X]

theorem splitEquiv_rename_update (σ : Equiv.Perm (Fin (m τ₀))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)) S) = rename σ (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)))) =
      ((rename σ).restrictScalars R).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, Function.update_of_ne h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem splitEquiv_rename_rest (w' : ∀ τ : {τ // τ ≠ τ₀}, Equiv.Perm (Fin (m τ.1))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)) S) =
      MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)))) =
      (mapAlgHom (rename (Equiv.sigmaCongrRight w'))).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem rename_chernRootsOver (T : MvPolynomial ({τ // τ ≠ τ₀} × ℕ) R) :
    rename (fun y : Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) => (⟨y.1.1, y.2⟩ : Root m))
      (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1) T) =
      chernRootsOver R m (rename (Prod.map Subtype.val id) T) := by
  induction T using MvPolynomial.induction_on with
  | C r => simp [chernRootsOver]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp]
    congr 1
    simp [chernRootsOver, rename_rename]
    rfl

end Split

theorem mem_range_chernRootsOver (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ) (S : MvPolynomial (Root m) R),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    S ∈ (chernRootsOver R m).range := by
  induction n with
  | zero =>
    intro ι _ _ hc R _ m S _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    rw [eq_C_of_isEmpty S]
    exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
    intro ι _ _ hc R _ m S hS
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    let f : Fin (m τ₀) → MvPolynomial (Fin (m τ₀)) R' := fun i => esymm (Fin (m τ₀)) R' (↑i + 1)
    have hsym : splitEquiv R τ₀ S ∈ symmetricSubalgebra (Fin (m τ₀)) R' := by
      rw [mem_symmetricSubalgebra]
      intro σ
      rw [← splitEquiv_rename_update, hS]
    obtain ⟨T, hT⟩ := esymmAlgHom_fin_surjective R' (m := m τ₀) (n := m τ₀) le_rfl ⟨_, hsym⟩
    have hT' : aeval f T = splitEquiv R τ₀ S := by
      rw [← esymmAlgHom_apply, hT]
    have hcoef : ∀ d, coeff d T ∈ (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1)).range := by
      intro d
      apply ih _ hc' R
      intro w'
      have hinv : MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom T = T := by
        apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
        apply Subtype.ext
        rw [esymmAlgHom_apply, esymmAlgHom_apply]
        change aeval f _ = aeval f T
        rw [hT', ← hS (fun τ => if h : τ = τ₀ then 1 else w' ⟨τ, h⟩), splitEquiv_rename_rest, ← hT',
          aeval_def, aeval_def, algebraMap_eq, eval₂_map, eval₂_comp_left, map_comp_C]
        congr 1
        funext i
        exact (map_esymm _ _ _ _).symm
      have := congrArg (coeff d) hinv
      rwa [coeff_map] at this
    let k : MvPolynomial (Fin (m τ₀)) R' →+* MvPolynomial (Root m) R :=
      (splitEquiv R τ₀).symm.toRingEquiv.toRingHom
    have hSE : S = k (eval₂ C f T) := by
      change S = (splitEquiv R τ₀).symm _
      rw [← algebraMap_eq, ← aeval_def, hT', AlgEquiv.symm_apply_apply]
    have key : k (eval₂ C f T) = eval₂ (k.comp C) (k ∘ f) T := eval₂_comp_left k C f T
    rw [hSE, key, eval₂_eq]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · obtain ⟨Tc, hTc⟩ := (AlgHom.mem_range _).mp (hcoef d)
      rw [RingHom.comp_apply, ← hTc]
      change (splitEquiv R τ₀).symm (C _) ∈ _
      rw [splitEquiv_symm_C, rename_chernRootsOver]
      exact AlgHom.mem_range_self _ _
    · change (splitEquiv R τ₀).symm (esymm _ _ _) ∈ _
      rw [splitEquiv_symm_esymm]
      exact AlgHom.mem_range_self _ _

theorem exists_chernRoots_eq_of_blockSymmetric : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  intro ι _ m S hS
  classical
  obtain ⟨R, hR⟩ := (AlgHom.mem_range _).mp (mem_range_chernRootsOver _ ι rfl ℝ m S hS)
  exact ⟨R, hR⟩

end GlobalTheory.BlockSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleValueAtThetaPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

section Unif

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem exists_unif_of_frame {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) (i : Fin F.n)
    {P : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) {y : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P)
    {s : LB.Sec (PPx y)} (Φ : FibKey Xo ℂ y) (ht : SecTie Φ.m Φ.th s)
    {θ : (Fin g → ℂ) → ℂ} {fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ}
    (c₁ : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (c₂ : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (c₃ : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (c₄ : ∀ j, ⊤ ≤ (F.ex i P 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (c₆ : ∀ j z (pt : Sp ℂ ⟶ Gx y), pt ≫ gxFst y = (F.ex i P z).left → pt ≫ gxSnd y = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) :
    ∃ u : HolUnif Φ.key.P.A Φ.key.P.L g, u.Λ = P.range.toIntSubmodule ∧
      u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧ ∀ z, (u.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := by
  subst hy
  obtain ⟨w, ⟨hw, hrig⟩, hth⟩ := val_tie Φ.m ht
  obtain ⟨w', hw', hinv⟩ := ConjUnif.exists_inv w hw
  have hL := Φ.T.t.PP.isLB
  have hM := pull_isLB Xo.univ.t.PP.isLB Φ.m.φ
  have hol := isHolTo_exp F i hP
  let u₁ := fibreUnif Φ.m.cart (F.ex i P) P.range fr (F.ex_add i P hP) (F.ex_onto i P hP) (F.ex_ker i P hP)
    hP.2.2.1 hP.2.2.2.1 hol c₁ c₂ c₃
  have hex : ∀ z, (u₁.ex z).left ≫ Φ.m.φ = (F.ex i P z).left := fun z => liftPt_comp Φ.m.cart _
  have hle : ∀ z j, ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ (Xo.univ.t.PP.L.pull Φ.m.φ).U j →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j PUnit.unit) := fun z j => (lift_le Φ.m.cart _ j).1
  have hfr : ∀ (j : Xo.univ.t.PP.L.ι) (k : Φ.T.t.PP.L.ι) (z : Fin g → ℂ),
      ⊤ ≤ (u₁.ex z).left ⁻¹ᵁ ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k) →
      valAt' (u₁.ex z).left ((Xo.univ.t.PP.L.pull Φ.m.φ).U (fun _ => j) ⊓ Φ.T.t.PP.L.U k)
        (w.s (fun _ => j, k)).val * (carry u₁ hM hL hw').fr k z = fr j z := by
    intro j k z hz
    obtain ⟨hj, hk⟩ := (top_le_preimage_inf _ _ _).1 hz
    rw [carry_fr u₁ hM hL hw' k (fun _ => j) z hk hj, hinv _ _ _ hz]
    exact mul_inv_cancel_left₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j, k))) _
  refine ⟨carry u₁ hM hL hw', rfl, ?_, ?_, hex⟩
  · intro k hk
    have h0 : (u₁.ex 0).left = eSec Φ.T.t.G := by
      rw [(u₁.ker 0).2 u₁.Λ.zero_mem, Hom.one_def]
      simp [eSec]
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex 0).left
    have hk' : ⊤ ≤ (u₁.ex 0).left ⁻¹ᵁ Φ.T.t.PP.L.U (k PUnit.unit) := by
      rw [h0]
      exact fun p hp => mem_pull.1 (hk hp)
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk'⟩
    have e := hfr (j PUnit.unit) (k PUnit.unit) 0 hz
    rw [c₄ _ (hle 0 j hj), h0] at e
    rw [h0] at hz
    have e' := val_rig Φ.m.cm.e_comm w Φ.T.t.PP.rig Xo.univ.t.PP.rig hrig (j PUnit.unit) (k PUnit.unit) hz
    rw [Φ.m.base] at e'
    exact mul_left_cancel₀ (valAt'_unit_ne_zero _ hz _) (e.trans e')
  · intro k z hk
    obtain ⟨j, hj⟩ := exists_chart_at hM (u₁.ex z).left
    have hz := (top_le_preimage_inf _ _ _).2 ⟨hj, hk⟩
    obtain ⟨pt, p₁, p₂, hpt⟩ := hth (u₁.ex z).left (Over.w _)
    have e := hfr (j PUnit.unit) k z hz
    refine mul_left_cancel₀ (valAt'_unit_ne_zero _ hz (w.s (fun _ => j PUnit.unit, k))) ?_
    have e₁ := hpt (j PUnit.unit) k hz
    have e₂ := c₆ (j PUnit.unit) z pt (p₁.trans (hex z)) p₂ (hle z j hj)
    rw [← e] at e₂
    exact e₁.symm.trans (e₂.trans (mul_left_comm _ _ _))

end Unif

theorem mulVec_period {g : ℕ} {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (h τ : Matrix (Fin g) (Fin g) ℂ)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) (a : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas a) = (fun i => (a (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (a (Sum.inr i) : ℂ)) := by
  have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
    intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : a = ∑ s, a s • (Pi.single s 1 : Fin g ⊕ Fin g → ℤ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [h1 (fun i => a (Sum.inl i)), h1 (fun i => a (Sum.inr i))]
  conv_lhs => rw [h2]
  simp only [map_sum, map_zsmul, Fintype.sum_sum_type, map_add, Matrix.mulVec_add, Matrix.mulVec_sum,
    Matrix.mulVec_smul, (hn _).1, (hn _).2]

theorem normalAt_of_coord (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) {La : Type} [AddCommGroup La]
    (P : La →+ (Fin x.P.g → ℂ)) (bas : (Fin x.P.g ⊕ Fin x.P.g → ℤ) ≃ₗ[ℤ] La)
    (h τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c₁ c₂ : Fin x.P.g → ℂ) (a : ℂ) (hu : IsUnit h.det)
    (hsymm : τ.IsSymm) (hpos : (τ.map Complex.im).PosDef)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1)
    (hΛ : u.Λ = P.range.toIntSubmodule) (hR : u.IsRig x.rig)
    (hF : u.IsFn x.th fun z => a * thetaChar τ c₁ c₂ (h *ᵥ z)) (hD : ∀ i, u.IsDiff (Pi.single i 1) (x.v i)) :
    KeyPow.NormalAt x τ ((2 * Real.pi * Complex.I : ℂ) • hᵀ) c₁ c₂ a := by
  let φ : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm.toContinuousLinearEquiv
  have hφ : ∀ z, h *ᵥ φ z = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).apply_symm_apply z
  have hφ' : ∀ z, φ (h *ᵥ z) = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm_apply_apply z
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  clear_value φ
  refine ⟨KeyNormalForm.change u φ (fun _ => 0) (differentiable_const _), hsymm, hpos, fun z => ?_,
    KeyNormalForm.isRig_change u φ _ _ rfl hR,
    KeyNormalForm.isFn_change u φ _ _ hF fun z => by simp only [hφ, Complex.exp_zero, mul_one],
    fun i => KeyNormalForm.isDiff_change u φ _ _ ?_⟩
  · rw [KeyNormalForm.mem_change, hΛ]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨m, rfl⟩ := bas.surjective v
      refine ⟨fun i => m (Sum.inl i), fun i => m (Sum.inr i), ?_⟩
      rw [← hφ z, ← hv]
      exact mulVec_period _ bas _ _ hn m
    · rintro ⟨m, n, rfl⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      rw [← hφ' (P _), mulVec_period _ bas _ _ hn]
      rfl
  · have e₁ : (2 * Real.pi * Complex.I : ℂ)⁻¹ • ((2 * Real.pi * Complex.I : ℂ) • hᵀ) i = h *ᵥ Pi.single i 1 := by
      funext j
      simp only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.mulVec_single_one,
        Matrix.col_apply]
      rw [inv_mul_cancel_left₀ hπ]
    rw [e₁, hφ']
    exact hD i

theorem value_at_thetaPt : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.ThetaOne κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (a : ℂ) (y : FrPt Xo c (CAt σ)) (Φ : FibKey Xo ℂ y.x), a ≠ 0 → IsThetaPt T b a y → Tied (S := ℂ) e y.s y.u Φ → a ^ 8 * (κ ℂ Φ.key : ℂ) = ((2 * Real.pi * Complex.I) ^ g * (T.h b).det) ^ 4 := by
  intro κ hH hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb a y Φ ha ⟨hx, hder, hsec⟩ ⟨ht, hg, hv⟩
  subst hg
  have hP := T.isPer _ hb
  obtain ⟨hu, hsymm, hpos, hn⟩ := T.norm b hb
  have hj : Differentiable ℂ (fun z : Fin Φ.T.g → ℂ => (b, z)) := by fun_prop
  obtain ⟨u, hΛ, hR, hF, hex⟩ := exists_unif_of_frame F k hP hx Φ ht
    (θ := fun z => a * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) (fr := fun j z => T.fr j (b, z))
    (fun j => (T.fr_hol j).comp hj.differentiableOn fun z hz => ⟨hb, hz⟩)
    (fun j z hz => T.fr_ne j b z hb hz) (fun j j' z hz => T.fr_coc j j' b z hb hz)
    (fun j hj => (T.fr_rig j b hb hj).trans (congrArg (fun q => valAt' q _ _) hx.symm)) hsec
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hN := normalAt_of_coord Φ.key u _ T.bas (T.h b) (T.ta b) T.c₁ T.c₂ a hu hsymm hpos hn hΛ hR hF fun i => by
    obtain ⟨W, hW, -⟩ := (existsUnique_isDiff_and_linear Φ.key u).1 _ (Φ.basis.1 i)
    have d := OrthoMetric.isDerivAt0_comp u Φ.m.φ (e := fun z => (F.ex k (T.Pf (T.co b)) z).left) hex (Φ.basis.1 i) hW
    have d' := hder (e i).1 (e i).2
    rw [show e.symm ⟨(e i).1, (e i).2⟩ = i from e.symm_apply_apply i,
      ← show _ = y.u (e i).1 (e i).2 from hv i] at d'
    obtain ⟨t₁, -, t₃⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ F k _ hP
    have hWi : W = Pi.single i 1 := (t₃ _ (t₁ _ _ d)).unique d d'
    exact hWi ▸ hW
  have hdet : ((2 * Real.pi * Complex.I : ℂ) • (T.h b)ᵀ).det = (2 * Real.pi * Complex.I) ^ Φ.T.g * (T.h b).det := by
    rw [Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  have key := KeyCl.value_of_normalAt hH hT Φ.key ⟨T.half₁, T.half₂⟩ ha
    (hdet.trans_ne (mul_ne_zero (pow_ne_zero _ hπ) hu.ne_zero)) hN
  rw [key, mul_div_cancel₀ _ (pow_ne_zero 8 ha)]
  exact congrArg (· ^ 4) hdet

end GlobalTheory.KeyFourth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToShimXEqShimXOfPkg
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam

def shimXOfPkg {D : D7} {G : DV.Geo D.what₂.LL} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
    {N j : ℕ} {Comp : Type} [Fintype Comp] [Nonempty Comp] (cx : CxPkg D.what₂.Tau N j Comp)
    (alg : AlgPkg G D.what₂.Tau N Comp) (pad : PadPkg D N j Comp jC ng) (h : 1 ≤ j ∧ j < N) (lev : Finset ℕ)
    (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX D.what₂.Tau where
  N := N
  j := j
  j_pos := h.1
  j_lt := h.2
  lev := lev
  lev_prime := hlev
  Comp := Comp
  vol := cx.vol
  chern := cx.chern
  chern_homog := fun P d hd hP => chernOf_homog D.what₂.Tau N cx.vol P d hd hP
  arDeg := pad.arDeg
  arDeg_homog := pad.arDeg_homog
  arMix := pad.arMix
  arMix_HT := pad.arMix_HT
  arMix_DR := pad.arMix_DR
  CurveHT := pad.CurveHT
  degHT := pad.degHT
  CurveDR := pad.CurveDR
  degDR := pad.degDR
  FibComp := pad.FibComp
  fibInBd := pad.fibInBd
  Pt := pad.Pt
  phiDR := pad.phiDR
  phiMod := pad.phiMod
  phiFr := pad.phiFr
  XC := cx.XC
  rfn := cx.rfn
  rfn_ge := cx.rfn_ge
  hLo := cx.hLo
  hUp := cx.hUp
  hLo_le := cx.hLo_le
  connN := cx.connN
  curvN := cx.curvN
  compOf := cx.compOf
  normDetInf := cx.normDetInf
  compPt := pad.compPt
  normDetT := pad.normDetT
  normDetH := pad.normDetH
  htDetT := pad.htDetT
  ALB := alg.ALB
  arSelf := fun L => ∑ c, alg.arSelfC L c
  arSelfC := alg.arSelfC
  arSelf_sum := fun _ => rfl
  geo := fun L => ∑ c, alg.geoC L c
  geoC := alg.geoC
  geo_sum := fun _ => rfl
  arVol := alg.arVol
  semipos := alg.semipos
  nefFib := alg.nefFib
  arNef := alg.arNef
  Mbar := alg.Mbar

section
variable {D : D7} {A : Amb D} {F : SrcFam A} {L : CmList A} {C : CxSt D.what₂.LL} (K : CutSt C) (R : ResSt C)
  {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (k : Kits F L C jC ng)

def shimXAt (N j : ℕ) (hN : 2 ≤ N) (hj : j ≤ N) (κ : Lv A) (h : 1 ≤ j ∧ j < N) : DV.ShimX D.what₂.Tau :=
  shimXOfPkg ((F.src N j hN hj κ).cx L (k N j hN hj κ).B (k N j hN hj κ).fl)
    ((F.src N j hN hj κ).alg L C K R (k N j hN hj κ).Φ (k N j hN hj κ).dim_eq (k N j hN hj κ).Mb)
    (k N j hN hj κ).pad h κ.primes (fun _ hp => Nat.prime_of_mem_primeFactors hp)

end

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionCommutesRingActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCharacterRestriction_commutes_ringAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (a : 𝓞 E) (x : P.D.toPre.X), ρ (a • x) = a • ρ x := by
  first | exact @GlobalTheory.restrict_torus_smul_comm | exact GlobalTheory.restrict_torus_smul_comm | (intros; apply GlobalTheory.restrict_torus_smul_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCharacterRestriction_trait_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    Function.Surjective ρ := by
  first | exact @GlobalTheory.TorusOnto.restrict_surjective | exact GlobalTheory.TorusOnto.restrict_surjective | (intros; apply GlobalTheory.TorusOnto.restrict_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSign
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem antisymm_rename_sigmaCongrRight : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))),
    rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  intro ι _ m Q w
  classical
  unfold antisymm
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun v => ?_)
  rw [map_zsmul, rename_rename, smul_smul]
  have hf : (⇑(Equiv.sigmaCongrRight w) ∘ fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) =
      fun x : Root m => (⟨x.1, (Equiv.mulLeft w v) x.1 x.2⟩ : Root m) := by
    funext x; rfl
  rw [hf]
  congr 1
  have hs : (∏ τ, Equiv.Perm.sign ((Equiv.mulLeft w v) τ) : ℤˣ) =
      (∏ τ, Equiv.Perm.sign (w τ)) * ∏ τ, Equiv.Perm.sign (v τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Equiv.Perm.sign_mul]
  rw [hs, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]

end GlobalTheory.GoodMetric
end

