import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0006
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0757
import Formalism.HermitianLattices.FinalMass
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleStructureGlProof
section
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

namespace NablaStr

theorem coeff_der_diag_row {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) (m : Fin r × Fin n →₀ ℕ) :
    coeff m (Formalism.CohomologicalDescent.LR.der r n a a f) = ((Finsupp.weight (rowW r n) m a : ℕ) : ℚ) * coeff m f := by
  rw [← Formalism.CohomologicalDescent.LR.rowDiv_one, lgraded_coeff_euler, lgraded_weight_rowW]

theorem der_diag_eq_weight_smul_of_isWeightedHomogeneous {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℚ) (μ : Fin r → ℕ) :
    IsWeightedHomogeneous (rowW r n) f μ → ∀ a, Formalism.CohomologicalDescent.LR.der r n a a f = (μ a : ℚ) • f := by
  intro h a
  ext m
  rw [coeff_der_diag_row, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m f = 0
  · rw [hm, mul_zero, mul_zero]
  · rw [h hm]

theorem eV_val {N : ℕ} (ν : Fin N → ℕ) (a b : ℕ) (ha : a < N) (hb : b < N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  unfold eV
  rw [dif_pos ⟨ha, hb⟩]
  rfl

theorem eV_pow_val {N : ℕ} (ν : Fin N → ℕ) (a b : ℕ) (ha : a < N) (hb : b < N) (k : ℕ) (x : dualWeyl ℚ N N ν) :
    (((eV N ν a b ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      ((Formalism.CohomologicalDescent.LR.der N N ⟨a, ha⟩ ⟨b, hb⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) ^ k)
        (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, eV_val ν a b ha hb, pow_succ, Module.End.mul_apply]
    rfl

theorem weight_rowW_eq {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp [rowW, rowDeg]
  · intro b _ hb
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · simp

theorem glRel_eV (N : ℕ) (ν : Fin N → ℕ) : GlRel N (eV N ν) := by
  intro a b c d ha hb hc hd
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := Formalism.CohomologicalDescent.LR.der_comm (n := N) ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ (x : MvPolynomial (Fin N × Fin N) ℚ)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
  rw [eV_val ν a b ha hb, eV_val ν c d hc hd, eV_val ν c d hc hd, eV_val ν a b ha hb, h]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp only [if_true, LinearMap.sub_apply, Submodule.coe_sub, eV_val ν d d ha hd, eV_val ν b b hc hb]
  · subst hbc
    have : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩ := fun h => hda (Fin.mk.inj h)
    simp only [if_true, this, if_false, hda, sub_zero, eV_val ν a d ha hd]
    simp
  · subst hda
    have : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun h => hbc (Fin.mk.inj h)
    simp only [if_true, this, if_false, hbc, zero_sub, LinearMap.neg_apply, Submodule.coe_neg, eV_val ν c b hc hb]
    simp
  · have h1 : (⟨b, hb⟩ : Fin N) ≠ ⟨c, hc⟩ := fun h => hbc (Fin.mk.inj h)
    have h2 : (⟨d, hd⟩ : Fin N) ≠ ⟨a, ha⟩ := fun h => hda (Fin.mk.inj h)
    simp [h1, h2, hbc, hda]

theorem wtSpan_eV (N : ℕ) (ν : Fin N → ℕ) : WtSpan N (eV N ν) := by
  classical
  rw [WtSpan, eq_top_iff]
  rintro x -
  set f : MvPolynomial (Fin N × Fin N) ℚ := (x : MvPolynomial (Fin N × Fin N) ℚ) with hf
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum : f = ∑ μ ∈ hfin.toFinset, weightedHomogeneousComponent (rowW N N) μ f := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (rowW N N) f]
    exact finsum_eq_sum_of_support_subset _ (fun μ hμ => (Set.Finite.mem_toFinset hfin).mpr hμ)
  have hmem : ∀ μ, weightedHomogeneousComponent (rowW N N) μ f ∈ dualWeyl ℚ N N ν :=
    fun μ => dualWeylRowGraded ℚ N N ν μ f x.2
  have hx : x = ∑ μ ∈ hfin.toFinset, (⟨_, hmem μ⟩ : dualWeyl ℚ N N ν) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hsum
  rw [hx]
  refine Submodule.sum_mem _ fun μ _ => Submodule.subset_span ?_
  refine ⟨fun c => if h : c < N then (μ ⟨c, h⟩ : ℤ) else 0, fun c hc => ?_⟩
  apply Subtype.ext
  rw [eV_val ν c c hc hc]
  simp only [dif_pos hc]
  have h := der_diag_eq_weight_smul_of_isWeightedHomogeneous _ μ
    (weightedHomogeneousComponent_isWeightedHomogeneous μ f) ⟨c, hc⟩
  rw [Submodule.coe_smul]
  simpa using h

theorem sum_range_dite (N k : ℕ) (hk : k ≤ N) (F : Fin N → ℕ) :
    ∑ c ∈ Finset.range k, (if h : c < N then (F ⟨c, h⟩ : ℤ) else 0) =
      ((∑ a : Fin N with a.val < k, F a : ℕ) : ℤ) := by
  push_cast
  rw [Finset.sum_filter]
  have e : ∀ a : Fin N, (if a.val < k then (F a : ℤ) else 0) =
      (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) a.val := by
    intro a
    simp [a.isLt]
  rw [Finset.sum_congr rfl (fun a _ => e a),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < k then (if h : i < N then (F ⟨i, h⟩ : ℤ) else 0) else 0) N,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem dom_eV (N : ℕ) (ν : Fin N → ℕ) : Dom N (eV N ν) (wtZ ν) := by
  classical
  intro μ x hx hx0
  have hx0' : (x : MvPolynomial (Fin N × Fin N) ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hx0'
  have hμ : ∀ c (hc : c < N), μ c = (rowDeg m ⟨c, hc⟩ : ℤ) := by
    intro c hc
    have h1 := congrArg (fun y : dualWeyl ℚ N N ν => coeff m (y : MvPolynomial (Fin N × Fin N) ℚ)) (hx c hc)
    simp only [eV_val ν c c hc hc, coeff_der_diag_row, Submodule.coe_smul, coeff_smul, smul_eq_mul,
      weight_rowW_eq] at h1
    have h2 := mul_right_cancel₀ hm h1
    exact_mod_cast h2.symm
  have hdom := GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν (x : MvPolynomial (Fin N × Fin N) ℚ) x.2 m
    (mem_support_iff.mpr hm)
  have hsμ : ∀ k ≤ N, ∑ c ∈ Finset.range k, μ c = ((∑ a : Fin N with a.val < k, rowDeg m a : ℕ) : ℤ) := by
    intro k hk
    rw [← sum_range_dite N k hk]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcN : c < N := lt_of_lt_of_le (Finset.mem_range.mp hc) hk
    rw [dif_pos hcN, hμ c hcN]
  have hsν : ∀ k ≤ N, ∑ c ∈ Finset.range k, wtZ ν c = ((∑ a : Fin N with a.val < k, ν a : ℕ) : ℤ) := by
    intro k hk
    rw [← sum_range_dite N k hk]
    exact Finset.sum_congr rfl fun c _ => rfl
  have hall : ∀ F : Fin N → ℕ, (∑ a : Fin N with a.val < N, F a) = ∑ a : Fin N, F a := by
    intro F
    rw [Finset.filter_true_of_mem (fun a _ => a.isLt)]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [hsμ k hk, hsν k hk]
    exact_mod_cast hdom.1 k
  · rw [hsμ N le_rfl, hsν N le_rfl, hall, hall]
    exact_mod_cast hdom.2

theorem divStable_eV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ))
    (hM : ∀ (a b : Fin N) (k : ℕ), ∀ f ∈ M, rowDiv ℤ a b k f ∈ M) : DivStable N (eV N ν) (latV N ν M) := by
  intro i hi j hj hij k x hx
  simp only [latV, Submodule.mem_comap, Submodule.mem_map] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : map (Int.castRingHom ℚ) y = (x : MvPolynomial (Fin N × Fin N) ℚ) := hyx
  refine ⟨rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y, hM _ _ k y hy, ?_⟩
  have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := fun h => hij (Fin.mk.inj h)
  change map (Int.castRingHom ℚ) (rowDiv ℤ ⟨i, hi⟩ ⟨j, hj⟩ k y) =
    (((k.factorial : ℚ)⁻¹ • (eV N ν i j ^ k) x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ)
  rw [Submodule.coe_smul, eV_pow_val ν i j hi hj, ← Formalism.CohomologicalDescent.LR.der_pow _ _ hne, ← lclosedeq_rowDiv_map, hyx']

end NablaStr

open NablaStr

theorem nablaGl : NablaGl := by
  intro N ν _
  refine ⟨glRel_eV N ν, wtSpan_eV N ν, dom_eV N ν, divStable_eV N ν _ ?_, divStable_eV N ν _ ?_⟩
  · intro a b k f hf
    exact rowDivStable ℤ N N ν a b k f hf
  · intro a b k f hf
    exact weylRowDivStable ℤ N N le_rfl ν a b k f hf

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfShearAutomorphismLiftNilpotent
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearLift

theorem eq_of_fst_snd_left {C : Type*} [Category C] [Limits.HasPullbacks C] {B : C} {Y : Over B} {T : C}
    {a b : T ⟶ (Y ⊗ Y).left} (h₁ : a ≫ (fst Y Y).left = b ≫ (fst Y Y).left)
    (h₂ : a ≫ (snd Y Y).left = b ≫ (snd Y Y).left) : a = b := by
  rw [Over.fst_left] at h₁
  rw [Over.snd_left] at h₂
  exact Limits.pullback.hom_ext h₁ h₂

theorem eq_of_shear : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∀ (m : X ⊗ X ⟶ X), l ≫ m.left = (μ[A₀]).left ≫ i → IsIso (lift (fst X X) m) →
    ∀ (P : Over (Sp R)) (P₀ : Over (Sp R₀)) (k : P₀.left ⟶ P.left), IsPullback k P₀.hom P.hom (spMap π) →
    Smooth P.hom → IsProper P.hom → GeometricallyConnected P.hom →
    ∀ (ε : Sp R ⟶ P.left), ε ≫ P.hom = 𝟙 _ → ∀ (f f' : P ⟶ X), k ≫ f.left = k ≫ f'.left → ε ≫ f.left = ε ≫ f'.left → f = f' := by
  intro R R₀ _ _ π hπ hnil A₀ _ X i hi l hl1 hl2 m hm hσ P P₀ k hk hsm hpr hgc ε hε f f' hk' hε'
  have hσl : IsIso (lift (fst X X) m).left := Functor.map_isIso (Over.forget (Sp R)) (lift (fst X X) m)

  have hsq : (k ≫ f.left) ≫ X.hom = P₀.hom ≫ spMap π := by
    rw [Category.assoc, Over.w f]; exact hk.w
  let f₀ : P₀ ⟶ A₀ := Over.homMk (hi.lift (k ≫ f.left) P₀.hom hsq) (hi.lift_snd _ _ _)
  have hf₀i : f₀.left ≫ i = k ≫ f.left := hi.lift_fst _ _ _

  have hlσ : l ≫ (lift (fst X X) m).left = (lift (fst A₀ A₀) μ).left ≫ l := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hl1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hm, hl2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have hred : k ≫ (lift f f).left = (lift f₀ f₀).left ≫ l := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hl1, ← Category.assoc, ← Over.comp_left, lift_fst, hf₀i]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hl2, ← Category.assoc, ← Over.comp_left, lift_snd, hf₀i]
  let h₀ : P₀ ⟶ A₀ ⊗ A₀ := lift f₀ (toUnit P₀ ≫ η)
  have hh₀ : h₀ ≫ lift (fst A₀ A₀) μ = lift f₀ f₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [h₀]
    · simp only [h₀, Category.assoc, lift_snd]
      exact lift_comp_one_right _ _
  obtain ⟨gu, hgu_def⟩ : ∃ g, g = lift f f' ≫ inv (lift (fst X X) m) := ⟨_, rfl⟩
  obtain ⟨gv, hgv_def⟩ : ∃ g, g = lift f f ≫ inv (lift (fst X X) m) := ⟨_, rfl⟩
  have eu : gu.left ≫ (lift (fst X X) m).left = (lift f f').left := by
    rw [← Over.comp_left, hgu_def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have ev : gv.left ≫ (lift (fst X X) m).left = (lift f f).left := by
    rw [← Over.comp_left, hgv_def, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hgv : k ≫ gv.left = h₀.left ≫ l := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, ev, hred, Category.assoc, hlσ,
      ← Category.assoc, ← Over.comp_left, hh₀]
  have hpair_k : k ≫ (lift f f').left = k ≫ (lift f f).left := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]; exact hk'.symm
  have hpair_ε : ε ≫ (lift f f').left = ε ≫ (lift f f).left := by
    apply eq_of_fst_snd_left
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]; exact hε'.symm
  have hgu_k : k ≫ gu.left = k ≫ gv.left := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, Category.assoc, eu, ev, hpair_k]
  have hgu_ε : ε ≫ gu.left = ε ≫ gv.left := by
    rw [← cancel_mono (lift (fst X X) m).left, Category.assoc, Category.assoc, eu, ev, hpair_ε]

  have e2 : (h₀ ≫ snd A₀ A₀).left = P₀.hom ≫ (η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left := by
    simp only [h₀, lift_snd, Over.comp_left, Over.toUnit_left]
  have hv₀ : k ≫ (gv ≫ snd X X).left = P₀.hom ≫ ((η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left ≫ i) := by
    calc k ≫ (gv ≫ snd X X).left = (k ≫ gv.left) ≫ (snd X X).left := by
          rw [Over.comp_left, Category.assoc]
      _ = h₀.left ≫ (l ≫ (snd X X).left) := by rw [hgv, Category.assoc]
      _ = (h₀ ≫ snd A₀ A₀).left ≫ i := by rw [hl2, Over.comp_left, Category.assoc]
      _ = _ := by rw [e2, Category.assoc]
  have hu₀ : k ≫ (gu ≫ snd X X).left = P₀.hom ≫ ((η : 𝟙_ (Over (Sp R₀)) ⟶ A₀).left ≫ i) := by
    rw [Over.comp_left, ← Category.assoc, hgu_k, Category.assoc, ← Over.comp_left]; exact hv₀
  have cu := GlobalTheory.T.eq_comp_section_of_proper_smooth_nilpotent_rigidity R R₀ π hπ hnil P X P₀ k hk hsm hpr hgc ε hε _ _ hu₀
  have cv := GlobalTheory.T.eq_comp_section_of_proper_smooth_nilpotent_rigidity R R₀ π hπ hnil P X P₀ k hk hsm hpr hgc ε hε _ _ hv₀
  have huv : gu ≫ snd X X = gv ≫ snd X X := by
    apply Over.OverMorphism.ext
    rw [cu, cv, Over.comp_left, Over.comp_left, ← Category.assoc ε gu.left, hgu_ε, Category.assoc]
  have hinvfst : inv (lift (fst X X) m) ≫ fst X X = fst X X := by
    rw [IsIso.inv_comp_eq, lift_fst]
  have hg : gu = gv := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [hgu_def, hgv_def, Category.assoc, Category.assoc, hinvfst, lift_fst, lift_fst]
    · exact huv
  rw [hgu_def, hgv_def] at hg
  have hff : lift f f' = lift f f := (cancel_mono (inv (lift (fst X X) m))).1 hg
  have := congrArg (· ≫ snd X X) hff
  simp only [lift_snd] at this
  exact this.symm

end GlobalTheory.ShearLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNormLtOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes

namespace GlobalTheory.StdMassLower

section
variable {E : Type} [Field E] [NumberField E]

theorem eq_zero_of_norm_lt_one (z : 𝓞 E) (h : ∀ φ : E →+* ℂ, ‖φ (z : E)‖ < 1) : z = 0 := by
  classical
  by_contra hz
  have h0 : Algebra.norm ℤ z ≠ 0 := Algebra.norm_ne_zero_iff.2 hz
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ z : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  have h2 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (z : E))
  rw [← Algebra.coe_norm_int, norm_prod] at h2
  have h3 : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (z : E)‖ < 1 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (z : E)‖ ≤ ‖τ.toRatAlgHom (z : E)‖ := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ.toRatAlgHom)]
          exact mul_le_of_le_one_right (norm_nonneg _)
            (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun σ _ => (h σ.toRingHom).le)
      _ < 1 := h τ
  rw [← h2] at h3
  simp only [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast] at h3
  linarith

theorem eq_of_mk_eq (x y : 𝓞 E) (hx : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ ≤ 1) (hy : ∀ φ : E →+* ℂ, ‖φ (y : E)‖ ≤ 1)
    (h : Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) x = Ideal.Quotient.mk _ y) : x = y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨z, hz⟩ := h
  have : z = 0 := eq_zero_of_norm_lt_one z fun φ => by
    have e : φ (x : E) - φ (y : E) = 3 * φ (z : E) := by
      have := congrArg (fun t : 𝓞 E => φ (algebraMap (𝓞 E) E t)) hz
      simpa only [map_sub, map_mul, map_ofNat] using this
    have e2 := norm_sub_le (φ (x : E)) (φ (y : E))
    rw [e, norm_mul] at e2
    have := hx φ
    have := hy φ
    simp only [Complex.norm_ofNat] at e2
    linarith
  rw [this, mul_zero] at hz
  exact sub_eq_zero.1 hz

theorem card_quot_three :
    Nat.card (𝓞 E ⧸ Ideal.span {(3 : 𝓞 E)}) = 3 ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have : (3 : 𝓞 E) = algebraMap ℤ (𝓞 E) 3 := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp

theorem coord_of_mem {n : ℕ} {x : Fin n → E} (hx : x ∈ Formalism.MainNotions.StandardLattice.stdLat E n) (i : Fin n) :
    ∃ a : 𝓞 E, (a : E) = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [← ha, ← hb]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨r * a, by simp [← ha, Algebra.smul_def]⟩

theorem isLattice_std (n : ℕ) : Submodule.IsLattice E (Formalism.MainNotions.StandardLattice.stdLat E n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span ⟨j, rfl⟩

variable [StarRing E]

omit [NumberField E] in
theorem re_form (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (x : Fin n → E)
    (τ : E →+* ℂ) : (τ (Formalism.MainNotions.StandardLattice.stdForm E n x x)).re = ∑ i, Complex.normSq (τ (x i)) := by
  change (τ (∑ i, star (x i) * x i)).re = _
  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hφ, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem trace_pos (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (x : Fin n → E)
    (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (Formalism.MainNotions.StandardLattice.stdForm E n x x) := by
  have h1 := congrArg Complex.re
    (trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := Formalism.MainNotions.StandardLattice.stdForm E n x x))
  rw [Complex.re_sum] at h1
  have h2 : 0 < ∑ σ : E →ₐ[ℚ] ℂ, (σ (Formalism.MainNotions.StandardLattice.stdForm E n x x)).re := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine Finset.sum_pos (fun σ _ => ?_) ⟨τ.toRatAlgHom, Finset.mem_univ _⟩
    refine lt_of_lt_of_eq ?_ (re_form hφ x σ.toRingHom).symm
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
    exact Complex.normSq_pos.2 ((map_ne_zero σ.toRingHom).2 hi)
  rw [← h1] at h2
  simpa using h2

omit [NumberField E] in
theorem isSymm_std (n : ℕ) : (Formalism.MainNotions.StandardLattice.stdForm E n).IsSymm := by
  constructor
  intro x y
  change starRingEnd _ (∑ i, star (x i) * y i) = ∑ i, star (y i) * x i
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star]

omit [NumberField E] in

theorem norm_entry_le (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (Formalism.MainNotions.StandardLattice.stdForm E n)) (j i : Fin n)
    (τ : E →+* ℂ) : ‖τ (g (Pi.single j 1) i)‖ ≤ 1 := by
  have e : Formalism.MainNotions.StandardLattice.stdForm E n (g (Pi.single j 1)) (g (Pi.single j 1)) = 1 := by
    rw [hg]
    change ∑ i, star ((Pi.single j (1 : E) : Fin n → E) i) * (Pi.single j (1 : E) : Fin n → E) i = 1
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have h1 := re_form hφ (g (Pi.single j 1)) τ
  rw [e, map_one, Complex.one_re] at h1
  have h2 := Finset.single_le_sum (f := fun i => Complex.normSq (τ (g (Pi.single j 1) i)))
    (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [← h1, Complex.normSq_eq_norm_sq] at h2
  exact (sq_le_one_iff₀ (norm_nonneg _)).1 h2

theorem card_aut_std (hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) (n : ℕ) :
    Finite (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) ∧
    Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) ≤
      3 ^ (Module.finrank ℚ E * n ^ 2) := by
  have hm : ∀ (g : Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) (j i : Fin n),
      ∃ a : 𝓞 E, (a : E) = g.1 (Pi.single j 1) i := fun g j i => by
    refine coord_of_mem ?_ i
    exact g.2.2.le ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  choose a ha using hm
  have hq := card_quot_three (E := E)
  haveI : Finite (𝓞 E ⧸ Ideal.span {(3 : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hq]; positivity)
  have hinj : Function.Injective fun g j i => Ideal.Quotient.mk (Ideal.span {(3 : 𝓞 E)}) (a g j i) := by
    intro g g' h
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    refine (Pi.basisFun E (Fin n)).ext fun j => ?_
    funext i
    rw [Pi.basisFun_apply]
    change g.1 _ i = g'.1 _ i
    rw [← ha, ← ha, eq_of_mk_eq (a g j i) (a g' j i) (fun φ => ?_) (fun φ => ?_) (congrFun (congrFun h j) i)]
    · rw [ha]; exact norm_entry_le hφ g.2.1 j i φ
    · rw [ha]; exact norm_entry_le hφ g'.2.1 j i φ
  refine ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans_eq ?_⟩
  rw [Nat.card_fun, Nat.card_fun, hq, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← pow_mul, sq]

end

theorem card_aut_gmap {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (N : Submodule (𝓞 K) V) :
    Nat.card (Formalism.ThetaLiftIndependence.autL h N) = Nat.card (Formalism.ThetaLiftIndependence.autL h (Formalism.HermitianLatticesTheory.gmap g N)) := by
  have hmul : ∀ (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V),
      Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := fun a b M => by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have hone : ∀ M : Submodule (𝓞 K) V, Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := fun M => Submodule.map_id M
  refine Nat.card_congr
    { toFun := fun u => ⟨g * u.1 * g⁻¹, mul_mem (mul_mem hg u.2.1) (inv_mem hg), ?_⟩
      invFun := fun u => ⟨g⁻¹ * u.1 * g, mul_mem (mul_mem (inv_mem hg) u.2.1) hg, ?_⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
  · rw [← hmul, inv_mul_cancel_right, hmul, u.2.2]
  · rw [hmul, hmul, u.2.2, ← hmul, inv_mul_cancel, hone]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E], (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ, ((3 : ℝ) ^ (Module.finrank ℚ E * n ^ 2))⁻¹ ≤ Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  intro E _ _ _ _ hst n
  have hφ : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a) := fun φ a => by
    rw [hst, IsCMField.complexEmbedding_complexConj]
  obtain ⟨⟨s, hs⟩, hm, -⟩ := Formalism.HermitianLatticesTheory.final_massBasic E (Fin n → E) _ (isSymm_std n) (trace_pos hφ) _
    (isLattice_std n)
  obtain ⟨N, ⟨hN, g, hg, e⟩, -⟩ := hs.2 (Formalism.MainNotions.StandardLattice.stdLat E n)
    ⟨isLattice_std n, fun p _ => ⟨1, one_mem _, Submodule.map_id _⟩⟩
  obtain ⟨hf, hc⟩ := card_aut_std hφ n
  haveI : Nonempty (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) :=
    ⟨⟨1, one_mem _, Submodule.map_id _⟩⟩
  have hp : 0 < Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n)) := Nat.card_pos
  rw [hm s hs]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun M => ((Nat.card (Formalism.ThetaLiftIndependence.autL (Formalism.MainNotions.StandardLattice.stdForm E n) M) : ℝ))⁻¹) (fun _ _ => by positivity) hN)
  beta_reduce
  rw [card_aut_gmap _ hg N, e]
  exact inv_anti₀ (by exact_mod_cast hp) (by exact_mod_cast hc)

end GlobalTheory.StdMassLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfNeZeroMapIsotypicSumOfCopiesStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equiv_of_ne_zero_map_isotypicSumOfCopies : ∀ (H : Type) [Group H] [Finite H] (V V' W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (τ : Representation ℂ H V) (τ' : Representation ℂ H V') (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W'), ρ.IsIrreducible → ρ'.IsIrreducible → IsIsotypicOf τ ρ → IsIsotypicOf τ' ρ' → ∀ T : Representation.IntertwiningMap τ τ', T ≠ 0 → Nonempty (Representation.Equiv ρ ρ') := by
  first | exact @GlobalTheory.IsotypicMap.equiv_of_isotypic_map | exact GlobalTheory.IsotypicMap.equiv_of_isotypic_map | (intros; apply GlobalTheory.IsotypicMap.equiv_of_isotypic_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvSubstNatMultiplePrimePowConstantStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ev_subst_natMultiple_prime_pow_constant : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, c.ev n (subst (nmul c.μ (p ^ n)) f) = algebraMap O _ (constantCoeff f)) ∧ (∀ s, c.ev₂ n (pull2 (nmul c.μ (p ^ n)) s) = algebraMap O _ (constantCoeff s)) ∧ ∀ f, c.ev (n + 1) (subst (nmul c.μ p) f) = G.mulP n (c.ev n f) := by
  first | exact @GlobalTheory.QLog.Chart.ev_nmul_pow | exact GlobalTheory.QLog.Chart.ev_nmul_pow | (intros; apply GlobalTheory.QLog.Chart.ev_nmul_pow <;> assumption)
end

