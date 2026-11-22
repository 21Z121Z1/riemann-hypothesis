import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0916
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0917
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorIner
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.UseFive

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem exists_good_gen (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (g0 : GE N)
    (hw : ∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w))
    (hord : orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
      N.l i - 1)
    (hu : ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b →
      IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)))
    (eB e1 X0 : N.X i → MatN N i) (hT : CharPolyIn (N.T i) rep)
    (hspan : Submodule.span (N.O i) (Set.range (mat (ρ π))) = ⊤)
    (hid : InRing (N.T i) rep eB ∧ InRing (N.T i) rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧
      e1 * eB = 0 ∧ (∀ x, ((eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((e1 x).map (toK N i)).rank = 1))
    (e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)))
    (hd : IsDecomp (t := R.t) (rep π) (ρ π) (N.chi i) e)
    (heB : ∀ u, e (((eB π).map (toK N i)).mulVec u) = (0, (e u).2))
    (hX : InRing (N.T i) rep X0) (hX1 : eB * X0 = X0) (hX2 : X0 * eB = X0)
    (hXπ : ∀ u, e (((X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i) * (e u).2 c))
    (hβ : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c))) :
    ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧ IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition N rep ρ π S := by
  classical
  have hinjχ : Set.InjOn (fun c => ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) (Finset.Icc 1 R.t : Set ℕ) := by
    intro a ha b hb hab
    by_contra hne
    have := hu a ha b hb hne
    simp only at hab
    rw [hab, sub_self] at this
    exact not_isUnit_zero this
  have hβ' : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c)) ∧
      (x = π → ∀ c, β c = ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i)) := by
    intro x
    by_cases hx : x = π
    · subst hx
      refine ⟨fun c => ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i), fun a b hab => ?_, ?_,
        fun _ _ => rfl⟩
      · have := hinjχ (x₁ := (a : ℕ) + 1) (by simp) (x₂ := (b : ℕ) + 1) (by simp) hab
        exact Fin.ext (by omega)
      · apply Polynomial.map_injective (toK N i) (IsFractionRing.injective _ _)
        rw [blockPol_map, (GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hXπ).2, Polynomial.map_prod]
        simp
    · obtain ⟨β, h1, h2⟩ := hβ x
      exact ⟨β, h1, h2, fun h => absurd h hx⟩
  choose β hβi hβp hβπ using hβ'
  have hrπ : ∀ c ∈ Finset.Icc 1 R.t, root β c (π, 1) = ((N.chi i c g0 : (N.O i)ˣ) : N.O i) := by
    intro c hc
    obtain ⟨a, rfl⟩ := exists_succ hc
    rw [root_succ]
    exact hβπ π rfl a
  have hset : (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ) =
      Set.range fun c : Fin R.t => fun x' : N.X i × Equiv.Perm (Fin R.t) => β x'.1 (x'.2 c) := by
    ext f
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, rfl⟩ := exists_succ hc
      exact ⟨a, funext fun x' => (root_succ β a x').symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℕ) + 1, by simp, funext fun x' => root_succ β a x'⟩
  let T' : Subalgebra (N.O i) (N.X i × Equiv.Perm (Fin R.t) → N.O i) :=
    Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f x'.1) '' (N.T i : Set _) ∪
      (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ))
  have hTT : ∀ f ∈ N.T i, (fun x' : N.X i × Equiv.Perm (Fin R.t) => f x'.1) ∈ T' :=
    fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  have hT' : CharPolyIn T' (fun x' => rep x'.1) := fun h d => hTT _ (hT h d)
  obtain ⟨ψρ, ψχ, hψ, hψs⟩ := GlobalTheory.T.exists_block_action_of_decomposition T' (fun x' => rep x'.1) (ρ π) (N.chi i) (π, 1) e hspan hd
  have hpol : ∀ x' : N.X i × Equiv.Perm (Fin R.t),
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (root β c x')) =
        blockPol (eB x'.1) (X0 x'.1) := by
    intro x'
    rw [prod_Icc_eq, hβp, ← Equiv.prod_comp x'.2 (fun c => Polynomial.X - Polynomial.C (β x'.1 c))]
    simp only [root_succ]
  have hE := fun x' : N.X i × Equiv.Perm (Fin R.t) =>
    GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain R.nV R.t (eB x'.1) (X0 x'.1) (fun c => root β c x') (two_le_ranks_t R)
      (congrFun hid.2.2.1 _) (congrFun hX1 _) (congrFun hX2 _) (by
        intro c hc c' hc' h
        obtain ⟨a, rfl⟩ := exists_succ hc
        obtain ⟨a', rfl⟩ := exists_succ hc'
        simp only [root_succ] at h
        rw [x'.2.injective (hβi _ h)]) (hpol x')
  refine ⟨{ eB := eB, e1 := e1, g0 := g0, X0 := X0, X' := N.X i × Equiv.Perm (Fin R.t), p := Prod.fst,
            T' := T', rr := root β, π' := (π, 1), e := e, ψρ := ψρ, ψχ := ψχ }, rfl,
    hid, hd, hψ, hψs, hw, hord, ⟨hX, hX1, hX2, hXπ⟩, ⟨hTT, ?_, rfl, ?_, ?_⟩, hpol, ⟨rfl, hrπ⟩,
    ⟨fun x' => (hE x').1, fun x' => (hE x').2, ?_, ?_⟩, GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T' _ hT', GlobalTheory.T.blockDet_mem_heckeAlgebra_of_heckeSpan T' _ hT'⟩
  · exact fun c hc => Algebra.subset_adjoin (Or.inr ⟨c, hc, rfl⟩)
  · have := GlobalTheory.SplittingAlgebra.main (N.T i) R.t β hβi (N.T_sep i) (fun j => by
      simpa only [hβp] using blockPol_coeff_mem hT hid.1 hX j)
    simp only [← hset] at this
    exact this
  · intro x
    have : {x' : N.X i × Equiv.Perm (Fin R.t) // x'.1 = x} ≃ Equiv.Perm (Fin R.t) :=
      { toFun := fun a => a.1.2
        invFun := fun σ => ⟨(x, σ), rfl⟩
        left_inv := by rintro ⟨⟨y, σ⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr this).trans (by simp [Fintype.card_perm])
  · refine GlobalTheory.T.prod_other_root_factors_action_first_coordinate e (eB π) (X0 π) (fun c => root β c (π, 1)) (two_le_ranks_t R) heB (fun u => ?_)
    rw [hXπ]
    congr 1
    funext c
    rw [hrπ _ (by simp)]
  · have h2 := two_le_ranks_t R
    have : del51 N (⟨eB, e1, g0, X0, N.X i × Equiv.Perm (Fin R.t), Prod.fst, T', root β, (π, 1), e, ψρ, ψχ⟩ :
        IdempotentChoiceData N i) (π, 1) = ∏ c ∈ Finset.Ioc 1 R.t,
        (((N.chi i 1 g0 : (N.O i)ˣ) : N.O i) - ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) := by
      refine Finset.prod_congr rfl fun c hc => ?_
      show root β 1 (π, 1) - root β c (π, 1) = _
      rw [hrπ 1 (by simp; omega), hrπ c (Finset.Ioc_subset_Icc_self hc)]
    rw [this]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun c hc => ?_)
    have hc' := Finset.mem_Ioc.1 hc
    exact hu 1 (by simp; omega) c (Finset.Ioc_subset_Icc_self hc) (by omega)

end Record

theorem objects_globalStep_gen : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  intro D i r ρ π _ hG1 _ _ _ hdec _ hres _ hun ht
  classical
  obtain ⟨e, hd⟩ := hdec
  obtain ⟨w, hw, g0, hg0, hord⟩ := GlobalTheory.T.exists_inertia_cyclotomic_generates_units_mod D.nd i hun
  have hu := GlobalTheory.T.isUnit_sub_charValues_of_cyclotomic_generator D.nd i g0 hord ht
  have hT : CharPolyIn (D.nd.T i) r := hG1
  have hspan : Submodule.span (D.nd.O i) (Set.range (mat (ρ π))) = ⊤ := GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top (ρ π) hres
  obtain ⟨eB, e1, ⟨hB, h1, hBB, h11, hB1, h1B⟩, heB, ε, hε, he1⟩ :=
    GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep (D.nd.l i) (D.nd.T i) r (ρ π) (D.nd.chi i) π e (two_le_r _) hspan hd
  have hl := D.nd.T_local i
  have hXπ : ∀ u, e (((eB π * mat (r π) g0 * eB π).map (toK D.nd i)).mulVec u) =
      (0, fun c : Fin D.R.t => toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g0 : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c) := by
    intro u
    rw [Matrix.map_mul, Matrix.map_mul]
    exact corner_act e heB (hd g0) u
  have hat := GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hXπ
  have hrB : ∀ x, ((eB x).map (toK D.nd i)).rank = D.R.t := fun x => by
    rw [rank_const hl hT hB hBB x π]; exact hat.1
  have hr1 : ∀ x, ((e1 x).map (toK D.nd i)).rank = 1 := fun x => by
    rw [rank_const hl hT h1 h11 x π, GlobalTheory.T.rank_eq_of_mulVec_through_first_block e _ ε he1, hε]
  have hX : InRing (D.nd.T i) r (fun x => eB x * mat (r x) g0 * eB x) :=
    inRing_mul (inRing_mul hB (inRing_mat g0)) hB
  have hBx : ∀ x, eB x * eB x = eB x := congrFun hBB
  have hX1 : eB * (fun x => eB x * mat (r x) g0 * eB x) = fun x => eB x * mat (r x) g0 * eB x := by
    funext x; simp only [Pi.mul_apply, ← mul_assoc, hBx]
  have hX2 : (fun x => eB x * mat (r x) g0 * eB x) * eB = fun x => eB x * mat (r x) g0 * eB x := by
    funext x; simp only [Pi.mul_apply, mul_assoc, hBx]
  haveI := D.nd.O_complete i
  have hβ := GlobalTheory.T.exists_injective_roots_of_distinct_units_roots (t := D.R.t) (D.nd.T i) hl (fun x => blockPol (eB x) (eB x * mat (r x) g0 * eB x))
    (blockPol_coeff_mem hT hB hX)
    (fun x => by
      have hm := blockPol_monic (congrFun hBB x) (hrB x) (congrFun hX1 x) (congrFun hX2 x)
      exact ⟨Polynomial.monic_of_injective (IsFractionRing.injective _ _) hm.1,
        (Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _).symm.trans hm.2⟩)
    π (fun c => ((D.nd.chi i ((c : ℕ) + 1) g0 : (D.nd.O i)ˣ) : D.nd.O i))
    (fun a b hab => hu _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (fun h => hab (Fin.ext (by omega))))
    (by
      apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective _ _)
      rw [blockPol_map, hat.2, Polynomial.map_prod]
      simp)
  obtain ⟨S, -, hS⟩ := exists_good_gen D.nd i r ρ π g0 ⟨w, hw, hg0⟩ hord hu eB e1 _ hT hspan
    ⟨hB, h1, hBB, h11, hB1, h1B, hrB, hr1⟩ e hd heB hX hX1 hX2 hXπ hβ
  exact ⟨S, hS⟩

end GlobalTheory.UseFive

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHubDataFamily
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem exists_setup_large : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → FactsF Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ AdmissibleParameterJ.AdmJ (Fm.L x i) ∧ Setup (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  intro hP eps Fm C C₂ CT hTw hF
  obtain ⟨i0⟩ := Fm.Ix_zero
  have he : 0 < eps := Fm.L_eps 0 i0 ▸ (Fm.L 0 i0).sc.eps_pos
  obtain ⟨xa, hxa⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) he
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.specialPrimes_small_along_family Fm 1 le_rfl
  obtain ⟨xc, hxc⟩ := hTw
  refine ⟨max xa (max xb xc), fun x hx hx1 i hsha exc => ?_⟩
  have hxa' : xa ≤ x := le_trans (le_max_left _ _) hx
  have hxb' : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxc' : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, N0, S, hgood⟩ := hxc x hxc' hx1 i
  obtain ⟨hfa, -⟩ := hF x hx1 i
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x i)
  have hCLw : (Fm.params x hx1 i).CLw ≤ Fm.PK.getD 7 0 := by
    rw [← Fm.params_K x hx1 i]
    exact le_refl _
  have hsx : xa ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx1]; exact hxa'
  obtain ⟨hpar, hpar67⟩ := hxa (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i) (Fm.L_eps x i) hCLw hsx
  obtain ⟨X, hcan, -, hexc, hI, -⟩ := GlobalTheory.HubX.exists_hubData GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.L x i) HW (rowC C₂)
    hfa.adm.1.1.2.2.2.1 hfa.Conclusion1.1 (fun _ _ _ _ => 0) (fun _ => exc) ⟨twE Fm x hx1 i, N0, S⟩
  obtain ⟨-, hbig, hsplit, -⟩ := hxb x hxb' hx1 i
  have hrow : GlobalTheory.PtCore.GoodPtRow (Fm.D x i) :=
    GlobalTheory.Proof.LocalGlobalAssembly.main _ hfa.adm.1.1.1 hfa.Conclusion1.2.2 hfa.Conclusion2.2.2
  have h6 := GlobalTheory.JointSix.main GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.ex x hx1 i).nch X.r X.ρ hcan.fam hfa.nct hfa.trip
    hfa.same hrow (GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred _ hfa.rhoBar)
  have hkill : KillingConditions.KillAt X.ρ := GlobalTheory.T.chosenTwist_annihilates_selmerGroups (Fm.D x i) (Fm.ex x hx1 i).nch X.I X.ρ hfa.nct (hI ▸ hgood) h6
  exact ⟨HW, F, Cm, X, hexc, hfa.admJ _ hpar, ⟨hfa, hcan, hpar, hpar67, hbig, hsplit, hkill, hsha⟩⟩

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocal
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.LiftW

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def basisVec (k : ℕ) (j : Fin k) : ↥(stdG O LL k) :=
  ⟨Pi.single j 1, ⟨Pi.single j 1, by
    funext j'
    simp [Pi.single_apply]⟩⟩

def coordQ (k : ℕ) (j : Fin k) : ((Fin k → LL) ⧸ stdG O LL k) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL k).mapQ (intO LL) (LinearMap.proj j) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u j, rfl⟩)

theorem coordQ_mk (k : ℕ) (j : Fin k) (v : Fin k → LL) :
    coordQ (O := O) LL k j (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v j) := rfl

theorem iotaW_tmul (lam : O) (a k : ℕ) (t : ↥(stdG O LL k)) (s : LL)
    (hs : (Submodule.Quotient.mk s : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a) :
    iotaW LL lam a k (t ⊗ₜ ⟨Submodule.Quotient.mk s, hs⟩) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := rfl

theorem exists_sum (k : ℕ) {X : Type} [AddCommGroup X] [Module O X] (u : ↥(stdG O LL k) ⊗[O] X) :
    ∃ x : Fin k → X, u = ∑ j, basisVec LL k j ⊗ₜ[O] x j := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t y =>
    obtain ⟨_, c, rfl⟩ := t
    refine ⟨fun j => c j • y, ?_⟩
    simp only [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    apply Subtype.ext
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  | add u v hu hv =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x + y, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem coordQ_iotaW (lam : O) (a k : ℕ) (x : Fin k → ↥(Xq LL lam a)) (j : Fin k) :
    coordQ LL k j (iotaW LL lam a k (∑ j', basisVec LL k j' ⊗ₜ[O] x j')) = x j := by
  have h : ∀ j', coordQ LL k j (iotaW LL lam a k (basisVec LL k j' ⊗ₜ[O] x j')) =
      if j = j' then (x j' : LL ⧸ intO (O := O) LL) else 0 := by
    intro j'
    obtain ⟨y, hy⟩ := x j'
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [iotaW_tmul, coordQ_mk]
    by_cases hj : j = j' <;> simp [basisVec, hj]
  simp [map_sum, h]

theorem iotaW_injective (lam : O) (a k : ℕ) : Function.Injective (iotaW LL lam a k) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨x, rfl⟩ := exists_sum LL k u
  have : x = 0 := by
    funext j
    apply Subtype.ext
    rw [← coordQ_iotaW, hu]
    simp
  simp [this]

theorem exists_iotaW (lam : O) (a k : ℕ) (q : (Fin k → LL) ⧸ stdG O LL k) (hq : lam ^ a • q = 0) :
    ∃ u, iotaW LL lam a k u = q := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx : ∀ j, (Submodule.Quotient.mk (v j) : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a := by
    intro j
    have := congrArg (coordQ LL k j) hq
    rw [map_smul, map_zero, coordQ_mk] at this
    exact this
  refine ⟨∑ j, basisVec LL k j ⊗ₜ[O] ⟨_, hx j⟩, ?_⟩
  simp only [map_sum, iotaW_tmul]
  have : v = ∑ j, v j • (basisVec (O := O) LL k j : Fin k → LL) := by
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [this]
  exact (map_sum (stdG O LL k).mkQ _ _).symm

variable {LL}

theorem iotaW_actTw (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (u : ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a)) :
    iotaW LL lam a k (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g u) =
      actD (stdLatG hinj N) g (iotaW LL lam a k u) := by
  induction u using TensorProduct.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)).symm)
  | add u v hu hv =>
    have e1 := map_add (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g) u v
    have e2 := map_add (actD (stdLatG hinj N) g) (iotaW LL lam a k u) (iotaW LL lam a k v)
    refine (congrArg _ e1).trans ((map_add _ _ _).trans ?_)
    rw [map_add]
    exact (congrArg₂ (· + ·) hu hv).trans e2.symm
  | tmul t y =>
    obtain ⟨y, hy⟩ := y
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine (map_smul (iotaW LL lam a k) (((θ g)⁻¹ : Oˣ) : O)
      ((show ↥(stdG O LL k) from actT (stdLatG hinj (twistM N θ)) g t) ⊗ₜ[O] ⟨Submodule.Quotient.mk s, hy⟩)).trans ?_
    rw [iotaW_tmul, iotaW_tmul, ← Submodule.Quotient.mk_smul]
    refine congrArg Submodule.Quotient.mk ?_
    show (((θ g)⁻¹ : Oˣ) : O) • s • (((((θ g : Oˣ) : O) • N g).map (algebraMap O LL)).mulVec (t : Fin k → LL)) =
      ((N g).map (algebraMap O LL)).mulVec (s • (t : Fin k → LL))
    have e : (((θ g : Oˣ) : O) • N g).map (algebraMap O LL) = ((θ g : Oˣ) : O) • (N g).map (algebraMap O LL) := by
      ext p q
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [Algebra.smul_def]
    rw [e, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_comm s, smul_smul, Units.inv_mul, one_smul]

theorem exists_twistedCocycle_lift_torsion (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  choose z hz using fun g => exists_iotaW LL lam a k (f g) (hk g)
  refine ⟨z, ⟨?_, fun g h => ?_⟩, hz⟩
  · refine IsLocallyConstant.desc z (iotaW LL lam a k) ?_ (iotaW_injective LL lam a k)
    have : (iotaW LL lam a k) ∘ z = f := funext hz
    rw [this]
    exact hf.1
  · apply iotaW_injective LL lam a k
    refine (hz _).trans ((hf.2 g h).trans ?_)
    refine Eq.trans ?_ (map_add (iotaW LL lam a k) (z g) _).symm
    rw [hz g, ← hz h]
    exact congrArg _ (iotaW_actTw hinj lam a N θ g (z h)).symm

theorem lift_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : χ = θ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  subst hχ
  exact exists_twistedCocycle_lift_torsion hinj lam a N χ f hf hk

end Gen

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  ext g
  simp [chiT, chiOC]

theorem lift_cocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  intro D i w hw C lam _ k N θ a f hf hk
  exact lift_gen Subtype.val_injective lam a N θ (chiT C θ 1) (chiT_one C θ) f hf hk

end GlobalTheory.UseLoc.Cases.LiftW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsDetRootFinPartOne
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFinPart

theorem eq_one_of_finPart_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (h : ChrEq c χ)
    {n : ℕ} (hn : 0 < n) (ho : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [map_pow]
  exact key y

theorem isDetRoot_mul' {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem exists_isDetRoot_finPart_one {D : D7} (V : HSp D) (a : GA D V) (ha : finHom V a = 1) (z : (AE D)ˣ)
    (hz : IsDetRoot V a z) : ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ IsDetRoot V a y := by
  obtain ⟨y, hyi, hyf⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D (z : AE D)) 1
  obtain ⟨y', hyi', hyf'⟩ := GlobalTheory.PlaceIdem.parts_surj D (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1
  have hyy : y * y' = 1 := GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [RingHom.map_mul, hyi, hyi', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
    (by rw [RingHom.map_mul, hyf, hyf', mul_one, RingHom.map_one])
  have hc : ∀ w : AE D, infPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D w) := fun w => GlobalTheory.PlaceIdem.infPart_cA D w
  have hf : ∀ w : AE D, finPart D (sigR (AF D.host.F) D.sp.cm.sig w) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := fun w => GlobalTheory.PlaceIdem.finPart_cA D w
  have e2 : finPart D (matHom V a).1.det = 1 := by
    have e : finPart D (matHom V a).1.det = (finHom V a).1.det := (finPart D).map_det _
    rw [e, ha]
    simp
  refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, hyf, ?_⟩
  show y = (matHom V a).1.det * sigR (AF D.host.F) D.sp.cm.sig y
  refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
  · have h1 := congrArg (infPart D) hz
    unfold IsDetRoot at h1
    rw [RingHom.map_mul, hc] at h1
    rw [RingHom.map_mul, hc, hyi]
    exact h1
  · rw [RingHom.map_mul, hf, hyf, e2, RingHom.map_one, one_mul]

theorem eq_of_finHom_of_triv {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hχ : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → χ y = 1) (dd : GA D V → ℂ) (hd : MuVal V χ dd)
    (h h' : GA D V) (hh : finHom V h = finHom V h') : dd h = dd h' := by
  have ha : finHom V (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, hh, inv_mul_cancel]
  obtain ⟨x, hx⟩ := hd.1 h
  obtain ⟨z, hz⟩ := hd.1 (h⁻¹ * h')
  obtain ⟨y, hy1, hy⟩ := exists_isDetRoot_finPart_one V _ ha z hz
  have hxy := isDetRoot_mul' V h (h⁻¹ * h') x y hx hy
  rw [mul_inv_cancel_left] at hxy
  rw [hd.2 h x hx, hd.2 h' _ hxy, map_mul, hχ y hy1, mul_one]

theorem twist_eq_of_finHom : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ)
    (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ,
    (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ h h' : GA D V, finHom V h = finHom V h' → dd h = dd h' := by
  intro D V pd k _ σ δ δc hT dd hdd h h' hh
  obtain ⟨hc, ⟨n, hn, ho⟩, -⟩ := hT
  have h1 : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 → δc y = 1 := eq_one_of_finPart_eq_one D δc δ hc hn ho
  rcases hdd with hd | hd
  · exact eq_of_finHom_of_triv V δc h1 dd hd h h' hh
  · exact eq_of_finHom_of_triv V δc⁻¹ (fun y hy => by rw [MonoidHom.inv_apply, h1 y hy, inv_one]) dd hd h h' hh

end GlobalTheory.TwistFinPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreenStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_of_green : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (Γ : GrpSide D), GreenLab Γ → SplitLoc hL D := by
  first | exact @GlobalTheory.BlockTypeSplit.main | exact GlobalTheory.BlockTypeSplit.main | (intros; apply GlobalTheory.BlockTypeSplit.main <;> assumption)
end

