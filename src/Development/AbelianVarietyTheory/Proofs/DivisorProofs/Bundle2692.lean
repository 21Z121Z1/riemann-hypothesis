import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0782
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0149
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentInvariantOfChartwiseProjection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.descent_eqn_of_chart_projection : ∀ (B S X G : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)) (ψ : J → (U.left ⟶ G)) (β : X ⟶ G), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ j, e j ≫ β = pullback.fst _ _ ≫ ψ j) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  intro B S X G π f Φ U J e ψ β he hcov hf hβ hch
  let 𝒰 : (pullback f (pullback.fst π π)).OpenCover :=
    Scheme.Cover.mkOfCovers J (fun j => pullback (e j) (pullback.fst f (pullback.fst π π)))
      (fun j => pullback.snd _ _) (by
        intro q
        obtain ⟨j, y, hy⟩ := (by simpa [Set.mem_range] using hcov (pullback.fst f (pullback.fst π π) q) :
          ∃ j, ∃ y, (e j) y = pullback.fst f (pullback.fst π π) q)
        obtain ⟨p, -, hp⟩ := Scheme.exists_preimage_of_isPullback
          (IsPullback.of_hasPullback (e j) (pullback.fst f (pullback.fst π π))) y q hy
        exact ⟨j, p, hp⟩)
  refine Scheme.Cover.hom_ext 𝒰 _ _ (fun (j : J) => ?_)
  change pullback.snd (e j) (pullback.fst f (pullback.fst π π)) ≫ _ =
    pullback.snd (e j) (pullback.fst f (pullback.fst π π)) ≫ _
  have hc := pullback.condition (f := e j) (g := pullback.fst f (pullback.fst π π))
  generalize pullback.snd (e j) (pullback.fst f (pullback.fst π π)) = z at hc ⊢
  generalize pullback.fst (e j) (pullback.fst f (pullback.fst π π)) = y₁ at hc
  have h1 : y₁ ≫ pullback.snd U.hom π = (z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.fst π π := by
    calc y₁ ≫ pullback.snd U.hom π = y₁ ≫ e j ≫ f := by rw [hf]
      _ = z ≫ pullback.fst f (pullback.fst π π) ≫ f := by rw [reassoc_of% hc]
      _ = z ≫ pullback.snd f (pullback.fst π π) ≫ pullback.fst π π := by rw [pullback.condition]
      _ = _ := (Category.assoc _ _ _).symm
  have h2 : (y₁ ≫ pullback.fst U.hom π) ≫ U.hom =
      ((z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.snd π π) ≫ π := by
    calc (y₁ ≫ pullback.fst U.hom π) ≫ U.hom = y₁ ≫ pullback.snd U.hom π ≫ π := by
          rw [Category.assoc, pullback.condition]
      _ = (z ≫ pullback.snd f (pullback.fst π π)) ≫ pullback.fst π π ≫ π := by rw [reassoc_of% h1]; simp only [Category.assoc]
      _ = _ := by rw [pullback.condition]; simp only [Category.assoc]
  have hΦ := hch j _ y₁ (pullback.lift _ _ h2) _ (pullback.lift_fst _ _ _).symm h1
    (pullback.lift_snd _ _ _) z hc.symm rfl
  calc z ≫ pullback.fst f (pullback.fst π π) ≫ β = y₁ ≫ e j ≫ β := by
        rw [reassoc_of% hc]
    _ = pullback.lift _ _ h2 ≫ e j ≫ β := by
        rw [hβ, pullback.lift_fst_assoc, Category.assoc]
    _ = z ≫ Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
        have h3 := congrArg (· ≫ β) hΦ
        simpa only [Category.assoc] using h3.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantPerturbationBound
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem detClose_norm_prod_sub_lt {C : Type} [NormedField C] [IsUltrametricDist C] {ι : Type}
    (s : Finset ι) (f g : ι → C) (hf : ∀ i, ‖f i‖ ≤ 1) (hfg : ∀ i, ‖f i - g i‖ < 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ < 1 := by
  classical
  have hg : ∀ i, ‖g i‖ ≤ 1 := fun i => by
    have : g i = f i + -(f i - g i) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf i) (by rw [norm_neg]; exact (hfg i).le))
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ 1 * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ :=
            mul_le_mul_of_nonneg_right (hf a) (norm_nonneg _)
        _ < 1 := by simpa using ih
    · rw [norm_mul, norm_prod]
      calc ‖f a - g a‖ * ∏ i ∈ s, ‖g i‖ ≤ ‖f a - g a‖ * 1 :=
            mul_le_mul_of_nonneg_left (Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hg i))
              (norm_nonneg _)
        _ < 1 := by simpa using hfg a

theorem detClose_norm_sum_lt {C : Type} [NormedField C] [IsUltrametricDist C] {ι : Type}
    (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, ‖f i‖ < 1) : ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem detClose_norm_det_sub_lt {C : Type} [NormedField C] [IsUltrametricDist C] {k : ℕ}
    (B B' : Matrix (Fin k) (Fin k) C) (hB : ∀ i j, ‖B i j‖ ≤ 1)
    (hBB : ∀ i j, ‖B i j - B' i j‖ < 1) : ‖B.det - B'.det‖ < 1 := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  apply detClose_norm_sum_lt
  intro σ _
  rw [← mul_sub, norm_mul]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : C)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  exact detClose_norm_prod_sub_lt _ _ _ (fun i => hB _ _) (fun i => hBB _ _)

theorem det_sub_lt_of_close_on_unitBall : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] (J : Type) (k : ℕ) (P P' : J → Fin k → C) (N : ℝ), 0 < N → (∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ ≤ N) → (∃ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ = N) → (∀ cf : Fin k → C, (∀ j, ‖∑ l, cf l * P j l‖ ≤ 1) → ∀ j, ‖∑ l, cf l * (P j l - P' j l)‖ < 1) → ∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det - (Matrix.of fun r l => P' (σ r) l).det‖ < N := by
  intro C _ _ J k P P' N hN hle ⟨σ₀, hσ₀⟩ hclose σ
  classical
  set A : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P (σ₀ r) l with hA
  have hdetA : A.det ≠ 0 := by
    intro h; rw [h, norm_zero] at hσ₀; linarith
  set Q := A⁻¹ with hQ

  have hcol : ∀ (c : Fin k) (j : J), ‖∑ l, Q l c * P j l‖ ≤ 1 := by
    intro c j
    have h1 : ∑ l, A.adjugate l c * P j l = (A.updateRow c (P j)).det := by
      rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
        ← Matrix.adjugate_transpose]
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    have h2 : A.updateRow c (P j) = Matrix.of fun r l => P (Function.update σ₀ c j r) l := by
      ext r l
      by_cases hr : r = c
      · subst hr; simp [Matrix.updateRow_apply]
      · simp [Matrix.updateRow_apply, hr, Function.update_of_ne hr, hA]
    have h3 : ∑ l, Q l c * P j l = (A.det)⁻¹ * ∑ l, A.adjugate l c * P j l := by
      rw [hQ, Matrix.inv_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, mul_assoc]
    rw [h3, h1, h2, norm_mul, norm_inv, hσ₀]
    rw [inv_mul_le_iff₀ hN, mul_one]
    exact hle _
  set M : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P (σ r) l
  set M' : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P' (σ r) l
  have hB : ∀ r c, ‖(M * Q) r c‖ ≤ 1 := by
    intro r c
    rw [Matrix.mul_apply]
    simpa [M, mul_comm] using hcol c (σ r)
  have hBB : ∀ r c, ‖(M * Q) r c - (M' * Q) r c‖ < 1 := by
    intro r c
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
    have := hclose (fun l => Q l c) (fun j => hcol c j) (σ r)
    convert this using 2
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [M, M']; ring
  have hkey := detClose_norm_det_sub_lt (M * Q) (M' * Q) hB hBB
  have hQA : Q.det * A.det = 1 := by
    rw [hQ, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_mul_cancel₀ hdetA]
  have e : M.det - M'.det = ((M * Q).det - (M' * Q).det) * A.det := by
    rw [Matrix.det_mul, Matrix.det_mul, sub_mul, mul_assoc, mul_assoc, hQA, mul_one, mul_one]
  show ‖M.det - M'.det‖ < N
  rw [e, norm_mul, hσ₀]
  calc ‖(M * Q).det - (M' * Q).det‖ * N < 1 * N := mul_lt_mul_of_pos_right hkey hN
    _ = N := one_mul N

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSiegelHeisenbergInvariantFormUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagSiegelUniq

open GlobalTheory.WeilM

theorem diagMat_eq_mul {A : Type} [CommRing A] {m n : ℕ} (w : Matrix (Fin m) (Fin n) A) :
    GlobalTheory.DiagSiegel.diagMat w =
      w * ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id)ᵀ := by
  ext i j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases j with j | j <;>
    simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, id] <;>
    simp [diagCols, Matrix.one_apply]

theorem transpose_transport (D : D7) (S T : HSp D) (ν : Measure (Formalism.IndefR.Datum.WO T S))
    (𝓕 : Set (Formalism.IndefR.Datum.WO T S)) (h : Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕) :
    ∃ (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
      (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)),
      ν'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν' ∧
      ∀ f : Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) → ℂ,
        ∫ u in 𝓕', f u ∂ν' = ∫ w in 𝓕, f wᵀ ∂ν := by
  classical
  haveI : BorelSpace (Formalism.IndefR.Datum.WO T S) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank) := ⟨rfl⟩
  obtain ⟨hH, hF, -⟩ := h
  let e : Formalism.IndefR.Datum.WO T S ≃+ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    Matrix.transposeAddEquiv _ _ _
  have hc : Continuous e := Continuous.matrix_transpose continuous_id
  have hcs : Continuous e.symm := Continuous.matrix_transpose continuous_id
  let E' : Formalism.IndefR.Datum.WO T S ≃ᵐ Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank :=
    (Homeomorph.mk e.toEquiv hc hcs).toMeasurableEquiv
  have hE' : ∀ w, E' w = wᵀ := fun _ => rfl
  let eG : Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank ≃ ratL S T :=
    { toFun := fun g => ⟨(g : Matrix (Fin T.rank) (Fin S.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      invFun := fun g => ⟨(g : Matrix (Fin S.rank) (Fin T.rank) _)ᵀ, by
        obtain ⟨γ, hγ⟩ := g.2
        exact ⟨γᵀ, by rw [← hγ]; rfl⟩⟩
      left_inv := fun g => Subtype.ext (Matrix.transpose_transpose _)
      right_inv := fun g => Subtype.ext (Matrix.transpose_transpose _) }
  refine ⟨ν.map E', E' '' 𝓕, ?_, ?_, fun f => ?_⟩
  · exact AddEquiv.isAddHaarMeasure_map ν e hc hcs
  · refine hF.image_of_equiv E'.toEquiv (E'.quasiMeasurePreserving_symm ν) eG fun g x => ?_
    show (((eG g : ratL S T) : Matrix (Fin S.rank) (Fin T.rank) _) + x)ᵀ = (g : Matrix (Fin T.rank) (Fin S.rank) _) + xᵀ
    rw [Matrix.transpose_add]
    exact congrArg (· + xᵀ) (Matrix.transpose_transpose _)
  · rw [E'.restrict_map, E'.preimage_image, MeasureTheory.integral_map_equiv]
    rfl

theorem lubinTateSeries_eq_of_coeff_one_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hξ : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (κ : Type) [Fintype κ]
    (J' : Matrix (Fin (T.rank + T.rank)) (Fin (T.rank + T.rank)) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ = J')
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ J' (incM D.host.F JB)) κ)
    (hrat : ∀ x : Matrix (Fin (T.rank + T.rank)) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i)))
    (ν' : Measure (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank))
    (𝓕' : Set (Formalism.IndefR.DatumF.WOF D.host.F D.host.E S.rank T.rank)) (hν' : ν'.IsAddHaarMeasure)
    (h𝓕' : IsAddFundamentalDomain (Formalism.IndefR.DatumF.ratLF D.host.F D.host.E S.rank T.rank) 𝓕' ν')
    (l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ)
    (hinv : ∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
      ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
          (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) :
    ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν' 𝓕'
      ((diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank)
        (AF D.host.F ⊗[D.host.F] D.host.E)).submatrix finSumFinEquiv.symm id)
      (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) := by
  subst hJ
  classical
  obtain ⟨v₁, -, -, ⟨τ₁⟩⟩ := GlobalTheory.TripleDarboux.exists_good_place D ∅
  let B : Base D.host.F D.host.E :=
    { ψ := ψ, emb := fun _ => Classical.arbitrary _, mα := 0, mβ := 0, P := ∅,
      τ := fun v => absurd v.2 (Finset.notMem_empty _), v₁ := v₁, τ₁ := τ₁ }
  have hB : B.IsGood D.sp.cm.sig :=
    GlobalTheory.TripleDarboux.base_isGood B hψ fun v hv => absurd hv (Finset.notMem_empty _)
  exact GlobalTheory.T.diagonalLagrangian_invariantForm_unique D.host.F D.host.E D.sp.cm.sig B hB S.rank T.rank S.gram T.gram
    (GlobalTheory.Doubling.isHermND_gram S) (GlobalTheory.Doubling.isHermND_gram T) D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    (Formalism.L2.Pj.conj_xi0_alt D) JB ξ hξ κ co hrat ν' 𝓕' hν' h𝓕' l hl fun z Φ hΦ => by
      rw [← diagMat_eq_mul]
      exact hinv z Φ hΦ

theorem uniq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO T S)) (𝓕 : Set (Formalism.IndefR.Datum.WO T S)),
            Formalism.IndefR.Datum.IsCovolOne (ratL S T) ν 𝓕 →
          ∀ l : ((κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm κ →
            (∀ z : Matrix (Fin S.rank) (Fin T.rank) (AF D.host.F ⊗[D.host.F] D.host.E),
              ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                l ((GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co).rho ψ
                  (GlobalTheory.DiagSiegel.diagMat z) Φ) = l Φ) →
            ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, l Φ = c * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕
              (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) ψ Φ) := by
  intro D ψ hψ S T JB ξ hξ κ _ co hrat ν 𝓕 hcov l hl hinv
  obtain ⟨ν', 𝓕', hν', h𝓕', hint⟩ := transpose_transport D S T ν 𝓕 hcov
  have hJ : incM D.host.F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG T.gram)ᵀ =
      incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ) := by
    rw [← GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM (F := D.host.F) (J := T.gram) rfl,
      GlobalTheory.WeilSchrodinger.DblTarget.reindex_dbl_incM T rfl]
  obtain ⟨c, hc⟩ := lubinTateSeries_eq_of_coeff_one_eq D ψ hψ S T JB ξ hξ κ _ hJ co hrat ν' 𝓕' hν' h𝓕' l hl hinv
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [hc Φ hΦ, GlobalTheory.LagrTheta.lagrInt, hint, GlobalTheory.DiagSiegel.thetaDiagInt]
  congr 2
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilSchrodinger.transD_rho, diagMat_eq_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]

end GlobalTheory.DiagSiegelUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.CUniq

theorem map_max {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (θ : R →+* V) [IsLocalHom θ]
    {x : R} (hx : x ∈ maximalIdeal R) : θ x ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun h => hx (isUnit_of_map_unit θ x h)

theorem diff_pow {A R V : Type} [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ψ : A →+* R) (hψ : IsComplAt ψ) (θ₁ θ₂ : R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (h : θ₁.comp ψ = θ₂.comp ψ) (k : ℕ) : ∀ r : R, θ₁ r - θ₂ r ∈ maximalIdeal V ^ k := by
  have hc : ∀ a, θ₁ (ψ a) = θ₂ (ψ a) := fun a => congrArg (fun f => f a) h
  induction k with
  | zero => intro r; simp
  | succ k ih =>
    have hm : ∀ x ∈ maximalIdeal R, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 1) := by
      intro x hx
      rw [← hψ.2.2.2.1] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, -, rfl⟩ := hy
        simp [hc]
      | zero => simp
      | add y z _ _ hy hz =>
        have := add_mem hy hz
        simpa [map_add, sub_add_sub_comm] using this
      | smul a y hy' hy =>
        have hyM : y ∈ maximalIdeal R := hψ.2.2.2.1 ▸ hy'
        have e : θ₁ (a • y) - θ₂ (a • y) = θ₁ a * (θ₁ y - θ₂ y) + (θ₁ a - θ₂ a) * θ₂ y := by
          simp only [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ hy) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih a) (map_max θ₂ hyM)
    intro r
    obtain ⟨a, b, hb, hx⟩ := hψ.2.2.2.2 r
    have e := hm _ hx
    have hu : IsUnit (θ₁ (ψ b)) := hb.map θ₁
    have e2 : θ₁ (r * ψ b - ψ a) - θ₂ (r * ψ b - ψ a) = (θ₁ r - θ₂ r) * θ₁ (ψ b) := by
      simp only [map_sub, map_mul, hc]; ring
    rw [e2] at e
    obtain ⟨u, hu'⟩ := hu
    have : θ₁ r - θ₂ r = (θ₁ r - θ₂ r) * θ₁ (ψ b) * ↑u⁻¹ := by
      rw [← hu', _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ e

end GlobalTheory.TChart.CUniq

theorem GlobalTheory.TChart.cuniq : ∀ (A R V : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (ψ : A →+* R), IsComplAt ψ → ∀ θ₁ θ₂ : R →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp ψ = θ₂.comp ψ → θ₁ = θ₂ := by
  intro A R V _ _ _ _ _ _ ψ hψ θ₁ θ₂ h₁ h₂ h
  ext r
  have hk := fun k => GlobalTheory.TChart.CUniq.diff_pow ψ hψ θ₁ θ₂ h k r
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top
  have : θ₁ r - θ₂ r ∈ ⨅ k : ℕ, maximalIdeal V ^ k := Ideal.mem_iInf.mpr hk
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimAddRank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem Trait.dim_add_rank : ∀ {g n : ℕ}, 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F),
    T.D.toPre.P.g + Module.finrank ℤ T.D.toPre.X = g := by
  intro g n hn F T
  have hn0 : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn0]; exact Units.isUnit _
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ hn hζ (isUnit_natCast hn0)
  have hA : SmoothOfRelativeDimension g T.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback T.cart.1 hd
  have e : T.A.g = g :=
    H1.dim_unique _ T.A.smoothDim hA ((η[T.A.A]).left (IsLocalRing.closedPoint _))
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyFormulaDivisor
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem discrep_isAt_eq_neg_mult : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ), 0 < m → IsDivOfForm K η → ∀ (E : DivOver q) (w : Y) (g : Y.functionFieldˣ), E.IsAt w → G.IsEqn w g → discrep E η m g = -((G - m • K).mult w : ℚ) / m := by
  intro k _ _ Y _ _ q n _ η hη K G m hm hK E w g hE hg
  obtain ⟨c, hc⟩ := K.exists_isEqn w
  have h1 := (hg.sub (hc.nsmul m)).mult_eq
  rw [← hE.ord_eq, div_eq_mul_inv, E.ord_mul, E.ord_inv, E.ord_pow] at h1
  have h2 := GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm k Y q n η hη K hK E w hE
  rw [hc.mult_eq, ← hE.ord_eq] at h2
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, h1, h2]
  push_cast
  field_simp
  ring

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerHomotopyOperatorValuesGeneratorsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerHomotopyOperator_values_generators : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (N n : ℕ) (α : DR R B), hot v Q.e N (Q.e n • h.mDR α) = 0 ∧ (n < N → hot v Q.e N (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e (n + 1) • h.mDR α) := by
  first | exact @GlobalTheory.PDForm.hot_values | exact GlobalTheory.PDForm.hot_values | (intros; apply GlobalTheory.PDForm.hot_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentBasisPulledFrameCompatiblePointChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualTangentBasis_pulledFrame_compatible_pointChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R R' : Type)
    [CommRing R] [CommRing R'] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ))
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')), spMap r ≫ ξ = ξ' → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    KeyVals.IsDual c ξ y → KeyVals.IsDual c ξ' y' →
    ∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ := by
  first | exact @GlobalTheory.KeyVals.Vec.dual_vec | exact GlobalTheory.KeyVals.Vec.dual_vec | (intros; apply GlobalTheory.KeyVals.Vec.dual_vec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTransStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualTangentVectors_genericFibre_det_eq_detOmegaTrans : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsSemiAbelian G →
    SmoothOfRelativeDimension g G.hom → ∀ (c c' : VB.Chart (LieVB.omega G) g)
    (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
    (y y' : Fin g → (epsR (KeyVals.FF S) ⟶ KeyVals.bG G (KeyVals.genPt S))),
    KeyVals.IsDual c (KeyVals.genPt S) y → KeyVals.IsDual c' (KeyVals.genPt S) y' →
    ∃ M : Matrix (Fin g) (Fin g) (KeyVals.FF S), (∀ j, IsLieComb (M j) y' (y j)) ∧
      M.det = S.presheaf.germ _ (genericPoint S) h1
        ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) := by
  first | exact @GlobalTheory.KeyVals.LieRel.lieRel | exact GlobalTheory.KeyVals.LieRel.lieRel | (intros; apply GlobalTheory.KeyVals.LieRel.lieRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrComapFiniteIndexEssFiniteTypeComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_comap_finiteIndex_essFiniteType_complex : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V] (hc : ∀ a, φ (c a) ∈ V), ((φ.comp c).codRestrict V hc).EssFiniteType → IsDiscreteValuationRing (V.comap φ) ∧ (c.codRestrict (V.comap φ) hc).EssFiniteType := by
  first | exact @GlobalTheory.restrict_dvr_essFiniteType | exact GlobalTheory.restrict_dvr_essFiniteType | (intros; apply GlobalTheory.restrict_dvr_essFiniteType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivRegularFunctionsAffineOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_fderiv_regular_functions_affineOpen : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), IsAffineOpen U → ∀ z ∈ pre u.ex U, ∀ w : Fin g → ℂ, (∀ b : Γ(A.left, U), fderiv ℂ (val u.ex U b) z w = 0) → w = 0 := by
  first | exact @GlobalTheory.CechPerImm.main | exact GlobalTheory.CechPerImm.main | (intros; apply GlobalTheory.CechPerImm.main <;> assumption)
end

