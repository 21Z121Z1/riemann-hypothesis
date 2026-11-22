import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotent
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAlgebraPointLiesInCover
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_away_cover_sm : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a, Sm W (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) := by
  intro R _ X K W hW D _ _ x
  let f : Sp D ⟶ X.left := x.left
  let S : Set D := {s | ∃ i, ∀ q : PrimeSpectrum D, q ∈ PrimeSpectrum.basicOpen s → f q ∈ W i}
  have hS : Ideal.span S = ⊤ := by
    by_contra h'
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h'
    let p : PrimeSpectrum D := ⟨m, hm.isPrime⟩
    have hp : f p ∈ (⨆ i, W i) := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := f ⁻¹' (W i : Set X.left)) hi ((W i).isOpen.preimage f.continuous)
    have hsS : s ∈ S := ⟨i, fun q hq ↦ hsub hq⟩
    exact hs (hle (Ideal.subset_span hsS))
  have h1 : (1 : D) ∈ Submodule.span D S := by
    change (1 : D) ∈ Ideal.span S; rw [hS]; trivial
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun a ↦ (T.equivFin.symm a : D), ?_, ?_⟩
  · have hr : Set.range (fun a ↦ (T.equivFin.symm a : D)) = (T : Set D) := by
      ext y; constructor
      · rintro ⟨a, rfl⟩; exact (T.equivFin.symm a).2
      · intro hy; exact ⟨T.equivFin ⟨y, hy⟩, by simp⟩
    rw [hr, Ideal.eq_top_iff_one]; exact hT
  · intro a
    obtain ⟨i, hi⟩ := hTS (T.equivFin.symm a).2
    refine ⟨i, fun q _ ↦ ?_⟩
    have hq : (spMap (algebraMap D (Localization.Away ((T.equivFin.symm a : D)))) q : PrimeSpectrum D) ∈
        PrimeSpectrum.basicOpen ((T.equivFin.symm a : D)) :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away ((T.equivFin.symm a : D))) _).le ⟨q, rfl⟩
    exact hi _ hq

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedIntegerGoodCoverThetaSeriesIntegralStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_integer_goodCover_thetaSeries_integral : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∃ Na : ℕ, 0 < Na ∧ Real.log Na ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n ∧ ∀ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt (GlobalTheory.CovGmin.badC Y) → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ s : Y.d.c₂.F, Submodule.span (𝓞 Y.d.c₂.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.Ln τ ^ (T.Q.Dw j).mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt Y.d.c₂ La.La τ ^ (T.Q.Dw j).mult τ → ∀ y₁ : Y.V (wtZ a n), (y₁ : Rul Y.d.Xo₂ Y.d.c₂) = s • (y : Rul Y.d.Xo₂ Y.d.c₂) → Na • y₁ ∈ AllWt.latW Y.U (wtZ a n) := by
  first | exact @GlobalTheory.CovInt.integral_smul_thLa | exact GlobalTheory.CovInt.integral_smul_thLa | (intros; apply GlobalTheory.CovInt.integral_smul_thLa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierLocusOverDenseOpenBaseStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartier_locus_over_dense_open_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ (U : (Sp R).Opens) (c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme), (U : Set (Sp R)).Nonempty ∧ IsLocus c ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.DivStart.exists_locus_over_dense_open | exact GlobalTheory.DivStart.exists_locus_over_dense_open | (intros; apply GlobalTheory.DivStart.exists_locus_over_dense_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionLocusOfAmpleSpanStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierSectionLocus_of_ample_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  first | exact @GlobalTheory.Desc.exists_locus_of_span | exact GlobalTheory.Desc.exists_locus_of_span | (intros; apply GlobalTheory.Desc.exists_locus_of_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellOfLeadingMinors
section
set_option autoImplicit false

namespace GlobalTheory.ShFam.Cell

open Matrix

variable {R : Type} [CommRing R]

theorem exists_lowInv_mul_upperUni_of_leadingMinors :
    ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (N.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, IsLowInv L ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧ N = L * U
  | 0, N, _ => ⟨1, 1, ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      by ext i; exact Fin.elim0 i⟩
  | n + 1, N, hN => by
    set P : Matrix (Fin n) (Fin n) R := N.submatrix Fin.castSucc Fin.castSucc with hP
    have hPm : ∀ (k : ℕ) (hk : k ≤ n), IsUnit (P.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have e : P.submatrix (Fin.castLE hk) (Fin.castLE hk)
          = N.submatrix (Fin.castLE (hk.trans (Nat.le_succ n))) (Fin.castLE (hk.trans (Nat.le_succ n))) := by
        ext i j; rfl
      rw [e]; exact hN k _
    obtain ⟨L₀, U₀, ⟨hL₀z, hL₀d⟩, hU₀z, hU₀d, hPLU⟩ := exists_lowInv_mul_upperUni_of_leadingMinors n P hPm
    have hdL₀ : IsUnit L₀.det := by
      rw [Matrix.det_of_lowerTriangular L₀ (fun i j h => hL₀z i j h)]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hL₀d i)
    have hdU₀ : IsUnit U₀.det := by
      rw [Matrix.det_of_upperTriangular (fun i j h => hU₀z i j h)]
      simp [hU₀d]
    set q : Fin n → R := fun i => N (Fin.castSucc i) (Fin.last n)
    set r : Fin n → R := fun j => N (Fin.last n) (Fin.castSucc j)
    set u : Fin n → R := L₀⁻¹ *ᵥ q with hu
    set l : Fin n → R := r ᵥ* U₀⁻¹ with hl
    set d : R := N (Fin.last n) (Fin.last n) - l ⬝ᵥ u with hd
    have hq : L₀ *ᵥ u = q := by rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdL₀, Matrix.one_mulVec]
    have hr : l ᵥ* U₀ = r := by rw [hl, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdU₀, Matrix.vecMul_one]
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases d l j) (fun i' => Fin.lastCases 0 (fun j' => L₀ i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases (u i') (fun j' => U₀ i' j') j) i
    have hLz : ∀ i j, i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i' =>
        induction j using Fin.lastCases with
        | last => simp [L]
        | cast j' => simpa [L] using hL₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hLdiag : ∀ i, L i i = Fin.lastCases d (fun i' => L₀ i' i') i := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [L]
      | cast i' => simp [L]
    have hUz : ∀ i j, j < i → U i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j' => simp [U]
      | cast i' =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j' => simpa [U] using hU₀z i' j' (Fin.castSucc_lt_castSucc_iff.1 hij)
    have hUd : ∀ i, U i i = 1 := by
      intro i
      induction i using Fin.lastCases with
      | last => simp [U]
      | cast i' => simpa [U] using hU₀d i'
    have hNLU : N = L * U := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one]
          rw [hd]; simp [dotProduct]
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_zero, add_zero]
          have := congrFun hr j'
          simpa [vecMul, dotProduct, r] using this.symm
      | cast i' =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, mul_one, zero_mul, add_zero]
          have := congrFun hq i'
          simpa [mulVec, dotProduct, q] using this.symm
        | cast j' =>
          simp only [L, U, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, zero_mul, add_zero]
          have := congrFun (congrFun hPLU i') j'
          simpa [hP, Matrix.mul_apply] using this
    have hdet : IsUnit L.det := by
      have h1 : N.det = L.det * U.det := by rw [hNLU, Matrix.det_mul]
      have h2 : U.det = 1 := by
        rw [Matrix.det_of_upperTriangular (fun i j h => hUz i j h)]; simp [hUd]
      have h3 : N = N.submatrix (Fin.castLE (le_refl (n+1))) (Fin.castLE (le_refl (n+1))) := by
        ext i j; rfl
      have := hN (n+1) le_rfl
      rw [← h3, h1, h2, mul_one] at this
      exact this
    have hdu : IsUnit d := by
      rw [Matrix.det_of_lowerTriangular L (fun i j h => hLz i j h), Fin.prod_univ_castSucc] at hdet
      have := isUnit_of_mul_isUnit_right hdet
      simpa [hLdiag] using this
    refine ⟨L, U, ⟨hLz, fun i => ?_⟩, hUz, hUd, hNLU⟩
    rw [hLdiag i]
    induction i using Fin.lastCases with
    | last => simpa using hdu
    | cast i' => simpa using hL₀d i'

theorem exists_inCell_of_leadingMinors_isUnit {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (w : Equiv.Perm (Fin m))
    (h : ∀ (k : ℕ) (hk : k ≤ m), IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ a, InCell M w a := by
  obtain ⟨L, U, hL, hUz, hUd, hLU⟩ := exists_lowInv_mul_upperUni_of_leadingMinors m (M.submatrix id w) h
  refine ⟨fun p => U p.1.1 p.1.2, L, hL, ?_⟩
  have hU : upMat (fun p : Above m => U p.1.1 p.1.2) = U := by
    ext i j
    unfold upMat
    by_cases hij : i < j
    · rw [dif_pos hij]
    · rw [dif_neg hij]
      by_cases e : i = j
      · subst e; rw [if_pos rfl, hUd]
      · rw [if_neg e, hUz i j (lt_of_le_of_ne (not_lt.1 hij) (Ne.symm e))]
  rw [hU]; exact hLU

end GlobalTheory.ShFam.Cell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentreOfValuationSubringProperDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProperCentre

theorem exists_regAt_centre : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsProper s]
    (V : ValuationSubring Y.functionField) (x : X), (∀ f, RegAt x f → functionFieldMap s f ∈ V) →
    ∃ y : Y, s y ⤳ x ∧ ∀ f, RegAt y f → f ∈ V := by
  intro X Y _ _ s _ _ V x h
  let ψ : X.presheaf.stalk x →+* V :=
    ((GlobalTheory.functionFieldMap s).comp (algebraMap (X.presheaf.stalk x) X.functionField)).codRestrict
      V.toSubring (fun a => h _ ⟨a, rfl⟩)
  let r : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x
  have hc : GlobalTheory.genericFieldPoint Y ≫ s = GlobalTheory.specAlgebraMap V Y.functionField ≫ r := by
    rw [← GlobalTheory.specMap_functionFieldMap, ← GlobalTheory.specAlgebraMap_fromSpecStalk x]
    simp only [r, GlobalTheory.specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc, ?_, ?_⟩
  · rw [GlobalTheory.apply_valCentre_base]
    have := (IsLocalRing.specializes_closedPoint (R := X.presheaf.stalk x)
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk x).continuous
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact this
  · have hd : GlobalTheory.DominatesStalk V (GlobalTheory.valCentre s r (GlobalTheory.genericFieldPoint Y) hc) :=
      GlobalTheory.dominatesStalk_iff_exists_hom.mpr
        ⟨_, GlobalTheory.specAlgebraMap_valExt s r (GlobalTheory.genericFieldPoint Y) hc, rfl⟩
    rintro f ⟨a, rfl⟩
    exact hd.1 a

end GlobalTheory.ProperCentre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharacterSymmetricDefectTwiceFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_char_of_cub [ConnectedSpace S] [Module.Free ℤ X] (u : Γ((splitTorus S X).left, ⊤)ˣ)
    (h₃ : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u)
    (h₁ : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left),
      gm t.left z ⊤ u = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  have := connectedSpace_torus (S := S) (X := X)
  let pb : ∀ {W : Over S}, (W ⟶ splitTorus S X) → Γ(W.left, ⊤)ˣ := fun p => Units.map p.left.appTop.hom.toMonoidHom u
  have hpb : ∀ {W Z : Over S} (p : W ⟶ splitTorus S X) (r : Z ⟶ W) (z : Z.left),
      gm r.left z ⊤ (pb p) = gm (r ≫ p).left z ⊤ u := fun p r z => gm_pull r.left p.left z ⊤ trivial u
  have hmul : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y).left z ⊤ u = gm x.left z ⊤ u * gm y.left z ⊤ u := by
    intro Z x y z
    let d : Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)ˣ :=
      pb (fst _ _ * snd _ _) * (pb (fst _ _))⁻¹ * (pb (snd _ _))⁻¹
    have hd : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left), gm (lift x y).left z ⊤ d =
        gm (x * y).left z ⊤ u * (gm x.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u)⁻¹ := fun Z x y z => by
      simp only [d, map_mul, map_inv, hpb, MonObj.comp_mul, lift_fst, lift_snd]
    have e := eq_one_of_mul d (fun Z t t' y z => by
      have e' := congrArg Additive.ofMul (h₃ Z t t' y z)
      rw [hd, hd, hd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e') (fun Z t z => by
        rw [hd, _root_.mul_one, h₁, mul_inv_cancel, inv_one, _root_.one_mul]) Z x y z
    rw [hd, _root_.mul_assoc, ← mul_inv, mul_inv_eq_one] at e
    exact e
  have : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  let ρ : Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)ˣ := pb (fst _ _)
  have hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ 𝟙_ (Over S)) (z : Z.left),
      gm (lift t y).left z ⊤ ρ = gm t.left z ⊤ u := fun Z t y z => by rw [hpb, lift_fst]
  obtain ⟨χ, hχ, -⟩ := existsUnique_char ρ fun Z t t' y z => by rw [hρ, hρ, hρ, hmul]
  exact ⟨χ, fun Z t z => (hρ Z t (toUnit _) z).symm.trans (hχ Z t _ z)⟩

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem cub_down_alg {U : Type} [CommGroup U] {a₁ a₂ a₃ a₄ a₅ a₆ a₇ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₀ c c₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : U}
    (h : v₁ * v₂ * v₃ * v₄ = c * v₅ * v₆ * v₇) (hc : c * w₅ * w₆ * w₇ * w₀ = w₁ * w₂ * w₃ * w₄ * c₀)
    (r₁ : v₁ = w₁ * w₀⁻¹ * a₁) (r₂ : v₂ = w₂ * w₀⁻¹ * a₂) (r₃ : v₃ = w₃ * w₀⁻¹ * a₃) (r₄ : v₄ = w₄ * w₀⁻¹ * a₄)
    (r₅ : v₅ = w₅ * w₀⁻¹ * a₅) (r₆ : v₆ = w₆ * w₀⁻¹ * a₆) (r₇ : v₇ = w₇ * w₀⁻¹ * a₇) :
    a₁ * a₂ * a₃ * a₄ = c₀ * a₅ * a₆ * a₇ := by
  subst r₁ r₂ r₃ r₄ r₅ r₆ r₇
  have a := congrArg Additive.ofMul h
  have b := congrArg Additive.ofMul hc
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a b ⊢
  linear_combination (norm := abel) a + b

theorem ratio_alg {U : Type} [CommGroup U] {a₁ a₂ a₃ a₄ a₅ a₆ a₇ s₁ s₂ s₃ s₄ s₅ s₆ s₇ g₁ g₂ g₃ g₄ g₅ g₆ g₇ c : U}
    (ha : a₁ * a₂ * a₃ * a₄ = c * a₅ * a₆ * a₇) (hs : s₁ * s₂ * s₃ * s₄ = c * s₅ * s₆ * s₇)
    (r₁ : s₁ = g₁ * a₁) (r₂ : s₂ = g₂ * a₂) (r₃ : s₃ = g₃ * a₃) (r₄ : s₄ = g₄ * a₄)
    (r₅ : s₅ = g₅ * a₅) (r₆ : s₆ = g₆ * a₆) (r₇ : s₇ = g₇ * a₇) :
    g₁ * g₂ * g₃ * g₄ = g₅ * g₆ * g₇ := by
  subst r₁ r₂ r₃ r₄ r₅ r₆ r₇
  have a := congrArg Additive.ofMul ha
  have b := congrArg Additive.ofMul hs
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a b ⊢
  linear_combination (norm := abel) b - a

theorem even_alg {U : Type} [CommGroup U] {A₁ A Wi Wx W₀ E s s' g : U}
    (e₁ : Wi * W₀⁻¹ * A₁ = E * (s * (Wx * W₀⁻¹ * A))) (e₂ : s * Wx = Wi * s')
    (e₃ : g⁻¹ * A₁ = s' * (g * A)) : E = g * g := by
  have a := congrArg Additive.ofMul e₁
  have b := congrArg Additive.ofMul e₂
  have d := congrArg Additive.ofMul e₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a b d ⊢
  linear_combination (norm := abel) d - a - b

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem exists_char_odd {S : Scheme.{0}} [ConnectedSpace S] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G} [IsMonHom i] (P : CP G) (σ : CubTriv P.c i) :
    ∃ κ : X, ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J →
      val σ.s (x⁻¹).left z J = gm (𝟙 T.left) z ⊤ (chV x κ) * (val P.sym (x ≫ i).left z J * val σ.s x.left z J) := by
  obtain ⟨E, hE⟩ := exists_odd P σ.s σ.gen
  obtain ⟨κ, hκ⟩ := exists_char_of_cub E (fun T x y u z => by
      obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      have a := σ.cub T x⁻¹ y⁻¹ u⁻¹ z C hC
      have b := P.sym_cub T (x ≫ i) (y ≫ i) (u ≫ i) z C hC
      simp only [← MonObj.mul_comp, ← GrpObj.inv_comp] at b
      have o := odd_alg (σ := fun a : T ⟶ splitTorus S X => val σ.s a.left z C)
        (s := fun a => val P.sym (a ≫ i).left z C) (E := fun a => gm a.left z ⊤ E) (fun a => hE T a z C hC)
        (σ.cub T x y u z C hC) a b
      have o' := congrArg Additive.ofMul o
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_one] at o' ⊢
      linear_combination (norm := abel) o')
    (fun T z => by
      obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      have e := hE T 1 z C hC
      rw [inv_one, σ.val_one hC, MonObj.one_comp, P.val_sym_one hC, _root_.mul_one, _root_.mul_one] at e
      exact e.symm)
  exact ⟨κ, fun T x z J hJ => (hE T x z J hJ).trans (by rw [hκ])⟩

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem exists_twist_even : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k → IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] [IsCommMonObj G'₀] (β₀ : G'₀.left ⟶ G₀.left) (hβ₀ : IsGrpPullback G'₀ G₀ (spMap ρ) β₀) (P₀ : GlobalTheory.UU.CP G₀) (P'₀ : GlobalTheory.UU.CP G'₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G₀) (i₁ : splitTorus (Sp k') X ⟶ G'₀), IsMonHom i → IsMonHom i₁ → GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ i → ∀ (σ : GlobalTheory.UU.CubTriv P₀.c i) (σ₁ : GlobalTheory.UU.CubTriv P'₀.c i₁), GlobalTheory.UU.CubTriv.Even (P := P'₀) σ₁ → ∃ χ : X, GlobalTheory.UU.CubTriv.Even (P := P₀) (σ.twist χ) := by
  intro k k' _ _ hk hk' ρ G₀ _ _ G'₀ _ _ β₀ hβ₀ P₀ P'₀ w₀ hm X _ _ _ i i₁ hi hi₁ hc σ σ₁ hσ₁
  haveI := hi
  haveI := hi₁
  haveI : ConnectedSpace (Sp k) := by letI := hk.toField; infer_instance
  haveI : ConnectedSpace (Sp k') := by letI := hk'.toField; infer_instance
  obtain ⟨κ, hκ⟩ := exists_char_odd P₀ σ
  let f := spMap ρ
  let hw : β₀ ≫ G₀.hom = G'₀.hom ≫ f := hβ₀.1.w
  have hi' : SplitTorus.bcMap f X ≫ i.left = i₁.left ≫ β₀ := torusCompat_iff.1 hc
  have hcc : ∀ n : Fin 2, ![i₁.left, (1 : splitTorus (Sp k') X ⟶ G'₀).left] n ≫ β₀ =
      SplitTorus.bcMap f X ≫ ![i.left, (1 : splitTorus (Sp k) X ⟶ G₀).left] n := fun n => by
    fin_cases n
    · exact hi'.symm
    · refine (one_left_comp hm.mul _).trans (Eq.trans ?_ (congrArg (SplitTorus.bcMap f X ≫ ·) (one_left G₀ _)).symm)
      rw [← SplitTorus.bcMap_hom, Category.assoc]
  obtain ⟨a, ha, H⟩ := CubTransport.exists_pmaps ((isGen_iff w₀).1 hm.gen) P₀.L.isLB P'₀.L.isLB
    (SplitTorus.bcMap f X) hcc σ.s σ.gen

  let up : ∀ T : Over (Sp k'), (T ⟶ splitTorus (Sp k') X) →* (Over.mk (T.hom ≫ f) ⟶ splitTorus (Sp k) X) :=
    fun T => toBaseHom (hw := SplitTorus.bcMap_hom f X) (fun T x y => Over.OverMorphism.ext
      (SplitTorus.mul_left_bcMap f X T x y _ _ rfl rfl).symm) T
  have up_left : ∀ {T : Over (Sp k')} (x : T ⟶ splitTorus (Sp k') X), (up T x).left = x.left ≫ SplitTorus.bcMap f X :=
    fun _ => rfl
  have up_comp : ∀ {T : Over (Sp k')} (x : T ⟶ splitTorus (Sp k') X), (up T x ≫ i).left = (x ≫ i₁).left ≫ β₀ :=
    fun x => by rw [Over.comp_left, up_left, Category.assoc, hi', Over.comp_left, Category.assoc]
  have vrel : ∀ (T : Over (Sp k')) (z : T.left) (C₀ C), Good P'₀.L.L z C₀ → Good P₀.L.L z C →
      ∀ x : T ⟶ splitTorus (Sp k') X, val σ.s (up T x).left z C =
        gw w₀ (x ≫ i₁).left z (C ((x ≫ i₁).left ≫ β₀)) (C₀ (x ≫ i₁).left) *
          (gw w₀ (1 : T ⟶ G'₀).left z (C ((1 : T ⟶ G'₀).left ≫ β₀)) (C₀ (1 : T ⟶ G'₀).left))⁻¹ *
          val a x.left z C₀ := fun T z C₀ C hC₀ hC x =>
    (CubTransport.val_pmaps hcc H x.left hC hC₀).trans
      (congrArg₂ (· * ·) (prod_triv (i := i₁) x (fun q => gw w₀ q z (C (q ≫ β₀)) (C₀ q))) rfl)

  obtain ⟨r, hr⟩ := TorusCoord.exists_ratio P'₀.L.isLB (fun _ _ _ => rfl) σ₁.s σ₁.gen a ha
  have a_one : ∀ (T : Over (Sp k')) (z : T.left) (C₀), Good P'₀.L.L z C₀ →
      val a (1 : T ⟶ splitTorus (Sp k') X).left z C₀ = 1 := fun T z C₀ hC₀ => by
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have e := vrel T z C₀ C hC₀ hC 1
    rw [map_one, σ.val_one hC, MonObj.one_comp, mul_inv_cancel, _root_.one_mul] at e
    exact e.symm
  have a_cub : ∀ (T : Over (Sp k')) (x y u : T ⟶ splitTorus (Sp k') X) (z : T.left) (C₀), Good P'₀.L.L z C₀ →
      val a (x * y * u).left z C₀ * val a x.left z C₀ * val a y.left z C₀ * val a u.left z C₀ =
        cubV P'₀.c z C₀ (x ≫ i₁) (y ≫ i₁) (u ≫ i₁) * val a (x * y).left z C₀ * val a (x * u).left z C₀ *
          val a (y * u).left z C₀ := fun T x y u z C₀ hC₀ => by
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have h₀ := σ.cub (Over.mk (T.hom ≫ f)) (up T x) (up T y) (up T u) z C hC
    have hup : ∀ q : T ⟶ splitTorus (Sp k') X, up T q ≫ i = toBase hw (q ≫ i₁) :=
      fun q => Over.OverMorphism.ext (up_comp q)
    simp only [← map_mul, hup] at h₀
    have c := (hm.vals T z C₀ C hC₀ hC _ (fun _ => rfl)).2.2 (x ≫ i₁) (y ≫ i₁) (u ≫ i₁)
    simp only [← MonObj.mul_comp] at c
    exact cub_down_alg h₀ c (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _)
      (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _)
  obtain ⟨ψ, hψ⟩ := exists_char_of_cub r (fun T x y u z => by
      obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
      exact ratio_alg (a_cub T x y u z C₀ hC₀) (σ₁.cub T x y u z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀)
        (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀))
    (fun T z => by
      obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
      have e := hr _ (1 : T ⟶ splitTorus (Sp k') X).left z C₀ hC₀
      rw [σ₁.val_one hC₀, a_one T z C₀ hC₀, _root_.mul_one] at e
      exact e.symm)

  have key : ∀ (T : Over (Sp k')) (x : T ⟶ splitTorus (Sp k') X) (z : T.left),
      gm (𝟙 T.left) z ⊤ (chV x κ) = gm (𝟙 T.left) z ⊤ (chV x (ψ + ψ)) := fun T x z => by
    obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have hchv : chV (up T x) κ = chV x κ := Units.ext (by
      rw [chV_val, chV_val, up_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
        bcMap_charUnit])
    have e₁ := hκ (Over.mk (T.hom ≫ f)) (up T x) z C hC
    rw [← map_inv, up_comp, vrel T z C₀ C hC₀ hC, vrel T z C₀ C hC₀ hC, hchv] at e₁
    have s₁ := (hm.vals T z C₀ C hC₀ hC _ (fun _ => rfl)).2.1 (x ≫ i₁)
    rw [← GrpObj.inv_comp] at s₁
    have ev := hσ₁ T x z C₀ hC₀
    rw [hr _ _ z C₀ hC₀, hr _ _ z C₀ hC₀, hψ, hψ, chV_inv, map_inv] at ev
    exact (even_alg e₁ s₁ ev).trans (by rw [chV_add, map_mul])
  have hκψ : κ = ψ + ψ := by
    apply SplitTorusHom.charUnit_injective (S := Sp k')
    have e : chV (𝟙 (splitTorus (Sp k') X)) κ = chV (𝟙 (splitTorus (Sp k') X)) (ψ + ψ) :=
      unit_ext fun z _ => key _ _ z
    have e' := congrArg Units.val e
    rwa [chV_val, chV_val, Over.id_left, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply,
      RingHom.id_apply] at e'
  refine ⟨ψ, fun T t z J hJ => ?_⟩
  rw [σ.val_twist ψ _ hJ, σ.val_twist ψ _ hJ, hκ T t z J hJ, hκψ, chV_inv, chV_add, map_inv, map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TwistCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFiniteEtaleCoverGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_finite_etale_cover_generic_point : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  first | exact @GlobalTheory.Poinc.Chart.exists_chart | exact GlobalTheory.Poinc.Chart.exists_chart | (intros; apply GlobalTheory.Poinc.Chart.exists_chart <;> assumption)
end

