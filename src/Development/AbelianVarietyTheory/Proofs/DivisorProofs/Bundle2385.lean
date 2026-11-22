import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagCellContainingFramedPoint
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cell_lies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (q : PrimeSpectrum S), ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P' := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ P q
  classical
  obtain ⟨b, hb⟩ := A.cov ((frX P ≫ Y.j) q)
  obtain ⟨f₀, hf₀, hV⟩ := GlobalTheory.T.exists_basicOpen_nbhd_point_mem_open S Y.X (frX P ≫ Y.j) (A.k b).V q hb
  let ι₀ : S →ₐ[c.F] Localization.Away f₀ := IsScalarTower.toAlgHom c.F S (Localization.Away f₀)
  obtain ⟨P₀, hP₀⟩ := exists_frMap ι₀ P
  have hx₀ : frX P₀ ≫ Y.j = spMap (algebraMap S (Localization.Away f₀)) ≫ frX P ≫ Y.j := by
    rw [← frX_frMap hP₀, Category.assoc]; rfl
  have h₀ : ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V := by rw [hx₀]; exact hV
  choose T hTu hT using GlobalTheory.T.frameVectors_eq_eigenFrame_mul_invertible E H Dw l Xo c Y p A b _ P₀ h₀
  have hq₀ : (Ideal.map (algebraMap S (Localization.Away f₀)) q.asIdeal).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) _ q.asIdeal q.2
      ((Ideal.disjoint_powers_iff_notMem _ q.2.isRadical).2 hf₀)
  have hdet : ∀ σ, (T σ).det ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q.asIdeal :=
    fun σ h => hq₀.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hTu σ))
  choose w hw using fun σ => GlobalTheory.T.exists_perm_leadingMinors_not_mem _ _ (T σ) _ hq₀ (hdet σ)
  obtain ⟨f, hf, φ, hφ⟩ := GlobalTheory.T.exists_basicOpen_isUnit_of_notMem_map' S f₀ q.asIdeal q.2 hf₀ (Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1))
    (fun i => (((T i.1).submatrix (w i.1) id).submatrix (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))
      (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))).det) (fun i => hw i.1 _ _)
  refine ⟨f, hf, ?_⟩
  let φ' : Localization.Away f₀ →ₐ[c.F] Localization.Away f := φ.restrictScalars c.F
  have hcomp : φ'.comp ι₀ = IsScalarTower.toAlgHom c.F S (Localization.Away f) :=
    AlgHom.ext fun s => φ.commutes s
  obtain ⟨P₁, hP₁⟩ := exists_frMap φ' P₀
  have hP₁' : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P₁ :=
    hcomp ▸ PullbackSections.frMap_trans ι₀ φ' hP₀ hP₁
  have hx₁ : frX P₁ ≫ Y.j = spMap φ'.toRingHom ≫ frX P₀ ≫ Y.j := by rw [← frX_frMap hP₁, Category.assoc]
  have h₁ : ⊤ ≤ (frX P₁ ≫ Y.j) ⁻¹ᵁ (A.k b).V := by rw [hx₁]; exact le_preimage_comp _ h₀
  have hM₁ : ⊤ ≤ (frX P₁ ≫ Y.j) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h₁
  have hminor : ∀ σ (k : ℕ) (hk : k ≤ Dw.mult σ), IsUnit ((((T σ).map φ').submatrix (w σ) id).submatrix
      (Fin.castLE hk) (Fin.castLE hk)).det := by
    intro σ k hk
    have h := hφ ⟨σ, ⟨k, Nat.lt_succ_of_le hk⟩⟩
    have e : (((T σ).map φ').submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk) =
        (φ : Localization.Away f₀ →+* Localization.Away f).mapMatrix
          (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk)) := rfl
    rw [e, ← RingHom.map_det]
    exact h
  choose L U hL0 hL1 hU hUu hLU using fun σ => GlobalTheory.T.exists_lu_of_isUnit_leading_minors (Localization.Away f) (Dw.mult σ)
    (((T σ).map φ').submatrix (w σ) id) (hminor σ)
  let ψ₀ : Γ(Y.X, (A.V b).1) →+* Localization.Away f := ev (frX P₁ ≫ Y.j) _ h₁
  let xc : CellVar Dw.mult → Localization.Away f := fun v => L v.1 v.2.1.1 v.2.1.2
  obtain ⟨hzπ, hz, huAt⟩ := GlobalTheory.T.flagCellPoint_image_and_frame E H Dw l Xo c Y p A Z π g κ hZ ht b w _ ψ₀ xc _ rfl
  refine ⟨spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w, fun P' hP' => ?_⟩
  obtain rfl := frMap_unique hP₁' hP'
  have hx : (spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w) ≫ π = frX P₁ ≫ Y.j :=
    hzπ.trans (spMap_ev _ (A.V b).2 h₁)
  refine GlobalTheory.T.carries_framedPoint_of_unitTriangular_chart E H Dw l Xo c c.F (RingHom.id c.F) Y Z π (cellFrames hZ ht)
    (GlobalTheory.T.flagCellFrames_lastStep_eigenmodules E H Dw l Xo c Y p A Z π g κ hZ ht) _ P₁ _ ((b, w) : A.B × Pm Dw.mult) hz hx U hU hUu ?_
  intro σ i
  rw [hT σ _ φ' P₁ hP₁ h₁ hM₁ i]
  have hcell : Matrix.of (cell xc σ) = L σ := by
    ext i j
    simp only [Matrix.of_apply, cell, xc]
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hL1 σ i).symm
    · exact (hL0 σ i j (lt_of_le_of_ne (not_lt.1 h1) h2)).symm
  have key : ((A.k b).u σ).map ψ₀ * (T σ).map φ' =
      ((((A.k b).u σ).map ψ₀).submatrix id (w σ) * L σ) * U σ := by
    rw [Matrix.mul_assoc, ← hLU σ, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  simp only [Frames.vecAt, huAt σ, hcell, ← map_smul, ← map_sum]
  congr 1
  funext r
  change (((A.k b).u σ).map ψ₀ * (T σ).map φ') r i = _
  rw [key, Matrix.mul_apply]
  erw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact _root_.mul_comm _ _

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionConstantPeriodRatioPolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HalfRatio

variable {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}

theorem lamVal_change (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) (hw : w.IsGen)
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) {J₁ J₂ : (Z ⟶ B.left) → M.ι} {J₁' J₂' : (Z ⟶ B'.left) → M'.ι}
    (h₁ : Good M z J₁) (h₂ : Good M z J₂) (h₁' : Good M' z J₁') (h₂' : Good M' z J₂') :
    lamVal w p z J₁ J₁' =
      (∏ I, gm (p ≫ β₂ ≫ PrimCocycle.lamφ B I) z (M.U (J₁ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)) ⊓ M.U (J₂ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)))
          (M.g (J₁ (p ≫ β₂ ≫ PrimCocycle.lamφ B I)) (J₂ (p ≫ β₂ ≫ PrimCocycle.lamφ B I))) ^ PrimCocycle.lamε I) *
      (∏ I, gm (p ≫ PrimCocycle.lamφ B' I) z (M'.U (J₁' (p ≫ PrimCocycle.lamφ B' I)) ⊓ M'.U (J₂' (p ≫ PrimCocycle.lamφ B' I)))
          (M'.g (J₁' (p ≫ PrimCocycle.lamφ B' I)) (J₂' (p ≫ PrimCocycle.lamφ B' I))) ^ PrimCocycle.lamε I)⁻¹ *
      lamVal w p z J₂ J₂' := by
  have mQ : ∀ {J : (Z ⟶ B.left) → M.ι}, Good M z J → p z ∈ LB.wchart (abelian₂ B M) (fun _ : PUnit => β₂)
      (fun _ I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) := fun hJ =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)
  have mQ' : ∀ {J : (Z ⟶ B.left) → M.ι}, Good M z J → (p ≫ β₂) z ∈ (abelian₂ B M).U
      (fun I => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) := fun hJ =>
    Set.mem_iInter.2 fun I => hJ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)
  have mD : ∀ {J' : (Z ⟶ B'.left) → M'.ι}, Good M' z J' → p z ∈ (abelian₂ B' M').U
      (fun I => J' (p ≫ (psum B' (x2 B') I.down).left)) := fun hJ =>
    hJ.mem (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) p
  have mi : p z ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
      (fun _ I => J₁ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₁' (p ≫ (psum B' (x2 B') I.down).left)) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨mQ h₁, mD h₁'⟩
  have mj : p z ∈ (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U
      (fun _ I => J₂ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₂' (p ≫ (psum B' (x2 B') I.down).left)) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨mQ h₂, mD h₂'⟩
  have e := congrArg (gm p z _) (hw (fun _ I => J₁ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₁' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ I => J₂ (p ≫ β₂ ≫ (psum B (x2 B) I.down).left), fun I => J₂' (p ≫ (psum B' (x2 B') I.down).left)))
  rw [gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), map_mul, gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩)] at e
  refine e.trans (congrArg (· * _) ?_)
  have gQ := gm_linComb (abelian₂ B M) (fun _ : PUnit => β₂) (fun _ => 1) p z _ _ (mQ h₁) (mQ h₂)
  have gQ' := gm_linComb M (fun I : ULift (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (p ≫ β₂) z _ _ (mQ' h₁) (mQ' h₂)
  have gD := gm_linComb M' (fun I : ULift (Finset (Fin 2)) => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) p z _ _ (mD h₁') (mD h₂')
  rw [Fintype.prod_unique, zpow_one] at gQ
  simp only [Category.assoc] at gQ'
  erw [map_mul, map_inv, gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), gm_res p z _ (TopologicalSpace.Opens.mem_inf.2 ⟨mi, mj⟩), gQ, gQ', gD]

end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
theorem ag1 {G : Type*} [CommGroup G] (a b c d : G) : (a⁻¹*b*c*d⁻¹) * (a*b⁻¹*c⁻¹*d) = 1 := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_one]; abel
theorem ag2 {G : Type*} [CommGroup G] (A₂ B₂ C₂ TA TDl TQl TQt : G) (h1 : TA * TDl = 1) (h2 : TQl * TQt = 1) : (TA*A₂)⁻¹ * (TQl * TDl⁻¹ * B₂) * (TQt * C₂) = A₂⁻¹ * B₂ * C₂ := by
  rw [eq_inv_of_mul_eq_one_right h1, eq_inv_of_mul_eq_one_right h2]
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, inv_inv]; abel
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio

theorem exists_unitOn (K : Type) [Field K] (z : Sp K) (r : ((Sp K).presheaf.stalk z)ˣ) :
    ∃ k : Kˣ, gm (𝟙 (Sp K)) z ⊤ (unitOn k) = r := by
  obtain ⟨U, hz, f, hf⟩ := TopCat.Presheaf.germ_exist (Sp K).presheaf r.val
  have hs : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain rfl : U = ⊤ := top_unique fun x _ => (Subsingleton.elim z x) ▸ hz
  have h0 : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom f ≠ 0 := fun h => by
    have : f = 0 := ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply f).symm.trans
      ((congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom h).trans (map_zero _))
    rw [this, map_zero] at hf
    exact r.ne_zero hf.symm
  refine ⟨Units.mk0 _ h0, Units.ext ((gm_val _ z ⊤ trivial _).trans (Eq.trans ?_ hf))⟩
  exact congrArg ((Sp K).presheaf.germ ⊤ z hz).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply f)

theorem prod_neg {S : Scheme.{0}} {B : Over S} [GrpObj B] {T : Over S} (x y : T ⟶ B) {Z : Scheme.{0}} (κ : Z ⟶ T.left)
    {U : Type} [CommGroup U] (h : (Z ⟶ B.left) → U) : ∏ k, h (κ ≫ lamPts x y k) ^ negε k =
      (h (κ ≫ (x * y).left))⁻¹ * h (κ ≫ x.left) * h (κ ≫ y.left) * (h (κ ≫ (1 : T ⟶ B).left))⁻¹ := by
  simp only [Fin.prod_univ_four]
  simp [lamPts, negε]
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
theorem prod_tau {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a b : D.X) {U : Type} [CommGroup U]
    (h : ((TK R).left ⟶ D.P.A.left) → U) :
    ∏ k : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit, h (𝟙 _ ≫ Sum.elim (Sum.elim (Sum.elim (fun _ => ptK (D.c (a + b))) fun _ => ptK (D.c a))
        fun _ => ptK (D.c b)) (fun _ => (toUnit (TK R)).left ≫ eSec D.P.A) k) ^
      (Sum.elim (Sum.elim (Sum.elim (fun _ => -1) fun _ => - -1) fun _ => - -1) (fun _ => -1) k : ℤ) =
      (h (ptK (D.c (a + b))))⁻¹ * h (ptK (D.c a)) * h (ptK (D.c b)) * (h ((toUnit (TK R)).left ≫ eSec D.P.A))⁻¹ := by
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Category.id_comp]
  simp
end GlobalTheory.HalfRatio

namespace GlobalTheory.HalfRatio
variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R'] {Q : Data R} {ρ : R →+* R'}
  {D : DegPre R'} {e : D.X ≃+ Q.X} {β : D.P.A.left ⟶ Q.B.left} {β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left}

theorem prod_cancel (hpb : IsGrpPullback D.P.A Q.B (spMap ρ) β) (hsq : IsSquare β β₂)
    (hc : ∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) {κ : (TK R').left ⟶ (TK R).left}
    (hκ : κ ≫ jK R = jK R' ≫ spMap ρ) {a b : D.X} {x y : TK R' ⟶ D.P.A} (hx : x = toUnit (TK R') ≫ D.c a)
    (hy : y = toUnit (TK R') ≫ D.c b) {U : Type} [CommGroup U] (H : ((TK R').left ⟶ Q.B.left) → U) :
    (∏ I, H ((lift x y).left ≫ β₂ ≫ PrimCocycle.lamφ Q.B I) ^ PrimCocycle.lamε I) *
      ∏ k, H (κ ≫ lamPts (toUnit (TK R) ≫ Q.c (e a)) (toUnit (TK R) ≫ Q.c (e b)) k) ^ negε k = 1 := by
  have hT : ∀ χ, (toUnit (TK R') ≫ D.c χ).left ≫ β = κ ≫ (toUnit (TK R) ≫ Q.c (e χ)).left := fun χ => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hc χ]
    show jK R' ≫ spMap ρ ≫ _ = κ ≫ jK R ≫ _
    rw [← Category.assoc, ← hκ, Category.assoc]
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((D.c_add 0 0).symm.trans (by rw [add_zero]))
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hxy : toUnit (TK R') ≫ D.c (a + b) = x * y := by
    rw [hx, hy, ← MonObj.comp_mul]; exact congrArg (toUnit (TK R') ≫ ·) (D.c_add a b)
  let T' : Over (Sp R) := Over.mk ((TK R').hom ≫ spMap ρ)
  let up : (TK R' ⟶ D.P.A) → (T' ⟶ Q.B) := fun u => Over.homMk (u.left ≫ β)
    ((Category.assoc _ _ _).trans ((congrArg (u.left ≫ ·) hpb.1.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap ρ) (Over.w u)))))
  have f₁ : ((lift x y).left ≫ β₂) ≫ (fst Q.B Q.B).left = (up x).left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift x y).left ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (lift_fst x y))))
  have f₂ : ((lift x y).left ≫ β₂) ≫ (snd Q.B Q.B).left = (up y).left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift x y).left ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (lift_snd x y))))
  have hP : ((lift x y).left ≫ β₂) ≫ (G2 Q.B).hom = T'.hom :=
    (congrArg (_ ≫ ·) (Over.w (fst Q.B Q.B)).symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Q.B.hom) f₁).trans (Over.w (up x))))
  have hl : (lift (up x) (up y)).left = (lift x y).left ≫ β₂ := by
    have : lift (up x) (up y) = (Over.homMk _ hP : T' ⟶ G2 Q.B) :=
      CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (Over.OverMorphism.ext f₁.symm))
        ((lift_snd _ _).trans (Over.OverMorphism.ext f₂.symm))
    exact congrArg (fun q : T' ⟶ G2 Q.B => q.left) this
  have ux : (up x).left = κ ≫ (toUnit (TK R) ≫ Q.c (e a)).left := hx ▸ hT a
  have uy : (up y).left = κ ≫ (toUnit (TK R) ≫ Q.c (e b)).left := hy ▸ hT b
  have uxy : (up x * up y).left = κ ≫ (toUnit (TK R) ≫ Q.c (e a) * toUnit (TK R) ≫ Q.c (e b)).left := by
    refine (hpb.2 _ x y (up x) (up y) rfl rfl).trans ?_
    rw [← hxy, hT, map_add, Q.c_add, MonObj.comp_mul]
  have u1 : (1 : T' ⟶ Q.B).left = κ ≫ (1 : TK R ⟶ Q.B).left := by
    have h : up 1 * up 1 = up 1 := Over.OverMorphism.ext ((hpb.2 _ 1 1 (up 1) (up 1) rfl rfl).trans
      (congrArg (fun q : TK R' ⟶ D.P.A => q.left ≫ β) (_root_.mul_one 1)))
    have h' := hT 0
    rw [map_zero, c0, q0, MonObj.comp_one, MonObj.comp_one] at h'
    rw [← mul_eq_left.1 h]; exact h'
  have h := PrimCocycle.prod_lam (up x) (up y) H
  have h₀ : (∏ I, H ((lift x y).left ≫ β₂ ≫ PrimCocycle.lamφ Q.B I) ^ PrimCocycle.lamε I) = _ :=
    Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => H q ^ PrimCocycle.lamε I)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ PrimCocycle.lamφ Q.B I) hl.symm))) h
  rw [h₀, prod_neg _ _ κ H, ← ux, ← uy, ← uxy, ← u1, _root_.mul_comm]
  exact ag1 _ _ _ _

theorem ratio_indep (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂))
    (hpb : IsGrpPullback D.P.A Q.B (spMap ρ) β) (hsq : IsSquare β β₂) (hw : w.IsGen)
    (hc : ∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) {κ : (TK R').left ⟶ (TK R).left}
    (hκ : κ ≫ jK R = jK R' ≫ spMap ρ) {a b : D.X} {x y : TK R' ⟶ D.P.A} (hx : x = toUnit (TK R') ≫ D.c a)
    (hy : y = toUnit (TK R') ≫ D.c b) :
    letI := D.P.isAb.comm
    ∀ z J₁ J₁' J₂ J₂', Good Q.M.L z J₁ → Good D.P.L z J₁' → Good Q.M.L z J₂ → Good D.P.L z J₂' →
      (val (D.tau a b) (𝟙 _) z J₁')⁻¹ * lamVal w (lift x y).left z J₁ J₁' * val (Q.tau (e a) (e b)) κ z J₁ =
      (val (D.tau a b) (𝟙 _) z J₂')⁻¹ * lamVal w (lift x y).left z J₂ J₂' * val (Q.tau (e a) (e b)) κ z J₂ := by
  letI := D.P.isAb.comm
  have hxy : toUnit (TK R') ≫ D.c (a + b) = x * y := by
    rw [hx, hy, ← MonObj.comp_mul]; exact congrArg (toUnit (TK R') ≫ ·) (D.c_add a b)
  intro z J₁ J₁' J₂ J₂' h₁ h₁' h₂ h₂'
  rw [GlobalTheory.UU.val_change (DVR.tau_isGen D a b) (𝟙 _) h₁' h₂', lamVal_change w hw _ z h₁ h₂ h₁' h₂',
    GlobalTheory.UU.val_change (Q.tau_gen _ _) κ h₁ h₂]
  refine ag2 _ _ _ _ _ _ _ ?_ ?_
  · refine (congrArg₂ (· * ·) ?_ (PrimCocycle.prod_lam x y
      fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q)))).trans (ag1 _ _ _ _)
    have e₁ : ptK (D.c (a + b)) = (x * y).left := congrArg (fun q : TK R' ⟶ D.P.A => q.left) hxy
    have e₂ : (toUnit (TK R')).left ≫ eSec D.P.A = (1 : TK R' ⟶ D.P.A).left := rfl
    have e₃ : ptK (D.c a) = x.left := hx ▸ rfl
    have e₄ : ptK (D.c b) = y.left := hy ▸ rfl
    have gen : ∀ (U : Type) [CommGroup U] (H : ((TK R').left ⟶ D.P.A.left) → U),
        (H (ptK (D.c (a + b))))⁻¹ * H (ptK (D.c a)) * H (ptK (D.c b)) * (H ((toUnit (TK R')).left ≫ eSec D.P.A))⁻¹ =
        (H (x * y).left)⁻¹ * H x.left * H y.left * (H (1 : TK R' ⟶ D.P.A).left)⁻¹ := fun U _ H =>
      congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (fun q => (H q)⁻¹) e₁) (congrArg H e₃))
        (congrArg H e₄)) (congrArg (fun q => (H q)⁻¹) e₂)
    exact (prod_tau D a b fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q))).trans
      (gen _ fun q => gm q z (D.P.L.U (J₁' q) ⊓ D.P.L.U (J₂' q)) (D.P.L.g (J₁' q) (J₂' q)))
  · exact prod_cancel hpb hsq hc hκ hx hy fun q => gm q z (Q.M.L.U (J₁ q) ⊓ Q.M.L.U (J₂ q)) (Q.M.L.g (J₁ q) (J₂ q))

theorem ratio_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : letI := D.P.isAb.comm; LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)), IsGrpPullback D.P.A Q.B (spMap ρ) β → IsSquare β β₂ → w.IsGen → (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) → ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b, ∃ k : (FractionRing R')ˣ, ∀ z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn k) = (letI := D.P.isAb.comm; lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J') * val (Q.tau (e a) (e b)) κ z J := by
  intro R _ _ R' _ _ Q ρ D e β β₂ w hpb hsq hw hc κ hκ a b
  letI := D.P.isAb.comm
  have indep := ratio_indep w hpb hsq hw hc hκ (a := a) (b := b) rfl rfl
  have hs : Subsingleton (TK R').left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R')))
  let z₀ : (TK R').left := (⊥ : PrimeSpectrum (FractionRing R'))
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.UU.exists_good_pt Q.M.isLB z₀
  obtain ⟨J₀', hJ₀'⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z₀
  obtain ⟨k, hk⟩ := exists_unitOn (FractionRing R') z₀ ((val (D.tau a b) (𝟙 _) z₀ J₀')⁻¹ *
    lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z₀ J₀ J₀' * val (Q.tau (e a) (e b)) κ z₀ J₀)
  refine ⟨k, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim _ _
  have hk' : gm (𝟙 (TK R').left) z₀ ⊤ (unitOn k) = _ := hk.trans (indep _ _ _ _ _ hJ₀ hJ₀' hJ hJ')
  rw [hk', _root_.mul_assoc, mul_inv_cancel_left]
end GlobalTheory.HalfRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameChangeEigenframeExponentialsHolArc
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.ShFam.BdArc

open GlobalTheory.HolHom GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections LatSec

theorem exists_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (g' : ℕ) (ρ : ℝ) (e' : ∀ u, (Fin g' → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G)), IsArc Z σ φ x ψ r → 0 < ρ → ρ ≤ r → IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g' → ℂ) => (show Sp ℂ ⟶ Z.t.G.left from (e' q.1 q.2).left)) → (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e' u (z + w) = e' u z * e' u w) ∧ Function.Surjective (e' u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (e' u z).left)) ∧ (∀ w, ∃! v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, IsDerivAt0 (fun z => (e' u z).left) w v.left) ∧ (∀ v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' u 0).left → ∃! w, IsDerivAt0 (fun z => (e' u z).left) w v.left)) → ∃ h : ℂ → (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), ∀ u ∈ Metric.ball (0 : ℂ) ρ, (h u).IsInvertible ∧ ContinuousAt (fun u => (h u).inverse) u ∧ ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z z', ex (z + z') = ex z * ex z') → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2)) → ∀ z, ex z = e' u (h u z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e g' ρ e' harc hρ hρr hol hexp
  have hA : ∀ u ∈ Metric.ball (0 : ℂ) ρ, HolAt (fun z => (e' u z).left) 0 := fun u hu =>
    holAt_of_isHolTo (hexp u hu).2.2.1 trivial
  have hh : ∀ u, ∃ h : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ), u ∈ Metric.ball (0 : ℂ) ρ → h.IsInvertible ∧
      ∀ j, IsDerivAt (fun z => (e' u z).left) 0 (h (Pi.single j 1))
        (spMap (dualMap (ψ u)) ≫ fr.v (e j).1 (e j).2) := fun u => by
    by_cases hu : u ∈ Metric.ball (0 : ℂ) ρ
    · obtain ⟨D, hD⟩ := exists_lieEquiv Z.t (hexp u hu).1 (hA u hu) (hexp u hu).2.2.2.2
      obtain ⟨f, hf⟩ := GlobalTheory.T.exists_eigFrame_baseChange' E H Dw l Xo c O β Z A ℂ φ _ fr (ψ u)
      obtain ⟨b, hb⟩ := exists_basis f
      refine ⟨((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv, fun _ => ⟨⟨_, rfl⟩, fun j => ?_⟩⟩
      have h1 := hD (D.symm (f.vec (e j).1 (e j).2))
      rw [D.apply_symm_apply] at h1
      have h2 : ((b.reindex e.symm).equivFun.symm.trans D.symm).toContinuousLinearEquiv (Pi.single j 1) =
          D.symm (f.vec (e j).1 (e j).2) := by simp [hb, Pi.single_apply]
      rw [← hf, ContinuousLinearEquiv.coe_coe, h2]
      exact h1
    · exact ⟨0, fun h => absurd h hu⟩
  choose h hh using hh
  refine ⟨h, fun u hu => ⟨(hh u hu).1, ?_, fun ex hadd hex hd z => ?_⟩⟩
  · refine ((hh u hu).1.contDiffAt_map_inverse (n := 1)).continuousAt.comp (continuousAt_clm_apply.2 fun z => ?_)
    have : ∀ u, h u z = ∑ j, z j • h u (Pi.single j 1) := fun u => by
      simp only [← map_smul, ← map_sum]
      exact congrArg _ (pi_eq_sum_univ' z)
    simp only [this]
    refine tendsto_finset_sum _ fun j _ => ContinuousAt.const_smul ?_ (z j)
    exact continuousAt_dir hol hu (hexp u hu).2.2.2.2 (fun b hb => (hh b hb).2 j) (continuousAt_snd (fun a =>
      ((harc.1.2 a).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρr hu))).continuousAt) _)
  · obtain ⟨hu1, -, hu2, -, hu3⟩ := hexp u hu
    obtain ⟨k, hk, -⟩ := existsUnique_linear hadd hu1 hex hu2 hu3
    have hkh : k = (h u).toLinearMap := (Pi.basisFun ℂ (Fin g)).ext fun i => by
      have h1 := (isDerivAt0_iff _ _ _).1 (hd i)
      simp only [hk] at h1
      have h2 := (isDerivAt_comp_iff (hA u hu) (LinearMap.toContinuousLinearMap k) _ _).1 h1
      rw [Pi.basisFun_apply]
      exact (hu3 (Over.homMk _ h2.over) h2.1).unique ((isDerivAt0_iff _ _ _).2 h2)
        ((isDerivAt0_iff _ _ _).2 ((hh u hu).2 i))
    rw [hk, hkh, ContinuousLinearMap.coe_coe]

end GlobalTheory.ShFam.BdArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.PicGenericInj

theorem exists_gen_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ N : LB G.left, N.IsLB → (∃ t : LB.Gen (N.pull (pullback.fst G.hom (jK R))), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro R _ _ _ _ _ G _ hG N hN ht
  have := hG.smooth
  have := hG.geomConnected
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  exact GenericExtend.exists_isGen_of_densePart _ _ (jK R) ((isNormalScheme_iff_pred _).1 inferInstance) h₁ h₂
    h₃ inferInstance G (eSec G) N (Over.w η[G]) ‹_› (geometricallyIntegral_of_smooth G.hom) hN
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hN _)) ht

end GlobalTheory.PicGenericInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMumfordBundleInvPullbackPrimitive
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

variable {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G]

theorem lam_inv_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) :
    lam (cls L hL) x⁻¹ z = - lam (cls L hL) x z := by
  have h := lam_mul_left hL hΘ x⁻¹ x z
  rw [inv_mul_cancel, lam_one_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem lam_inv_inv {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y : T ⟶ G) :
    lam (cls L hL) x⁻¹ y⁻¹ = lam (cls L hL) x y := by
  rw [lam_inv_left hL hΘ, lam_comm, lam_inv_left hL hΘ, lam_comm, neg_neg]

theorem lam_pull_inv (c : Pic G.left) (x y : T ⟶ G) :
    lam (pull (ι[G]).left c) x y = lam c x⁻¹ y⁻¹ := by
  simp only [lam, ← pull_comp, ← Over.comp_left, ← Hom.inv_def, mul_inv, inv_one]

end GlobalTheory.PolDeg.NegPrim

namespace GlobalTheory.PolDeg.NegPrim
open GlobalTheory.CechPic

theorem lam_negPull_sub_isTrivial : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  intro A _ _ _ B _ _ M cub _
  have hΘ : ∃ t : LB.Gen (Theta B M.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  have hN : (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).IsLB := LB.isLB_linComb M.isLB _ _
  have hΛ : (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])).IsLB := LB.isLB_linComb hN _ _
  refine (cls_eq_zero_iff hΛ).1 ?_
  have hc : cls _ hN = pull (ι[B]).left (cls M.L M.isLB) - cls M.L M.isLB := by
    rw [cls_linComb M.isLB, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id, sub_eq_add_neg]
  refine (cls_cube_two hN (fst B B) (snd B B) hΛ).trans ?_
  have e : ∀ (c c' : Pic B.left) (x y : B ⊗ B ⟶ B), lam (c - c') x y = lam c x y - lam c' x y := fun c c' x y => by
    simp only [lam, map_sub]; abel
  rw [hc, e, lam_pull_inv, lam_inv_inv M.isLB hΘ, sub_self]

end GlobalTheory.PolDeg.NegPrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsAdaptedToQuotientGenerators
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pinch_gens_adapted : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  intro R R₀ R' C' D E ν _ _ _ _ _ _ _ _ _ a m π ψ ζ hm hπ hζ po
  choose ξ₀ hξ₀ using fun s => hπ (ψ (ζ s))
  have hcomm : ψ.comp ((algebraMap R₀ D).comp m) = (π.comp (algebraMap R' C')).comp a := by
    have := po.w
    exact congrArg CommRingCat.Hom.hom this
  have hsurj : Function.Surjective (π.comp (MvPolynomial.aeval ξ₀ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨r, rfl⟩)
    · obtain ⟨f, rfl⟩ := hζ d
      obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective m hm f
      refine ⟨MvPolynomial.map a g, ?_⟩
      simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      induction g using MvPolynomial.induction_on with
      | C c =>
        have := congrArg (fun h => h c) hcomm
        simpa using this.symm
      | add p q hp hq => simp [hp, hq]
      | mul_X p s hp => simp [hp, hξ₀]
    · exact ⟨MvPolynomial.C r, by simp⟩
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' C').FG)
  choose p hp using fun t : S => hsurj (π t)
  refine ⟨S, inferInstance, Sum.elim (fun t => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀, ?_, ?_⟩
  · rintro (t | s)
    · have := hp t
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      simp [map_sub, this]
    · simp [hξ₀]
  · intro x
    have hx : x ∈ Algebra.adjoin R' (S : Set C') := by rw [hS]; trivial
    have hle : Algebra.adjoin R' (S : Set C') ≤
        (MvPolynomial.aeval (Sum.elim (fun t : S => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀) :
          MvPolynomial (S ⊕ ν) R' →ₐ[R'] C').range := by
      rw [Algebra.adjoin_le_iff]
      intro t ht
      refine ⟨MvPolynomial.X (Sum.inl ⟨t, ht⟩) + MvPolynomial.rename Sum.inr (p ⟨t, ht⟩), ?_⟩
      simp [MvPolynomial.aeval_rename, Function.comp_def]
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricSymplecticLevelLiftSiegelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_symplectic_level_lift_siegel : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := by
  first | exact @GlobalTheory.SiegGeomLift.exists_geom_level | exact GlobalTheory.SiegGeomLift.exists_geom_level | (intros; apply GlobalTheory.SiegGeomLift.exists_geom_level <;> assumption)
end

