import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsNonvanishingFiniteSet
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem exists_tens_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (S : Set Y), S.Finite →
      ∃ (A : HermLB q) (s : (M.tens A).B.Sec) (u : A.B.Sec), S ⊆ nonzeroLocus s ∧ S ⊆ nonzeroLocus u := by
  intro k _ Y q hq M S hS
  have := hq.isNoetherian
  obtain ⟨N, j, hj, e⟩ := hq.isProjOver
  let A₀ : HermLB q := (ProjSpace.hermitianTwistingSheaf k N).pull j e
  have hA : IsAmpleLB A₀.B := (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  obtain ⟨n, h₁, h₂⟩ := (tendsto_natCast_atTop_atTop.eventually
    ((hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS).and
      (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv Y) hS))).exists
  obtain ⟨s, hs⟩ := h₁ (CechPic.tens M.B (lbPow A₀.B n)) (isLB_tens M.isLB (isLB_lbPow A₀.isLB n)) (by
    rw [cls_tens M.isLB (isLB_lbPow A₀.isLB n), cls_lbPow A₀.isLB, natCast_zsmul])
  obtain ⟨u, hu⟩ := h₂ (lbPow A₀.B n) (isLB_lbPow A₀.isLB n) (by
    rw [cls_lbPow A₀.isLB, cls_triv, zero_add, natCast_zsmul])
  exact ⟨A₀.pow n, s, u, hs, hu⟩

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorsionPointOfComponentTuple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_pow {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (h : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by
      have := h.2.2.1 0 0 j
      rw [add_zero] at this
      exact (add_eq_left.1 this.symm)
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem exists_ptRel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (ps : Fin r → QkPt D.toPre F k), ∃ p' : QkPt D'.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k ps
  have B := GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have B' := GlobalTheory.Ex.GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hT := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  choose qs hqs using fun i => ((B.2.2.2.2 k).1 (ps i)).exists
  obtain ⟨v', hv'⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT fun j => (qs j).1.2
  obtain ⟨y', hy'⟩ := hT.2.2.2.1.2 fun i => (qs i).1.1.toAdd
  have hk : v' ^ k = N'.io y' := by
    refine GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT _ _ (fun j => N.io (chi T ν ν' y' j))
      ?_ (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT y')
    have hp := gtRelV_pow hT hv' k
    have e : ((fun j => (qs j).1.2) ^ k : Fin r → N.Gt) = fun j => N.io (chi T ν ν' y' j) := by
      funext j
      rw [Pi.pow_apply, hy']
      exact (qs j).2
    rwa [e] at hp
  let q' : N'.QT k := ⟨(Multiplicative.ofAdd y', v'), hk⟩
  obtain ⟨p', hp'⟩ := (B'.2.2.2.2 k).2.1 q'
  exact ⟨p', q', qs, hp', hqs, fun i => congrFun hy' i, hv'⟩

end GlobalTheory.Mum.TensTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareGeneric

theorem exists_gen_square :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  intro R' _ _ _ _ _ G' _ hG hA N hN a
  have := hG.comm
  let j := jK R'
  let πA := pullback.fst G'.hom j
  have hp : IsProper (pullback.snd G'.hom j) := hA.proper
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.RigCube.exists_gen_theta_generic G' hG hp hN
  let c : G' ⟶ G' := toUnit G' ≫ a
  let c' : G' ⟶ G' := toUnit G' ≫ a⁻¹
  let ℓ : G' ⟶ G3 G' := lift (𝟙 G') (lift c c')
  let h : pullback G'.hom j ⟶ pullback (G3 G').hom j :=
    pullback.map _ _ _ _ ℓ.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Over.w]) (by simp)
  have hh : h ≫ pullback.fst (G3 G').hom j = πA ≫ ℓ.left := pullback.lift_fst _ _ _
  let t₁ := LB.pullGen (Theta G' N) (fun _ => pullback.fst (G3 G').hom j) (fun _ => 1) t₀ h
  have ht₁ : t₁.IsGen := DVR.pullGen_isGen _ _ _ _ ht₀ _
  obtain ⟨t₂, ht₂⟩ := gen_chartPull (chartPullIn N (thφ G' (x3 G')) thε (h ≫ pullback.fst (G3 G').hom j)) t₁ ht₁
  have hcc : c * c' = 1 := by
    simp only [c, c']
    rw [← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one]

  have hconst : ∀ s : 𝟙_ (Over (Sp R')) ⟶ G', ∃ i, ∀ y, (πA ≫ (toUnit G' ≫ s).left) y ∈ N.U i := by
    intro s
    obtain ⟨p₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := inferInstance
    obtain ⟨i, hi⟩ := exists_chart hN ((j ≫ s.left) p₀)
    have e : πA ≫ (toUnit G' ≫ s).left = pullback.snd G'.hom j ≫ j ≫ s.left := by
      have w : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
      rw [Over.comp_left, w, ← Category.assoc, pullback.condition, Category.assoc]
    refine ⟨i, fun y => ?_⟩
    rw [e, Scheme.Hom.comp_apply, Subsingleton.elim ((pullback.snd G'.hom j) y) p₀]
    exact hi
  let s₃ : Fin 3 → (𝟙_ (Over (Sp R')) ⟶ G') := ![a, a⁻¹, η[G']]
  choose i hi using fun k => hconst (s₃ k)
  let φw : Fin 3 → (pullback G'.hom j ⟶ G'.left) := fun k => πA ≫ (toUnit G' ≫ s₃ k).left
  obtain ⟨w, hw⟩ := GlobalTheory.AbSquare.exists_gen_of_mem_chart hN φw ![1, 1, -2] i hi
  let ψ : Fin 3 → (G'.left ⟶ G'.left) := ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left]
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FormEq
      (Sum.elim (fun I => (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) φw)
      (Sum.elim (fun I => -thε I) ![1, 1, -2]) (fun k => πA ≫ ψ k) ![1, 1, -2] := by
    intro U _ g
    rw [Fintype.prod_sum_type]
    dsimp only [Sum.elim_inl, Sum.elim_inr]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    have e : ∀ I, (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I = πA ≫ (ℓ.left ≫ thφ G' (x3 G') I) :=
      fun I => by rw [hh, Category.assoc]
    have e2 : (∏ I : thK, g ((h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) ^ thε I) =
        ∏ I : thK, (fun q => g (πA ≫ q)) ((lift (𝟙 G') (lift c c')).left ≫ thφ G' (x3 G') I) ^ thε I :=
      Finset.prod_congr rfl fun I _ => by rw [e I]
    rw [e2, prod_cub (𝟙 G') c c' (fun q => g (πA ≫ q))]
    rw [show 𝟙 G' * c * c' = 𝟙 G' by rw [_root_.mul_assoc, hcc, _root_.mul_one], hcc]
    have f0 : φw 0 = πA ≫ c.left := rfl
    have f1 : φw 1 = πA ≫ c'.left := rfl
    have f2 : φw 2 = πA ≫ (1 : G' ⟶ G').left := rfl
    have p0 : ψ 0 = (𝟙 G' * c).left := rfl
    have p1 : ψ 1 = (𝟙 G' * c').left := rfl
    have p2 : ψ 2 = Over.Hom.left (𝟙 G') := (Over.id_left _).symm
    rw [Fin.prod_univ_three, Fin.prod_univ_three, f0, f1, f2, p0, p1, p2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨u, hu, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF (LB.mulGen N _ _ _ _ (LB.invGen N _ _ t₂) w)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht₂) hw)
  obtain ⟨v, hv⟩ := gen_chartPull (chartPullOut N ψ ![1, 1, -2] πA (fun k => πA ≫ ψ k) (fun _ => rfl)) u hu
  exact GlobalTheory.PicGenericInj.exists_gen_of_generic R' G' hG _ (LB.isLB_linComb hN _ _) ⟨v, hv⟩

end GlobalTheory.SquareGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantLevelSquareNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstant_levelSquare_ne_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S) (c : Fin N → K), Odd m → 3 ≤ m → (m : K) ≠ 0 → PolFib G L g x → HasTh G L ρ m x c → ∃ a, c a ≠ 0 := by
  first | exact @GlobalTheory.UMin.ThNe.th_ne_zero | exact GlobalTheory.UMin.ThNe.th_ne_zero | (intros; apply GlobalTheory.UMin.ThNe.th_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstantList_algClosed : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  first | exact @GlobalTheory.UMin.exists_thList | exact GlobalTheory.UMin.exists_thList | (intros; apply GlobalTheory.UMin.exists_thList <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_frame_cube_constant_root_of_unity : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  first | exact @GlobalTheory.Poinc.CubeConst.exists_frame_cube_const | exact GlobalTheory.Poinc.CubeConst.exists_frame_cube_const | (intros; apply GlobalTheory.Poinc.CubeConst.exists_frame_cube_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaImm

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

theorem isUnit_resG_of_le {X : Scheme.{0}} {U V : X.Opens} (r : Γ(X, U)) (h : V ≤ X.basicOpen r) :
    IsUnit (resG X (h.trans (X.basicOpen_le r)) r) := by
  have := (X.toRingedSpace.isUnit_res_basicOpen r).map (resG X h)
  exact (congrArg IsUnit (resG_resG (X.basicOpen_le r) h r)).mp this

theorem exists_immersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (S : Finset D.toPre.X) (k₁ : ℕ), ∀ k ≥ k₁, ∃ (N : ℕ) (α : Fin (N + 1) → D.toPre.X) (b : ∀ i, D.toPre.SecB k (α i)) (τ : Fin (N + 1) → SecK D.toPre.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤), (∀ i, α i ∈ S ∧ IsTermOf Y (b i) (τ i)) ∧ IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
  intro R _ _ _ hR D Y
  classical
  have : IsNoetherianRing R := hR.1.1
  obtain ⟨-, hqa, -, -, hterm⟩ := GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := GlobalTheory.Mum.ext_torus R D.toPre Y
  let bs := Module.Free.chooseBasis ℤ D.toPre.X
  choose k₀ hk₀ using fun c => GlobalTheory.Mum.exists_secB_generating R D.toPre (bs c)
  refine ⟨insert 0 (Finset.univ.image bs), max 4 (Finset.univ.sup k₀), fun k hk => ?_⟩
  obtain ⟨m, s, hs⟩ := GlobalTheory.Mum.WeightZero.exists_veryAmpleBy_secB_zero R D.toPre k (le_of_max_le_left hk)
  choose n bb hbb using fun c => hk₀ c k ((Finset.le_sup (Finset.mem_univ c)).trans (le_of_max_le_right hk))
  let J := Fin (m + 1) ⊕ Σ c, Fin (n c)
  let αJ : J → D.toPre.X := Sum.elim (fun _ => 0) (fun p => bs p.1)
  let bJ : ∀ j : J, D.toPre.SecB k (αJ j) := fun j => match j with
    | .inl a => s a
    | .inr p => bb p.1 p.2
  choose τJ hτJ using fun j : J => hterm k (αJ j) (bJ j)
  have hcard : Fintype.card J = (Fintype.card J - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.2 ⟨.inl 0⟩)).symm
  let e : Fin (Fintype.card J - 1 + 1) ≃ J := (Fintype.equivFinOfCardEq hcard).symm
  have ht₀ : ∀ a, IsTermOf Y (s a) (τJ (e (e.symm (.inl a)))) := fun a => by
    rw [e.apply_symm_apply]; exact hτJ (.inl a)
  have htc : ∀ c l, IsTermOf Y (bb c l) (τJ (e (e.symm (.inr ⟨c, l⟩)))) := fun c l => by
    rw [e.apply_symm_apply]; exact hτJ (.inr ⟨c, l⟩)
  obtain ⟨hs₁, hsc⟩ := (veryAmpleBy_iff _ s).1 hs
  have hsi := (isClosedImmersion_toProj_iff _ s hs₁).1 hsc
  have hτ : ⨆ i, nonzeroLocus (τJ (e i)) = ⊤ := top_le_iff.1 fun y _ => by
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs₁.ge (Set.mem_univ (Y.q.left y)))
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm (.inl a), ?_⟩
    rw [GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k 0 _ _ (ht₀ a)]
    exact ha
  refine ⟨_, fun i => αJ (e i), fun i => bJ (e i), fun i => τJ (e i), hτ, fun i => ⟨?_, hτJ (e i)⟩, ?_⟩
  · show αJ (e i) ∈ _
    generalize e i = j
    rcases j with a | p
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem bs (Finset.mem_univ p.1))
  refine GlobalTheory.isImmersion_of_forall_affine_surjective_appLE _ _ _ fun y => ?_
  set φ := toProj Y.H.hom (fun i => τJ (e i)) hτ with hφ
  let q := Y.q.left
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs₁.ge (Set.mem_univ (q y)))
  choose l hl using fun c => TopologicalSpace.Opens.mem_iSup.1 ((hbb c).ge (Set.mem_univ (q y)))

  let V₀ := nonzeroLocus (s a)
  have hV₀ : IsAffineOpen V₀ := (hsi a).1
  let O : D.toPre.P.A.left.Opens := V₀ ⊓ Finset.univ.inf fun c => nonzeroLocus (bb c (l c))
  have hyO : q y ∈ O := by
    refine ⟨ha, ?_⟩
    show q y ∈ ((Finset.univ.inf fun c => nonzeroLocus (bb c (l c)) : D.toPre.P.A.left.Opens) : Set _)
    rw [TopologicalSpace.Opens.coe_finset_inf]
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter, Function.comp_apply]
    exact fun c => hl c
  obtain ⟨f, hfO, hyf⟩ := hV₀.exists_basicOpen_le (V := O) ⟨q y, hyO⟩ ha
  let V := D.toPre.P.A.left.basicOpen f
  have hV : IsAffineOpen V := hV₀.basicOpen f
  have hVV₀ : V ≤ V₀ := D.toPre.P.A.left.basicOpen_le f
  have hVc : ∀ c, V ≤ nonzeroLocus (bb c (l c)) := fun c x hx => by
    have h := (hfO hx).2
    change x ∈ ((Finset.univ.inf fun c => nonzeroLocus (bb c (l c)) : D.toPre.P.A.left.Opens) : Set _) at h
    rw [TopologicalSpace.Opens.coe_finset_inf] at h
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter, Function.comp_apply] at h
    exact h c
  let i₀ := e.symm (.inl a)
  let iκ := fun c =>  e.symm (.inr ⟨c, l c⟩)
  have hloc₀ : nonzeroLocus (τJ (e i₀)) = q ⁻¹ᵁ V₀ := GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k 0 _ _ (ht₀ a)
  have hlocc : ∀ c, nonzeroLocus (τJ (e (iκ c))) = q ⁻¹ᵁ nonzeroLocus (bb c (l c)) := fun c =>
    GlobalTheory.Mum.TermLocus.nonzeroLocus_eq R D.toPre Y k _ _ _ (htc c (l c))
  have hch₀ : φ ⁻¹ᵁ chart R _ i₀ = q ⁻¹ᵁ V₀ := (toProj_preimage_chart _ _ hτ i₀).trans hloc₀

  let base := (baseRingHom (PSpace.str R _) (chart R _ i₀)).hom
  let rat : Fin (m + 1) → Γ(PSpace R _, chart R _ i₀) := fun j => ratio R _ i₀ (e.symm (.inl j))
  have hW₀ : ∀ {W' : Y.H.left.Opens}, W' ≤ q ⁻¹ᵁ V₀ → W' ≤ φ ⁻¹ᵁ chart R _ i₀ := fun h => h.trans hch₀.ge
  have hpoly : ∀ (W' : Y.H.left.Opens) (hq : W' ≤ q ⁻¹ᵁ V₀) (P : MvPolynomial (Fin (m + 1)) R),
      (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom (MvPolynomial.eval₂Hom base rat P) =
      (q.appLE V₀ W' hq).hom (MvPolynomial.eval₂Hom (baseRingHom D.toPre.P.A.hom V₀).hom
        (fun j => secRatio (s a) (s j)) P) := by
    intro W' hq P
    have e1 : (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom.comp (MvPolynomial.eval₂Hom base rat) =
        (q.appLE V₀ W' hq).hom.comp (MvPolynomial.eval₂Hom (baseRingHom D.toPre.P.A.hom V₀).hom
          (fun j => secRatio (s a) (s j))) := by
      rw [MvPolynomial.comp_eval₂Hom, MvPolynomial.comp_eval₂Hom]
      congr 1
      · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, baseRingHom_appLE, baseRingHom_appLE, toProj_str]
        exact congrArg (fun g => (baseRingHom g W').hom) (Over.w Y.q).symm
      · funext j
        show pullRatio φ W' i₀ _ _ = _
        rw [pullRatio_toProj_on]
        exact (GlobalTheory.Mum.secRatio_isTermOf_zero R D.toPre Y k (s a) (s j) _ _ (ht₀ a) (ht₀ j) W' hq _).symm
    exact RingHom.congr_fun e1 P
  let W := q ⁻¹ᵁ V
  have hWV₀ : W ≤ q ⁻¹ᵁ V₀ := q.preimage_mono hVV₀
  obtain ⟨p, hp⟩ := (hsi a).2 f
  let F₀ := MvPolynomial.eval₂Hom base rat p
  let G := F₀ * ∏ c, ratio R _ i₀ (iκ c)
  let U := (PSpace R _).basicOpen G
  have hU : IsAffineOpen U := (isAffineOpen_chart R _ i₀).basicOpen G
  have hUc : U ≤ chart R _ i₀ := (PSpace R _).basicOpen_le G
  have hF : ∀ (W' : Y.H.left.Opens) (hq : W' ≤ q ⁻¹ᵁ V₀),
      (φ.appLE (chart R _ i₀) W' (hW₀ hq)).hom F₀ = (q.appLE V₀ W' hq).hom f := fun W' hq => by
    rw [hpoly W' hq p, hp]
  have hUW : φ ⁻¹ᵁ U ≤ W := by
    intro x hx
    have hx₀ : x ∈ q ⁻¹ᵁ V₀ := hch₀.le (φ.preimage_mono hUc hx)
    have h1 : x ∈ Y.H.left.basicOpen ((φ.appLE (chart R _ i₀) (q ⁻¹ᵁ V₀) (hW₀ le_rfl)).hom G) := by
      rw [Scheme.basicOpen_appLE]; exact ⟨hx₀, hx⟩
    rw [map_mul, Scheme.basicOpen_mul, hF _ le_rfl, Scheme.basicOpen_appLE] at h1
    exact h1.1.2
  have hWU : W ≤ φ ⁻¹ᵁ U := by
    intro x hx
    have hx₀ : x ∈ q ⁻¹ᵁ V₀ := hWV₀ hx
    have h1 : x ∈ Y.H.left.basicOpen ((φ.appLE (chart R _ i₀) (q ⁻¹ᵁ V₀) (hW₀ le_rfl)).hom G) := by
      rw [map_mul, Scheme.basicOpen_mul, hF _ le_rfl, Scheme.basicOpen_appLE, map_prod]
      refine ⟨⟨hx₀, hx⟩, ?_⟩
      refine Finset.prod_induction _ (fun r => x ∈ Y.H.left.basicOpen r)
        (fun r r' h h' => by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩)
        (by rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial) fun c _ => ?_
      show x ∈ Y.H.left.basicOpen (pullRatio φ _ i₀ _ (iκ c))
      rw [basicOpen_pullRatio, toProj_preimage_chart]
      refine ⟨hx₀, ?_⟩
      show x ∈ nonzeroLocus (τJ (e (iκ c)))
      rw [hlocc c]
      exact hVc c hx
    rw [Scheme.basicOpen_appLE] at h1
    exact h1.2
  haveI := hqa
  refine ⟨U, W, hWU, hU, hWU hyf, hUW, hV.preimage q, ?_⟩

  let S := (φ.appLE U W hWU).hom.range
  have hS_chart : ∀ r : Γ(PSpace R _, chart R _ i₀), (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom r ∈ S :=
    fun r => ⟨resG _ hUc r, appLE_resG φ hUc hWU r⟩
  have hS_unit : ∀ r : Γ(PSpace R _, chart R _ i₀), U ≤ (PSpace R _).basicOpen r →
      ∃ w ∈ S, (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom r * w = 1 := by
    intro r hr
    obtain ⟨v, hv⟩ := isUnit_resG_of_le r hr
    refine ⟨(φ.appLE U W hWU).hom ↑v⁻¹, ⟨_, rfl⟩, ?_⟩
    rw [← appLE_resG φ hUc hWU r, ← map_mul]
    have : resG _ hUc r = ↑v := hv.symm
    rw [this, Units.mul_inv, map_one]
  have hUF : U ≤ (PSpace R _).basicOpen F₀ := fun x hx => by
    have := hx
    change x ∈ (PSpace R _).basicOpen G at this
    rw [Scheme.basicOpen_mul] at this
    exact this.1
  have hUr : ∀ c, U ≤ (PSpace R _).basicOpen (ratio R _ i₀ (iκ c)) := fun c x hx => by
    have := hx
    change x ∈ (PSpace R _).basicOpen G at this
    rw [Scheme.basicOpen_mul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Scheme.basicOpen_mul] at this
    exact this.2.1
  have hS_q : ∀ x : Γ(D.toPre.P.A.left, V₀), (q.appLE V₀ W hWV₀).hom x ∈ S := fun x => by
    obtain ⟨P, rfl⟩ := (hsi a).2 x
    rw [← hpoly W hWV₀ P]
    exact hS_chart _
  have hWτ₀ : W ≤ nonzeroLocus (τJ (e i₀)) := hWV₀.trans hloc₀.ge
  have hWb : ∀ c, W ≤ Y.H.left.basicOpen (secRatio (τJ (e i₀)) (τJ (e (iκ c)))) := fun c x hx => by
    rw [basicOpen_secRatio]
    refine ⟨hWτ₀ hx, ?_⟩
    rw [hlocc c]
    exact hVc c hx
  let u : _ → Γ(Y.H.left, W)ˣ := fun c => (isUnit_resG_of_le _ (hWb c)).unit
  have hu : ∀ c, (u c).val = resG _ hWτ₀ (secRatio (τJ (e i₀)) (τJ (e (iκ c)))) := fun c =>
    (isUnit_resG_of_le _ (hWb c)).unit_spec
  have hupr : ∀ c, (u c).val = (φ.appLE (chart R _ i₀) W (hW₀ hWV₀)).hom (ratio R _ i₀ (iκ c)) := fun c => by
    rw [hu c]
    exact (pullRatio_toProj_on _ _ hτ i₀ (iκ c) (hW₀ hWV₀)).symm
  have hSt : S = ⊤ := by
    refine GlobalTheory.Mum.subring_eq_top_of_weight_units R D.toPre Y i hi₁ hi₂ bs V hV u (fun c => ?_) S (fun c => ?_) (fun c => ?_)
    · rw [hu c]
      exact (GlobalTheory.Mum.TermWeight.isWt_secRatio R D.toPre Y i hi₃ hi₂ k (bs c) (s a) (bb c (l c)) _ _ (ht₀ a) (htc c (l c))).res hWτ₀
    · have := hV₀.isLocalization_basicOpen f
      obtain ⟨⟨a', _, n', rfl⟩, ha'⟩ := IsLocalization.surj (Submonoid.powers f) c
      have ha'' : c * resG _ hVV₀ (f ^ n') = resG _ hVV₀ a' := ha'
      have happ : ∀ x : Γ(D.toPre.P.A.left, V₀), (q.app V).hom (resG _ hVV₀ x) = (q.appLE V₀ W hWV₀).hom x := fun x => by
        rw [Scheme.Hom.app_eq_appLE]
        exact appLE_resG q hVV₀ le_rfl x
      obtain ⟨w, hw, hfw⟩ := hS_unit F₀ hUF
      rw [hF W hWV₀] at hfw
      have key := congrArg (q.app V).hom ha''
      rw [map_mul, happ, happ, map_pow] at key
      have : (q.app V).hom c = (q.appLE V₀ W hWV₀).hom a' * w ^ n' := by
        rw [← key, _root_.mul_assoc, ← mul_pow, hfw, one_pow, _root_.mul_one]
      rw [this]
      exact S.mul_mem (hS_q a') (S.pow_mem hw n')
    · refine ⟨(hupr c).symm ▸ hS_chart _, ?_⟩
      obtain ⟨w, hw, hrw⟩ := hS_unit _ (hUr c)
      rw [← hupr c] at hrw
      rw [Units.mul_eq_one_iff_inv_eq.1 hrw]
      exact hw
  intro x
  have hx : x ∈ S := hSt ▸ Subring.mem_top x
  exact hx

end GlobalTheory.Mum.ThetaImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionLabelClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toricTorsion_label_closed_point : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ lam : D.toPre.X →+ ZMod (S.r * S.N), ∃ b : S.Gam, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), (∀ χ, ((τ' (Multiplicative.ofAdd (ε χ)) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o' S.R S.ζ) ^ (S.r * S.N * (lam χ).val)) → ∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x' → x'.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left := by
  first | exact @GlobalTheory.Poinc.ToricLabel.exists_label | exact GlobalTheory.Poinc.ToricLabel.exists_label | (intros; apply GlobalTheory.Poinc.ToricLabel.exists_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacterStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toric_torsion_point_of_lattice_character : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (z : F), 1 ≤ k → z ^ k = 1 → ∀ c : D.toPre.X →+ ℤ, ∃ x : TFK (R := V) F ⟶ A.A, TorAt U F k z c x := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_torAt | exact GlobalTheory.Poinc.Sep.Spz.exists_torAt | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_torAt <;> assumption)
end

