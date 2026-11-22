import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCube
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupModelRegularFunctionOrInverse
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.RegOrInvModel

theorem exists_idealSheaf_principalises_of_ne_zero : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, ∃ k, A j k ≠ 0) → ∃ J : X.IdealSheafData, genericPoint X ∉ J.support ∧ ∀ (W : Scheme.{0}) (b : W ⟶ X), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W) (j : Fin n), b w ∈ U j → ∃ (V : W.Opens) (hV : V ≤ b ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', (b.appLE (U j) V hV).hom (A j k) ∣ (b.appLE (U j) V hV).hom (A j k') := by
  intro X _ _ n U m A hU hA
  choose J hJU hJp using fun j => GlobalTheory.Principalise.kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hηV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hsupp : ∀ I : X.IdealSheafData, genericPoint X ∉ I.support ↔
      ∃ f ∈ I.ideal ⟨V₀, hV₀⟩, genericPoint X ∈ X.basicOpen f := by
    intro I
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V₀, hV₀⟩) hηV₀, Scheme.mem_zeroLocus_iff]
    push_neg
    rfl
  have hmul : ∀ I I' : X.IdealSheafData, genericPoint X ∉ I.support → genericPoint X ∉ I'.support →
      genericPoint X ∉ (I * I').support := by
    intro I I' h h'
    obtain ⟨f, hf, hηf⟩ := (hsupp I).1 h
    obtain ⟨f', hf', hηf'⟩ := (hsupp I').1 h'
    refine (hsupp _).2 ⟨f * f', ?_, ?_⟩
    · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
      exact Ideal.mul_mem_mul hf hf'
    · rw [Scheme.basicOpen_mul]
      exact ⟨hηf, hηf'⟩
  have hone : genericPoint X ∉ (1 : X.IdealSheafData).support := by
    refine (hsupp _).2 ⟨1, ?_, ?_⟩
    · show (1 : Γ(X, V₀)) ∈ (⊤ : X.IdealSheafData).ideal ⟨V₀, hV₀⟩
      rw [Scheme.IdealSheafData.ideal_top]
      exact Submodule.mem_top
    · rw [Scheme.basicOpen_one]
      exact hηV₀
  have hJj : ∀ j, genericPoint X ∉ (J j).support := by
    intro j
    obtain ⟨k, hk⟩ := hA j
    have hb : X.basicOpen (A j k) ≠ ⊥ := fun h0 => hk ((basicOpen_eq_bot_iff _).1 h0)
    obtain ⟨x, hx⟩ : ∃ x, x ∈ X.basicOpen (A j k) := by
      by_contra hc
      push_neg at hc
      exact hb (eq_bot_iff.2 fun x hx => (hc x hx).elim)
    have hηb : genericPoint X ∈ X.basicOpen (A j k) := gen_mem hx
    have hηU : genericPoint X ∈ U j := X.basicOpen_le _ hηb
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U j, hU j⟩) hηU, Scheme.mem_zeroLocus_iff, hJU j]
    exact fun h => h _ (Ideal.subset_span ⟨k, rfl⟩) hηb
  refine ⟨∏ j, J j, ?_, ?_⟩
  · exact Finset.prod_induction J (fun I => genericPoint X ∉ I.support) hmul hone fun j _ => hJj j
  · intro W b hE w j hw
    obtain ⟨V₁, f, hw₁, hf, hV₁⟩ := hE w
    obtain ⟨g, hgle, hwg⟩ := V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨w, hw₁, hw⟩ hw₁
    have hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j := hgle.trans inf_le_right
    have hDV : (W.affineBasicOpen g).1 ≤ V₁.1 := W.basicOpen_le g
    have hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1) :=
      (GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1
        (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)
    have hI1 := ((∏ i, J i).comap b).map_ideal_basicOpen V₁ g
    rw [hV₁, Ideal.map_span, Set.image_singleton] at hI1
    have hI2 := GlobalTheory.Principalise.comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp] at hI2
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)] at hI1
    have hwD : w ∈ (W.affineBasicOpen g).1 := hwg
    obtain ⟨k, s, hsP, hdiv⟩ := GlobalTheory.Principalise.exists_dvd_of_span_mul_eq
      (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 w hwD).hom (IsLocalRing.maximalIdeal _)) _ _
      (hI2.symm.trans hI1.symm) hfD
    have hsu : w ∈ W.basicOpen s := by
      rw [Scheme.mem_basicOpen _ _ _ hwD]
      by_contra hc
      exact hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)
    have hED : W.basicOpen s ≤ (W.affineBasicOpen g).1 := W.basicOpen_le s
    have hV : W.basicOpen s ≤ b ⁻¹ᵁ U j := fun x hx => hDU (hED hx)
    refine ⟨W.basicOpen s, hV, hsu, (W.affineBasicOpen g).2.basicOpen s, k, fun k' => ?_⟩
    have key : b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op = b.appLE (U j) (W.basicOpen s) hV :=
      Scheme.Hom.appLE_map _ _ _
    have hu := W.toRingedSpace.isUnit_res_basicOpen s
    have h1 := map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')
    rw [map_mul] at h1
    have h2 := hu.dvd_mul_left.1 h1
    rw [← key]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    exact h2

theorem exists_model_regAt_or_regAt_inv : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ g : X.functionField, g ≠ 0 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ y : Y, RegAt y (φ g) ∨ RegAt y (φ g)⁻¹ := by
  intro k _ X _ p D hX g hg
  have := hX.isLocallyNoetherian
  have := hX.isNoetherian
  choose V hVa hxV using fun x : X => (by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hx⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  let e := t.equivFin
  let U : Fin t.card → X.Opens := fun j => V (e.symm j).1
  have hU : ∀ j, IsAffineOpen (U j) := fun j => hVa _
  have hη : ∀ j, genericPoint X ∈ U j := fun j => gen_mem (hxV (e.symm j).1)
  have hfr : ∀ j, ∃ a b : Γ(X, U j), b ≠ 0 ∧ fnOf (U j) (hη j) a / fnOf (U j) (hη j) b = g := by
    intro j
    have : Nonempty (U j) := ⟨⟨_, hη j⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X (U j) (hU j)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, U j)) g
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, hab⟩
  choose a b hb hab using hfr
  let A : ∀ j, Fin 2 → Γ(X, U j) := fun j => ![a j, b j]
  obtain ⟨J, hJη, hJdiv⟩ := exists_idealSheaf_principalises_of_ne_zero X t.card U (fun _ => 2) A hU fun j => ⟨1, hb j⟩
  obtain ⟨Y, ρ, hY, hE, hiso⟩ := GlobalTheory.BlowArith.exists_isArithVar_effCartier_isIso k X p D hX J hJη
  have : IsIntegral Y := hY.isIntegral
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open X Y ρ J.support.compl ⟨genericPoint X, hJη⟩ (hiso _ fun _ hx => hx)
  obtain ⟨-, -, hfn, -⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p (ρ ≫ p) ρ rfl φ hφ
  refine ⟨Y, inferInstance, ρ, φ, hY, hφ, fun y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ : ∃ x ∈ t, ρ y ∈ V x := by
    simpa using ht (Set.mem_univ (ρ y))
  set j := e ⟨x, hxt⟩ with hj
  have hyj : ρ y ∈ U j := by simpa [U, j] using hyx
  obtain ⟨W, hW, hyW, -, kk, hdiv⟩ := hJdiv Y ρ hE y j hyj
  have hWη : genericPoint Y ∈ W := gen_mem hyW
  have key : ∀ c : Γ(X, U j), fnOf W hWη ((ρ.appLE (U j) W hW).hom c) = φ (fnOf (U j) (hη j) c) := by
    intro c
    rw [hfn (U j) (hη j) (hW hWη) c]
    exact fnOf_resG hW hWη ((ρ.app (U j)).hom c)
  have hbne : φ (fnOf (U j) (hη j) (b j)) ≠ 0 := by
    rw [map_ne_zero]
    exact fun h0 => hb j (fnOf_injective _ _ (h0.trans (map_zero _).symm))
  have hane : φ (fnOf (U j) (hη j) (a j)) ≠ 0 := by
    rw [map_ne_zero]
    intro h0
    apply hg
    rw [← hab j, h0, zero_div]
  have hφg : φ g = φ (fnOf (U j) (hη j) (a j)) / φ (fnOf (U j) (hη j) (b j)) := by
    rw [← hab j, map_div₀]
  fin_cases kk
  · right
    obtain ⟨c, hc⟩ := hdiv 1
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : (φ g)⁻¹ = fnOf W hWη c := by
      rw [hφg, inv_div, div_eq_iff hane]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c
  · left
    obtain ⟨c, hc⟩ := hdiv 0
    have e1 := congrArg (fnOf W hWη) hc
    rw [map_mul, key, key] at e1
    have : φ g = fnOf W hWη c := by
      rw [hφg, div_eq_iff hbne]
      exact e1.trans (mul_comm _ _)
    rw [this]
    exact regAt_fnOf hyW hWη c

end GlobalTheory.RegOrInvModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCancelGrpPullbackWithSquaresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cancel_grpPullback_with_squares : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] (B : Over SB) [GrpObj B] (C : Over SC) [GrpObj C] (g : SA ⟶ SB) (f : SB ⟶ SC) (a : A.left ⟶ C.left) (b : B.left ⟶ C.left) (a₂ : (G2 A).left ⟶ (G2 C).left) (b₂ : (G2 B).left ⟶ (G2 C).left), IsGrpPullback A C (g ≫ f) a → IsGrpPullback B C f b → IsSquare a a₂ → IsSquare b b₂ → ∃ (β : A.left ⟶ B.left) (β₂ : (G2 A).left ⟶ (G2 B).left), IsGrpPullback A B g β ∧ IsSquare β β₂ ∧ β ≫ b = a ∧ β₂ ≫ b₂ = a₂ := by
  first | exact @GlobalTheory.GrpCancel.exists_cancel_square | exact GlobalTheory.GrpCancel.exists_cancel_square | (intros; apply GlobalTheory.GrpCancel.exists_cancel_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCubeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_carriedFrame_theoremOfCube : ∀ {S : Scheme.{0}} (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (L : RigLB G') (c : CubicalStr G' L) (θ : L.L.Sec) (T : Over S) (x a b c' : T ⟶ G') (W : T.left.Opens), (∀ g ∈ cubeTen x a b c', W ≤ g.left ⁻¹ᵁ secNz θ) → ∃ τ : ∀ k : L.L.ι, Γ(T.left, W ⊓ x.left ⁻¹ᵁ L.L.U k)ˣ, FrameAlong L.L x.left W τ ∧ ∀ (f : G'.left ⟶ G'.left) (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (w : LB.Iso L.L (L.L.pull f)), w.IsGen → PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS → PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 → SecCarried L.L θ f w → ∀ hT : T.left ⟶ T.left, hT ≫ T.hom = T.hom ≫ fS → x.left ≫ f = hT ≫ x.left → a.left ≫ f = hT ≫ a.left → b.left ≫ f = hT ≫ b.left → c'.left ≫ f = hT ≫ c'.left → FrameCarriedAlong L.L x.left W τ f w hT := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_of_cubeTen | exact GlobalTheory.Mum.exists_carried_frame_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_carried_frame_of_cubeTen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)], ∃ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ ∧ ∀ a : (E →+* ℂ) → ℤ, ∃ D : CartierDiv (X₀ TF.Y Z), CechPic.pull (π₀ TF.X Z) (cls (toLB D) (isLB_toLB D)) = cls (LL₀ TF.X Z fun ix => ix.elim 0 fun x => a x.1) (LB.isLB_pull (TF.X.F.isLB_LL _) _) ∧ ∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-a τ)) := by
  first | exact @GlobalTheory.EigDiv.exists_detDiv | exact GlobalTheory.EigDiv.exists_detDiv | (intros; apply GlobalTheory.EigDiv.exists_detDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ) (J : Type) [Finite J] (f : J → X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H a c ∧ ∀ j, g * f j ∈ P.H a c := by
  first | exact @GlobalTheory.HSNef.Den.exists_clear_denominators | exact GlobalTheory.HSNef.Den.exists_clear_denominators | (intros; apply GlobalTheory.HSNef.Den.exists_clear_denominators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreChartPointMumfordMultiplierNonzStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedFibre_chart_point_mumfordMultiplier_nonzero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i')), GlobalTheory.MumMult.LeadPt U b m → ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ GlobalTheory.MumMult.multW U b 0 i i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i') := by
  first | exact @GlobalTheory.MumMult.exists_pt_chart_of_leadPt | exact GlobalTheory.MumMult.exists_pt_chart_of_leadPt | (intros; apply GlobalTheory.MumMult.exists_pt_chart_of_leadPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreIsoTorusExtensionBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closedFibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∃ (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' ∧ GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' ∧ IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' := by
  intro R _ _ _ hR D C Y W _ _ _ T
  haveI := T.loc
  let κ : ResidueField R →+* ResidueField W := ResidueField.map T.φ
  have hκ : κ.comp (residue R) = (residue W).comp T.φ := RingHom.ext fun r => ResidueField.map_residue T.φ r
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.FormalModel.exists_carries T.hD Y.rep (T.U.gt 0)
  have gA := GlobalTheory.T.isGrpPullback_thickening_of_carries_torusCoordinates T.hD T.U.toUnifPre Y hφ₀
  have hle : maximalIdeal W ^ (0 + 1) ≤ RingHom.ker (residue W) := by
    rw [zero_add, pow_one, ker_residue]
  let c : W ⧸ maximalIdeal W ^ (0 + 1) →+* ResidueField W :=
    Ideal.Quotient.lift _ (residue W) fun a ha => (RingHom.mem_ker).1 (hle ha)
  have hc : spMap c ≫ thick W (maximalIdeal W) 0 = spMap (residue W) := by
    rw [show thick W (maximalIdeal W) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have hc' : spMap c ≫ thick W (maximalIdeal W) 0 ≫ spMap T.φ = spMap κ ≫ spMap (residue R) := by
    rw [← Category.assoc, hc, ← spMap_comp, ← spMap_comp, hκ]
  let P := (Over.pullback (spMap c)).obj (thickObj W (maximalIdeal W) 0 T.G)
  have g1 : IsGrpPullback P T.G (spMap (residue W))
      (pullback.fst _ _ ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0)) :=
    ((isGrpPullback_pullback _ (spMap c)).comp (isGrpPullback_pullback T.G (thick W (maximalIdeal W) 0))).congr hc rfl
  obtain ⟨e1, he1, he1'⟩ := grpPullback_iso g1 (isGrpPullback_pullback T.G (spMap (residue W)))
  have g2 : IsGrpPullback P Y.H (spMap κ ≫ spMap (residue R)) (pullback.fst _ _ ≫ φ₀) :=
    ((isGrpPullback_pullback _ (spMap c)).comp gA).congr hc' rfl
  have g3 := (isGrpPullback_pullback ((Over.pullback (spMap (residue R))).obj Y.H) (spMap κ)).comp
    (isGrpPullback_pullback Y.H (spMap (residue R)))
  obtain ⟨e2, he2, he2'⟩ := grpPullback_iso g2 g3
  refine ⟨κ, e1.symm ≪≫ e2, hκ, ?_, ?_⟩
  · haveI := he1; haveI := he2
    show IsMonHom (e1.inv ≫ e2.hom)
    infer_instance
  · intro Z p p' y hp hy
    have i1 : e1.inv.left ≫ pullback.fst _ _ ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0) =
        pullback.fst T.G.hom (spMap (residue W)) := by
      rw [← he1', ← Category.assoc, ← Over.comp_left, e1.inv_hom_id, Over.id_left, Category.id_comp]
    let g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left := p ≫ e1.inv.left ≫ pullback.fst _ _
    have hy' : y = g ≫ φ₀ := by
      rw [hy]
      have := he2'
      simp only [Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc, g]
      rw [this]
    subst hy'
    obtain ⟨ξ', h1, h2⟩ := GlobalTheory.T.torusExtensionPoint_of_thickening_eq_transport T.hD T.U.toUnifPre Y hφ₀ Z g
    refine ⟨g, ξ', ?_, h1, h2⟩
    rw [hp]
    show (p ≫ e1.inv.left ≫ pullback.fst _ _) ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0) = _
    rw [Category.assoc, Category.assoc, i1]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclesOmega
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.exists_cocycles_omega : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c),
    ∃ (z : G.cocycles) (w : G.omega), (∀ n, z.1 n = d.coc n) ∧ ∀ n, w.1 n = d.om n := by
  intro R _ A _ hA p G t c d
  have hs : IsSymCoc d.g := isSymCoc_of_isAdd R A hA _ _ d.add
  refine ⟨⟨fun n => d.coc n, fun n => ⟨coc_mem_symCocycles R A p G t c d hs n,
    Dat.pullTwo_res_coc R A p G t c d n⟩⟩, ⟨fun n => d.om n, fun n => OmRes.cotMap_res_om R A p G t c d n⟩,
    fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonGenericFibreDiagonalEndEighthPower
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GenCmp

theorem diagEnd_unique_comm {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T') (hu : h ≫ u' = u)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A))
    (hS : IsDiagEnd F W P u ε) (hS' : IsDiagEnd F W P' u' ε') :
    ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) ∧
      ∀ E, (ε E).left ≫ α = α ≫ (ε' E).left := by
  subst hu
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun', hdiag'⟩ := hS'
  obtain ⟨κ, κ₂, hκ, hsq, hw, -⟩ := GlobalTheory.SiegelPullComp.pb_cancel hc' hc
  have hκw : κ ≫ c'.A.hom = c.A.hom ≫ h := hκ.1.w
  obtain ⟨x₀, hx₀, -⟩ := huniv' (Over.mk (P.A.hom ≫ h)) (fun a => pushPt hκw (pr a))
  let α : P.A.left ⟶ P'.A.left := x₀.left
  have hα : ∀ a, α ≫ (pr' a).left = (pr a).left ≫ κ := fun a => congrArg (fun q => q.left) (hx₀ a)
  have hαw : α ≫ P'.A.hom = P.A.hom ≫ h := Over.w x₀
  have ext' : ∀ {T₁ : Over T'} (v w : T₁ ⟶ P'.A), (∀ a, (v ≫ pr' a).left = (w ≫ pr' a).left) → v = w := by
    intro T₁ v w e
    obtain ⟨_, -, hu⟩ := huniv' T₁ (fun a => w ≫ pr' a)
    exact (hu v fun a => Over.OverMorphism.ext (e a)).trans (hu w fun _ => rfl).symm
  have key : ∀ {Z : Scheme.{0}} (z₁ : Z ⟶ P'.A.left) (z₂ : Z ⟶ T), z₁ ≫ P'.A.hom = z₂ ≫ h →
      ∃! m : Z ⟶ P.A.left, m ≫ α = z₁ ∧ m ≫ P.A.hom = z₂ := by
    intro Z z₁ z₂ e
    have ea : ∀ a, (z₁ ≫ (pr' a).left) ≫ c'.A.hom = z₂ ≫ h := fun a => by
      rw [Category.assoc, Over.w (pr' a), e]
    let ya : Fin 8 → (Over.mk z₂ ⟶ c.A) := fun a =>
      Over.homMk (hκ.1.lift (z₁ ≫ (pr' a).left) z₂ (ea a)) (hκ.1.lift_snd _ _ _)
    have hya : ∀ a, (ya a).left ≫ κ = z₁ ≫ (pr' a).left := fun a => hκ.1.lift_fst _ _ _
    obtain ⟨x, hx, hxu⟩ := huniv (Over.mk z₂) ya
    have hxw : x.left ≫ P.A.hom = z₂ := Over.w x
    refine ⟨x.left, ⟨?_, hxw⟩, fun m ⟨hm₁, hm₂⟩ => ?_⟩
    · have w₁ : (x.left ≫ α) ≫ P'.A.hom = z₂ ≫ h := by rw [Category.assoc, hαw, ← Category.assoc, hxw]
      have := ext' (T₁ := Over.mk (z₂ ≫ h)) (Over.homMk (x.left ≫ α) w₁) (Over.homMk z₁ e) fun a => by
        show (x.left ≫ α) ≫ (pr' a).left = z₁ ≫ (pr' a).left
        rw [Category.assoc, hα, ← Category.assoc, ← hya a, ← hx a]; rfl
      exact congrArg (fun q => q.left) this
    · have := hxu (Over.homMk m hm₂) fun a => Over.OverMorphism.ext (hκ.1.hom_ext (by
        show (m ≫ (pr a).left) ≫ κ = (ya a).left ≫ κ
        rw [Category.assoc, ← hα, ← Category.assoc, hm₁, hya]) (by
        show (m ≫ (pr a).left) ≫ c.A.hom = (ya a).left ≫ c.A.hom
        rw [Category.assoc, Over.w (pr a), hm₂]; exact (Over.w (ya a)).symm))
      exact congrArg (fun q => q.left) this
  have hpb : IsPullback α P.A.hom P'.A.hom h := by
    refine ⟨⟨hαw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (key s.fst s.snd s.condition).exists.choose)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.1)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.2)
      (fun s m h₁ h₂ => (key s.fst s.snd s.condition).unique ⟨h₁, h₂⟩
        (key s.fst s.snd s.condition).exists.choose_spec)⟩⟩
  have hmul : ∀ (T₀ : Over T) (x y : T₀ ⟶ P.A) (x₁ y₁ : Over.mk (T₀.hom ≫ h) ⟶ P'.A),
      x₁.left = x.left ≫ α → y₁.left = y.left ≫ α → (x₁ * y₁).left = (x * y).left ≫ α := by
    intro T₀ x y x₁ y₁ hx hy
    have wz : ((x * y).left ≫ α) ≫ P'.A.hom = (Over.mk (T₀.hom ≫ h)).hom := by
      rw [Category.assoc, hαw, ← Category.assoc, Over.w (x * y)]; rfl
    have := ext' (x₁ * y₁) (Over.homMk ((x * y).left ≫ α) wz) fun a => by
      haveI := hpr a
      haveI := hpr' a
      rw [MonObj.mul_comp]
      have e := hκ.2 T₀ (x ≫ pr a) (y ≫ pr a) (x₁ ≫ pr' a) (y₁ ≫ pr' a)
        (by show x₁.left ≫ (pr' a).left = x.left ≫ (pr a).left ≫ κ; rw [hx, Category.assoc, hα])
        (by show y₁.left ≫ (pr' a).left = y.left ≫ (pr a).left ≫ κ; rw [hy, Category.assoc, hα])
      rw [e, ← MonObj.mul_comp]
      show ((x * y).left ≫ (pr a).left) ≫ κ = ((x * y).left ≫ α) ≫ (pr' a).left
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hα a).symm).trans (Category.assoc _ _ _).symm)
    exact congrArg (fun q => q.left) this
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr ab.1) (pr ab.2)).left ≫ κ₂ = α ≫ (lift (pr' ab.1) (pr' ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (α ≫ P'.A.hom)) (T' := P.A)
      (𝟙 P.A.left) (pr ab.1) (pr ab.2) (Z := P'.A) α (pr' ab.1) (pr' ab.2)
      ((Category.id_comp _).trans (hα ab.1).symm) ((Category.id_comp _).trans (hα ab.2).symm))
  let wt : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c'.P q' wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' wt
  have l1 : (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB _ wt
  have l2 : (LB.LinComb (c'.P.pull κ₂) q wt).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c'.P.pull κ₂) (pull_isLB c'.isLB κ₂) q wt
  have l3 : (LB.LinComb c.P q wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q wt
  have refl1 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P'.L.pull α) ((LB.LinComb c'.P q' wt).pull α) := GlobalTheory.SiegelPullComp.iso_pull α hbun'
  have i3 : LBIso ((LB.LinComb c'.P q' wt).pull α) (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) :=
    LBIso.chartPull (chartPullOut c'.P q' wt α _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) (LB.LinComb (c'.P.pull κ₂) q wt) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c'.P κ₂ q (fun ab => α ≫ q' ab) wt (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c'.P.pull κ₂) q wt) (LB.LinComb c.P q wt) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q wt
  have h1 := pull_isLB P'.isLB α
  have h2 := pull_isLB l0 α
  have chain : LBIso (P'.L.pull α) (LB.LinComb c.P q wt) :=
    LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5))
  refine ⟨α, ⟨hpb, hmul⟩, LBIso.trans P.isLB l3 h1 hbun chain.symm, fun E => ?_⟩

  have w1 : ((ε E).left ≫ α) ≫ P'.A.hom = P.A.hom ≫ h := by
    rw [Category.assoc, hαw, ← Category.assoc, Over.w (ε E)]
  let v : Over.mk (P.A.hom ≫ h) ⟶ P'.A := Over.homMk ((ε E).left ≫ α) w1
  have hvl : v.left = (ε E).left ≫ α := rfl
  have hpl : ∀ x : P.A ⟶ c.A, (pushPt hκw x).left = x.left ≫ κ := fun _ => rfl
  have e : v = x₀ ≫ ε' E := ext' v (x₀ ≫ ε' E) fun a => by
    have l : v ≫ pr' a = pushPt hκw (ε E ≫ pr a) := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hvl, hpl, Over.comp_left, Category.assoc, hα]
      exact (Category.assoc _ _ _).symm
    rw [l, Category.assoc x₀, hdiag E a, hdiag' E a]
    have r1 : pushPt hκw (((List.finRange 8).map fun b => pr b ^ E a b).prod) =
        pushHom hκ P.A (((List.finRange 8).map fun b => pr b ^ E a b).prod) := rfl
    have r2 : x₀ ≫ ((List.finRange 8).map fun b => pr' b ^ E a b).prod =
        diagPrecomp (M := c'.A) x₀ (((List.finRange 8).map fun b => pr' b ^ E a b).prod) := rfl
    rw [r1, r2, map_list_prod, map_list_prod, List.map_map, List.map_map]
    congr 2
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, map_zpow]
    congr 1
    exact (hx₀ b).symm
  exact congrArg (fun q => q.left) e

end GlobalTheory.Poinc.GenCmp

namespace GlobalTheory.Poinc

theorem exists_common_fibre_diagEnd : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R R' K : Type) [CommRing R] [CommRing R'] [Field K] (f : R →+* K) (f' : R' →+* K) (P : PolAV (Sp R)) (u : Sp R ⟶ F.X) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (P' : PolAV (Sp R')) (u' : Sp R' ⟶ F.X), IsDiagEnd F W P u ε → SharpOver F W P' u' → spMap f ≫ u = spMap f' ≫ u' → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A), IsDiagEnd F W P' u' ε' ∧ ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap f) a ∧ IsGrpPullback P₀.A P'.A (spMap f') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') ∧ ∀ E, (ε₀ E).left ≫ a = a ≫ (ε E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left := by
  intro g n F W R R' K _ _ _ f f' P u ε P' u' hD hS' he
  obtain ⟨P₀, a, -, ha, hLa⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f) P
  obtain ⟨ε₀, hD₀, hc₀⟩ := isDiagEnd_pullback F W P P₀ u (spMap f) a ε hD ha hLa
  obtain ⟨ε', hD', -⟩ := exists_diagEnd_isMonHom g n F W _ P' u' hS'
  obtain ⟨a', ha', hLa', hc'⟩ :=
    GenCmp.diagEnd_unique_comm F W P₀ P' (spMap f ≫ u) u' (spMap f') he.symm ε₀ ε' hD₀ hD'
  exact ⟨ε', hD', P₀, a, a', ε₀, ha, ha', hLa, hLa', fun E => ⟨hc₀ E, hc' E⟩⟩

end GlobalTheory.Poinc
end
end

