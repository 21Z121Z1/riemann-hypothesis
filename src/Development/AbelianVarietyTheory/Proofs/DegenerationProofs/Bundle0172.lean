import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0169
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPoint
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDiscreteValuationRingOfMemClosureCBis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPreUOfFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0171

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegraStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral : Laws → Laws2 → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing R) C], CExt R ⊥ C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n D.P.g := by
  first | exact @GlobalTheory.ValuesTorsion.tors_of_integral | exact GlobalTheory.ValuesTorsion.tors_of_integral | (intros; apply GlobalTheory.ValuesTorsion.tors_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_basis_fourier_term_sizes_torusPoint : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ s : J → Fam u.D.toPre (PadicAlgCl p) k, (∀ i, FamOf u.D.toPre _ (f i) (s i)) → ∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν : u.D.toPre.X → ℝ) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), u.GtN g ν → w.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ α, (∀ i, GlobalTheory.UT.coef (s i) g w α ≠ 0 → ∃ m, α = cls i + k • m) ∧ (∀ i, ‖GlobalTheory.UT.coef (s i) g w α‖ ≤ κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α))) ∧ ∃ i, ‖GlobalTheory.UT.coef (s i) g w α‖ = κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α)) := by
  first | exact @GlobalTheory.TermSize.term_sizes | exact GlobalTheory.TermSize.term_sizes | (intros; apply GlobalTheory.TermSize.term_sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescendedTorsionIsometryThetaCoordinatesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_torsion_isometry_theta_coordinates : Laws → AllD fun {E} _ _ _ {H} D => ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (o : Full D K) (o' : Full D C), FullExt f o o' → ∀ (I' : FullI o') (ζ : ℕ → Kˣ), (∀ n, 0 < n → (I'.ζ n : C) = f (ζ n)) → ∃ I : FullI o, (∀ n, 0 < n → I.ζ n = ζ n) ∧ ∀ m, Odd m → (∀ (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Theta m v' → (withI o I).Theta m v) ∧ ∀ j, 0 < j → ∀ z (v : D.La → K) (v' : D.La → C) (s : Cˣ), (∀ x, f (v x) = s * v' x) → (withI o' I').Coord m (I'.ev j z) v' → (withI o I).Coord m (I.ev j z) v := by
  first | exact @GlobalTheory.DescendIso.exists_descend | exact GlobalTheory.DescendIso.exists_descend | (intros; apply GlobalTheory.DescendIso.exists_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullObject_of_thetaPoint_in_algClosed_subfield : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K κ : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field κ] [IsAlgClosed κ] (i : K →+* κ) (m : ℕ) (ρ z : K) (v : D.La → K) (o' : Full D κ), Odd m → Compat H (m ^ 2) z ρ → o'.ρ = i ρ → (o'.I.ζ (m ^ 2) : κ) = i z → o'.Theta m (fun x => i (v x)) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  first | exact @GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield | exact GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield | (intros; apply GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_neronNeutralComponent_finite_level : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [Algebra K K'], SH R K' → (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ P : Out.PolAV (Sp K), ∃ (s : Finset R) (c : ℕ), 1 ≤ c ∧ ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (L : Type) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (_ : Algebra K L), SmConn G ∧ (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsModel (L := L) P.A G ∧ SmoothOfRelativeDimension P.g G.hom ∧ (∃ N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N) ∧ ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left := by
  first | exact @GlobalTheory.NeutralLevel.exists_level_model | exact GlobalTheory.NeutralLevel.exists_level_model | (intros; apply GlobalTheory.NeutralLevel.exists_level_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianSplitCubicalExtensionClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.Assembly

theorem exists_sec_of_lbIso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (H : LBIso L' (L.pull F)) (s : LB.Sec L) :
    ∃ s' : LB.Sec L', ∀ y : X', F y ∈ Out.nonzeroLocus s → y ∈ Out.nonzeroLocus s' := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff W).1 hW) hL hL' s
  refine ⟨s', fun y hy => ?_⟩
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hy
  obtain ⟨k, hk⟩ := exists_chart hL' y
  have e := hs' _ (𝟙 _) y j k hj hk
  rw [Category.id_comp, gs_stalkMap F y _ hj] at e
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp (u.map (F.stalkMap y).hom))

theorem mulN_eq_pow' {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comm_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (mulN G n).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ mulN G n = pushHom h G' (𝟙 G') ^ n := by
    rw [mulN_eq_pow', MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_pow'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_sec_fibres {H S : Scheme.{0}} (p : H ⟶ S) {L M : LB H} (hL : L.IsLB) (hM : M.IsLB) (z : S)
    (h₁ : ∃ N : S.Opens, z ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι))
    (h₂ : ∃ (N : S.Opens) (σ : LB.Sec (M.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z') :
    ∃ (N : S.Opens) (σ : LB.Sec (L.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z' := by
  obtain ⟨N₁, hz₁, H₁⟩ := h₁
  obtain ⟨N₂, σ, hz₂, H₂⟩ := h₂
  have l₁ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₁ := fun _ hx => hx.1
  have l₂ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₂ := fun _ hx => hx.2
  have I : LBIso (L.pull (p ⁻¹ᵁ (N₁ ⊓ N₂)).ι) ((M.pull (p ⁻¹ᵁ N₂).ι).pull (H.homOfLE l₂)) :=
    H₁.chartPull (h := H.homOfLE l₁)
      (chartPullSame L _ _ _ _ fun _ => (H.homOfLE_ι l₁).symm)
      (chartPullLinComb M _ _ _ _ _ fun _ => (H.homOfLE_ι l₂).trans (H.homOfLE_ι l₁).symm)
  obtain ⟨σ', hσ'⟩ := exists_sec_of_lbIso_pull (pull_isLB hM _) (pull_isLB hL _) I σ
  refine ⟨N₁ ⊓ N₂, σ', ⟨hz₁, hz₂⟩, fun z' hz' => ?_⟩
  obtain ⟨x, hx, e⟩ := H₂ z' hz'.2
  have hm : x.1 ∈ p ⁻¹ᵁ (N₁ ⊓ N₂) := by
    change p x.1 ∈ N₁ ⊓ N₂
    exact (show p x.1 = z' from e) ▸ hz'
  refine ⟨⟨x.1, hm⟩, hσ' _ ?_, e⟩
  have : H.homOfLE l₂ ⟨x.1, hm⟩ = x := Subtype.ext (Scheme.homOfLE_apply l₂ _)
  rwa [this]

theorem exists_law_splitAll_cubical : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  intro hL C T n hT hI hC hS hF
  obtain ⟨L⟩ := Core.nonempty_law_of_hasTests_of_indep C hT hI
  refine ⟨L, ?_⟩
  letI := L.grp
  letI := L.comm
  obtain ⟨h₁, h₂⟩ := GlobalTheory.ZJ.FibreSplit.splitAll_and_isSemiAbelian C L hT hC
  obtain ⟨M, hM, hMa, hσ⟩ := GlobalTheory.T.exists_lineBundle_extension_thetaSection_semiAbelian hL.extend hL.mulN
    GlobalTheory.abelian_torsion_finite_and_mulN_surjective.2 C L T n h₂ hT hS hF
  obtain ⟨-, -, -, -, -, -, -, hcart, -, hN, -⟩ := GlobalTheory.ZJ.core_basic C
  have : Nonempty C.U.toScheme := C.ne.to_subtype
  have := h₂.smooth
  have := h₂.geomConnected
  have hgi : GeometricallyIntegral C.GG.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ C.GG
  obtain ⟨PP, cub, m, hF, he, hp, hsym⟩ :=
    GlobalTheory.NormalCubeExt.exists_cubical_extension C.Z C.normal C.U.toScheme C.U.ι C.GG C.A C.a L.pull T.L T.cub M hM hMa
  have iso := GlobalTheory.T.lineBundleIso_extend_of_normal_base C.Z C.normal C.U.toScheme C.G.toScheme C.A.left C.U.ι C.GG.hom C.e C.a C.A.hom
    h₂.smooth hgi C.e_sec hcart
  have hw : LBIso T.L.L (PP.L.pull C.a) := by
    obtain ⟨w, hw, -⟩ := hp
    exact hF ▸ ⟨w, hw⟩
  refine ⟨h₁, h₂, PP, cub, m, hF, he, hp, hsym, fun z => ?_, fun z => ?_⟩
  · refine exists_sec_fibres C.GG.hom PP.isLB hM z ((iso PP.L M PP.isLB hM ?_).2 z) (hσ z)
    exact (LBIso.trans (pull_isLB hM _) T.L.isLB (pull_isLB PP.isLB _) hMa hw).symm
  · refine (iso T.O₁ (PP.L.pull (mulN C.GG T.m).left) T.isLB (pull_isLB PP.isLB _) ?_).2 z
    have i₁ : LBIso (T.L.L.pull (mulN C.A T.m).left) ((PP.L.pull (mulN C.GG T.m).left).pull C.a) :=
      hw.chartPull (h := (mulN C.A T.m).left) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb PP.L _ _ _ _ _ fun _ => (mulN_comm_of_isGrpPullback L.pull T.m).symm)
    exact LBIso.trans (pull_isLB T.isLB _) (pull_isLB T.L.isLB _) (pull_isLB (pull_isLB PP.isLB _) _)
      (LBIso.symm ⟨T.w, T.w_gen⟩) i₁

end GlobalTheory.ZJ.Assembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_point_primitive_component_valuation_zero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (s : Fam D.toPre F k) (α : D.toPre.X), VGe D F v k α (s.s α) 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (i : ℕ) (g o : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul (n ^ i) g o ∧ ∀ w : Frm D.toPre F k g.b, w.IsGen → GenV hϖ hv w 0 → v (coef s g w α) = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero | exact GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero | (intros; apply GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTraitSpecialisationOfMemClosureThetaPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ThetaClosure
open GlobalTheory.ThetaCharts GlobalTheory.LevCover

theorem eval₂_smul {R K J : Type} [CommRing R] [CommRing K] (f : R →+* K) {G : MvPolynomial J R} {d : ℕ}
    (hG : G.IsHomogeneous d) (c : K) (v : J → K) :
    MvPolynomial.eval₂ f (c • v) G = c ^ d * MvPolynomial.eval₂ f v G := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h : ∑ i ∈ s.support, s i = d := by
    have := hG (MvPolynomial.mem_support_iff.1 hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

theorem exists_residue {W C : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [NormedField C] [IsUltrametricDist C]
    [Algebra (FractionRing W) C] (h : CExt W (IsLocalRing.maximalIdeal W) C) :
    ∃ (S : ValuationSubring C) (κ : Type) (_ : Field κ) (_ : IsAlgClosed κ) (res : S →+* κ) (j : W →+* S),
      (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) ∧
      ∀ w, (j w : C) = algebraMap (FractionRing W) C (algebraMap W _ w) := by
  let S := (NormedField.valuation (K := C)).valuationSubring
  have hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  refine ⟨S, AlgebraicClosure (IsLocalRing.ResidueField S), inferInstance, inferInstance,
    (algebraMap _ _).comp (IsLocalRing.residue S),
    ((algebraMap (FractionRing W) C).comp (algebraMap W _)).codRestrict S.toSubring fun w => (hS _).2 (h.1 w), hS,
    fun x hx => ?_, fun _ => rfl⟩
  rw [RingHom.comp_apply, (IsLocalRing.residue_eq_zero_iff x).2, map_zero]
  rintro ⟨u, rfl⟩
  have e : ((u : S) : C) * ((u⁻¹ : Sˣ) : S) = 1 := congrArg (fun z : S => (z : C)) u.mul_inv
  have e' := congrArg norm e
  rw [norm_mul, norm_one] at e'
  have := (hS _).1 ((u⁻¹ : Sˣ) : S).2
  nlinarith [norm_nonneg ((u : S) : C), norm_nonneg (((u⁻¹ : Sˣ) : S) : C)]

theorem exists_lift_of_finite {F W : Type} [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [CommRing W] [IsDomain W]
    [IsIntegrallyClosed W] [Algebra ℚ W] (g : F →+* FractionRing W) :
    ∃ b : F →+* W, (algebraMap W (FractionRing W)).comp b = g := by
  have hinj := IsFractionRing.injective W (FractionRing W)
  have hr : ∀ x, g x ∈ (algebraMap W (FractionRing W)).range := fun x => by
    have h1 : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
    have h2 : IsIntegral W (g x) := h1.map_of_comp_eq (algebraMap ℚ W) g (Subsingleton.elim _ _)
    exact IsIntegrallyClosed.algebraMap_eq_of_integral h2
  let e := RingEquiv.ofBijective (algebraMap W (FractionRing W)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  exact ⟨e.symm.toRingHom.comp (g.codRestrict _ hr), RingHom.ext fun x =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict _ hr x))⟩

theorem theta_iff (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {K : Type}
    [Field K] (o : Full D K) {m : ℕ} (hm : Odd m) {v v' : D.La → K} (hv : o.Theta m v) :
    o.Theta m v' ↔ ∃ c : Kˣ, v' = (c : K) • v := by
  haveI := o.closed
  haveI := o.charZero
  obtain ⟨-, h2, h3, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL K (Sp K) o.P (𝟙 _) m hm (Nat.cast_ne_zero.2 hm.pos.ne') D.La
    (o.I.ev (m ^ 2)) (fun a => (o.I.onto _ (pow_pos hm.pos 2) _).2 ⟨a, rfl⟩)
  exact (h3 v').trans (h2 1 v v' ((h3 v).1 hv))

theorem finiteType_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    QuasiCompact f ∧ LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem exists_trait : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (m : ℕ) (ρ z : K) (v : D.La → K), Odd m → Compat H (m ^ 2) z ρ → v ≠ 0 → (∀ G, VanishC D m G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (S : ValuationSubring C) (κ : Type) (_ : Field κ) (_ : IsAlgClosed κ) (res : S →+* κ) (i : K →+* κ) (o : Full D C) (_ : Mdl o) (v' : D.La → S) (r' z' : S), (∀ n : ℕ, 0 < n → ‖(n : C)‖ = 1) ∧ (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) ∧ o.Theta m (fun x => v' x) ∧ (∀ x, res (v' x) = i (v x)) ∧ (r' : C) = o.ρ ∧ res r' = i ρ ∧ (z' : C) = o.I.ζ (m ^ 2) ∧ res z' = i z := by
  intro hV h6 hU hX hT hE hA E _ _ _ H D l Xo c W₀ Y K _ _ _ m ρ z v hm hc hv hvan
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hN : 0 < m ^ 2 := pow_pos hm.pos 2
  haveI := c.fin
  have hζ : IsPrimitiveRoot (zeta (m ^ 2)) (m ^ 2) := Complex.isPrimitiveRoot_exp _ hN.ne'
  let L : IntermediateField c.F ℂ := IntermediateField.adjoin c.F {zeta (m ^ 2)}
  haveI : FiniteDimensional c.F L := IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hN).tower_top
  let ξ₀ : L := ⟨zeta (m ^ 2), IntermediateField.mem_adjoin_simple_self _ _⟩
  have hξ₀ : IsPrimitiveRoot ξ₀ (m ^ 2) := IsPrimitiveRoot.of_map_of_injective (f := L.val.toRingHom) hζ
    Subtype.val_injective
  let ξ : Lˣ := (hξ₀.isUnit hN.ne').unit
  have hξ : IsPrimitiveRoot ξ (m ^ 2) := IsPrimitiveRoot.coe_units_iff.1 hξ₀
  let r₀ : c.F := IntermediateField.inclusion c.le (baseKA l).ρ
  obtain ⟨hqc, hlft⟩ := finiteType_of_qproj Xo.qproj
  obtain ⟨Ix, _, A, _, x, gam, J, _, q, w, hq, hft, hs, hcov, hpt⟩ := exists_charts (L := L) hL hV.1.2.1 Y.oF
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hm hξ
  let χ₀ : MvPolynomial (Fin 2) ℤ →+* L := cf ξ₀ (algebraMap c.F L r₀)
  have hχ₀ : L.val.toRingHom.comp χ₀ = cf (zeta (m ^ 2)) H.rt0 := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun i => ?_
    fin_cases i
    · simp [χ₀, ξ₀]
    · simp [χ₀]; rfl
  have key : ∀ (G : MvPolynomial D.La (MvPolynomial (Fin 2) ℤ)) (d : ℕ), G.IsHomogeneous d →
      (∀ i, MvPolynomial.eval₂ ((gam i).comp χ₀) (fun a => w i (q a)) G = 0) →
      MvPolynomial.eval₂ (cf z ρ) v G = 0 := fun G d hG h0 => by
    refine hvan G ⟨hm, ⟨d, hG⟩, fun o hρ hz u hu => ?_⟩
    obtain ⟨I', hI'⟩ := GlobalTheory.TateRoot.exists_tateIso_zeta_eq E H D l ℂ _ _ _ o.I l.A (zeta l.A) l.A_pos
      (Complex.isPrimitiveRoot_exp _ l.A_pos.ne')
    obtain ⟨y, ⟨hy, φ, h1, h2, h3, -⟩, -⟩ := (GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hV h6 hU hX hT hE hA E H D l Xo c W₀ Y ℂ c.F.val.toRingHom).1
      { o with I := I' } (fun r hr => hρ.trans hr.symm) (fun r hr => hI'.trans hr.symm)
    obtain ⟨i, f, hf, hth⟩ := hcov ℂ y o φ L.val.toRingHom ⟨h1, h2, h3⟩ hy hz
    obtain ⟨s, rfl⟩ := (theta_iff hL o hm hth).1 hu
    have e := congrArg f (h0 i)
    rw [MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hf, hχ₀, map_zero] at e
    rw [eval₂_smul _ hG]
    exact mul_eq_zero_of_right _ e
  let r := Function.surjInv hq
  have hr : ∀ j, q (r j) = j := Function.surjInv_eq hq
  have hvr : ∀ a, v (r (q a)) = v a := fun a => by
    have := key (MvPolynomial.X (r (q a)) - MvPolynomial.X a) 1
      ((MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_X _ _)) fun i => by simp [hr]
    simpa [sub_eq_zero] using this
  letI : ∀ i, Algebra ℚ (A i) := fun i => (((gam i).comp (algebraMap c.F L)).comp (algebraMap ℚ c.F)).toAlgebra
  haveI := Fintype.ofFinite J
  obtain ⟨i, W, _, _, _, _, f, s, w', hW, hs0, hf, hw⟩ := GlobalTheory.T.cone_closure_arc_of_integral_image_reduction_alt GlobalTheory.T.exists_complete_discreteValuationRing_of_mem_closure_cones_alt GlobalTheory.T.exists_field_of_isIntegral_image' _
    (cf (zeta (m ^ 2)) H.rt0) (fun p => by
      have h1 : IsIntegral ℤ H.rt0 := IsIntegral.of_pow two_pos (by
        rw [H.sqrt_neg_disc_sq]; exact (isIntegral_natCast H.d).neg)
      induction p using MvPolynomial.induction_on with
      | C a => simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := a)
      | add p p' hp hp' => rw [map_add]; exact hp.add hp'
      | mul_X p i hp =>
        rw [map_mul]
        refine hp.mul ?_
        fin_cases i
        · simpa using hζ.isIntegral hN
        · simpa using h1)
    K J Ix (cf z ρ) hc A
    (fun i => (hft i).comp (RingHom.finite_algebraMap.2 (inferInstance : Module.Finite ℚ c.F)).finiteType)
    (fun i => (gam i).comp χ₀) (fun i p hp => by
      have : χ₀ p = 0 := Subtype.val_injective ((RingHom.congr_fun hχ₀ p).trans hp)
      rw [RingHom.comp_apply, this, map_zero])
    w (fun j => v (r j)) (fun h => hv (funext fun a => (hvr a).symm.trans (congrFun h (q a))))
    (fun G d hG h0 => by
      have := key (MvPolynomial.rename r G) d hG.rename_isHomogeneous fun i => by
        rw [MvPolynomial.eval₂_rename]
        simpa only [Function.comp_def, hr] using h0 i
      rwa [MvPolynomial.eval₂_rename] at this)
  haveI : CharZero W := charZero_of_injective_algebraMap (algebraMap K W).injective
  have hcdv : CDV W := ⟨inferInstance, hW, inferInstance⟩
  obtain ⟨C, _, _, _, _, _, g, hg, hext⟩ := GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W (FractionRing W)
  have hg' : ∀ t, g t = algebraMap (FractionRing W) C t := hg
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing W) C).injective
  obtain ⟨S, κ, _, _, res, j, hS, hres, hj⟩ := exists_residue hext
  letI : Algebra ℚ W := ((algebraMap K W).comp (algebraMap ℚ K)).toAlgebra
  obtain ⟨b, hb⟩ := exists_lift_of_finite (f.comp ((gam i).comp (algebraMap c.F L)))
  let bF : c.F →+* C := (g.comp f).comp ((gam i).comp (algebraMap c.F L))
  obtain ⟨o₁, ho₁⟩ := (GlobalTheory.T.fullTorsionObject_existsUnique_moduliPoint hV h6 hU hX hT hE hA E H D l Xo c W₀ Y C bF).2.1 (spMap g ≫ spMap f ≫ x i)
  obtain ⟨M, -⟩ := GlobalTheory.T.moduli_model_ultrametric_points hV h6 hU hX hT hE hA E H D l Xo c W₀ Y C W hcdv hext (FractionRing W) g hg
    (spMap f ≫ x i) (b.comp (c.V W₀).subtype) (by
      rw [Model.j, Category.assoc Y.jQ, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, Category.assoc,
        ← Category.assoc (x i), hs, spMap_comp'', spMap_comp'', ← RingHom.comp_assoc, ← hb]
      refine Eq.trans ?_ (congrArg (spMap _ ≫ ·) (spMap_comp'' _ (algebraMap W (FractionRing W))).symm)
      rw [spMap_comp'']) o₁ ho₁
  rw [← Category.assoc, spMap_comp''] at ho₁
  obtain ⟨φ, h1, h2, h3, -⟩ := ho₁
  obtain ⟨hdet, -⟩ := Y.oF.geom C (𝟙 _ ≫ spMap (g.comp f) ≫ x i)
    (bF.comp (IntermediateField.inclusion c.le).toRingHom) (by
      rw [Category.id_comp, pullback.condition, Category.assoc, ← Category.assoc (x i), hs, spMap_comp'', spMap_comp''])
  let o₂ : Full D C :=
    { o₁ with
      ρ := bF r₀
      ρ_sq := by
        have := congrArg (bF.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq
        rwa [map_pow, map_neg, map_natCast] at this
      det := fun τ => by
        have e := GlobalTheory.LiePull.lieMult_pull _ _ _ Y.oF.t.G o₁.P.A _ φ Y.oF.t.act (ofRingAct o₁.oa.toRingAct) h1 h3 C (𝟙 _) τ
        rw [e, e]
        exact hdet τ }
  obtain ⟨I', hI', hth⟩ := hpt i C (g.comp f) o₂ φ ⟨h1, h2, h3⟩
  have hjK : ∀ p, (j (algebraMap K W (cf z ρ p)) : C) = g (f (gam i (χ₀ p))) := fun p => by
    rw [hj, ← hg', ← hf]; rfl
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, S, κ, inferInstance,
    inferInstance, res, (res.comp j).comp (algebraMap K W), { o₂ with I := I' },
    { M with }, fun a => j (w' (q a)), j (algebraMap K W ρ), j (algebraMap K W z), fun n hn => ?_, hS, hres, ?_,
    fun a => ?_, ?_, rfl, ?_, rfl⟩
  · have h1 := hext.1 (algebraMap K W n)
    have h2 := hext.1 (algebraMap K W (n : K)⁻¹)
    have e : algebraMap (FractionRing W) C (algebraMap W _ (algebraMap K W n)) *
        algebraMap (FractionRing W) C (algebraMap W _ (algebraMap K W (n : K)⁻¹)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one, map_one, map_one]
    have e' := congrArg norm e
    rw [norm_mul, norm_one] at e'
    rw [map_natCast, map_natCast, map_natCast] at e' h1
    nlinarith [norm_nonneg (n : C)]
  · refine (theta_iff hL _ hm hth).2 ⟨Units.mk0 (g s) ((map_ne_zero g).2 hs0), funext fun a => ?_⟩
    rw [hj, ← hg', (hw _).1, map_mul]
    rfl
  · have := hres (j (w' (q a) - algebraMap K W (v (r (q a))))) (by rw [hj]; exact hext.2 _ (hw _).2)
    rw [map_sub, map_sub, sub_eq_zero, hvr] at this
    exact this
  · have := hjK (MvPolynomial.X 1)
    simp only [χ₀, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    exact this
  · have := hjK (MvPolynomial.X 0)
    simp only [χ₀, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    exact this.trans hI'.symm

end GlobalTheory.ThetaClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformizationDataCompleteLocalPrime
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

theorem GlobalTheory.PreUnifLocal.exists_preU_local :
    Laws → Laws2 → Laws3 → Ega → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → SplitOver G I → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : PreU I D A G), U.P = P ∧ U.gen = gen :=
  GlobalTheory.PreUnifLocal.exists_preU_of_fibres GlobalTheory.ClosedPol.main
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeriesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierSeries_product_eq_product_series : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  first | exact @GlobalTheory.ZH.SeriesProd.main | exact GlobalTheory.ZH.SeriesProd.main | (intros; apply GlobalTheory.ZH.SeriesProd.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableFourierCoefficientsFamilyFiniteExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_fourierCoefficients_family_finite_extension : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (s : Fam u.D.toPre (PadicAlgCl p) k) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), w.IsGen → Summable (fun χ => GlobalTheory.UT.coef s g w χ) ∧ Filter.Tendsto (fun χ => GlobalTheory.UT.coef s g w χ) Filter.cofinite (nhds 0) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ χ, GlobalTheory.UT.coef s g w χ ∈ K := by
  first | exact @GlobalTheory.ZH.SeriesConv.summable_coef | exact GlobalTheory.ZH.SeriesConv.summable_coef | (intros; apply GlobalTheory.ZH.SeriesConv.summable_coef <;> assumption)
end

