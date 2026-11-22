import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionPullbackPowerLocusLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0103
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrix
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparatesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → (∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → w ≠ 0) ∧ (∀ (a a' : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (u.H k) σ (u.toG a') w → a = a') ∧ ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∃ a' : u.PtC, u.toG a' = a := by
  first | exact @GlobalTheory.ZH.AdaptedSep.basis_separates | exact GlobalTheory.ZH.AdaptedSep.basis_separates | (intros; apply GlobalTheory.ZH.AdaptedSep.basis_separates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionPullbackPowerLocusLeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_pullbackPowerLocus_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G →  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → IsAbelianScheme B → ∀ (L : LB G.left), AmpleCub G L → ∀ (F : G ⟶ G) (Q : ℕ), 2 ≤ Q → IsMonHom F → PullPow F.left L Q → i ≫ F = i ^ Q → ∃ C : ℕ, ∀ n, 1 ≤ n → Finite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ≫ F = x ^ Q ∧ x ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ≫ F = x ^ Q ∧ x ^ n = 1} ≤ C * n ^ Module.finrank ℤ X := by
  first | exact @GlobalTheory.SS.PowLocus.card_torsion_powLocus_le | exact GlobalTheory.SS.PowLocus.card_torsion_powLocus_le | (intros; apply GlobalTheory.SS.PowLocus.card_torsion_powLocus_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubicalOfGroupSchemeIsoStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleCubical_of_groupScheme_iso : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (e : G ≅ G'), IsMonHom e.hom → ∀ L' : LB G'.left, AmpleCub G' L' → ∃ L : LB G.left, AmpleCub G L := by
  first | exact @GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso | exact GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso | (intros; apply GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAutomorphismPermutationMaxOrderMembers
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem Model.twist_twist_symm {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
    (M : Model R A) (f : A ≅ A') : (M.twist f).twist f.symm = M := by
  obtain ⟨Y, e, h₁, h₂, h₃⟩ := M
  simp [Model.twist]

theorem isIntegral_of_abelian {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem exists_genIso_of_max_ord (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) (π : R) (hπ : Irreducible π) (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A) (hD : IsFrame D)
    (J : Type) (M : J → Model R A) (hI : ∀ j, (M j).Irr) (hW : WeakNeron M) (o : J → ℤ)
    (ho : ∀ j, HasOrd (M j) D π (o j)) (ρ : ℤ) (hρ : ∀ j, o j ≤ ρ) (f : A ≅ A) (i : J) (hi : o i = ρ) :
    ∃ i', o i' = ρ ∧ GenIso (M i) (M i') f.hom := by
  have hint := isIntegral_of_abelian A hA
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  have bound : ∀ (N : Model R A) (m : ℤ), N.Irr → HasOrd N D π m →
      m ≤ ρ ∧ (m = ρ → ∃ i', o i' = ρ ∧ GenIso N (M i') (𝟙 A)) := by
    intro N m hN hm
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_modelMapDefined_weakNeronFamily R K A J M hW N hN
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.jacobian_order_monotone_semistableModel R K π hπ A I D hD N (M j) m (o j) hN (hI j) hm (ho j) hj
    have := hρ j
    exact ⟨h₁.trans this, fun e => ⟨j, by omega, h₂ (by omega)⟩⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder R K π hπ A hA I D hD f
  obtain ⟨c', hc'⟩ := GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder R K π hπ A hA I D hD f.symm
  have t₁ := hc _ _ (ho i)
  have t₂ := hc' _ _ (ho i)
  have t₃ := hc' _ _ t₁
  rw [Model.twist_twist_symm] at t₃
  have e₃ := (GlobalTheory.T.existsUnique_modelHasJacobianOrder R K π hπ A I D hD (M i) (hI i)).unique t₃ (ho i)
  have i₁ : ((M i).twist f).Irr := hI i
  have i₂ : ((M i).twist f.symm).Irr := hI i
  obtain ⟨b₁, b₁'⟩ := bound _ _ i₁ t₁
  obtain ⟨b₂, -⟩ := bound _ _ i₂ t₂
  obtain ⟨i', hi', hg⟩ := b₁' (by omega)
  exact ⟨i', hi', (h3 A A (M i) (M i') f).2.1.2 hg⟩

theorem WeakNeron.nonempty {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) {A : Over (Sp K)} [GrpObj A] {J : Type} {M : J → Model R A} (hW : WeakNeron M) :
    Nonempty J := by
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  obtain ⟨i, -⟩ := hW R K (by simp) (η[A]).left (by
    rw [← Category.assoc, Over.w]
    simp)
  exact ⟨i⟩

theorem exists_permuted_members : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ S : Finset (Fin n), S.Nonempty ∧ (∀ (f : A ≅ A), ∀ i ∈ S, ∃ i' ∈ S, GenIso (M i) (M i') f.hom) ∧ ∀ (Θ : A ⊗ A ≅ A ⊗ A), ∀ i ∈ S, ∀ j ∈ S, ∃ i' ∈ S, ∃ j' ∈ S, GenIso ((M i).prod (M j)) ((M i').prod (M j')) Θ.hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  have hne := hW.nonempty hSH
  have hdvr := hSH.1
  have hfr := hSH.2.2.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_vectorFieldFrame_smooth_commGrpScheme K A g hg
  choose o ho using fun i => (GlobalTheory.T.existsUnique_modelHasJacobianOrder R K π hπ A (Fin g) D hD (M i) (hI i)).exists
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max o
  refine ⟨Finset.univ.filter fun i => o i = o i₀, ⟨i₀, by simp⟩, ?_, ?_⟩
  · intro f i hi
    obtain ⟨i', hi', h⟩ := exists_genIso_of_max_ord R K hSH π hπ A hA _ D hD _ M hI hW o ho (o i₀) hi₀ f i
      (by simpa using hi)
    exact ⟨i', by simpa using hi', h⟩
  · intro Θ i hi j hj
    have hi : o i = o i₀ := by simpa using hi
    have hj : o j = o i₀ := by simpa using hj
    obtain ⟨D₂, hD₂, hp⟩ := GlobalTheory.T.vectorFieldOrder_add_of_prod_strictHenselian R K hSH π hπ A A _ _ D D hD hD
    obtain ⟨p₁, p₂⟩ := GlobalTheory.T.prod_irr_and_weakNeron' R K hSH A A
    obtain ⟨⟨i', j'⟩, h', h⟩ := exists_genIso_of_max_ord R K hSH π hπ (A ⊗ A)
      (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ D₂ hD₂ (Fin n × Fin n)
      (fun p => (M p.1).prod (M p.2)) (fun p => p₁ _ _ (hI _) (hI _)) (p₂ _ _ M M hW hW)
      (fun p => o p.1 + o p.2) (fun p => hp _ _ _ _ (hI _) (hI _) (ho _) (ho _)) (o i₀ + o i₀)
      (fun p => add_le_add (hi₀ _) (hi₀ _)) Θ (i, j) (by simp [hi, hj])
    have a₁ := hi₀ i'
    have a₂ := hi₀ j'
    have h' : o i' + o j' = o i₀ + o i₀ := h'
    exact ⟨i', by simp; omega, j', by simp; omega, h⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteSplitTorusExtensionOfTorusExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SS

theorem exists_finite_torusExtension_of_torusExt : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  intro k _ G _ ⟨T⟩
  have := T.q_hom
  have := T.i_hom
  obtain ⟨-, k', _, _, hfin, X, _, hfree, hX, e, he⟩ := GlobalTheory.torus_isAffineHom_and_splits_finite k T.T₀ T.isTorus
  refine ⟨k', inferInstance, inferInstance, hfin, ?_⟩
  let f : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hq := isPullback_overPullback_map_left f T.q
  have : IsMonHom e.inv := inferInstance
  refine ⟨{ X := X
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.inv ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrixStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertible_adaptedBasis_link_matrix : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∃ b : Matrix S.J S.J (FractionRing u.V), b.det ≠ 0 ∧ u.Link σ b := by
  first | exact @GlobalTheory.ZH.LinkMatrix.exists_link | exact GlobalTheory.ZH.LinkMatrix.exists_link | (intros; apply GlobalTheory.ZH.LinkMatrix.exists_link <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftIntegralPointClosureTestModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosLift

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap (OO p).subtype)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]
  exact bot_le

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  rw [ρ.N_eq]
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  nlinarith

theorem gPt_j {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V :=
  (spMap_comp' _ _).trans (spMap_comp' (algebraMap u.V (FractionRing u.V)) (algebraMap (FractionRing u.V) (PadicAlgCl p))).symm

theorem exists_generic {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ}
    [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}
    (tm : Q.TMap t c) (x : Sp (PadicAlgCl p) ⟶ Q.P.left) (hx : x ≫ Q.P.hom = gPt p ≫ y) :
    ∃ a : Sp (PadicAlgCl p) ⟶ t.u.G.left, a ≫ t.u.G.hom = gPt p ≫ spMap t.u.j ∧
      a ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
  set κ := spMap (algebraMap (FractionRing t.u.V) (PadicAlgCl p)) with hκ
  have h1 : x ≫ Q.P.hom = (κ ≫ c.yK) ≫ U₀.ι := by
    rw [hx, Category.assoc, c.yK_fac, ← Category.assoc, ← gPt_j, Category.assoc, c.fac]
  let a1 := Q.cart.lift x (κ ≫ c.yK) h1
  have e1 : a1 ≫ Q.a₀ = x := Q.cart.lift_fst _ _ _
  have e2 : a1 ≫ pullback.snd _ _ = κ ≫ c.yK := Q.cart.lift_snd _ _ _
  have h2 : (a1 ≫ pullback.fst _ _) ≫ ρ.P.A.hom = κ ≫ spMap t.u.yK := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, e2, Category.assoc, c.yK_u]
  let a2 := t.u.cart.1.lift (a1 ≫ pullback.fst _ _) κ h2
  have e3 : a2 ≫ t.u.φ = a1 ≫ pullback.fst _ _ := t.u.cart.1.lift_fst _ _ _
  have e4 : a2 ≫ t.u.A.A.hom = κ := t.u.cart.1.lift_snd _ _ _
  let a3 : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V) := a2 ≫ t.u.U.gen.inv.left
  have e5 : a3 ≫ pullback.snd _ _ = κ := by
    rw [← e4]
    exact (Category.assoc _ _ _).trans (congrArg (a2 ≫ ·) (Over.w t.u.U.gen.inv))
  have e6 : a3 ≫ t.u.U.gen.hom.left = a2 := by
    refine (Category.assoc _ _ _).trans ((congrArg (a2 ≫ ·) ?_).trans (Category.comp_id _))
    exact congrArg CommaMorphism.left t.u.U.gen.inv_hom_id
  have e7 : a3 ≫ tm.φ = a1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, tm.φ_fst, ← e3, ← e6]
      exact (Category.assoc _ _ _).symm
    · rw [Category.assoc, tm.φ_snd, ← Category.assoc, e5, e2]
  refine ⟨a3 ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, e5, gPt_j]
  · rw [Category.assoc, ← tm.φ_f, ← Category.assoc, e7, e1]

theorem exists_lift : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ b : Sp (OO p) ⟶ Q.P.left, b ≫ Q.P.hom = y → ⊤ ≤ b ⁻¹ᵁ Q.G → ∃ c' : Sp (OO p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b := by
  intro _ o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hbig b hb hG
  have hW : ⊤ ≤ b ⁻¹ᵁ (Q.P.hom ⁻¹ᵁ Q.W tm.l) := by
    rw [← Scheme.Hom.comp_preimage, hb]
    exact (CrdCalc.top_le_iff y _).2 tm.mem
  obtain ⟨b', hb'⟩ : ∃ b' : Sp (OO p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, b' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b :=
    ⟨IsOpenImmersion.lift _ b (by
      rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 hW), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (pull_isLB Q.isLB (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) b'
  have hdet : ∀ {R : Type} [CommRing R] (ψ : t.u.V →+* R), IsUnit (tm.m.map ψ).det := fun ψ => by
    have := tm.unit.map ψ
    rwa [RingHom.map_det] at this
  obtain ⟨w, rfl⟩ : ∃ w, w' = (tm.m.map t.u.j).mulVec w :=
    ⟨(tm.m.map t.u.j)⁻¹.mulVec w', by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hdet _), Matrix.one_mulVec]⟩
  have hmap : ∀ {R : Type} [CommRing R] (ψ : OO p →+* R), Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l)
      (spMap ψ ≫ b') ((tm.m.map (ψ.comp t.u.j)).mulVec fun i => ψ (w i)) := fun ψ => by
    have := CrdCalc.crd_map ψ hw'
    refine (congrArg _ (funext fun i => ?_)).mp this
    exact RingHom.map_mulVec ψ _ _ i
  obtain ⟨i₀, hi₀, hne⟩ := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hbig (rPt p ≫ b')
    (fun i => IsLocalRing.residue (OO p) (w i))
    (by rw [Category.assoc, ← Category.assoc b', hb', hb]) (hmap _)).1 (by
      rw [Category.assoc, hb']
      exact fun z _ => hG (Set.mem_univ (rPt p z)))
  have hu : IsUnit (w i₀) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hne
  have hn : 1 ≤ ‖(w i₀ : PadicAlgCl p)‖ := not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hu
  obtain ⟨a, ha, haf⟩ := exists_generic tm (gPt p ≫ b) (by rw [Category.assoc, hb])
  have haf' : a ≫ tm.f = gPt p ≫ b' := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι, Category.assoc, haf, Category.assoc, hb']
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists t.mod.isLB t.σ a
  have h1 := tm.crd _ ((OO p).subtype.comp t.u.j) a v (ha.trans (spMap_comp' _ _)) hv
  rw [haf'] at h1
  obtain ⟨κ, hκ⟩ := CrdCalc.crd_unique h1 (hmap (OO p).subtype)
  have h2 : (fun i => (OO p).subtype (w i)) = fun i => (κ : PadicAlgCl p) * v i := by
    refine Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (hdet ((OO p).subtype.comp t.u.j))) ?_
    have : (fun i => (κ : PadicAlgCl p) * v i) = (κ : PadicAlgCl p) • v := rfl
    rw [this, Matrix.mulVec_smul]
    exact funext hκ
  have h3 := CrdCalc.crd_smul κ hv
  rw [← h2] at h3
  obtain ⟨c', hc', hc''⟩ := GlobalTheory.T.isIntegral_of_weightZeroCoordinate_dominates p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls t.mod
    (big ρ hbig) a _ ha h3 ⟨i₀, hi₀, fun i => ((mem_OO_iff _).1 (w i).2).trans hn⟩
  refine ⟨c', hc', ?_⟩
  have := isDominant_gPt p
  have := Q.proper
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_
  · rw [Category.assoc, Category.assoc, tm.f_over, ← Category.assoc, hc', c.fac, hb]
  · rw [← Category.assoc, hc'', haf]

end GlobalTheory.ZH.ClosLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TripleExt

open GlobalTheory.CechPic

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem isLB_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) : (cubeLB G x L).IsLB :=
  LB.isLB_linComb hL _ _

theorem cls_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls _ (isLB_cube x hL) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls_pre {T T' : Over S} (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) :
    pull u.left (cubeCls x c) = cubeCls (fun i => u ≫ x i) c := by
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z => _ • pull (CommaMorphism.left z) c) (psum_hom (preHom u) x I.down)

theorem pull_cubeCls_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (u : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = u ≫ x i)
    (c : Pic G.left) : pull (Y := T'.left) u.left (cubeCls x c) = cubeCls x' (pull φ c) := by
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp, psum_push h x' x u hx]

theorem cubeCls_one {n : ℕ} (c : Pic G.left) (hc : pull (eSec G) c = 0) :
    cubeCls (fun _ : Fin n => η[G]) c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have e : psum G (fun _ : Fin n => η[G]) I.down = η[G] := by
    have := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ : Fin n => η[G]) I.down
    simp only [MonoidHom.one_apply, e₁] at this
    exact this.symm
  rw [e]
  exact (congrArg _ hc).trans (smul_zero _)

end Cube

theorem pic_ext (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) {U H HU : Scheme.{0}}
    [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (hp : Smooth p)
    (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (hj : IsPullback jH pU p j) (α β : Pic H)
    (h₁ : pull jH α = pull jH β) (h₂ : pull e α = pull e β) : α = β := by
  obtain ⟨A, hA, rfl⟩ := cls_surj α
  obtain ⟨B, hB, rfl⟩ := cls_surj β
  exact (cls_eq_iff hA hB).2 ((GlobalTheory.T.lineBundleIso_extend_of_normal_base S hS U H HU j p e jH pU hp hg he hj A B hA hB
    ((cls_eq_iff (pull_isLB hA _) (pull_isLB hB _)).1 h₁)).1 ((cls_eq_iff (pull_isLB hA _) (pull_isLB hB _)).1 h₂))

theorem exists_sab_extension : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (U : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] [IsCommMonObj G] (semi : IsSemiAbelian G) (act : OAct (NumberField.RingOfIntegers E) G) (t₀ : SAB H U) (a : t₀.G.left ⟶ G.left), IsGrpPullback t₀.G G j a → (∀ x, (t₀.act.act x).left ≫ a = a ≫ (act.act x).left) → ∀ M : LB G.left, M.IsLB → LBIso (M.pull a) t₀.PP.L → ∃ (PP : RigLB G) (cub : CubicalStr G PP) (h₁ : _) (h₂ : _) (h₃ : _) (m : SABMap t₀ (SAB.mk G semi act PP cub h₁ h₂ h₃) j), m.φ = a := by
  intro S _ _ hS E _ _ _ H U _ j _ G _ _ semi act t₀ a h hact M hM hMa
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨PP, cub, m, rfl, hme, hlin, hsym⟩ := GlobalTheory.T.exists_rigidified_cubical_symmetric_extension_normalBase S hS U j G t₀.G a h t₀.PP t₀.cub M hM hMa
  have hc₀ : cls t₀.PP.L t₀.PP.isLB = pull m.F (cls PP.L PP.isLB) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact (cls_eq_iff t₀.PP.isLB (pull_isLB PP.isLB _)).2 ⟨w, hw⟩
  have hrig : pull (eSec G) (cls PP.L PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  have pa : ∀ {T : Over U} (x : T ⟶ t₀.G) b,
      pushPt h.1.w (x ≫ t₀.act.act b) = pushPt h.1.w x ≫ act.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ha1 : ∀ b, η[G] ≫ act.act b = η[G] := fun b => by have := act.hom b; exact IsMonHom.one_hom _
  refine ⟨PP, cub, hsym t₀.sym, fun b => ?_, ?_, ⟨m, h, hme, hact, hlin⟩, rfl⟩
  · refine (cls_eq_iff (isLB_cube _ PP.isLB) (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB, cls_cube _ PP.isLB]
    have hsm : Smooth (G ⊗ G).hom := by
      show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
      infer_instance
    have hgc : GeometricallyConnected (G ⊗ G).hom := by
      show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
      exact GeometricallyConnected.comp _ _
    let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
    let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
    have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ y := fun y =>
      ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
    obtain ⟨y₁, hy₁⟩ := hy (fst G G)
    obtain ⟨y₂, hy₂⟩ := hy (snd G G)
    let e : 𝟙_ (Over S) ⟶ G ⊗ G := lift η[G] η[G]
    refine pic_ext S hS j (G ⊗ G).hom e.left u.left T'.hom hsm
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_iff (isLB_cube _ t₀.PP.isLB) (isLB_cube _ t₀.PP.isLB)).2 (t₀.adj b)
      rw [cls_cube _ t₀.PP.isLB, cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift y₁ y₂).left) h₀
      rw [pull_cubeCls_pre, pull_cubeCls_pre] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
        (h₁.trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
      · fin_cases i
        · simp [pa, hy₁]
        · simp [hy₂]
      · fin_cases i
        · simp [hy₁]
        · simp [pa, hy₂]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
      congr 1
      funext i
      fin_cases i <;> simp [e, ha1]
  · refine (cls_eq_iff PP.isLB (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB]
    refine pic_ext S hS j G.hom (eSec G) m.F t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · have h₀ := (cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := pull_cubeCls_push h ![𝟙 t₀.G, t₀.act.act H.w0] ![𝟙 G, act.act H.w0] (pushPt h.1.w (𝟙 t₀.G))
        (fun i => by
          fin_cases i
          · simp
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)) (cls PP.L PP.isLB)
      have e : (pushPt h.1.w (𝟙 t₀.G)).left = m.F := Category.id_comp _
      rw [e] at h₁
      exact h₀.trans h₁.symm
    · refine hrig.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
      refine (cubeCls_one (n := 2) _ hrig).symm.trans ?_
      congr 1
      funext i
      fin_cases i <;> simp [ha1]

end GlobalTheory.TripleExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndepStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep : ∀ C : Core, C.Indep → C.Fib := by
  first | exact @GlobalTheory.ZJ.Core.fib_of_indep | exact GlobalTheory.ZJ.Core.fib_of_indep | (intros; apply GlobalTheory.ZJ.Core.fib_of_indep <;> assumption)
end

