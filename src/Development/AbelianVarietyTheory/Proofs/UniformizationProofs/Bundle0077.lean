import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0071

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroupStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.abelian_sections_irreducible_theta_group : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.ThetaIrred.main | exact GlobalTheory.ThetaIrred.main | (intros; apply GlobalTheory.ThetaIrred.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaCoefficientsAbelianSquareStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionFormula_coefficients_abelian_square : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → AddB D (𝟙_ _) f₀ r f f') := by
  first | exact @GlobalTheory.AddCoeff.main | exact GlobalTheory.AddCoeff.main | (intros; apply GlobalTheory.AddCoeff.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorEigenDiagonalThetaOrderTwoStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionTensor_eigen_diagonal_theta_order_two : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (th : EA P p 1) (n : ℕ) (t t' u u' : Fin n → EA P p 2), AddA P (Over.mk p) th.sec (fun i => (t i).sec) (fun i => (t' i).sec) → ∀ θ : ThetaGrp P.A P.L ((2 : ℕ) : ℤ) (Over.mk p), θ.pt ^ 2 = 1 → (∀ i, IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t i).sec (u i).sec ∧ IsActOf P.A P.L ((2 : ℕ) : ℤ) θ (t' i).sec (u' i).sec) → ∃ r : F, ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by
  first | exact @GlobalTheory.AddEig.main | exact GlobalTheory.AddEig.main | (intros; apply GlobalTheory.AddEig.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.card_quotient_kTorsion_pairs : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → Nat.card (Quot (QkPt.Equiv D.toPre F (k := k))) = k ^ (2 * (D.toPre.rank + D.toPre.P.g)) := by
  first | exact @GlobalTheory.UT.card_qk | exact GlobalTheory.UT.card_qk | (intros; apply GlobalTheory.UT.card_qk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChartExpansionOfValueExpansionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.chartExpansion_of_valueExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U.ExpF (FractionRing R) k t s.s → U'.Expands k σ s := by
  first | exact @GlobalTheory.UU.ExpFrac.expands_of_expF | exact GlobalTheory.UU.ExpFrac.expands_of_expF | (intros; apply GlobalTheory.UU.ExpFrac.expands_of_expF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianDim

theorem exists_relDim_of_connected {S : Scheme.{0}} [ConnectedSpace S] (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) : ∃ g, SmoothOfRelativeDimension g B.hom := by
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group S B).1
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  exact exists_dim_of_preconnected B.hom x

theorem connectedSpace_spec_of_isLocalRing (A : Type) [CommRing A] [IsLocalRing A] :
    ConnectedSpace (Spec (CommRingCat.of A)) := by
  show ConnectedSpace (PrimeSpectrum A)
  rw [connectedSpace_iff_univ]
  refine ⟨⟨IsLocalRing.closedPoint A, trivial⟩, ?_⟩
  intro u v hu hv huv ⟨x, _, hx⟩ ⟨y, _, hy⟩
  have hc : IsLocalRing.closedPoint A ∈ u ∪ v := huv trivial
  rcases hc with h | h
  · exact ⟨y, trivial, (IsLocalRing.specializes_closedPoint y).mem_open hu h, hy⟩
  · exact ⟨x, trivial, hx, (IsLocalRing.specializes_closedPoint x).mem_open hv h⟩

theorem exists_relDim : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B], IsAbelianScheme B → ∃ g, SmoothOfRelativeDimension g B.hom := by
  intro A _ _ B _ hB
  have := connectedSpace_spec_of_isLocalRing A
  exact exists_relDim_of_connected B hB

end GlobalTheory.AbelianDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAddFinrankOfKernel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem dim_eq_add_finrank_of_kernel {S : Scheme.{0}} (y : S) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G) [IsMonHom q]
    [IsMonHom i] [Flat q.left] [Surjective q.left] [IsAffineHom q.left] (hk : IsPullback i (toUnit _) q (η[B]))
    {g g' : ℕ} (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' B.hom) :
    g = g' + Module.finrank ℤ X := by
  have := (H1.torus_dim S X).smooth
  have : Smooth q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback i q hk).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hk.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

theorem PreU.dim_eq : (AllPre fun {_} _ _ _ {D} {A} {_} _ _ _ => A.g = D.P.g + D.rank) := by
  intro V _ _ _ _ D A G _ _ U
  have hs : Smooth G.hom := U.semi.smooth
  have : GeometricallyConnected G.hom := U.semi.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have bc : ∀ {S' : Scheme.{0}} {X : Over (Spec (CommRingCat.of V))} {m : ℕ} (f : S' ⟶ Spec (CommRingCat.of V)),
      SmoothOfRelativeDimension m X.hom → SmoothOfRelativeDimension m ((Over.pullback f).obj X).hom :=
    fun f h => (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) h
  have h₁ : n = A.g := by
    have a := A.smoothDim
    have b : SmoothOfRelativeDimension (0 + A.g) ((Over.pullback (jK V)).obj G).hom := by
      have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
      rw [← Over.w U.gen.hom]; infer_instance
    exact (H1.dim_unique _ (bc _ hn) b (eSec _ (Classical.arbitrary (Spec (CommRingCat.of (FractionRing V)))))).trans (zero_add _)
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
  let c := U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  exact h₁.symm.trans (dim_eq_add_finrank_of_kernel (Classical.arbitrary _) c.q c.i c.isKernel (bc _ hn)
    (bc _ D.P.smoothDim))

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelianStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G) (c : CubicalStr G L), L.IsSymmetric → ∃ P : CP G, P.L = L ∧ HEq P.c c := by
  first | exact @GlobalTheory.UU.exists_cp_of_isSymmetric | exact GlobalTheory.UU.exists_cp_of_isSymmetric | (intros; apply GlobalTheory.UU.exists_cp_of_isSymmetric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.BaseExpansionExists

section General
variable {X X₁ X₂ Y Y' Z : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (e : ∀ i, φ' i = h ≫ φ i)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun i => h ≫ φ i := funext e
  exact ⟨_, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem exists_carry (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => f₁) (fun _ => (k : ℤ)))) :
    ∃ τ : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval τ r z J₂ = (gw w r z (J₂ (r ≫ f₂)) (fun _ => J₁ (r ≫ f₁))).val ^ k * sval s r z J₁ := by
  obtain ⟨τ, hτ⟩ := GenericFibreSections.exists_transfer hL₁ hL₂ f₁ f₂ k
    (fun i j => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))
    (fun i j y hi hj => ⟨mem_pull.2 hj, mem_pull.2 hi⟩)
    (fun i j => (show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
      w.s (fun _ => j, fun _ => i)) ^ k) (fun y i i' j j' hi hi' hj hj' => by
      have e := GenericFibreSections.gw_trans hw y hi hi' hj hj'
      rw [map_pow, map_pow, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
      exact congrArg (· ^ k) e) s
  refine ⟨τ, fun Z r z J₁ J₂ h₁ h₂ => ?_⟩
  rw [hτ Z r z J₁ J₂ h₁ h₂, map_pow, Units.val_pow_eq_pow_val]
  rfl

theorem sval_zero {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0)
    (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) : sval s r z J = 0 :=
  (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))

theorem zero_of_sval (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j) : s.f j = 0 := by
  refine fn_ext fun y hy => ?_
  obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
  rw [h y J hJ, mul_zero] at e
  exact e.trans ((gs_eq (𝟙 Y) y _ hy _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem sval_eq_of_id {Y₁ : Scheme.{0}} {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y₁ ⟶ X)} {ε' : K' → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} {s' : LB.Sec (LB.LinComb L φ' ε')}
    {p : Y' ⟶ Y} {p' : Y' ⟶ Y₁} (h : ∀ y J, Good L y J → sval s p y J = sval s' p' y J)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) : sval s (r ≫ p) z J = sval s' (r ≫ p') z J := by
  obtain ⟨h₀, h₁, -⟩ := values_natural X Y Y' Z L K φ ε p r z J hJ
  obtain ⟨-, h₂, -⟩ := values_natural X Y₁ Y' Z L K' φ' ε' p' r z J hJ
  rw [h₁, h₂, h _ _ h₀]

theorem sum_of_id {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {N : Type} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ₁ : N → K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : N → K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {τ : LB.Sec (LB.LinComb L φ ε)} {f : ∀ α, LB.Sec (LB.LinComb L (φ₁ α) ε₁)}
    {t : ∀ α, LB.Gen (LB.LinComb L (φ₂ α) ε₂)} {q : Y ⟶ Y'} {S : Finset N}
    (h : ∀ y J, Good L y J → sval τ (𝟙 Y) y J = ∑ α ∈ S, sval (f α) q y J * (val (t α) (𝟙 Y) y J).val)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval τ r z J = ∑ α ∈ S, sval (f α) (r ≫ q) z J * (val (t α) r z J).val := by
  obtain ⟨h₀, h₁, -⟩ := values_natural X Y Y Z L K φ ε (𝟙 Y) r z J hJ
  have a := h₁ τ
  rw [Category.comp_id, h _ _ h₀, map_sum] at a
  refine a.trans (Finset.sum_congr rfl fun α _ => ?_)
  have b := (values_natural X Y' Y Z L K₁ (φ₁ α) ε₁ q r z J hJ).2.1 (f α)
  have c := (values_natural X Y Y Z L K₂ (φ₂ α) ε₂ (𝟙 Y) r z J hJ).2.2.1 (t α)
  rw [Category.comp_id] at c
  rw [map_mul, b, c]

end General

section Levels
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

omit [GrpObj G] [IsCommMonObj G] in
theorem thickMap_fst (e : ℕ) : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_prBe (e : ℕ) : thickMap R I e D.P.A ≫ (D.prBe I (e + 1)).left = (D.prBe I e).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem pG_left {e : ℕ} (g : GtCoord I D e G) : g.pG.left = g.q.left ≫ (D.prBe I e).left := rfl

theorem q_thickMap (U : PreU I D A G) (e : ℕ) :
    (U.gt e).q.left ≫ thickMap R I e D.P.A = thickMap R I e G ≫ (U.gt (e + 1)).q.left := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg ((U.gt e).q.left ≫ ·) (thickMap_prBe e)).trans
      ((U.gt_q e).symm.trans (Category.assoc _ _ _).symm))
  · have a : (U.gt e).q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w (U.gt e).q
    have b : (U.gt (e + 1)).q.left ≫ pullback.snd D.P.A.hom (thick R I (e + 1)) =
      pullback.snd G.hom (thick R I (e + 1)) := Over.w (U.gt (e + 1)).q
    have c : ∀ H : Over (Spec (CommRingCat.of R)), thickMap R I e H ≫ pullback.snd H.hom (thick R I (e + 1)) =
      pullback.snd H.hom (thick R I e) ≫ thickTrans R I e := fun H => pullback.lift_snd _ _ _
    exact (Category.assoc _ _ _).trans ((congrArg ((U.gt e).q.left ≫ ·) (c _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ thickTrans R I e) a).trans ((c G).symm.trans
        ((congrArg (thickMap R I e G ≫ ·) b.symm).trans (Category.assoc _ _ _).symm)))))

theorem famφT_eq (T : Over (Spec (CommRingCat.of R))) (α : D.X) (i : Fin 4) :
    famφT D T α i = (snd T D.P.A).left ≫ D.famφB α i := by
  fin_cases i
  · exact (Category.comp_id _).symm
  · show (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    congr 1
    rw [padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · show (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A ≫ toUnit D.P.A ≫ D.c α).left
    congr 1
    simp
  · show (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A ≫ toUnit D.P.A ≫ η[D.P.A]).left
    congr 1
    simp

end Levels

theorem main : Laws → Laws2 → (AllPre fun U => ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U k hk σ
  have hB := D.P.isLB
  have hG := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ _) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]

  have lev : ∀ e : ℕ, ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => (U.gt e).pG.left) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left) (z : Z) JG J,
        Good U.P.L.L z JG → Good D.P.L z J →
        sval τ r z J = (gw (U.w e) r z (J (r ≫ (U.gt e).pG.left))
          (fun _ => JG (r ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left))).val ^ k *
          sval σ ((r ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) ≫ (λ_ G).inv.left) z JG := fun e => by
    obtain ⟨s, hs⟩ := exists_pull (φ' := fun _ : Fin 1 => (fstG (IsLocalRing.maximalIdeal V) e G).left)
      ((fstG (IsLocalRing.maximalIdeal V) e G).left ≫ (λ_ G).inv.left)
      (fun _ => by rw [Category.assoc, lam', Category.comp_id]) σ
    obtain ⟨τ, hτ⟩ := exists_carry hG hB (U.w e) (U.w_gen e) k s
    refine ⟨τ, fun Z r z JG J hJG hJ => (hτ Z r z JG J hJG hJ).trans (congrArg _ ((hs Z r z JG hJG).trans ?_))⟩
    exact congrArg (fun p => sval σ p z JG) (Category.assoc _ _ _).symm
  choose τ hτ using lev
  have ex := fun e => GlobalTheory.T.existsUnique_thickTorus_level_weight_expansion V _ D e G (U.gt e) k (τ e)
  choose f hf hu using ex
  choose S hS hsum using hf

  have compat : ∀ α e z J, Good D.P.L z J →
      sval (f (e + 1) α) (thickMap V _ e D.P.A) z J = sval (f e α) (𝟙 _) z J := by
    intro α e
    choose f' hf' using fun β => exists_pull
      (φ' := fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB β i) (thickMap V _ e D.P.A)
      (fun i => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.famφB β i) (thickMap_prBe e))).symm) (f (e + 1) β)
    have E : f' = f e := by
      refine hu e f' ⟨S (e + 1), fun β hβ => zero_of_sval hB fun y J hJ =>
        (hf' β _ _ y J hJ).trans (sval_zero (hS _ β hβ) _ hJ), fun z J hJ => ?_⟩
      obtain ⟨JG, hJG⟩ := exists_good_pt hG z
      have a := sum_of_id (hsum (e + 1)) (thickMap V _ e G) z hJ
      have b : sval (τ e) (𝟙 (thickObj V (IsLocalRing.maximalIdeal V) e G).left) z J =
          sval (τ (e + 1)) (thickMap V _ e G) z J := by
        refine (hτ e _ _ z JG J hJG hJ).trans (Eq.trans ?_ (hτ (e + 1) _ _ z JG J hJG hJ).symm)
        have c := U.w_compat e _ (𝟙 _) z _ _ (hJ (U.gt e).pG.left) (hJG (fstG (IsLocalRing.maximalIdeal V) e G).left)
        rw [Category.id_comp] at c
        rw [U.gt_q, thickMap_fst, c]
        simp only [Category.id_comp]
      refine b.trans (a.trans (Finset.sum_congr rfl fun β _ => congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
      · exact (congrArg (fun p => sval (f (e + 1) β) p z J) (q_thickMap U e).symm).trans (hf' β _ _ z J hJ).symm
      · exact ((congrArg (fun p => val ((U.gt (e + 1)).t β) p z J) (Category.id_comp _).symm).trans
          (val_pull hJ _ _ _).symm).trans (val_corr hJ (U.gt_t e β) _)
    intro z J hJ
    rw [← E]
    exact ((hf' α _ _ z J hJ).trans (congrArg (fun p => sval (f (e + 1) α) p z J) (Category.id_comp _))).symm
  choose s hs _ using fun α => GlobalTheory.T.existsUnique_twistedSection_of_compatible_levels h1 h2 V hV D k hk α (fun e => f e α) (compat α)
  choose F hF using fun α => exists_pull (snd (𝟙_ _) D.P.A).left (famφT_eq (𝟙_ _) α) (s α)
  refine ⟨F, fun e => ⟨S e, fun Z x rG rB hrG hrB _ z JG J hJG hJ => ?_⟩⟩
  have v : ∀ α, sval (F α) rB z J = sval (f e α) (x ≫ (U.gt e).q.left) z J := fun α => by
    refine (hF α _ _ z J hJ).trans ?_
    have a := sval_eq_of_id (hs α e) (x ≫ (U.gt e).q.left) z hJ
    refine Eq.trans (congrArg (fun p => sval (s α) p z J) (hrB.trans (Category.assoc _ _ _).symm)) (a.trans ?_)
    exact congrArg (fun p => sval (f e α) p z J) (Category.comp_id _)
  refine ⟨fun α hα => (v α).trans (sval_zero (hS e α hα) _ hJ), ?_⟩
  have r : rG = (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) ≫ (λ_ G).inv.left := by
    rw [← hrG, Category.assoc, lam, Category.comp_id]
  rw [r]
  refine (hτ e _ x z JG J hJG hJ).symm.trans ((sum_of_id (hsum e) x z hJ).trans ?_)
  exact Finset.sum_congr rfl fun α _ => congrArg (· * _) (v α).symm

end GlobalTheory.BaseExpansionExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfModelIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT

theorem exists_genericFibre_iso_of_model_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G') (ψ : G' ≅ G), IsMonHom ψ.hom → LBIso U'.LG.L (U.LG.L.pull ψ.hom.left) → ∃ φ : A'.A ≅ A.A, IsMonHom φ.hom ∧ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom = U'.gen.hom ≫ φ.hom ∧ LBIso A'.L (A.L.pull φ.hom.left) := by
  intro R _ _ I D D' A A' G G' _ _ _ _ U U' ψ hψ hL
  have := U.gen_hom
  have := U'.gen_hom
  have := hψ
  have hm : ((Over.pullback (jK R)).map ψ.hom).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ ψ.hom.left :=
    pullback.lift_fst _ _ _
  have hi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  refine ⟨U'.gen.symm ≪≫ (Over.pullback (jK R)).mapIso ψ ≪≫ U.gen, ?_, by simp, ?_⟩
  · show IsMonHom (U'.gen.inv ≫ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom)
    infer_instance
  · have h₁ : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))) :=
      LBIso.chartPull (chartPullSec A'.L _ U'.gen.inv.left hi)
        (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK R)) _ U'.gen.inv.left fun _ => rfl) U'.ext
    have h₂ : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)))
        (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ ψ.hom.left)) :=
      LBIso.chartPull (chartPullPull U'.LG.L _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => ψ.hom.left) _ _ fun _ => rfl) hL
    have h₃ : LBIso (A.L.pull (U'.gen.symm ≪≫ (Over.pullback (jK R)).mapIso ψ ≪≫ U.gen).hom.left)
        (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ ψ.hom.left)) :=
      LBIso.chartPull (h := U'.gen.inv.left ≫ ((Over.pullback (jK R)).map ψ.hom).left)
        (chartPullSame A.L _ (fun _ => U.gen.hom.left) _ _ fun _ => (Category.assoc _ _ _).symm)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ =>
          (Category.assoc _ _ _).trans ((congrArg (U'.gen.inv.left ≫ ·) hm.symm).trans (Category.assoc _ _ _).symm))
        U.ext
    exact LBIso.trans A'.isLB (pull_isLB U.LG.isLB _) (pull_isLB A.isLB _)
      (LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) h₁ h₂) h₃.symm

end GlobalTheory.UT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroupStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_addition_formula_group : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  first | exact @GlobalTheory.UU.exists_addG | exact GlobalTheory.UU.exists_addG | (intros; apply GlobalTheory.UU.exists_addG <;> assumption)
end

