import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.L2FiniteVolumePackageLawsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finVol_xiR_norm_and_cuspL2_of_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, VolTieG D → V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  first | exact @GlobalTheory.Member.finVol_and_cuspL2_of_pkgLaws | exact GlobalTheory.Member.finVol_and_cuspL2_of_pkgLaws | (intros; apply GlobalTheory.Member.finVol_and_cuspL2_of_pkgLaws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
  rw [this]
  exact continuous_snd.comp hc

theorem continuous_infPart (D : D7) : Continuous (infPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => (he z).1.symm
  rw [this]
  exact continuous_fst.comp hc

theorem continuous_finHom_val (D : D7) (V : HSp D) : Continuous (fun k : GA D V => (finHom V k).1) := by
  have h : Continuous (fun k : GA D V => (matHom V k).1) :=
    Units.continuous_val.comp continuous_subtype_val
  exact h.matrix_map (continuous_finPart D)

theorem latHat_open_and_continuous : ∀ (D : D7) (V : HSp D), (∀ N : ℕ, 0 < N → IsOpen {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E | ∃ y ∈ latHat V, z = N • y}) ∧ Continuous (fun k : GA D V => (finHom V k).1) ∧ Continuous (finPart D) ∧ Continuous (infPart D) := by
  intro D V
  refine ⟨?_, continuous_finHom_val D V, continuous_finPart D, continuous_infPart D⟩
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  rw [h1]
  exact (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E V.rank (latC V) h4).1

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndHalfEqPrimeProductStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_good_and_half_eq_prime_product : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H), (H.rt : D.host.E) = D.host.sqrtMinusD → l.M = D.host.g 0 * D.host.g 1 → (∀ p : ℕ, p.Prime → l.GoodAt p) ∧ ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧ l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  first | exact @GlobalTheory.LevelHalf.good_and_half_eq_prod | exact GlobalTheory.LevelHalf.good_and_half_eq_prod | (intros; apply GlobalTheory.LevelHalf.good_and_half_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LiftDatumAlternatingFormSignEqOneStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftDatum_alternatingForm_sign_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ), InR D j → (H.rt : D.host.E) = D.host.sqrtMinusD → H.rt0 = D.host.φ₀ D.host.sqrtMinusD → Dw.p = (D.R.sigW j).1 → Dw.q = (D.R.sigW j).2 → ∀ (φ : Dw.La →ₗ[𝓞 D.host.E] (D.sp.W j).V) (ε : ℤˣ), Function.Injective φ → Submodule.span D.host.E (Set.range φ) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 * (D.sp.W j).hT (φ x) (φ y))) → ε = 1 := by
  first | exact @GlobalTheory.Member.sign_eq_one | exact GlobalTheory.Member.sign_eq_one | (intros; apply GlobalTheory.Member.sign_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_adelicUnitary_eq_unitary : ∀ (D : D7) (V : HSp D), (∀ γ, γ ∈ GQ V ↔ ∃ γ', IsRat V γ γ') ∧ (∀ γ γ', IsRat V γ γ' → (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v)) ∧ (∀ γ' : GL (Fin V.rank) D.host.E, (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) → ∃ γ, IsRat V γ γ') ∧ (∀ γ γ' δ δ', IsRat V γ γ' → IsRat V δ δ' → IsRat V (γ * δ) (γ' * δ') ∧ IsRat V γ⁻¹ γ'⁻¹) ∧ ∀ γ γ', IsRat V γ γ' → (∀ v, (finHom V γ).1 *ᵥ finVec V v = finVec V ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)) ∧ ∀ τ θ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → archM V θ γ = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ := by
  first | exact @GlobalTheory.Member.RatElt.rational_elements | exact GlobalTheory.Member.RatElt.rational_elements | (intros; apply GlobalTheory.Member.RatElt.rational_elements <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmTypeStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realAdeles_cmField_equiv_complex_cmType : ∀ (D : D7), (∃ θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ))) ∧ ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧ Function.Bijective (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD}) => θ τ.1 z) := by
  first | exact @GlobalTheory.Member.infiniteAdele_bijective | exact GlobalTheory.Member.infiniteAdele_bijective | (intros; apply GlobalTheory.Member.infiniteAdele_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeLocallyTwoProjectiveFactors
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
noncomputable section
namespace GlobalTheory.CubeLocal

theorem trivAt_id_iff {X W : Scheme.{0}} (M : LB X) (r : W ⟶ X) :
    TrivAt M (fun _ : PUnit => 𝟙 X) (fun _ => 1) r ↔ Triv (M.pull r) := by
  unfold TrivAt
  simp only [Category.comp_id]

variable {S : Scheme.{0}} (X Y Z : Over S)

theorem exists_pair_chart {T : Scheme.{0}} (t : T ⟶ S) :
    ∃ m : ((Over.pullback t).obj X ⊗ (Over.pullback t).obj Y).left ⟶ (X ⊗ Y).left,
      IsPullback m ((Over.pullback t).obj X ⊗ (Over.pullback t).obj Y).hom (X ⊗ Y).hom t := by
  set B := (Over.pullback t).obj X
  set C := (Over.pullback t).obj Y
  have hB : IsPullback (pullback.fst X.hom t) B.hom X.hom t := IsPullback.of_hasPullback _ _
  have hC : IsPullback (pullback.fst Y.hom t) C.hom Y.hom t := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := IsPullback.of_hasPullback _ _
  have hBC : IsPullback (fst B C).left (snd B C).left B.hom C.hom := IsPullback.of_hasPullback _ _
  have ho : IsPullback ((fst B C).left ≫ pullback.fst X.hom t) (snd B C).left X.hom
      (pullback.fst Y.hom t ≫ Y.hom) := by
    rw [hC.w]; exact hBC.paste_horiz hB
  obtain ⟨m, m₁, m₂⟩ : ∃ m : (B ⊗ C).left ⟶ (X ⊗ Y).left,
      m ≫ (fst X Y).left = (fst B C).left ≫ pullback.fst X.hom t ∧
      m ≫ (snd X Y).left = (snd B C).left ≫ pullback.fst Y.hom t :=
    ⟨h2.lift _ _ (by rw [ho.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m (snd B C).left (snd X Y).left (pullback.fst Y.hom t) :=
    IsPullback.of_right (by rw [m₁]; exact ho) m₂ h2
  refine ⟨m, ?_⟩
  rw [← Over.w (snd B C), ← Over.w (snd X Y)]
  exact hm.paste_vert hC

theorem exists_triple_chart {T : Scheme.{0}} (j : T ⟶ Z.left) :
    ∃ q : ((Over.pullback (j ≫ Z.hom)).obj X ⊗ (Over.pullback (j ≫ Z.hom)).obj Y).left ⟶ (X ⊗ Y ⊗ Z).left,
      IsPullback q ((Over.pullback (j ≫ Z.hom)).obj X ⊗ (Over.pullback (j ≫ Z.hom)).obj Y).hom
        (snd X (Y ⊗ Z) ≫ snd Y Z).left j ∧
      q ≫ (fst X (Y ⊗ Z)).left =
        (fst _ _ : _ ⟶ (Over.pullback (j ≫ Z.hom)).obj X).left ≫ pullback.fst X.hom (j ≫ Z.hom) ∧
      q ≫ (snd X (Y ⊗ Z) ≫ fst Y Z).left =
        (snd _ _ : _ ⟶ (Over.pullback (j ≫ Z.hom)).obj Y).left ≫ pullback.fst Y.hom (j ≫ Z.hom) := by
  set B := (Over.pullback (j ≫ Z.hom)).obj X
  set C := (Over.pullback (j ≫ Z.hom)).obj Y
  have hB : IsPullback (pullback.fst X.hom (j ≫ Z.hom)) B.hom X.hom (j ≫ Z.hom) := IsPullback.of_hasPullback _ _
  have hC : IsPullback (pullback.fst Y.hom (j ≫ Z.hom)) C.hom Y.hom (j ≫ Z.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst Y Z).left (snd Y Z).left Y.hom Z.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst X (Y ⊗ Z)).left (snd X (Y ⊗ Z)).left X.hom (Y ⊗ Z).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B C).left (snd B C).left B.hom C.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : C.left ⟶ (Y ⊗ Z).left, m ≫ (fst Y Z).left = pullback.fst Y.hom (j ≫ Z.hom) ∧
      m ≫ (snd Y Z).left = C.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hC.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m C.hom (snd Y Z).left j := IsPullback.of_right (by rw [m₁]; exact hC) m₂ h2
  have mw : m ≫ (Y ⊗ Z).hom = C.hom ≫ j ≫ Z.hom := by
    rw [← Over.w (snd Y Z), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B C).left ≫ pullback.fst X.hom (j ≫ Z.hom)) (snd B C).left X.hom
      (m ≫ (Y ⊗ Z).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ C).left ⟶ (X ⊗ Y ⊗ Z).left,
      q ≫ (fst X (Y ⊗ Z)).left = (fst B C).left ≫ pullback.fst X.hom (j ≫ Z.hom) ∧
      q ≫ (snd X (Y ⊗ Z)).left = (snd B C).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B C).left (snd X (Y ⊗ Z)).left m := IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B C)]
    exact hq.paste_vert hm
  · show q ≫ (snd X (Y ⊗ Z)).left ≫ (fst Y Z).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]

variable {X Y Z}

theorem coord_eq {P A : Over S} {W : Scheme.{0}} (r : W ⟶ P.left) (c : P ⟶ A) (a : 𝟙_ (Over S) ⟶ A)
    (b : W ⟶ S) (h : r ≫ c.left = b ≫ a.left) :
    (Over.homMk r rfl : Over.mk (r ≫ P.hom) ⟶ P) ≫ c = toUnit _ ≫ a := by
  have hb : b = r ≫ P.hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  apply Over.OverMorphism.ext
  exact h.trans (by rw [hb]; rfl)

theorem trivAt_of_factor {P F T : Over S} {M : LB P.left} {i : F ⟶ P} (H : Triv (M.pull i.left))
    (x : T ⟶ P) (h : T ⟶ F) (e : h ≫ i = x) :
    TrivAt M (fun _ : PUnit => 𝟙 P.left) (fun _ => 1) x.left := by
  subst e
  exact ((trivAt_id_iff M i.left).2 H).comp h.left

theorem trivAt_face₁ {x₀ : 𝟙_ (Over S) ⟶ X} {M : LB (X ⊗ Y ⊗ Z).left}
    (H : Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left)) {W : Scheme.{0}}
    (r : W ⟶ (X ⊗ Y ⊗ Z).left) (b : W ⟶ S) (h : r ≫ (fst X (Y ⊗ Z)).left = b ≫ x₀.left) :
    TrivAt M (fun _ : PUnit => 𝟙 _) (fun _ => 1) r := by
  let x : Over.mk (r ≫ (X ⊗ Y ⊗ Z).hom) ⟶ X ⊗ Y ⊗ Z := Over.homMk r rfl
  have e : x ≫ _ = _ := coord_eq r _ x₀ b h
  refine trivAt_of_factor H x (x ≫ snd _ _) ?_
  clear_value x
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [e]
  · simp

theorem trivAt_face₂ {y₀ : 𝟙_ (Over S) ⟶ Y} {M : LB (X ⊗ Y ⊗ Z).left}
    (H : Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left)) {W : Scheme.{0}}
    (r : W ⟶ (X ⊗ Y ⊗ Z).left) (b : W ⟶ S) (h : r ≫ (snd X (Y ⊗ Z) ≫ fst Y Z).left = b ≫ y₀.left) :
    TrivAt M (fun _ : PUnit => 𝟙 _) (fun _ => 1) r := by
  let x : Over.mk (r ≫ (X ⊗ Y ⊗ Z).hom) ⟶ X ⊗ Y ⊗ Z := Over.homMk r rfl
  have e : x ≫ _ = _ := coord_eq r _ y₀ b h
  refine trivAt_of_factor H x (lift (x ≫ fst _ _) (x ≫ snd _ _ ≫ snd _ _)) ?_
  clear_value x
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
  · simp
  · simp [e]
  · simp

theorem trivAt_face₃ {z₀ : 𝟙_ (Over S) ⟶ Z} {M : LB (X ⊗ Y ⊗ Z).left}
    (H : Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left)) {W : Scheme.{0}}
    (r : W ⟶ (X ⊗ Y ⊗ Z).left) (b : W ⟶ S) (h : r ≫ (snd X (Y ⊗ Z) ≫ snd Y Z).left = b ≫ z₀.left) :
    TrivAt M (fun _ : PUnit => 𝟙 _) (fun _ => 1) r := by
  let x : Over.mk (r ≫ (X ⊗ Y ⊗ Z).hom) ⟶ X ⊗ Y ⊗ Z := Over.homMk r rfl
  have e : x ≫ _ = _ := coord_eq r _ z₀ b h
  refine trivAt_of_factor H x (lift (x ≫ fst _ _) (x ≫ snd _ _ ≫ fst _ _)) ?_
  clear_value x
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
  · simp
  · simp
  · simp [e]

theorem geometricallyConnected_of_integral {A B : Scheme.{0}} (f : A ⟶ B) [GeometricallyIntegral f] :
    GeometricallyConnected f :=
  ⟨fun _ _ y W a b h => by
    have : IsIntegral W := GeometricallyIntegral.geometrically_isIntegral y a b h
    infer_instance⟩

theorem exists_section_baseChange {T : Scheme.{0}} (t : T ⟶ S) {A : Over S} (a : 𝟙_ (Over S) ⟶ A) :
    ∃ a' : 𝟙_ (Over T) ⟶ (Over.pullback t).obj A, ∀ W : Over T,
      (toUnit W ≫ a').left ≫ pullback.fst A.hom t = (W.hom ≫ t) ≫ a.left := by
  have w : (t ≫ a.left) ≫ A.hom = 𝟙 T ≫ t := by
    rw [Category.assoc, Over.w]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  refine ⟨Over.homMk (pullback.lift (t ≫ a.left) (𝟙 T) w) (pullback.lift_snd _ _ _), fun W => ?_⟩
  change (W.hom ≫ pullback.lift (t ≫ a.left) (𝟙 T) w) ≫ _ = _
  rw [Category.assoc, pullback.lift_fst, Category.assoc]

theorem bijective_appTop_baseChange {k : Type} [Field k] (A : Over (Sp k)) (a : 𝟙_ (Over (Sp k)) ⟶ A)
    (hp : IsProper A.hom) (hi : GeometricallyIntegral A.hom) {R : Type} [CommRing R]
    {t : Spec (CommRingCat.of R) ⟶ Sp k} {W : Scheme.{0}} {m : W ⟶ A.left} {f : W ⟶ Spec (CommRingCat.of R)}
    (H : IsPullback m f A.hom t) (R' : Type) [CommRing R'] (g : R →+* R') (W' : Scheme.{0}) (π : W' ⟶ W)
    (f' : W' ⟶ Spec (CommRingCat.of R')) (H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
    Function.Bijective f'.appTop.hom := by
  obtain ⟨g₀, hg⟩ := Spec.map_surjective (Spec.map (CommRingCat.ofHom g) ≫ t)
  have := H'.paste_horiz H
  rw [← hg] at this
  exact GlobalTheory.UniversalConstants.bijective_appTop_baseChange k A a hp hi R' g₀.hom W' _ f' this

theorem triv_locally_of_faces :
    ∀ (k : Type) [Field k] (X Y Z : Over (Sp k)) (x₀ : 𝟙_ (Over (Sp k)) ⟶ X) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (z₀ : 𝟙_ (Over (Sp k)) ⟶ Z), Smooth X.hom → Smooth Y.hom → IsProper X.hom → IsProper Y.hom → IsProjBy X.hom → IsProjBy Y.hom → GeometricallyIntegral X.hom → GeometricallyIntegral Y.hom → ConnectedSpace Z.left → ∀ M : LB (X ⊗ Y ⊗ Z).left, M.IsLB → Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) → Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left) → Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left) → ∀ z : Z.left, ∃ V : Z.left.Opens, z ∈ V ∧ Triv (M.pull ((snd X (Y ⊗ Z) ≫ snd Y Z).left ⁻¹ᵁ V).ι) := by
  intro k _ X Y Z x₀ y₀ z₀ sX sY pX pY jX jY iX iY cZ M hM f₁ f₂ f₃
  have smXY : Smooth (X ⊗ Y).hom := by
    change Smooth (pullback.fst X.hom Y.hom ≫ X.hom); infer_instance
  have prXY : IsProper (X ⊗ Y).hom := by
    change IsProper (pullback.fst X.hom Y.hom ≫ X.hom); infer_instance
  have gcXY : GeometricallyConnected (X ⊗ Y).hom := by
    change GeometricallyConnected (pullback.fst X.hom Y.hom ≫ X.hom)
    have := geometricallyConnected_of_integral X.hom
    have := geometricallyConnected_of_integral Y.hom
    exact GeometricallyConnected.comp _ _
  have giXY : GeometricallyIntegral (X ⊗ Y).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ smXY gcXY
  have H := fibTriv_clopen M (fun _ : PUnit => 𝟙 _) (fun _ => 1) (snd X (Y ⊗ Z) ≫ snd Y Z).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_triple_chart X Y Z j
    obtain ⟨m, hm⟩ := exists_pair_chart X Y (j ≫ Z.hom)
    obtain ⟨x₁, hx⟩ := exists_section_baseChange (j ≫ Z.hom) x₀
    obtain ⟨y₁, hy⟩ := exists_section_baseChange (j ≫ Z.hom) y₀
    let B := (Over.pullback (j ≫ Z.hom)).obj X
    let C := (Over.pullback (j ≫ Z.hom)).obj Y
    have hB : IsPullback (pullback.fst X.hom (j ≫ Z.hom)) B.hom X.hom (j ≫ Z.hom) := IsPullback.of_hasPullback _ _
    have hC : IsPullback (pullback.fst Y.hom (j ≫ Z.hom)) C.hom Y.hom (j ≫ Z.hom) := IsPullback.of_hasPullback _ _
    have sB : Smooth B.hom := MorphismProperty.of_isPullback hB sX
    have sC : Smooth C.hom := MorphismProperty.of_isPullback hC sY
    have pB : IsProper B.hom := MorphismProperty.of_isPullback hB pX
    have pC : IsProper C.hom := MorphismProperty.of_isPullback hC pY
    have sm : Smooth (B ⊗ C).hom := MorphismProperty.of_isPullback hm smXY
    have pr : IsProper (B ⊗ C).hom := MorphismProperty.of_isPullback hm prXY
    have gi : GeometricallyIntegral (B ⊗ C).hom := MorphismProperty.of_isPullback hm giXY
    have pj : IsProjBy (B ⊗ C).hom := by
      obtain ⟨g₀, hg⟩ := Spec.map_surjective (j ≫ Z.hom)
      have hm' := hm
      conv at hm' => arg 4; rw [← hg]
      exact GlobalTheory.AbLaw.isProjBy_baseChange k R g₀.hom _ _ _ _ _ hm' (GlobalTheory.AbLaw.isProjBy_tensor k X Y jX jY)
    have hN : (LB.LinComb M (fun _ : PUnit => q ≫ 𝟙 _) (fun _ => 1)).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy R _ _ sm pj
    refine ⟨_, q, (B ⊗ C).hom, hq,
      GlobalTheory.TrivLocus.isClosed_trivLocus R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr gi,
      fun F _ g W π f' => GlobalTheory.T.lineBundle_trivial_basicOpen_of_trivial_fibre_product R B C x₁ y₁ inferInstance inferInstance pB pC
        (bijective_appTop_baseChange X x₀ pX iX hB) (bijective_appTop_baseChange Y y₀ pY iY hC)
        (bijective_appTop_baseChange (X ⊗ Y) (lift x₀ y₀) prXY giXY hm) _ hN (pf _ hN) ?_ ?_ F g W π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_face₂ f₂ _ (B.hom ≫ j ≫ Z.hom) ?_
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact hy B
    · rw [triv_pull_comp_iff]
      refine trivAt_face₁ f₁ _ (C.hom ≫ j ≫ Z.hom) ?_
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact hx C)
  have hclopen : IsClopen (fibTriv M (fun _ : PUnit => 𝟙 _) (fun _ => 1) (snd X (Y ⊗ Z) ≫ snd Y Z).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have ne : (fibTriv M (fun _ : PUnit => 𝟙 _) (fun _ => 1) (snd X (Y ⊗ Z) ≫ snd Y Z).left).Nonempty := by
    let g : Spec (CommRingCat.of k) ⟶ Z.left := z₀.left
    refine ⟨g (default : PrimeSpectrum k), k, inferInstance, g, _, _, _, ⟨_, rfl⟩,
      IsPullback.of_hasPullback (snd X (Y ⊗ Z) ≫ snd Y Z).left g, ?_⟩
    exact trivAt_face₃ f₃ _ (pullback.snd _ g) pullback.condition
  intro z
  obtain ⟨V, hV, hT⟩ := H.1 ((hclopen.eq_univ ne).ge (Set.mem_univ z))
  exact ⟨V, hV, (trivAt_id_iff M _).1 hT⟩

end GlobalTheory.CubeLocal
end
end

