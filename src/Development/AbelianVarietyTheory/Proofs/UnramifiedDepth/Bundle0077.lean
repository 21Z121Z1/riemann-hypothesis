import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0075
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0076

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPHomomorphismCubicalWeilTrivialRationalTors
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

def unitsOfΓ {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (A : Type) [CommRing A] [Algebra Ω A] :
    Γ((overAt s A).left, ⊤)ˣ →* Aˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom

theorem unitsOfΓ_injective {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (A : Type) [CommRing A]
    [Algebra Ω A] : Function.Injective (unitsOfΓ s A) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1

theorem unitsOfΓ_natural {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) {A B : Type} [CommRing A]
    [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (ζ : Γ((overAt s A).left, ⊤)ˣ) :
    unitsOfΓ s B (Units.map (homAt s f).left.appTop.hom.toMonoidHom ζ) = Units.map (f : A →* B) (unitsOfΓ s A ζ) := by
  have h₁ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* B))
  exact Units.ext (congrArg (fun φ => φ.hom ζ.val) h₁)

theorem cubWeil_alpha_rational : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (g : Fam s G), IsAlpha p s G g → ∀ x : overAt s Ω ⟶ G, x ^ p = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) 1 := by
  intro Ω _ p _ _ S s G _ _ L c g hg x hx
  classical
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hex : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), ∃ ζ : Γ((overAt s A).left, ⊤)ˣ,
      a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) ζ := by
    intro A _ _ a
    by_cases ha : a ^ p = 0
    · obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c (hg.pow_eq_one hp ha)
        (y := homAt s (Algebra.ofId Ω A) ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      exact ⟨ζ, fun _ => hζ⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose ζ hζ using hex
  intro A _ _ a ha
  have key := GlobalTheory.T.alphaP_multiplicativeCharacter_eq_one Ω p (fun A _ _ a => unitsOfΓ s A (ζ A a)) ?_ ?_ A a ha
  · have : ζ A a = 1 := unitsOfΓ_injective s A (key.trans (map_one _).symm)
    exact this ▸ hζ A a ha
  · intro A B _ _ _ _ f a ha
    beta_reduce
    have hb : f a ^ p = 0 := by rw [← map_pow, ha, map_zero]
    have h₁ := (hζ A a ha).comp (homAt s f)
    rw [← hg.1 A B f a ha, ← Category.assoc, hom_comp, Subsingleton.elim (f.comp (Algebra.ofId Ω A)) (Algebra.ofId Ω B)] at h₁
    rw [(hζ B (f a) hb).unique h₁, unitsOfΓ_natural]
  · intro A _ _ a a' ha ha'
    beta_reduce
    have hs : (a + a') ^ p = 0 := by
      rcases subsingleton_or_nontrivial A with _ | _
      · exact Subsingleton.elim _ _
      · haveI : CharP A p := charP_of_injective_algebraMap (algebraMap Ω A).injective p
        rw [add_pow_char, ha, ha', add_zero]
    have h₁ := (hζ A a ha).mul_left (hζ A a' ha')
    rw [← hg.2 A a a' ha ha'] at h₁
    rw [(hζ A (a + a') hs).unique h₁, map_mul]

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChartPointNilpotentCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalChart_point_nilpotent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), IsChartG t (𝟙 (Sp V)) d F act tg uv x → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω), ∃ P : PtFam (spMap β) t.G d, IsJetPt β x P ∧ IsPtLaw (spMap β) t.G (fun j => MvPowerSeries.map β (F j)) P := by
  first | exact @GlobalTheory.AlphaPair.exists_jetPt | exact GlobalTheory.AlphaPair.exists_jetPt | (intros; apply GlobalTheory.AlphaPair.exists_jetPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGeneratorOfRosatiAdjointLambdaBundleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_of_rosatiAdjoint_lambdaBundle : ∀ (O : Type) [CommRing O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)) (Z : Scheme.{0}) (Q : LB Z) (ψ₂ : (P.A ⊗ P.A).left ⟶ Z), Q.IsLB → Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) → ∀ f f' : P.A ⟶ P.A, IsMonHom f → IsMonHom f' → Out.RosatiAdj P.A P.L f f' → ∃ t : LB.Gen (LB.LinComb Q (K := Fin 2) ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]), t.IsGen := by
  first | exact @GlobalTheory.RosGen.exists_gen_of_rosatiAdj | exact GlobalTheory.RosGen.exists_gen_of_rosatiAdj | (intros; apply GlobalTheory.RosGen.exists_gen_of_rosatiAdj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairsStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_adjoint_projectors_placePairs : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o)), (∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' → ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0) → ∃ M : Orb → Fin 2 → Matrix (Fin dd) (Fin dd) C, (∀ o, IsEnd (Y.raw (p o)) V (M o 0) (M o 1) ∧ IsEnd (Y.raw (p o)) V (M o 1) (M o 0)) ∧ (∀ o g c, (M o g).mulVec ((p o).u g c) = (p o).u g c) ∧ (∀ o g o' g' c, (o, g) ≠ (o', g') → (M o g).mulVec ((p o').u g' c) = 0) ∧ ∀ o g v, ∃ b : I o g → C, (M o g).mulVec v = ∑ c, b c • (p o).u g c := by
  first | exact @GlobalTheory.PlaceProj.exists_orth_proj | exact GlobalTheory.PlaceProj.exists_orth_proj | (intros; apply GlobalTheory.PlaceProj.exists_orth_proj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusExtension_points_pullback_fieldPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S) (t' : SAB H S') (_ : SABMap t' t f) (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S'), s' ≫ f = s → ∀ n : ℕ, ∃ (τ : PtHom s s' t.G t'.G) (io : TorHom s t.G PUnit), IsTorExt s s' t.G t'.G PUnit τ io ∧ Transfer n t.cub t'.cub τ := by
  first | exact @GlobalTheory.AlphaPair.exists_isTorExt_pull | exact GlobalTheory.AlphaPair.exists_isTorExt_pull | (intros; apply GlobalTheory.AlphaPair.exists_isTorExt_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FramePartialLawsNilpotentCoordinates
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.Cube

section Alg

variable {V Ω A : Type} [CommRing V] [CommRing Ω] [CommRing A] [Algebra Ω A] {β : V →+* Ω} {m d : ℕ}

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem cc_psIn {n n' : ℕ} (r : Fin n → Fin n') (f : PS V n d) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.constantCoeff (psIn d m r f) = 0 := by
  rw [psIn, MvPolynomial.constantCoeff_rename, psTrunc, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [MvPolynomial.constantCoeff_monomial]
  split_ifs with h
  · subst h; simpa using hf
  · rfl

theorem subst_X {κ κ' : Type} (φ : κ → MvPolynomial κ' V) (i : κ) (h : MvPolynomial.constantCoeff (φ i) = 0) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = Ideal.Quotient.mk _ (φ i) := by
  simp only [jetSubstP, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X, h, map_zero, sub_zero]

theorem map_psIn {n n' : ℕ} (ψ : Jet V (Fin n' × Fin d) m →+* A)
    (hψ : ∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) (r : Fin n → Fin n') (f : PS V n d) :
    ψ (Ideal.Quotient.mk _ (psIn d m r f)) =
      evP (fun i j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X (r i, j)))) (MvPowerSeries.map β f) := by
  let g : Jet V (Fin n × Fin d) m →ₐ[V] Jet V (Fin n' × Fin d) m :=
    jetMap (fun p => MvPolynomial.X (r p.1, p.2)) fun _ => X_mem_orig _
  have h := ((GlobalTheory.T.jetRing_hom_exists_unique_spec V Ω A β (Fin n × Fin d) m).2 (ψ.comp g) (fun v => by
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes, hψ])).2.2 f
  simp only [g, psJet, RingHom.comp_apply, RingHom.coe_coe, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X] at h
  rw [evP, ← h, psIn, MvPolynomial.rename_eq_aeval]
  rfl

theorem gm_unit {B : Type} [CommRing B] (ψ : B →+* A) (z : Sp A) (u : Bˣ) :
    (gm (spMap ψ) z ⊤ (unitΓ u)).val = gs (𝟙 (Sp A)) z ⊤ (toΓ A (ψ u)) := by
  rw [gm_val _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
  have h := congrArg (fun q => q.hom (u : B)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  exact congrArg ((Sp A).presheaf.germ ⊤ z trivial).hom h.symm

end Alg

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] {t : SAB H (Sp V)}
  {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {Ω : Type} [Field Ω] {β : V →+* Ω}
  {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ}

def ptOf {n : ℕ} (ψ : Jet V (Fin n × Fin d) m →+* A) (hψ : ∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) :
    overAt (spMap β) A ⟶ jOG (𝟙 (Sp V)) d m n :=
  Over.homMk (spMap ψ) (by
    change spMap ψ ≫ spMap _ ≫ 𝟙 _ = spMap _ ≫ spMap β
    rw [Category.comp_id, spMap_spMap, spMap_spMap]
    exact congrArg spMap (RingHom.ext hψ))

theorem ptOf_jpt {P : PtFam (spMap β) t.G d} (hP : IsJetPt β x P) {n : ℕ} (ψ : Jet V (Fin n × Fin d) m →+* A)
    (hψ : ∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) (i : Fin n) :
    ptOf ψ hψ ≫ jptG t (𝟙 _) d x m i = P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) := by
  have h := hP A m (ψ.comp (jetCopy d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m)) (fun v => by
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes, hψ])
  simp only [jetCopy, RingHom.comp_apply, RingHom.coe_coe, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X] at h
  ext1
  rw [h, ← spMap_spMap, Category.assoc]
  rfl

theorem exists_val (β : V →+* Ω) (e : FrTyG t (𝟙 (Sp V)) d x m) (z : Sp A) (J : (Sp A ⟶ t.G.left) → t.PP.L.ι) :
    ∃ e' : (Fin d → A) → (Fin d → A) → ((Sp A).presheaf.stalk z)ˣ,
      ∀ ψ : Jet V (Fin 2 × Fin d) m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) →
        ∀ a u : Fin d → A, (∀ j, ψ (Ideal.Quotient.mk _ (MvPolynomial.X (0, j))) = a j) →
          (∀ j, ψ (Ideal.Quotient.mk _ (MvPolynomial.X (1, j))) = u j) →
          val (L := t.PP.L) (φ := cφG t ![jptG t (𝟙 _) d x m (0 : Fin 2), jptG t (𝟙 _) d x m (1 : Fin 2)])
            (ε := cε 2) e (spMap ψ) z J = e' a u := by
  classical
  let Q : (Fin d → A) → (Fin d → A) → (Jet V (Fin 2 × Fin d) m →+* A) → Prop := fun a u ψ =>
    (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) ∧
      ∀ q : Fin 2 × Fin d, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) = ![a, u] q.1 q.2
  refine ⟨fun a u => if h : ∃ ψ, Q a u ψ then
    val (L := t.PP.L) (φ := cφG t ![jptG t (𝟙 _) d x m (0 : Fin 2), jptG t (𝟙 _) d x m (1 : Fin 2)])
      (ε := cε 2) e (spMap h.choose) z J else 1, fun ψ hψ a u ha hu => ?_⟩
  have hQ : Q a u ψ := ⟨hψ, by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [ha j, hu j]⟩
  have h : ∃ ψ, Q a u ψ := ⟨ψ, hQ⟩
  have k : h.choose = ψ := Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext
    (fun v => (h.choose_spec.1 v).trans (hψ v).symm) fun q => (h.choose_spec.2 q).trans (hQ.2 q).symm)
  simp only [dif_pos h, k]

theorem val_pe (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) {z : Sp A} {J : (Sp A ⟶ t.G.left) → t.PP.L.ι}
    (hJ : Good t.PP.L z J) {n : ℕ} (ψ : Jet V (Fin n × Fin d) m →+* A)
    (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) V) :
    val (peG t (𝟙 _) d x e m φ) (spMap ψ) z J =
      val (L := t.PP.L) (φ := cφG t ![jptG t (𝟙 _) d x m (0 : Fin 2), jptG t (𝟙 _) d x m (1 : Fin 2)])
        (ε := cε 2) (e m) (spMap (ψ.comp (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2 :
          Jet V (Fin 2 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m))) z J := by
  rw [← spMap_spMap]
  exact val_pull hJ _ _ _

end Frame

theorem isPtCube_of_isFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), IsFrameG t (𝟙 (Sp V)) d x F act ph1 ph2 sy ad e → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtCube (spMap β) t.G t.cub (fun j => MvPowerSeries.map β (F j)) (MvPowerSeries.map β ph1) (MvPowerSeries.map β ph2) P := by
  intro E _ _ _ H V _ t d F act ph1 ph2 sy ad x e hfr hF Ω _ β P hP A _ _ I hI z J hJ
  obtain ⟨m, hm⟩ := id hI
  have hm' : I ^ (m + 1) = ⊥ := by rw [pow_succ, hm, zero_mul]; rfl
  obtain ⟨e', he'⟩ := exists_val (A := A) β (e m) z J
  refine ⟨e', fun a b u ha hb hu => ?_⟩
  obtain ⟨ψ, ⟨hψ, hX⟩, -⟩ := (GlobalTheory.T.jetRing_hom_exists_unique_spec V Ω A β (Fin 3 × Fin d) m).1 (fun q => ![a, b, u] q.1 q.2) (by
    refine le_bot_iff.1 (le_trans (Ideal.pow_right_mono (Ideal.span_le.2 ?_) _) hm'.le)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    fin_cases i
    exacts [ha j, hb j, hu j])
  have hpe : ∀ (φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) (v w : Fin d → A),
      (∀ i j, MvPolynomial.constantCoeff (φ i j) = 0) → (∀ j, ψ (Ideal.Quotient.mk _ (φ 0 j)) = v j) →
      (∀ j, ψ (Ideal.Quotient.mk _ (φ 1 j)) = w j) → val (peG t (𝟙 _) d x e m φ) (spMap ψ) z J = e' v w :=
    fun φ v w h h₀ h₁ => (val_pe e hJ ψ φ).trans (he' _
      (fun v => by simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes, hψ]) v w
      (fun j => (congrArg ψ (subst_X (fun p : Fin 2 × Fin d => φ p.1 p.2) (0, j) (h 0 j))).trans (h₀ j))
      (fun j => (congrArg ψ (subst_X (fun p : Fin 2 × Fin d => φ p.1 p.2) (1, j) (h 1 j))).trans (h₁ j)))
  have hXX : ∀ i k : Fin 3, val (peG t (𝟙 _) d x e m ![fun j => MvPolynomial.X (i, j), fun j => MvPolynomial.X (k, j)])
      (spMap ψ) z J = e' (![a, b, u] i) (![a, b, u] k) := fun i k =>
    hpe _ _ _ (fun l j => by fin_cases l <;> simp) (fun j => hX (i, j)) (fun j => hX (k, j))
  have hadd : ∀ (i k : Fin 3) (j : Fin d), ψ (Ideal.Quotient.mk _ (psIn d m ![i, k] (F j))) =
      addP (fun j => MvPowerSeries.map β (F j)) (![a, b, u] i) (![a, b, u] k) j := fun i k j => by
    rw [map_psIn ψ hψ, addP]
    congr 1
    funext l j'
    rw [hX]
    fin_cases l <;> rfl
  have hpt : ∀ i : Fin 3, ptOf ψ hψ ≫ jptG t (𝟙 _) d x m i = P A (![a, b, u] i) := fun i => by
    rw [ptOf_jpt hP]
    exact congrArg (P A) (funext fun j => hX (i, j))
  have hsc : ∀ (ph : PS V 3 d) (w : (Jet V (Fin 3 × Fin d) m)ˣ), (w : Jet V (Fin 3 × Fin d) m) = psJet m ph →
      (gm (spMap ψ) z ⊤ (unitΓ w)).val =
        gs (𝟙 (Sp A)) z ⊤ (toΓ A (evP ![a, b, u] (MvPowerSeries.map β ph))) := fun ph w hw => by
    rw [gm_unit, hw, ((GlobalTheory.T.jetRing_hom_exists_unique_spec V Ω A β (Fin 3 × Fin d) m).2 ψ hψ).2.2 ph, evP]
    simp only [hX]
  constructor
  · obtain ⟨w, hw, hc⟩ := hfr.ph1 m
    have k := (val_cub t.cub (ptOf ψ hψ) hJ _ _ _).symm.trans ((val_corr hJ hc (spMap ψ)).trans
      ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (hpe _ _ _ (fun l j => by fin_cases l; exacts [cc_psIn _ _ (hF j), MvPolynomial.constantCoeff_X _ _])
          (hadd 0 1) (fun j => hX (2, j)))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (hXX 0 2)))
          ((val_inv _ _).trans (congrArg (·⁻¹) (hXX 1 2))))))))))
    rw [hpt, hpt, hpt] at k
    have k' : cubV t.cub z J (P A a) (P A b) (P A u) = gm (spMap ψ) z ⊤ (unitΓ w) *
      (e' (addP (fun j => MvPowerSeries.map β (F j)) a b) u * ((e' a u)⁻¹ * (e' b u)⁻¹)) := k
    refine Eq.trans ?_ (congrArg (· * _) (hsc ph1 w hw))
    refine Eq.trans (congrArg Units.val ?_) (Units.val_mul _ _)
    rw [k']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · obtain ⟨w, hw, hc⟩ := hfr.ph2 m
    have k := (val_cub t.cub (ptOf ψ hψ) hJ _ _ _).symm.trans ((val_corr hJ hc (spMap ψ)).trans
      ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (hpe _ _ _ (fun l j => by fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, cc_psIn _ _ (hF j)])
          (fun j => hX (0, j)) (hadd 1 2))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (hXX 0 1)))
          ((val_inv _ _).trans (congrArg (·⁻¹) (hXX 0 2))))))))))
    rw [hpt, hpt, hpt] at k
    have k' : cubV t.cub z J (P A b) (P A u) (P A a) = gm (spMap ψ) z ⊤ (unitΓ w) *
      (e' a (addP (fun j => MvPowerSeries.map β (F j)) b u) * ((e' a b)⁻¹ * (e' a u)⁻¹)) := k
    refine Eq.trans ?_ (congrArg (· * _) (hsc ph2 w hw))
    refine Eq.trans (congrArg Units.val ?_) (Units.val_mul _ _)
    rw [k']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.AlphaPair.Cube
end
end

