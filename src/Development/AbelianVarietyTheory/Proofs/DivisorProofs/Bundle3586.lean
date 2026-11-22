import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3579
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3527
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3541

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingInd
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace GlobalTheory.EtC.GmStep

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem cechC_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] {R : Type} [CommRing R] (F : Shv R) (s : ℤ)
    (k : ℕ) (j : Fin (k + 2)) (y : H R (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) F s) :
    pull R (disc.map ((cechC A A').app (op ⦋k + 1⦌))) F s (pull R (disc.map ((cech (baseHom A A')).δ j)) F s y) =
      pull R (disc.map ((cech (laurentHom A A')).δ j)) F s (pull R (disc.map ((cechC A A').app (op ⦋k⦌))) F s y) := by
  simp only [SimplicialObject.δ]
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, (cechC A A').naturality]

theorem aug_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ) (j : Fin (k + 2)) :
    disc.map ((cech (laurentHom A A')).δ j) ≫ augK A A' k = augK A A' (k + 1) := by
  have h := (cechAug (laurentHom A A')).naturality (SimplexCategory.δ j).op
  exact (disc.map_comp _ _).symm.trans (congrArg disc.map (h.trans (Category.comp_id _)))

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem rowExact_base (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Finite A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A)
    (j : ℤ) (p : ℕ) : RowExact (ZMod q) (cech (baseHom A A')) (tw q j) 0 p := by
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI, hS⟩ := spec_integral_surj (algebraMap A A') hint hker
  have hB := @GlobalTheory.EtC.b4 q _ _ (baseHom A A') hI hS (isUnit_gamma q A hq) j
  refine GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic (ZMod q) (tw q j) _ (fun k s hs => GlobalTheory.T.cech_cohomology_vanishes_positive q A hA hq A' inferInstance k s j hs) (fun m hm => ?_) p
  haveI : Subsingleton (H (ZMod q) (sch.obj (Spec (CommRingCat.of A))) (tw q j) m) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) m hm
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (hB m).2 a
    obtain ⟨b', rfl⟩ := (hB m).2 b
    rw [Subsingleton.elim a' b']⟩

theorem gm_vanishing_step : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  intro q _ n hn IH A _ _ hA hq i
  suffices h : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨A', _, _, hfin, hker, hx⟩ := GlobalTheory.T.laurent_cohomology_finite_killing q A hA hq n i hn x
  haveI := hfin
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI', hS'⟩ := spec_integral_surj _ (laurentMap_isIntegral _ hint) (laurentMap_ker _ hker)
  have hqL : IsUnit (q : LaurentPolynomial A) := by simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  have hB := @GlobalTheory.EtC.b4 q _ _ (laurentHom A A') hI' hS' (isUnit_gamma q _ hqL) i
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
  apply (hB N).1
  rw [map_zero]
  obtain ⟨Δ, hΔ0, hΔ⟩ := GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base (laurentHom A A')
  refine GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact (ZMod q) (tw q i) (cech (laurentHom A A')) (yoneda.obj _) Δ hΔ0 N _ ?_ ?_
  · exact (pull_comp (ZMod q) Δ (cechAug (laurentHom A A')) (tw q i) N x).symm.trans
      ((congrArg (fun g => pull (ZMod q) g (tw q i) N x) hΔ).trans hx)
  · intro p hp
    rcases (by omega : (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 0 ∨ (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 1 ∨
        2 ≤ (N : ℤ) - ((p + 1 : ℕ) : ℤ)) with h0 | h1 | h2
    · rw [h0]
      exact rowExact_transfer (fun k => pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0)
        (fun k => GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero q A hA hq A' hfin k i) (fun k j y => cechC_face A A' _ _ k j y) p
        (rowExact_base q A hA hq A' hker i p)
    · rw [h1]
      refine rowExact_transfer (fun k => rowOne A A' q i k) (fun k => GlobalTheory.T.cech_degree_zero_bijective q A hA hq A' hfin k i) (fun k j y => ?_) p
        (rowExact_base q A hA hq A' hker (i - 1) p)
      simp only [rowOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [pull_cast, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1, cechC_face,
        ← pull_comp (ZMod q) (disc.map ((cech (laurentHom A A')).δ j)) (augK A A' k), aug_face]
    · intro y _
      haveI := GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton q N IH A hA hq A' hfin (p + 1) _ i h2 (by omega)
      exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end GlobalTheory.EtC.GmStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerDatumObjectComesFromBaseOfLinearPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerDatumObject_comes_from_base_of_linearPoints : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (L : LowBase D' c) (θ₀ : L.W →+* V) (e : X ≃ₗ[𝓞 E] L.D.X) (m : ObjMap o' L.o (spMap θ₀)), IsLocalHom θ₀ ∧ θ₀.comp L.b = bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ ≫ L.φB = spMap θ₀ ≫ (L.D.c (e y)).left := by
  first | exact @GlobalTheory.UCanon.lowBase_of_linearPoints | exact GlobalTheory.UCanon.lowBase_of_linearPoints | (intros; apply GlobalTheory.UCanon.lowBase_of_linearPoints <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootLiftsFromResidueCompleteLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ t : Sp R ⟶ S, Root A P (spMap (residue R) ≫ t) → Root A P t := by
  first | exact @GlobalTheory.PolRootComplete.root_of_residue | exact GlobalTheory.PolRootComplete.root_of_residue | (intros; apply GlobalTheory.PolRootComplete.root_of_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedThetaConstantsEqScalarMulRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd
  refine ⟨1, fun j hj V₁ _ _ _ hV hunit D X C _ e u mo hmo hT K _ _ ev ρ₀ hρ₀ th hth => ?_⟩
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, rfl⟩
    omega
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  obtain ⟨M, lam, hM, H⟩ := GlobalTheory.T.thetaGenerator_torsionFrame_value_eq_scalar_mul_root (n ^ j) (hodd.pow) hm3 V₁ hV hunit D X C e u mo hmo hT K ev ρ₀ hρ₀ th hth
  refine ⟨M, lam, hM, fun y c hc => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant (Sp V₁) D.P ρ₀ hρ₀ (n ^ j) (hodd.pow) _ th y _ hc
  exact H (y ^ n ^ j) τ c (GlobalTheory.T.isTorsionFrame_sq_of_torsion _ D.P ρ₀ (n ^ j) _ (y ^ n ^ j) τ hτ) hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishAtPlaces
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharpolyLattice

theorem pts_equiv (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) :
    ∃ e : (Over.mk (𝟙 (Sp k)) ⟶ B.X) ≃* B.Pt,
      ∀ (f : B ⟶ B) (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), e (q ≫ f.hom) = e q ≫ f.hom := by
  have hb : Function.Bijective (algebraMap k (AlgebraicClosure k)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsIso (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  haveI : IsIso (spMap (algebraMap k (AlgebraicClosure k))) :=
    inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  let i : ptOver k (AlgebraicClosure k) ≅ Over.mk (𝟙 (Sp k)) :=
    Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (Category.comp_id _)
  refine ⟨{ toFun := fun q => i.hom ≫ q
            invFun := fun q => i.inv ≫ q
            left_inv := fun q => by simp
            right_inv := fun q => by simp
            map_mul' := fun q q' => MonObj.comp_mul _ _ _ }, fun f q => ?_⟩
  exact (Category.assoc i.hom q f.hom).symm

theorem charpoly_reduce {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (n : R) (hn : π n = 0)
    {N Q : Type} [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    [AddCommGroup Q] [Module S Q] (e : N →+ Q) (he : Function.Surjective e)
    (hsmul : ∀ (r : R) (x : N), e (r • x) = π r • e x) (hk : ∀ x, e x = 0 → ∃ y, x = n • y)
    (g : N →ₗ[R] N) (G : Q →ₗ[S] Q) (hg : ∀ x, e (g x) = G (e x)) :
    ∃ (_ : Module.Free S Q) (_ : Module.Finite S Q),
      LinearMap.charpoly G = (LinearMap.charpoly g).map π := by
  classical
  let b := Module.Free.chooseBasis R N
  have hsum : ∀ c : Module.Free.ChooseBasisIndex R N → R,
      e (∑ i, c i • b i) = ∑ i, π (c i) • e (b i) := fun c => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have hli : LinearIndependent S fun i => e (b i) := by
    refine Fintype.linearIndependent_iff.2 fun s hs i => ?_
    choose c hc using fun i => hπ (s i)
    obtain ⟨y, hy⟩ := hk (∑ i, c i • b i) (by rw [hsum]; simpa only [hc] using hs)
    have h := congrArg (fun z => b.repr z i) hy
    simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    rw [← hc, h, map_mul, hn, zero_mul]
  have hsp : ⊤ ≤ Submodule.span S (Set.range fun i => e (b i)) := by
    intro q _
    obtain ⟨x, rfl⟩ := he q
    rw [← b.sum_repr x, hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = e (b i) := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  haveI := Module.Free.of_basis b'
  haveI := Module.Finite.of_basis b'
  rw [← LinearMap.charpoly_toMatrix G b', ← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', ← hg]
  conv_lhs => rw [← b.sum_repr (g (b j)), hsum]
  simp only [← hb']
  rw [Module.Basis.repr_sum_self]

open GlobalTheory.HTLat in

theorem lev_pow_smul {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    (s : Tate l M) (j n : ℕ) : (((l : ℤ_[l]) ^ j) • s).lev n = s.lev n ^ l ^ j := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rfl

open GlobalTheory.HTLat in

theorem tate_lev_eq_one_iff (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime]
    (t : GlobalTheory.HTLat.Tate l M) (j : ℕ) :
    t.lev j = 1 ↔ ∃ s : GlobalTheory.HTLat.Tate l M, t = ((l : ℤ_[l]) ^ j) • s := by
  constructor
  · intro ht
    refine ⟨Tate.mk (fun n => t.lev (j + n)) fun n => ⟨by rw [Tate.lev_add_pow, ht], Tate.lev_succ t (j + n)⟩,
      Tate.ext fun n => ?_⟩
    rw [lev_pow_smul, Tate.lev_mk, add_comm, Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [lev_pow_smul, Tate.lev_pow]

open GlobalTheory.HTLat in

theorem tate_lev_surj (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (j : ℕ) (x : M)
    (hx : x ^ (l ^ j) = 1) : ∃ t : GlobalTheory.HTLat.Tate l M, t.lev j = x := by
  choose L hL using GlobalTheory.TateFree.exists_pow_eq hc
  let u : ∀ m : ℕ, {y : M // y ^ l ^ (j + m) = 1} := fun m =>
    Nat.rec (motive := fun m => {y : M // y ^ l ^ (j + m) = 1}) ⟨x, hx⟩
      (fun m y => ⟨L (j + m) y.1 y.2, (hL _ _ _).1⟩) m
  have hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1 := fun m => (hL _ _ _).2
  have hu' : ∀ m, (u m).1 ^ l ^ m = x := fun m => by
    induction m with
    | zero => exact pow_one x
    | succ m ih => rw [pow_succ', pow_mul, hu, ih]
  refine ⟨Tate.mk (fun m => (u m).1 ^ l ^ j) fun m => ⟨?_, ?_⟩, hu' j⟩
  · rw [← pow_mul, ← pow_add]
    exact (u m).2
  · rw [← pow_mul, mul_comm, pow_mul, hu]

end GlobalTheory.CharpolyLattice

namespace GlobalTheory.AV.AbVar

open GlobalTheory.CharpolyLattice GlobalTheory.HTLat in

theorem charpoly_eq_lattice_model : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B)
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
    ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ B.X),
    (∀ j x y, ev j (x + y) = ev j x * ev j y) →
    (∀ j x, ev j (φ x) = ev j x ≫ f.hom) →
    (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
    (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
    LinearMap.charpoly φ = GlobalTheory.AV.AbVar.charpoly f := by
  intro k _ _ B f L _ _ _ φ l hl hlk ev hadd hequi hker him
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨e, he⟩ := pts_equiv k B
  obtain ⟨hfree, hfin, -⟩ := tl_free_finrank k l hlk B
  have hc : ∀ n : ℕ, Nat.card {x : B.Pt // x ^ (l ^ n) = 1} = l ^ (2 * B.dim * n) := by
    intro n
    rw [card_torsion_pt k B (l ^ n) (by push_cast; exact pow_ne_zero _ hlk), ← pow_mul, mul_comm n]
  let E : ℕ → L →+ Additive B.Pt := fun j =>
    AddMonoidHom.mk' (fun x => Additive.ofMul (e (ev j x))) fun x y => by
      rw [hadd, map_mul]; rfl
  have hE : ∀ j (n : ℕ) x, e (ev j (n • x)) = e (ev j x) ^ n := fun j n x =>
    congrArg Additive.toMul (map_nsmul (E j) n x)
  have key : ∀ j : ℕ, (LinearMap.charpoly φ).map (Int.castRingHom (ZMod (l ^ j))) =
      (LinearMap.charpoly (tend l B f)).map (PadicInt.toZModPow j) := by
    intro j
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.ne_zero⟩
    let K := (powMonoidHom (l ^ j) : B.Pt →* B.Pt).ker
    have hK : ∀ x : B.Pt, x ∈ K ↔ x ^ (l ^ j) = 1 := fun x => MonoidHom.mem_ker
    letI : Module (ZMod (l ^ j)) (Additive K) := AddCommGroup.zmodModule fun x =>
      congrArg Additive.ofMul (Subtype.ext (by
        change ((Additive.toMul x : K) : B.Pt) ^ (l ^ j) = 1
        exact (hK _).1 (Additive.toMul x).2))
    have hsm : ∀ (c : ZMod (l ^ j)) (q : Additive K), c • q = c.val • q := fun c q => by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      exact Nat.cast_smul_eq_nsmul _ _ _
    have hπ : ((l : ZMod (l ^ j))) ^ j = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    let G0 : Additive K →+ Additive K := AddMonoidHom.mk'
      (fun q => Additive.ofMul ⟨((Additive.toMul q : K) : B.Pt) ≫ f.hom, (hK _).2 (by
        rw [← ptMap_apply, ← map_pow, (hK _).1 (Additive.toMul q).2, map_one])⟩)
      fun q q' => congrArg Additive.ofMul (Subtype.ext (MonObj.mul_comp _ _ _))
    let G : Additive K →ₗ[ZMod (l ^ j)] Additive K := G0.toZModLinearMap (l ^ j)
    let eL : L →+ Additive K := AddMonoidHom.mk'
      (fun x => Additive.ofMul ⟨e (ev j x), (hK _).2 (by
        rw [← hE, (hker j _).2 ⟨x, rfl⟩, map_one])⟩)
      fun x y => congrArg Additive.ofMul (Subtype.ext (by
        change e (ev j (x + y)) = e (ev j x) * e (ev j y)
        rw [hadd, map_mul]))
    let eT : Tate l B.Pt →+ Additive K := AddMonoidHom.mk'
      (fun t => Additive.ofMul ⟨t.lev j, (hK _).2 (t.lev_pow j)⟩) fun s t => rfl
    obtain ⟨_, _, h1⟩ := charpoly_reduce (Int.castRingHom (ZMod (l ^ j))) ZMod.intCast_surjective
      ((l : ℤ) ^ j) (by rw [map_pow, map_natCast, hπ]) eL
      (fun q => by
        obtain ⟨x, hx⟩ := (him j (e.symm (Additive.toMul q : K))).1 (by
          rw [← map_pow, (hK _).1 (Additive.toMul q).2, map_one])
        refine ⟨x, congrArg Additive.ofMul (Subtype.ext ?_)⟩
        change e (ev j x) = _
        rw [hx, MulEquiv.apply_symm_apply]
        rfl)
      (fun r x => by rw [map_zsmul, eq_intCast, Int.cast_smul_eq_zsmul])
      (fun x hx => by
        have h0 : e (ev j x) = 1 := congrArg Subtype.val (congrArg Additive.toMul hx)
        obtain ⟨y, hy⟩ := (hker j x).1 ((map_eq_one_iff e e.injective).1 h0)
        exact ⟨y, by rw [hy, ← Nat.cast_pow, natCast_zsmul]⟩)
      φ G (fun x => congrArg Additive.ofMul (Subtype.ext (by
        change e (ev j (φ x)) = e (ev j x) ≫ f.hom
        rw [hequi, he])))
    obtain ⟨_, _, h2⟩ := charpoly_reduce (PadicInt.toZModPow j) (ZMod.ringHom_surjective _)
      ((l : ℤ_[l]) ^ j) (by rw [map_pow, map_natCast, hπ]) eT
      (fun q => by
        obtain ⟨t, ht⟩ := tate_lev_surj B.Pt l (2 * B.dim) hc j _ ((hK _).1 (Additive.toMul q).2)
        exact ⟨t, congrArg Additive.ofMul (Subtype.ext ht)⟩)
      (fun a t => by
        rw [hsm]
        rfl)
      (fun t ht => by
        obtain ⟨s, hs⟩ := (tate_lev_eq_one_iff B.Pt l t j).1
          (congrArg Subtype.val (congrArg Additive.toMul ht))
        exact ⟨s, hs⟩)
      (tend l B f) G (fun t => rfl)
    exact h1.symm.trans h2
  have hT := (charpoly_tate_det_trace k l hlk B f).2.1
  have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℤ_[l])) :=
    Polynomial.map_injective _ Int.cast_injective
  apply hinj
  rw [show Int.castRingHom ℤ_[l] = algebraMap ℤ ℤ_[l] from RingHom.ext_int _ _, hT]
  ext i
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  have h := congrArg (fun P => Polynomial.coeff P i) (key n)
  simp only [Polynomial.coeff_map, eq_intCast] at h ⊢
  rw [map_intCast]
  exact h

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSecondBlockTangentBasisDualLie
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecondTangent

theorem tangent_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (map Θ (e (Sum.inr j))) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ k e he hadapt Θ hΘ
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμeq : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  obtain ⟨k', es, lbs, hbs, -, hcobs, hlies⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hF

  have hlift1 : ∀ m, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = es m := by
    intro m
    have hq : QL (fun i => map F.θ (μ' i)) ⊤ (es m) := hμeq ▸ hbs.1 m
    choose b _ hb using hq.2.1
    choose w hw using fun i => F.frame.surj (b i)
    obtain ⟨f, hf, hf', -⟩ := GlobalTheory.QLog.KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hlift C hF
      Θ hΘ (es m) w hq (fun i => by rw [hb, hw])
    exact ⟨f, hf, hf'⟩
  choose f hfq hfm using hlift1
  have hfb : IsBasis μ' f := by
    refine GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hlift C hF Θ hΘ _ f hfq ?_
      (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    have : (fun i => map Θ (f i)) = es := funext hfm
    rw [this, hμeq]; exact hbs

  choose P hP using fun i => (hfb.2 (e i) (he.1 i)).exists
  choose P' hP' using fun j => (he.2 (f j) (hfq j)).exists
  obtain ⟨h1, h2⟩ := GlobalTheory.T.quasiLogarithmBasis_transitionMatrices_inverse μ' e f he hfb P P' hP hP'

  let Ls : Fin d ⊕ Fin k' → G.dual.Lie := Sum.elim 0 lbs
  have hLs : ∀ m, c.IsLie (es m) (Ls m) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF (es (Sum.inl i)) (hbs.1 _)
      have := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ l l 0 hl hl).2.2 (hcobs i)
      subst this; exact hl
    · exact hlies j
  have hμc : ∀ i, constantCoeff (μ' i) = 0 := hlift.const
  have hg : ∀ i, QL c.μ ⊤ (map Θ (e i)) := fun i => by
    rw [← hμeq]; exact GlobalTheory.SmallSecond.ql_map hΘ μ' hμc (he.1 i)
  have hrow : ∀ i, c.IsLie (map Θ (e i)) (∑ m, F.θ (P i m) • Ls m) := by
    intro i
    refine GlobalTheory.T.tangentVector_quasiLogarithm_of_congruent_combination p C v O hv G d c es (hbs.1) Ls hLs _ (hg i) _ ?_
    intro α
    obtain ⟨b, -, hb⟩ := hP i α
    refine ⟨F.θ b, trivial, ?_⟩
    have : map Θ (e i) - comb (fun m => F.θ (P i m)) es = map Θ (e i - comb (P i) f) := by
      rw [map_sub, GlobalTheory.SmallSecond.map_comb hΘ, funext hfm]
    rw [this, coeff_map, hb, hΘ]

  have hzero : ∀ i j, F.θ (P (Sum.inl i) (Sum.inr j)) = 0 := by
    intro i
    have hc : cob1 (up C c.μ) (map Θ (e (Sum.inl i))) = 0 := by
      rw [← hμeq]; exact GlobalTheory.SmallSecond.formalGroupLawCoboundaryOne_map_eq_zero hΘ μ' hμc (hadapt i).1
    have h0 := (GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF _ _ _ _ 0 (hrow (Sum.inl i)) (hrow (Sum.inl i))).2.2 hc
    simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
      Finset.sum_const_zero, zero_add] at h0
    exact (Fintype.linearIndependent_iff.1 lbs.linearIndependent) _ h0
  obtain ⟨lb, hlb⟩ := GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' O G.dual.Lie d k k' lbs ((Matrix.of P).map F.θ)
    ((Matrix.of P').map F.θ) (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]) hzero
  refine ⟨lb, fun j => ?_⟩
  have := hrow (Sum.inr j)
  simp only [Fintype.sum_sum_type, Ls, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, zero_add] at this
  rw [hlb]; exact this

end GlobalTheory.SmallSecondTangent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankPosNegativeWeightBundleStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_pos_negative_weight_bundle : GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → Covers fun Fm x _ ι p i Y _ _ => 0 < Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @GlobalTheory.CovTop.LowPos.lowered_rank_pos | exact GlobalTheory.CovTop.LowPos.lowered_rank_pos | (intros; apply GlobalTheory.CovTop.LowPos.lowered_rank_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionEqOfValuesAtLabelTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_eq_of_values_at_label_torsion : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th th₂ : SecA 𝔪.A (FractionRing V) 1),
  (∀ a, (fr a).IsGen) → (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) →
  (∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → th₂ = th := by
  first | exact @GlobalTheory.GSep.GMem.sec_eq_of_valAt | exact GlobalTheory.GSep.GMem.sec_eq_of_valAt | (intros; apply GlobalTheory.GSep.GMem.sec_eq_of_valAt <;> assumption)
end

