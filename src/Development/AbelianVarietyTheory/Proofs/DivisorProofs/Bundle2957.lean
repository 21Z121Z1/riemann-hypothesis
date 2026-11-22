import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiEven
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v))) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  first | exact @GlobalTheory.Poinc.Sep.Labels.yy_hom | exact GlobalTheory.Poinc.Sep.Labels.yy_hom | (intros; apply GlobalTheory.Poinc.Sep.Labels.yy_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  first | exact @GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre | exact GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre | (intros; apply GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomic
section
noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem exists_galoisCover_of_geom {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R)
    (N h M : ℕ) (h1 : 1 ≤ h) (hM0 : 0 < M) (hodd : Odd M) (hMp : M.Coprime p)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) (huniv : HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev)
    (ρ : sympSimGrp h M → (X ⟶ X)) (hρ : SympActs s s₁ u lev ρ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t)
    (geo : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)), SympCond o h M (Over.mk x) t₁ lv) :
    ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp h M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X) (o' : Obj b N (π₁ ≫ t)),
      GlobalTheory.ZM.IsGaloisCover (sympSimGrp h M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
      y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨Y, t₁, lu, hYf, hYe, hY⟩ := GlobalTheory.T.exists_finiteEtale_symplecticLevel_scheme p D R b N h M hM0 hMp S t o
  have hAu : SympCond o h M Y t₁ lu := (hY Y t₁ lu).2 ⟨𝟙 Y, by simp, fun a => Category.id_comp _⟩
  have uniqY : ∀ {T : Over S} (f g : T ⟶ Y), f.left ≫ t₁ = g.left ≫ t₁ → (∀ c, f ≫ lu c = g ≫ lu c) → f = g :=
    fun {T} f g e1 e2 => ((hY T (g.left ≫ t₁) (fun c => g ≫ lu c)).1 ((hY T _ _).2 ⟨g, rfl, fun _ => rfl⟩)).unique
      ⟨e1, e2⟩ ⟨rfl, fun _ => rfl⟩
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S Y.left t Y.hom o
  have hlift : ∀ c, ∃ g : 𝟙_ (Over Y.left) ⟶ o'.A, g.left ≫ m.φ = (lu c).left := fun c => by
    have w : (lu c).left ≫ o.A.hom = 𝟙 Y.left ≫ Y.hom := by rw [Over.w (lu c), Category.id_comp]
    exact ⟨Over.homMk (m.cart.1.lift (lu c).left (𝟙 Y.left) w) (m.cart.1.lift_snd _ _ _),
      m.cart.1.lift_fst _ _ _⟩
  choose lv' hlv' using hlift
  choose n σ hn hσζ hσs using fun a => (hρ a).2.1
  have hTw : ∀ a, SympCond o h M Y (t₁ ≫ spMap (σ a)) (sympTwist a lu) := fun a =>
    GlobalTheory.T.symplecticLevel_twist_by_similitude p D R b N h M hM0 S t o Y t₁ lu hAu a (n a) (σ a) (hn a) (hσζ a)
  choose r hr using fun a => ((hY Y _ _).1 (hTw a)).exists
  have hlev' : IsSympLev o'.P h M (zetaAway M) t₁ lv' := GlobalTheory.T.isSymplecticLevel_of_pulledBack_object p D R b N h M S t o Y t₁ o' m lv' lu hlv' hAu
  have hlevT : ∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv') := fun a =>
    GlobalTheory.T.isSymplecticLevel_of_pulledBack_object p D R b N h M S t o Y (t₁ ≫ spMap (σ a)) o' m (sympTwist a lv') (sympTwist a lu) (fun c => hlv' _) (hTw a)
  obtain ⟨y, ⟨hys, hys₁, my, hmy⟩, -⟩ := huniv Y.left (Y.hom ≫ t) t₁ o' lv' hlev'
  have hdet := (GlobalTheory.SiegelTor.cycAway_galois M (by omega)).2.1
  have hσ1 : σ 1 = RingHom.id _ := hdet _ (σ 1) (RingHom.id _) (by
    rw [hσζ, RingHom.id_apply]
    conv_rhs => rw [← pow_one (zetaAway M)]
    apply zetaAway_pow_eq M (by omega)
    have hm1 : IsMultOf (1 : sympSimGrp h M) 1 := fun x y => by simp
    exact_mod_cast isMultOf_unique h1 (hn 1) hm1)
  have hσmul : ∀ a c, (σ a).comp (σ c) = σ (a * c) := fun a c => hdet _ _ _ (by
    rw [RingHom.comp_apply, hσζ, map_pow, hσζ, hσζ, ← pow_mul]
    apply zetaAway_pow_eq M (by omega)
    have hm : IsMultOf (a * c) (n a * n c) := fun x y => by
      show omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x))
        ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y)) = _
      rw [hn a, hn c]
      push_cast
      ring
    exact isMultOf_unique h1 hm (hn (a * c)))
  have hsm : ∀ (k : ℕ) w, lu (k • w) = lu w ^ k := by
    have h0 : lu 0 = 1 := by
      have e0 := hAu.1 0 0
      rw [add_zero] at e0
      exact (by simpa using congrArg (· * (lu 0)⁻¹) e0 : (1 : Y ⟶ o.A) = lu 0).symm
    intro k w
    induction k with
    | zero => rw [zero_smul, h0, pow_zero]
    | succ k ih => rw [succ_nsmul, hAu.1, ih, pow_succ]
  have hper : ∀ c, lu (liftMod (reduceMod M c)) = lu c := by
    intro c
    have hw : liftMod (reduceMod M c) = c + M • (fun i => -(c i / M)) := by
      funext i
      simp only [liftMod, reduceMod, ZMod.val_intCast, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply]
      rw [Int.emod_def]
      ring
    rw [hw, hAu.1, hsm, hAu.2.1, _root_.mul_one]
  have hsp1 : spMap (RingHom.id (cycAway M)) = 𝟙 _ := Spec.map_id _
  have hr1 : r 1 = 𝟙 Y := uniqY _ _ (by rw [(hr 1).1, hσ1, hsp1]; simp) (fun c => by
    rw [(hr 1).2, Category.id_comp]
    exact hper c)
  have hrmul : ∀ a c, r (a * c) = r a ≫ r c := fun a c => uniqY _ _ (by
      rw [(hr _).1, Over.comp_left, Category.assoc, (hr c).1, ← Category.assoc, (hr a).1, Category.assoc,
        ← spMap_comp, hσmul])
    (fun d => by
      rw [(hr _).2, Category.assoc, (hr c).2]
      change sympTwist (a * c) lu d = r a ≫ lu (liftMod
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M d)))
      rw [(hr a).2]
      change lu (liftMod (((a * c : sympSimGrp h M) : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
          (reduceMod M d))) = lu (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
          (reduceMod M (liftMod ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
            (reduceMod M d))))))
      rw [reduceMod_liftMod]
      rfl)
  refine ⟨Y.left, Y.hom, fun a => (r a).left, y, o', ⟨sympSimGrp_finite h M, ?_, ?_, ?_, hYf, hYe, ?_, ?_⟩,
    ?_, hys, ⟨m⟩, ⟨my⟩⟩
  · show (r 1).left = _
    rw [hr1]
    rfl
  · intro a c
    show (r (a * c)).left = _
    rw [hrmul]
    rfl
  · intro a
    exact Over.w (r a)
  · refine ⟨fun pt => ?_⟩
    obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point S pt
    obtain ⟨t₀, lv, hlv⟩ := geo k x
    obtain ⟨f, -, -⟩ := (hY (Over.mk x) t₀ lv).1 hlv
    obtain ⟨q, hq⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨f.left q, by rw [← Scheme.Hom.comp_apply, Over.w f]; exact hq⟩
  · intro K _ _ y₁ y₂ h12
    let P1 : Over.mk (y₁ ≫ Y.hom) ⟶ Y := Over.homMk y₁ rfl
    let P2 : Over.mk (y₁ ≫ Y.hom) ⟶ Y := Over.homMk y₂ h12.symm
    have c1 : SympCond o h M (Over.mk (y₁ ≫ Y.hom)) (y₁ ≫ t₁) (fun c => P1 ≫ lu c) :=
      (hY _ _ _).2 ⟨P1, rfl, fun _ => rfl⟩
    have c2 : SympCond o h M (Over.mk (y₁ ≫ Y.hom)) (y₂ ≫ t₁) (fun c => P2 ≫ lu c) :=
      (hY _ _ _).2 ⟨P2, rfl, fun _ => rfl⟩
    obtain ⟨a, ⟨ha1, ha2⟩, hu⟩ := GlobalTheory.T.existsUnique_similitude_between_symplecticLevels p D R b N h M hM0 hodd h1 σ (fun a => ⟨n a, hn a, hσζ a⟩) S t o K
      (y₁ ≫ Y.hom) _ _ _ _ c1 c2
    refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
    · have : P1 ≫ r a = P2 := uniqY _ _ (by
          show y₁ ≫ (r a).left ≫ t₁ = y₂ ≫ t₁
          rw [(hr a).1, ← Category.assoc]
          exact ha1)
        (fun c => by rw [Category.assoc, (hr a).2]; exact ha2 c)
      exact congrArg (fun q => q.left) this
    · have e' : P1 ≫ r a' = P2 := Over.OverMorphism.ext ha'
      refine ⟨?_, fun c => ?_⟩
      · rw [Category.assoc, ← (hr a').1, ← Category.assoc]
        exact congrArg (· ≫ t₁) ha'
      · show P1 ≫ lu _ = P2 ≫ lu c
        rw [← e', Category.assoc, (hr a').2]
        rfl
  · exact fun a => GlobalTheory.T.classifyingMap_symplecticLevel_equivariant p D R b N h M X s s₁ u lev huniv ρ hρ σ hσs S t o Y t₁ lu o' m lv' hlv' hlevT y my hmy
      hys hys₁ r (fun a => (hr a).1) (fun a => (hr a).2) a

theorem exists_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
  (N M e : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e →
  (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P (Module.finrank ℤ D.La / 2) M (zetaAway M) s₁ lev →
    HarrisTaylorSymplecticLevelFamilyUniversalProperty b N (Module.finrank ℤ D.La / 2) M s s₁ u lev →
    ∀ ρ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X)
        (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover (sympSimGrp (Module.finrank ℤ D.La / 2) M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
        y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  intro p _ D R _ b N M e _ _ hM hodd hMp _ hMe hperf X s s₁ u lev _ huniv ρ hρ S t o
  have h1 : 1 ≤ Module.finrank ℤ D.La / 2 := by have := D.two_le_finrank_La; omega
  exact exists_galoisCover_of_geom b N _ M h1 (by omega) hodd hMp X s s₁ u lev huniv ρ hρ S t o
    (fun K _ _ x => GlobalTheory.T.exists_symplectic_level_geometric_point_harrisTaylor p D R b N M e hM hodd hMp hMe hperf S t o K x)

end GlobalTheory.HTSympCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionOnModel
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ArLieBase.exists_eig_subspace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)), GlobalTheory.LineNorm.IsTanBasis Z.t x e → ∀ (K : Type) [Field K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) → ∃ V : Submodule K (Fin g → K), Module.finrank K V = Dw.mult τ ∧ ∀ (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ Z.t.G.left), IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w → (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ cf ∈ V) := by
  intro E _ _ _ H Dw l Xo c Z R _ x τ g e he K _ ψ φ hφ
  have h0 : (spMap ψ ≫ x) ≫ Z.s = spMap φ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, hφ, Guard.sp_comp]
  let y : Sp K ⟶ gen Z := Limits.pullback.lift (spMap ψ ≫ x) (spMap φ) h0
  have hy1 : y ≫ genι Z = spMap ψ ≫ x := Limits.pullback.lift_fst _ _ _
  have hy2 : y ≫ genStr Z = spMap φ := Limits.pullback.lift_snd _ _ _
  have hf := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c _ _ Z K φ y hy2
  rw [hy1] at hf
  obtain ⟨f⟩ := hf
  have hv : ∀ i, IsTanAtG Z.t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e i) :=
    fun i => GlobalTheory.FactorDepth.isTanAtG_map Z.t ψ (he.1 i)
  have hb := he.2 K ψ
  choose a ha using fun i => (hb _ (f.tan τ i)).exists
  let A : Matrix (Fin g) (Fin (Dw.mult τ)) K := fun j i => a i j
  have heig : ∀ cf w, IsCombAtG Z.t (spMap ψ ≫ x) (f.v τ) cf w → ∀ b : 𝓞 E,
      w ≫ (Z.t.act.act b).left = spMap (epsMul (φ (embK c τ b))) ≫ w := fun cf w h1 b => by
    rw [← (isCombAtG_iff Z.t _ (fun j => ovT (f.tan τ j)) _ _).1 h1]
    have := Z.t.act.hom b
    exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (f.tan τ j)) (Z.t.act.act b) _
      (fun j => Over.OverMorphism.ext (f.eig τ j b)) cf)
  have hi : Guard.Indep Z.t (spMap ψ ≫ x) (f.v τ) := fun cf cf' w h1 h2 =>
    (f.basis τ w (Guard.comb_tan (f.tan τ) h1) (heig cf w h1)).unique h1 h2
  have hinj := (Guard.indep_iff hv (Guard.indep_of_basis hv hb) A ha).1 hi
  refine ⟨LinearMap.range A.mulVecLin, ?_, fun cf w hw => ⟨fun h => ?_, ?_⟩⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  · obtain ⟨b, hb', -⟩ := f.basis τ w h.1 h.2
    exact ⟨b, (hb w h.1).unique (tanLinG _ hv (f.v τ) A b w ha hb') hw⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨w', h1, h2⟩ := Guard.exists_comb (f.tan τ) b
    obtain rfl : w' = w := Guard.comb_unique hv (tanLinG _ hv (f.v τ) A b w' ha h2) hw
    exact ⟨h1, heig b w' h2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDifferentialUniqueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_mult_lift_divided_powers : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
  ∀ (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left),
    IsGrpPullback X₀.A A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
  ∀ (rm : OAct (𝓞 F) A), (∀ a, (X₀.rm.act a).left ≫ i = i ≫ (rm.act a).left) →
  ∀ (P : 𝔠.elt → LB (G2 A).left) (l : (G2 X₀.A).left ⟶ (G2 A).left), IsSquare i l → (∀ c, (P c).IsLB) →
    (∀ c, HasGen ((P c).pull (lift (1 : A ⟶ A) (𝟙 A)).left)) → (∀ c, HasGen ((P c).pull (lift (𝟙 A) (1 : A ⟶ A)).left)) →
    (∀ c, LBIso ((P c).pull l) (X₀.P c)) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ c c', LBIso (P c') (LB.div (P (c + c')) (P c))) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    (∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A ((P c).pull (lift (𝟙 A) (𝟙 A)).left)) →
  ∀ (c : 𝔠.elt) (T : Over (Sp R)) (x : T ⟶ A), HasGen ((P c).pull (lift (fst A T) (snd A T ≫ x)).left) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm.act a = 1 := by
  first | exact @GlobalTheory.KerDeform.ker_deform | exact GlobalTheory.KerDeform.ker_deform | (intros; apply GlobalTheory.KerDeform.ker_deform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseMatchingMonomialsRatioUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj.PerUnit

theorem dataFrom_ofDeg {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V]
    (T : TautBase o W) (ω : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ))
    (n : ℕ) (D : DegPre V) (hB : D.TauBimult) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left)
    (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))
    (h : From T ω s ε n D e β β₂ w) : DataFrom T ω s ε n (GlobalTheory.PolDeg.Wit.ofDeg D hB) e := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun a b => ?_⟩
  obtain ⟨k, hk, hv⟩ := h₅ a b
  exact ⟨k, hk, fun z J J' hJ hJ' => ((GlobalTheory.PolDeg.Wit.exists_tau D a b).choose_spec.2 _ (𝟙 _) z J' hJ').trans (hv z J J' hJ hJ')⟩

theorem exists_good_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (z : (TK V).left) :
    ∃ J : ((TK V).left ⟶ D.P.A.left) → D.P.L.ι, Good D.P.L z J ∧
      ∀ e : Sp V ⟶ D.P.A.left, e (closedPoint V) ∈ D.P.L.U (J ((TK V).hom ≫ e)) := by
  classical
  haveI : IsDominant (jK V) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : D.P.A.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from D.P.A.hom]; infer_instance
  have hinj : ∀ e e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = (TK V).hom ≫ e' → e = e' :=
    fun e e' h => ext_of_isDominant (jK V) h
  have hsp : ∀ (e : Sp V ⟶ D.P.A.left) (p : Sp V) (i : D.P.L.ι), e (closedPoint V) ∈ D.P.L.U i → e p ∈ D.P.L.U i :=
    fun e p i h => (((PrimeSpectrum.le_iff_specializes p (closedPoint V)).1
      (IsLocalRing.le_maximalIdeal p.2.ne_top)).map e.continuous).mem_open (D.P.L.U i).isOpen h
  choose pick hpick using exists_chart D.P.isLB
  refine ⟨fun ψ => if h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ then pick (h.choose (closedPoint V))
    else pick (ψ z), fun ψ => ?_, fun e => ?_⟩
  · by_cases h : ∃ e : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e = ψ
    · simp only [dif_pos h]
      have e1 : ψ z = ((TK V).hom ≫ h.choose) z :=
        (congrArg (fun q : (TK V).left ⟶ D.P.A.left => q z) h.choose_spec).symm
      rw [e1]
      exact hsp _ _ _ (hpick _)
    · simp only [dif_neg h]
      exact hpick _
  · have h : ∃ e' : Sp V ⟶ D.P.A.left, (TK V).hom ≫ e' = (TK V).hom ≫ e := ⟨e, rfl⟩
    simp only [dif_pos h]
    rw [hinj _ _ h.choose_spec]
    exact hpick _

theorem val_closed {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {X Y : Scheme.{0}} {L : LB X} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp V ⟶ Y) (z : (TK V).left)
    (J : ((TK V).left ⟶ X) → L.ι) (hJ : ∀ k, (y ≫ φ k) (closedPoint V) ∈ L.U (J ((TK V).hom ≫ y ≫ φ k))) :
    ∃ w : Vˣ, val t ((TK V).hom ≫ y) z J =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) w)) := by
  have hall : ∀ p : Sp V, y p ∈ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) := by
    intro p
    refine Set.mem_iInter.2 fun k => ?_
    have hsp : p ⤳ closedPoint V :=
      (PrimeSpectrum.le_iff_specializes p (closedPoint V)).1 (IsLocalRing.le_maximalIdeal p.2.ne_top)
    have hm := hJ k
    rw [← Category.assoc] at hm
    exact hsp.map (y ≫ φ k).continuous |>.mem_open (L.U _).isOpen hm
  have hU : y ⁻¹ᵁ LB.wchart L φ (fun k => J (((TK V).hom ≫ y) ≫ φ k)) = ⊤ := top_unique fun p _ => hall p
  have key : ∀ (U : (Sp V).Opens) (_ : U = ⊤) (a : Γ(Sp V, U)ˣ), ∃ w : Vˣ,
      gm (TK V).hom z U a = gm (TK V).hom z ⊤ (unitOn w) := by
    rintro U rfl a
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
    show a.val = (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val)
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  obtain ⟨w, hw⟩ := key _ hU (pullU y _ (t.s (fun k => J (((TK V).hom ≫ y) ≫ φ k))))
  refine ⟨w, ?_⟩
  have q : (toUnit (TK V)).left = (TK V).hom := by simp
  rw [← GlobalTheory.PolDeg.Taut.gm_jK_unitOn, q, ← hw]
  exact (gm_pull (TK V).hom y z _ (hall _) _).symm

end GlobalTheory.TInj.PerUnit

namespace GlobalTheory.TInj.PerUnit

set_option maxHeartbeats 2000000 in

theorem monomial_ratio_unit : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → ∀ y y' : D₁.X, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
  intro o W _ _ _ T I _ ε n V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hB₁ hB₂ f₁ f₂ m y y'
  obtain ⟨k₁, hk₁, U₁, -, hU₁⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₁ s₁ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₁ hB₁) e₁
    (dataFrom_ofDeg T ω₁ s₁ ε n D₁ hB₁ e₁ β₁ ββ₁ w₁ f₁) y (φ.symm.toAddMonoidHom (φ y'))
  obtain ⟨k₂, hk₂, U₂, -, hU₂⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator T ω₂ s₂ ε n (GlobalTheory.PolDeg.Wit.ofDeg D₂ hB₂) e₂
    (dataFrom_ofDeg T ω₂ s₂ ε n D₂ hB₂ e₂ β₂ ββ₂ w₂ f₂) (φ y) (φ y')
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_iota (F := F) hB₁ y
  obtain ⟨g', ha, hg'⟩ := m.2.2.2.2 y g hg
  obtain ⟨u, hu⟩ := m.2.2.2.1 (φ y')
  let z : (TK V).left := closedPoint (FractionRing V)
  obtain ⟨J₁, gJ₁, cJ₁⟩ := exists_good_closed D₁ z
  obtain ⟨J₂, gJ₂, cJ₂⟩ := exists_good_closed D₂ z
  obtain ⟨J, hJ, hl, hr⟩ := exists_good_join D₁.P.isLB D₂.P.isLB gJ₁ gJ₂
  have key := act_val_frac V D₂ D₁ b φ.symm.toAddMonoidHom F y (φ y) g g' hg hg' ha (φ y') u hu z J hJ
  have t₁ := ((GlobalTheory.PolDeg.Wit.exists_tau D₁ y (φ.symm.toAddMonoidHom (φ y'))).choose_spec.2 _ (𝟙 _) z (rl J)
    ((isPart_inl _ _).good hJ)).symm.trans (hU₁ z (rl J) ((isPart_inl _ _).good hJ))
  have t₂ := ((GlobalTheory.PolDeg.Wit.exists_tau D₂ (φ y) (φ y')).choose_spec.2 _ (𝟙 _) z (rr J)
    ((isPart_inr _ _).good hJ)).symm.trans (hU₂ z (rr J) ((isPart_inr _ _).good hJ))
  obtain ⟨v₁, hv₁⟩ := val_closed U₁ (𝟙 _) z (rl J) (fun k => by erw [hl]; exact cJ₁ _)
  obtain ⟨v₂, hv₂⟩ := val_closed U₂ (𝟙 _) z (rr J) (fun k => by erw [hr]; exact cJ₂ _)
  obtain ⟨v₃, hv₃⟩ := val_closed u (D₁.c y).left z J (fun k => by
    rcases k with k | k
    · have h1 := cJ₁ ((D₁.c y).left ≫ D₁.Oφ (𝟙 _) (φ.symm.toAddMonoidHom (φ y')) k)
      erw [← hl] at h1
      have h2 := ((isPart_inl D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inl, Category.assoc] at h2 ⊢
      exact h2
    · have h1 := cJ₂ ((D₁.c y).left ≫ D₂.Oφ b (φ y') k)
      erw [← hr] at h1
      have h2 := ((isPart_inr D₁.P.L D₂.P.L).mem _ _).2 h1
      simp only [Sum.elim_inr, Category.assoc] at h2 ⊢
      exact h2)
  have q₁ : (toUnit (TK V)).left = (TK V).hom ≫ 𝟙 (Sp V) := by simp
  have q₃ : ptK (D₁.c y) = (TK V).hom ≫ (D₁.c y).left := by simp [ptK]
  rw [← q₁] at hv₁ hv₂
  rw [← q₃] at hv₃
  have um : ∀ a c : (FractionRing V)ˣ, unitOn (a * c) = unitOn a * unitOn c := fun a c => map_mul _ a c
  have E : gm (𝟙 (TK V).left) z ⊤ (unitOn (k₂ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₂)) =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (k₁ * Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₁ *
        Units.map (algebraMap V (FractionRing V) : V →* FractionRing V) v₃)) := by
    rw [um, um, um, map_mul, map_mul, map_mul, ← hv₁, ← hv₂, ← hv₃, ← t₂, ← t₁]
    exact key
  have inj := GlobalTheory.DefectHom.gm_unitOn_inj z E
  have hc := congrArg (fun x : (FractionRing V)ˣ => (x : FractionRing V)) inj
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at hc
  have hk₁' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ y')) := by
    have h' : (k₁ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (e₁ y) (e₁ (φ.symm (φ y')))) := by
      exact hk₁
    rw [h', φ.symm_apply_apply]
  have hk₂' : (k₂ : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (e₂ (φ y)) (e₂ (φ y'))) := by
    exact hk₂
  refine ⟨v₁ * v₃ * v₂⁻¹, ?_⟩
  rw [← hk₂', ← hk₁']
  have hv2 : algebraMap V (FractionRing V) (v₂ : V) * algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simp only [Units.val_mul, map_mul]
  linear_combination (-(k₂ : FractionRing V)) * hv2 + algebraMap V (FractionRing V) ((v₂⁻¹ : Vˣ) : V) * hc

end GlobalTheory.TInj.PerUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_psi_mem_maximalIdeal_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Tens D.toPre D' W → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  first | exact @GlobalTheory.Mum.TensPos.psi_pos_tendsto | exact GlobalTheory.Mum.TensPos.psi_pos_tendsto | (intros; apply GlobalTheory.Mum.TensPos.psi_pos_tendsto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataTauBimultiplicativeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_tau_bimultiplicative : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  first | exact @GlobalTheory.TensBimult.main | exact GlobalTheory.TensBimult.main | (intros; apply GlobalTheory.TensBimult.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiEvenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegenerationData_psi_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → D'.PsiEven := by
  first | exact @GlobalTheory.PolTensEven.main | exact GlobalTheory.PolTensEven.main | (intros; apply GlobalTheory.PolTensEven.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTauBimultiplicativeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegenerationData_tau_bimultiplicative : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  first | exact @GlobalTheory.TensPolBimult.main | exact GlobalTheory.TensPolBimult.main | (intros; apply GlobalTheory.TensPolBimult.main <;> assumption)
end

