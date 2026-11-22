import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeThetaJets
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotent
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftGroupLaw

theorem exists_grpObj_isAbelianScheme : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left), l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i → l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i →
    ∀ (m : X ⊗ X ⟶ X), l ≫ m.left = (μ[A₀]).left ≫ i →
    ∃ _ : GrpObj X, IsGrpPullback A₀ X (spMap π) i ∧ IsAbelianScheme X := by
  intro R R₀ _ _ π hπ hN A₀ _ hA X i hi hsm e he he1 l hl1 hl2 m hm
  haveI : Smooth X.hom := hsm
  haveI : IsCommMonObj A₀ := hA.comm
  obtain ⟨hpX, hgX⟩ := GlobalTheory.T.isProper_geometricallyConnected_smooth_nilpotent_lift R R₀ π hπ hN X A₀ i hi hsm hA.proper hA.geomConnected
  haveI := hpX
  haveI := hgX
  have s2 : Smooth (X ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have p2 : IsProper (X ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have g2 : GeometricallyConnected (X ⊗ X).hom := by
    rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _
  haveI := s2
  haveI := p2
  haveI := g2
  have s3 : Smooth ((X ⊗ X) ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have p3 : IsProper ((X ⊗ X) ⊗ X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have g3 : GeometricallyConnected ((X ⊗ X) ⊗ X).hom := by
    rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _

  obtain ⟨jA, hjl⟩ : ∃ jA : (Over.map (spMap π)).obj A₀ ⟶ X, jA.left = i := ⟨Over.homMk i hi.w, rfl⟩
  obtain ⟨E, hEl⟩ : ∃ E : 𝟙_ (Over (Sp R)) ⟶ X, E.left = e := ⟨Over.homMk e he, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L : (Over.map (spMap π)).obj (A₀ ⊗ A₀) ⟶ X ⊗ X,
      L = lift ((Over.map (spMap π)).map (fst A₀ A₀) ≫ jA) ((Over.map (spMap π)).map (snd A₀ A₀) ≫ jA) := ⟨_, rfl⟩
  have hL : L.left = l := by
    have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
    refine p.hom_ext ?_ ?_
    · rw [← Over.comp_left, hLd, lift_fst, hl1, Over.comp_left, Over.map_map_left, hjl]
    · rw [← Over.comp_left, hLd, lift_snd, hl2, Over.comp_left, Over.map_map_left, hjl]
  have pt : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) = (Over.map (spMap π)).map (lift x y) ≫ L := by
    intro T x y
    rw [hLd, comp_lift, ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc, lift_fst, lift_snd]
  have hLm : L ≫ m = (Over.map (spMap π)).map μ[A₀] ≫ jA := by
    ext1; rw [Over.comp_left, hL, hm, Over.comp_left, Over.map_map_left, hjl]
  have ptm : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m = (Over.map (spMap π)).map (x * y) ≫ jA := by
    intro T x y
    rw [pt, Category.assoc, hLm, ← CategoryTheory.Functor.map_comp_assoc, Hom.mul_def]
  have hE : ∀ T : Over (Sp R₀), (Over.map (spMap π)).map (1 : T ⟶ A₀) ≫ jA = toUnit _ ≫ E := by
    intro T
    have h1 : (1 : T ⟶ A₀) = (Over.homMk T.hom (Category.comp_id T.hom) : T ⟶ Over.mk (𝟙 (Sp R₀))) ≫ 1 := (comp_one _).symm
    ext1
    rw [Over.comp_left, Over.comp_left, Over.map_map_left, h1, Over.comp_left, Category.assoc, hjl, he1,
      Over.toUnit_left, Over.map_obj_hom, hEl]
    rfl
  have hj : (Over.map (spMap π)).map (𝟙 A₀) ≫ jA = jA := by rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hjE : jA ≫ toUnit X ≫ E = (Over.map (spMap π)).map (1 : A₀ ⟶ A₀) ≫ jA := by
    rw [hE, comp_toUnit_assoc]

  obtain ⟨τ, hτd⟩ : ∃ τ : X ⟶ X, τ = lift (toUnit X ≫ E) (𝟙 X) ≫ m := ⟨_, rfl⟩
  have hτ : jA ≫ τ = jA := by
    rw [hτd, comp_lift_assoc, Category.comp_id, hjE]
    have h := ptm A₀ 1 (𝟙 A₀)
    rw [hj, _root_.one_mul, hj] at h
    exact h
  have τiso : IsIso τ := by
    refine GlobalTheory.T.isIso_of_flat_pullback_reduction R R₀ π hπ hN X X A₀ A₀ i i hi hi inferInstance τ (𝟙 A₀) ?_ inferInstance
    have h := congrArg (fun g => g.left) hτ
    simp only [Over.comp_left, hjl] at h
    rw [h, Over.id_left, Category.id_comp]
  obtain ⟨m₁, hm₁d⟩ : ∃ m₁ : X ⊗ X ⟶ X, m₁ = m ≫ inv τ := ⟨_, rfl⟩
  have hjτ : jA ≫ inv τ = jA := by
    conv_lhs => rw [← hτ]
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have ptm₁ : ∀ (T : Over (Sp R₀)) (x y : T ⟶ A₀),
      lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m₁ = (Over.map (spMap π)).map (x * y) ≫ jA := by
    intro T x y
    rw [hm₁d, ← Category.assoc, ptm, Category.assoc, hjτ]
  have hLm₁ : L ≫ m₁ = (Over.map (spMap π)).map μ[A₀] ≫ jA := by
    rw [hm₁d, ← Category.assoc, hLm, Category.assoc, hjτ]
  have hm₁ : l ≫ m₁.left = (μ[A₀]).left ≫ i := by
    have h := congrArg (fun g => g.left) hLm₁
    simp only [Over.comp_left, Over.map_map_left, hL, hjl] at h
    exact h
  have one_mul₁ : lift (toUnit X ≫ E) (𝟙 X) ≫ m₁ = 𝟙 X := by
    rw [hm₁d, ← Category.assoc, ← hτd, IsIso.hom_inv_id]
  have hEE : lift E E ≫ m₁ = E := by
    have h := congrArg (fun g => E ≫ g) one_mul₁
    simp only [comp_lift_assoc, Category.comp_id] at h
    rwa [← Category.assoc, toUnit_unique (E ≫ toUnit X) (𝟙 _), Category.id_comp] at h

  have hμ : μ[A₀] = fst A₀ A₀ * snd A₀ A₀ := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have σ₀iso : IsIso (lift (fst A₀ A₀) μ[A₀]) := by
    refine ⟨⟨lift (fst A₀ A₀) ((fst A₀ A₀)⁻¹ * snd A₀ A₀), ?_, ?_⟩⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · rw [Category.assoc, lift_snd, comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, hμ, inv_mul_cancel_left,
          Category.id_comp]
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · rw [Category.assoc, lift_snd, hμ, comp_mul, lift_fst, lift_snd, mul_inv_cancel_left, Category.id_comp]
  have hl₂ : IsPullback l (A₀ ⊗ A₀).hom (X ⊗ X).hom (spMap π) := GlobalTheory.AbDual.isPullback_prod hi hi hl1 hl2
  have hLfst : L ≫ fst X X = (Over.map (spMap π)).map (fst A₀ A₀) ≫ jA := by rw [hLd, lift_fst]
  have hLσ : L ≫ lift (fst X X) m₁ = (Over.map (spMap π)).map (lift (fst A₀ A₀) μ[A₀]) ≫ L := by
    rw [comp_lift, hLm₁, hLfst, ← pt]
  have σiso : IsIso (lift (fst X X) m₁) := by
    refine GlobalTheory.T.isIso_of_flat_pullback_reduction R R₀ π hπ hN (X ⊗ X) (X ⊗ X) (A₀ ⊗ A₀) (A₀ ⊗ A₀) l l hl₂ hl₂ inferInstance _ _ ?_ σ₀iso
    have h := congrArg (fun g => g.left) hLσ
    simp only [Over.comp_left, Over.map_map_left, hL] at h
    exact h
  have toLeft : ∀ {P Q : Over (Sp R)} (a : Q ⟶ P) (f f' : P ⟶ X), a ≫ f = a ≫ f' → a.left ≫ f.left = a.left ≫ f'.left :=
    fun a f f' h => by simpa only [Over.comp_left] using congrArg (fun g => g.left) h
  have EXT := GlobalTheory.T.eq_of_shear_automorphism_lift_nilpotent R R₀ π hπ hN A₀ X i hi l hl1 hl2 m₁ hm₁ σiso
  have hEu : toUnit (𝟙_ (Over (Sp R))) = 𝟙 _ := toUnit_unique _ _

  have mul_one₁ : lift (𝟙 X) (toUnit X ≫ E) ≫ m₁ = 𝟙 X := by
    refine EXT X A₀ i hi hsm hpX hgX e he _ _ ?_ ?_
    · rw [← hjl]
      apply toLeft
      rw [comp_lift_assoc, Category.comp_id, hjE]
      have h := ptm₁ A₀ (𝟙 A₀) 1
      rw [hj, _root_.mul_one, hj] at h
      exact h
    · rw [← hEl]
      apply toLeft
      simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, hEu, Category.id_comp, hEE]

  have comm₁ : (β_ X X).hom ≫ m₁ = m₁ := by
    refine EXT (X ⊗ X) (A₀ ⊗ A₀) l hl₂ s2 p2 g2 (lift E E).left (by simpa using Over.w (lift E E)) _ _ ?_ ?_
    · rw [← hL]
      apply toLeft
      rw [hLd, lift_braiding_hom_assoc, ptm₁, ptm₁, _root_.mul_comm]
    · apply toLeft
      rw [lift_braiding_hom_assoc]

  obtain ⟨L₃, hL₃d⟩ : ∃ L₃ : (Over.map (spMap π)).obj ((A₀ ⊗ A₀) ⊗ A₀) ⟶ (X ⊗ X) ⊗ X,
      L₃ = lift (lift ((Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀ ≫ fst A₀ A₀) ≫ jA)
        ((Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀ ≫ snd A₀ A₀) ≫ jA)) ((Over.map (spMap π)).map (snd (A₀ ⊗ A₀) A₀) ≫ jA) :=
    ⟨_, rfl⟩
  have hL₃1 : L₃ ≫ fst (X ⊗ X) X = (Over.map (spMap π)).map (fst (A₀ ⊗ A₀) A₀) ≫ L := by
    rw [hL₃d, lift_fst, pt, ← comp_lift, lift_fst_snd, Category.comp_id]
  have hL₃2 : L₃ ≫ snd (X ⊗ X) X = (Over.map (spMap π)).map (snd (A₀ ⊗ A₀) A₀) ≫ jA := by
    rw [hL₃d, lift_snd]
  have hk3 : IsPullback L₃.left ((A₀ ⊗ A₀) ⊗ A₀).hom ((X ⊗ X) ⊗ X).hom (spMap π) := by
    refine GlobalTheory.AbDual.isPullback_prod hl₂ hi (h := L₃.left) ?_ ?_
    · rw [← Over.comp_left, hL₃1, Over.comp_left, Over.map_map_left, hL]
    · rw [← Over.comp_left, hL₃2, Over.comp_left, Over.map_map_left, hjl]
  have assoc₁ : (m₁ ▷ X) ≫ m₁ = (α_ X X X).hom ≫ (X ◁ m₁) ≫ m₁ := by
    refine EXT ((X ⊗ X) ⊗ X) ((A₀ ⊗ A₀) ⊗ A₀) L₃.left hk3 s3 p3 g3 (lift (lift E E) E).left
      (by simpa using Over.w (lift (lift E E) E)) _ _ ?_ ?_
    · apply toLeft
      rw [hL₃d]
      simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, ptm₁]
      rw [_root_.mul_assoc]
    · apply toLeft
      simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hEE]

  obtain ⟨iX, hiXd⟩ : ∃ iX : X ⟶ X, iX = lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁) ≫ snd X X := ⟨_, rfl⟩
  have right_inv₁ : lift (𝟙 X) iX ≫ m₁ = toUnit X ≫ E := by
    have hp : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ lift (fst X X) m₁ = lift (𝟙 X) (toUnit X ≫ E) := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have h1 : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ fst X X = 𝟙 X := by
      have h := congrArg (· ≫ fst X X) hp
      simp only [Category.assoc, lift_fst] at h
      simpa only [Category.assoc] using h
    have h2 : (lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁)) ≫ m₁ = toUnit X ≫ E := by
      have h := congrArg (· ≫ snd X X) hp
      simp only [Category.assoc, lift_snd] at h
      simpa only [Category.assoc] using h
    have h3 : lift (𝟙 X) iX = lift (𝟙 X) (toUnit X ≫ E) ≫ inv (lift (fst X X) m₁) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, h1]
      · rw [lift_snd, hiXd, Category.assoc]
    rw [h3, h2]
  have left_inv₁ : lift iX (𝟙 X) ≫ m₁ = toUnit X ≫ E := by
    rw [← comm₁, lift_braiding_hom_assoc, right_inv₁]
  letI G : GrpObj X :=
    { one := E
      mul := m₁
      inv := iX
      one_mul := by
        rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id, ← one_mul₁, ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_one := by
        rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id, ← mul_one₁, ← Category.assoc]
        congr 1
        ext1 <;> simp
      mul_assoc := assoc₁
      left_inv := left_inv₁
      right_inv := right_inv₁ }
  refine ⟨G, ⟨hi, fun T x y x₀ y₀ hx hy => ?_⟩, ⟨⟨comm₁⟩, hsm, hpX, hgX⟩⟩
  have ex : ∀ (z : T ⟶ A₀) (z₀ : Over.mk (T.hom ≫ spMap π) ⟶ X), z₀.left = z.left ≫ i →
      z₀ = (Over.map (spMap π)).map z ≫ jA := fun z z₀ h => by
    ext1
    rw [h, Over.comp_left, Over.map_map_left, hjl]
  rw [ex x x₀ hx, ex y y₀ hy, Hom.mul_def]
  change (lift ((Over.map (spMap π)).map x ≫ jA) ((Over.map (spMap π)).map y ≫ jA) ≫ m₁).left = _
  rw [ptm₁, Over.comp_left, Over.map_map_left, hjl]

end GlobalTheory.LiftGroupLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagePrincipalOfEffCartier
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.VB

theorem mem_annihilator_cokernel_iff {X : Scheme.{0}} {E L : X.Modules} (φ : E ⟶ L)
    [SheafOfModules.IsQuasicoherent E] [SheafOfModules.IsQuasicoherent L]
    [QCoh.IsFiniteQC (Limits.cokernel φ)] {U : X.Opens} (hU : IsAffineOpen U)
    {l : Fin 1 → Γ(L, U)} (hl : IsFrame l) (a : Γ(X, U)) :
    a ∈ Module.annihilator Γ(X, U) Γ(Limits.cokernel φ, U) ↔ ∃ u, φ.app U u = a • l 0 := by
  have hex : Function.Exact (φ.app U) ((Limits.cokernel.π φ).app U) :=
    QCoh.exact_app_of_exact (S := ShortComplex.mk φ (Limits.cokernel.π φ)
      (Limits.cokernel.condition φ)) (ShortComplex.exact_cokernel φ) hU
  have hsur := QCoh.surjective_app_of_epi (Limits.cokernel.π φ) hU
  have hsm (b : Γ(X, U)) (s : Γ(L, U)) :
      (Limits.cokernel.π φ).app U (b • s) = b • (Limits.cokernel.π φ).app U s :=
    (QCoh.appLinear (Limits.cokernel.π φ) U).map_smul b s
  rw [Module.mem_annihilator]
  constructor
  · intro H
    refine (hex _).1 ?_
    rw [hsm]
    exact H _
  · rintro ⟨u, hu⟩ m
    obtain ⟨s, rfl⟩ := hsur m
    have h0 : a • (Limits.cokernel.π φ).app U (l 0) = 0 := by
      rw [← hsm]
      exact (hex _).2 ⟨u, hu⟩
    have hs := (hl.basis le_rfl).sum_repr s
    rw [Fin.sum_univ_one, IsFrame.basis_apply, Twist.resM_self] at hs
    rw [← hs, hsm, smul_comm, h0, smul_zero]

theorem exists_image_principal_of_effCartier : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (ρ : Y ⟶ X) (E L : X.Modules) (φ : E ⟶ L) (r : ℕ) [GlobalTheory.QCoh.IsFiniteQC (Limits.cokernel φ)], IsVB E r → IsVB L 1 → ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((GlobalTheory.QCoh.annihilatorSheaf (Limits.cokernel φ)).comap ρ) → ∀ y : Y, ∃ (V : Y.Opens) (l : Fin 1 → Γ((Scheme.Modules.pullback ρ).obj L, V)) (g : Γ(Y, V)) (t : Γ((Scheme.Modules.pullback ρ).obj E, V)), y ∈ V ∧ IsFrame l ∧ g ≠ 0 ∧ ((Scheme.Modules.pullback ρ).map φ).app V t = g • l 0 ∧ ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ((Scheme.Modules.pullback ρ).obj E, W)), ∃ a : Γ(Y, W), ((Scheme.Modules.pullback ρ).map φ).app W s = a • GlobalTheory.Twist.resM ((Scheme.Modules.pullback ρ).obj L) h (g • l 0) := by
  intro X Y _ ρ E L φ r _ hE hL hC y
  haveI := hE.isQuasicoherent
  haveI := hL.isQuasicoherent
  obtain ⟨U₀, l₀, hyU₀, hl₀⟩ := hL (ρ y)
  obtain ⟨U, e, hU, hyU, hle, he⟩ := hE.exists_affine hyU₀
  have hl := hl₀.res hle
  set l : Fin 1 → Γ(L, U) := fun i => resM L hle (l₀ i) with hldef
  obtain ⟨U', f, hyU', hf, hI⟩ := hC y
  obtain ⟨h, hhle, hyh⟩ := U'.2.exists_basicOpen_le (V := ρ ⁻¹ᵁ U) ⟨y, hyU⟩ hyU'
  let A : Y.affineOpens := Y.affineBasicOpen h
  have hAU : (A : Y.Opens) ≤ ρ ⁻¹ᵁ U := hhle
  have hAU' : A ≤ U' := Y.basicOpen_le h
  have hyA : y ∈ (A : Y.Opens) := hyh
  let g : Γ(Y, A) := Y.presheaf.map (homOfLE hAU').op f
  have hI1 : ((QCoh.annihilatorSheaf (Limits.cokernel φ)).comap ρ).ideal A = Ideal.span {g} := by
    rw [← Scheme.IdealSheafData.map_ideal _ hAU', hI, Ideal.map_span, Set.image_singleton]
  have hI2 := Principalise.comapIdealAffine (QCoh.annihilatorSheaf (Limits.cokernel φ)) ρ
    ⟨U, hU⟩ A hAU
  rw [hI1, QCoh.annihilatorSheaf_ideal] at hI2
  have hg : g ≠ 0 := by
    haveI : Nonempty (A : Y.Opens) := ⟨⟨y, hyA⟩⟩
    haveI : Nonempty (U' : Y.Opens) := ⟨⟨y, hyU'⟩⟩
    intro h0
    refine nonZeroDivisors.ne_zero hf ?_
    apply map_injective_of_isIntegral Y (homOfLE (show (A : Y.Opens) ≤ U' from hAU'))
    rw [map_zero]
    exact h0
  have hres (F : X.Modules) (s : Γ(F, U)) :
      resM _ hAU (QCoh.pullbackSections ρ F le_rfl s) = QCoh.pullbackSections ρ F hAU s :=
    QCoh.res_pullbackSections ρ F le_rfl hAU s
  have hl' : IsFrame fun i => QCoh.pullbackSections ρ L hAU (l i) := by
    simpa only [hres] using (hl.pullback ρ).res hAU
  have he' : IsFrame fun i => QCoh.pullbackSections ρ E hAU (e i) := by
    simpa only [hres] using (he.pullback ρ).res hAU
  set l' := QCoh.pullbackSections ρ L hAU (l 0) with hl'def
  let ψ := (Scheme.Modules.pullback ρ).map φ
  have key (u : Γ(E, U)) (a : Γ(X, U)) (hu : φ.app U u = a • l 0) :
      ψ.app A (QCoh.pullbackSections ρ E hAU u) = ρ.appLE U A hAU a • l' := by
    rw [QCoh.pullback_map_app_pullbackSections, hu, QCoh.pullbackSections_smul]
  let J : Ideal Γ(Y, A) := (LinearMap.range (QCoh.appLinear ψ A)).comap
    (LinearMap.toSpanSingleton Γ(Y, A) _ l')
  have hgJ : g ∈ J := by
    have : Ideal.span {g} ≤ J := by
      rw [hI2, Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨u, hu⟩ := (mem_annihilator_cokernel_iff φ hU hl a).1 ha
      exact ⟨_, key u a hu⟩
    exact this (Ideal.subset_span rfl)
  obtain ⟨t, ht⟩ := hgJ
  have hei (i : Fin r) : ∃ c : Γ(Y, A),
      ψ.app A (QCoh.pullbackSections ρ E hAU (e i)) = c • (g • l') := by
    have hs := (hl.basis le_rfl).sum_repr (φ.app U (e i))
    rw [Fin.sum_univ_one, IsFrame.basis_apply, Twist.resM_self] at hs
    have hm : ρ.appLE U A hAU ((hl.basis le_rfl).repr (φ.app U (e i)) 0) ∈ Ideal.span {g} := by
      rw [hI2]
      exact Ideal.mem_map_of_mem _ ((mem_annihilator_cokernel_iff φ hU hl _).2 ⟨_, hs.symm⟩)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨c, by rw [key _ _ hs.symm, ← hc, mul_smul]⟩
  choose c hc using hei
  refine ⟨A, _, g, t, hyA, hl', hg, ht, fun W hW s => ?_⟩
  refine ⟨∑ i, (he'.basis hW).repr s i * resG Y hW (c i), ?_⟩
  have hs := (he'.basis hW).sum_repr s
  calc ψ.app W s = QCoh.appLinear ψ W (∑ i, (he'.basis hW).repr s i • he'.basis hW i) := by
        rw [hs]; rfl
    _ = _ := by
      rw [map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, IsFrame.basis_apply, QCoh.appLinear_apply, app_resM, hc, resM_smul, mul_smul]

end GlobalTheory.VB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O.CompModel

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem stalkPt_genStr (C : FlagCpt Z e) (z : C.Y.X) (φ : c.F →+* C.Y.X.presheaf.stalk z)
    (hφ : constF e C.Y = (algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField).comp φ) :
    stalkPt C.Y z ≫ C.π ≫ genStr Z = spMap φ := by
  let ρ : c.F →+* C.Y.X.presheaf.stalk z := (Spec.preimage (stalkPt C.Y z ≫ C.π ≫ genStr Z)).hom
  have h0 : spMap ρ = stalkPt C.Y z ≫ C.π ≫ genStr Z := Spec.map_preimage _
  let j := algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField
  letI := (constF e C.Y).toAlgebra
  have hgen : spMap j ≫ stalkPt C.Y z = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)
  have h1 : spMap (j.comp ρ) = spMap (constF e C.Y) := by
    rw [← sp_comp, h0, ← Category.assoc, ← Category.assoc, hgen]
    exact (congrArg (· ≫ genStr Z) C.y0_x.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) Z.jQ_over).trans (pullback.lift_snd _ _ _)))
  have h2 : j.comp ρ = constF e C.Y := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : ρ = φ := RingHom.ext fun r => IsFractionRing.injective (C.Y.X.presheaf.stalk z) C.Y.X.functionField
      ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hφ r))
  rw [← h0, h3]

theorem exists_flagPt (C : FlagCpt Z e) {K : Type} [Field K] (p : Sp K ⟶ C.Y.X) :
    ∃ y : FlagPt Z K, p ≫ C.π = y.y ∧ C.Carries p y.frame := by
  obtain ⟨φ, f, t, hT, -⟩ := C.gr_spec (below p)
  let ψ : C.Y.X.presheaf.stalk (below p) →+* K := (Scheme.stalkClosedPointTo p).hom
  have hp : p = spMap ψ ≫ stalkPt C.Y (below p) := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  have hx : spMap ψ ≫ stalkPt C.Y (below p) ≫ C.π ≫ genι Z = (p ≫ C.π) ≫ genι Z := by
    rw [← Category.assoc, ← hp, Category.assoc]
  obtain ⟨g, hg⟩ : ∃ g : EigFrame Z (ψ.comp φ) ((p ≫ C.π) ≫ genι Z), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
    rw [← hx]
    exact EigFrame.exists_baseChange E H Dw l Xo c O β Z _ _ φ _ f ψ
  have ho : (p ≫ C.π) ≫ genStr Z = spMap (ψ.comp φ) := by
    rw [← sp_comp, ← stalkPt_genStr C _ φ hT.2.1, ← Category.assoc (spMap ψ), ← hp, Category.assoc]
  refine ⟨⟨ψ.comp φ, p ≫ C.π, ho, g.v, g.tan, g.eig, g.basis⟩, rfl, below p, ψ, φ, f, t, 1, hp, hT, hx.symm, rfl,
    fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  have := isCombAtG_single Z.t _ (g.tan τ) i
  rw [show (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g.v τ from funext fun k => (hg τ k).symm]
  exact this

end Free

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : TrueGeo.Model Y)

theorem dense_image_j (S : Set Y.X) : Dense (M.j '' S) ↔ Dense S := by
  have := M.ar.isIntegral
  have := SmallSec.isPreimmersion_j M
  have hd : DenseRange M.j := fun x =>
    (genericPoint_specializes x).mem_closed isClosed_closure
      (subset_closure (SmallSec.mem_range_j M (SmallSec.asIdeal_p_gen M)))
  exact (IsDenseInducing.mk M.j.isEmbedding.isInducing hd).dense_image

theorem irreducible_fibre {K : Type} [Field K] (σ : F →+* K) :
    IrreducibleSpace ↥(pullback M.p (spMap (σ.comp (algebraMap (𝓞 F) F)))) := by
  have h := ((IsPullback.of_hasPullback Y.str (spMap σ)).paste_horiz M.pb)
  rw [sp_comp] at h
  have : IsIntegral (pullback Y.str (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := Y.str) _ _ _ (IsPullback.of_hasPullback Y.str (spMap σ))
  exact h.isoPullback.hom.homeomorph.irreducibleSpace_iff.1 inferInstance

theorem isAlgPt_iff {K : Type} [Field K] (ε : K ≃+* AlgebraicClosure ℚ) (x : M.X) :
    IsAlgPt x ↔ ∃ p : Sp K ⟶ Y.X, M.j (below p) = x := by
  have hb {K K' : Type} [Field K] [Field K'] (a : K →+* K') (p : Sp K ⟶ Y.X) : below (spMap a ≫ p) = below p :=
    congrArg p (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  constructor
  · intro hx
    let σ : F →+* AlgebraicClosure ℚ := (IsAlgClosed.lift (R := ℚ) (S := F) (M := AlgebraicClosure ℚ)).toRingHom
    obtain ⟨z, rfl⟩ := exists_geomPt M.ar (σ.comp (algebraMap (𝓞 F) F)) hx
    have hz : z.1 ≫ M.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by rw [sp_comp]; exact z.2
    refine ⟨spMap ε.symm.toRingHom ≫ M.pb.lift z.1 (spMap σ) hz, ?_⟩
    rw [hb]
    exact congrArg (fun q : Sp (AlgebraicClosure ℚ) ⟶ M.X => q (IsLocalRing.closedPoint _)) (M.pb.lift_fst z.1 (spMap σ) hz)
  · rintro ⟨p, rfl⟩
    rw [← hb ε.toRingHom p]
    let q := spMap ε.toRingHom ≫ p
    exact GeomPt.isAlgPt (ι := (Spec.preimage ((q ≫ M.j) ≫ M.p)).hom) M.ar ⟨q ≫ M.j, (Spec.map_preimage _).symm⟩

end Model

theorem exists_isCompModel : ∀ (D : D7) (O : Setup D) (A : SlopeTestRemainingChoices O.Y), O.IsFlagHeightData A → ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (hM : IsArithVar M.p (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y)), ∃ b : O.Y.Pt → M.X, (∀ y : ShFam.Pad.Pt O.s, ShFam.Pad.compPt O.s y = c → b y = M.j (baseOn O.Φ c y)) ∧ IsCompModel A c (@ArMod.mk _ (𝓞 D.what₂.LL) _ M.X hM.isIntegral M.p hM) b := by
  intro D O A hA c M hM
  have : IsAlgClosure ℚ Qb := algebraicClosure.isAlgClosure ℚ ℂ
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, AlgebraicClosure.isAlgebraic ℚ⟩
  let ε : Qb ≃+* AlgebraicClosure ℚ := (IsAlgClosure.equiv ℚ Qb (AlgebraicClosure ℚ)).toRingEquiv
  refine ⟨fun y : ShFam.Pad.Pt O.s => M.j (baseOn O.Φ c y), fun _ _ => rfl, ⟨_, irreducible_fibre M
    (IsAlgClosed.lift (R := ℚ) (S := D.what₂.LL) (M := AlgebraicClosure ℚ)).toRingHom⟩, ?_, fun Z => ?_⟩
  · refine Set.ext fun x : M.X => Iff.trans ?_ (isAlgPt_iff M ε x).symm
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain rfl : compPt O.s y = c := hy
      obtain ⟨p, -, -, hp⟩ := liesUnder_basePt O.Φ y
      exact ⟨p, congrArg M.j hp⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨y, h₁, h₂⟩ := exists_flagPt (O.Φ.C c) p
      have h : LiesUnder O.Φ c y (below p) := ⟨p, h₁, h₂, rfl⟩
      obtain rfl : compPt O.s y = c := h.compPt_eq
      exact ⟨y, rfl, congrArg M.j ((existsUnique_liesUnder O.Φ y).unique (liesUnder_basePt O.Φ y) h)⟩
  · refine (hA.dense c Z).trans (and_congr Iff.rfl ?_)
    exact (dense_image_j M _).symm.trans (iff_of_eq (congrArg Dense (Set.image_image _ _ (Z : Set (ShFam.Pad.Pt O.s)))))

end GlobalTheory.Mean4O.CompModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeThetaJetsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatumBaseChange_thetaJets : ∀ (K C : Type) [Field K] [Field C] (f : K →+* C) (x : KeyIn K), ∃ (xC : KeyIn C) (hg : xC.P.g = x.P.g) (io : (Over.mk (spMap f) ⟶ x.P.A) ≃* (baseOver (Sp C) ⟶ xC.P.A)), KeyPB xC x f ∧ (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs xC.P.A xC.P.L k (io a) (io b) z → WeilIs x.P.A x.P.L k a b z) ∧ ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap f)))) (I : Type) (pt : I → (Over.mk (spMap f) ⟶ x.P.A)) (y : Fin x.P.g → (Sp (DualNumber C) ⟶ (Over.mk (spMap f) ⊗ x.P.A).left)) (ϑ : I → C) (J : I → Fin x.P.g → C), IsPolAVSectionInverseImage x.P (Over.mk (spMap f)) x.th th → (∀ j, y j ≫ (fst (Over.mk (spMap f)) x.P.A).left = spMap (algebraMap C (DualNumber C)) ∧ y j ≫ (snd (Over.mk (spMap f)) x.P.A).left = spMap (dualMap f) ≫ (x.v j).left) → ThJetT x.P x.rig m (spMap f) th pt y ϑ J → ThJet xC hg m (fun i => io (pt i)) ϑ J := by
  first | exact @GlobalTheory.MBLow.exists_keyPB_thJet | exact GlobalTheory.MBLow.exists_keyPB_thJet | (intros; apply GlobalTheory.MBLow.exists_keyPB_thJet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumFibreOfGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatum_fibre_of_grpPullback : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (y : KeyIn R) (P : PolAV (Sp K)) (φ : P.A.left ⟶ y.P.A.left) (hp : 1 ≤ P.g) (rig : LB.Gen (P.L.pull (eSec P.A))) (hr : rig.IsGen), P.g = y.P.g → IsGrpPullback P.A y.P.A (spMap f) φ → LBIso P.L (y.P.L.pull φ) → ∃ th hth v hv, KeyAtMap ⟨P, hp, rig, hr, th, hth, v, hv⟩ y f φ := by
  first | exact @GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback | exact GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback | (intros; apply GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumPolarisedAbelianLocalDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatum_polarisedAbelian_localDomain : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (P : PolAV (Sp W)), 1 ≤ P.g → ∃ y : KeyIn W, y.P = P := by
  first | exact @GlobalTheory.MBLow.exists_keyIn_local | exact GlobalTheory.MBLow.exists_keyIn_local | (intros; apply GlobalTheory.MBLow.exists_keyIn_local <;> assumption)
end

