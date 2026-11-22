import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0136
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0137
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionUniversalSquareZero

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialValueOfFactorPullbacks
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem bv_pulln_box {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {N p q : ℕ}
    (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1)) (x : Cn F N) :
    (bv F ρ₁ ρ₂ (pulln (boxL F) N x) = fun a _ ↦ pr F ρ₁ x a ⊗ₜ[R] 1) ∧
      (bv F ρ₁ ρ₂ (pulln (boxR F) N x) = fun _ b ↦ 1 ⊗ₜ[R] pr F ρ₂ x b) := by
  refine ⟨funext fun a => funext fun b => ?_, funext fun a => funext fun b => ?_⟩
  · show Algebra.TensorProduct.map _ _ (_ ⊗ₜ[R] 1) = _
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    congr 1
    all_goals first | exact map_one _ | rfl
  · show Algebra.TensorProduct.map _ _ (1 ⊗ₜ[R] _) = _
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    congr 1
    all_goals first | exact map_one _ | rfl

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxEvaluationPullbackLeftRight
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

private theorem cochainReindex_apply_const_obj (F : C ⥤ CommAlgCat.{0} R) {n m : ℕ}
    (e : Fin (n + 1) →o Fin (m + 1)) (x : MainStatements.Hodge.Cn F n) (T₀ : C) :
    GlobalTheory.CompanionTheory.HopfC.pr F e x ((Functor.const (Fin (m + 1))).obj T₀) =
      x ((Functor.const (Fin (n + 1))).obj T₀) := by
  first
  | exact GlobalTheory.CatCoh.mp_id F T₀ _
  | exact (GlobalTheory.CatCoh.mp_id F T₀ (x ((Functor.const (Fin (n + 1))).obj T₀)) : _)
  | (simp only [GlobalTheory.CompanionTheory.HopfC.pr]; exact GlobalTheory.CatCoh.mp_id F T₀ _)

theorem cocycle_const (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (x : Cn F 1) (hx : dn F 1 x = 0) :
    x ((Functor.const (Fin (1 + 1))).obj T₀) = 0 := by
  have h : MainStatements.Hodge.dn F 1 x ((Functor.const (Fin (1 + 1 + 1))).obj T₀) = 0 := by
    rw [hx]; rfl
  rw [GlobalTheory.CompanionTheory.HopfC.dn_eq] at h
  first
  | rw [Fin.sum_univ_three] at h
  | simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  simp only [Pi.add_apply, Pi.smul_apply, cochainReindex_apply_const_obj] at h
  first
  | simpa using h
  | (norm_num at h; exact h)

theorem evL_tmul_one (F : C ⥤ CommAlgCat.{0} R) (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (a : F.obj T₀) :
    evL F T₀ T ε (a ⊗ₜ[R] 1) = algebraMap R (F.obj T) (ε a) := by
  first
  | simp [MainStatements.Hodge.evL, Algebra.ofId_apply]
  | (rw [MainStatements.Hodge.evL, Algebra.TensorProduct.lift_tmul]; simp [Algebra.ofId_apply])

theorem evL_one_tmul (F : C ⥤ CommAlgCat.{0} R) (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (b : F.obj T) :
    evL F T₀ T ε (1 ⊗ₜ[R] b) = b := by
  first
  | simp [MainStatements.Hodge.evL, Algebra.ofId_apply]
  | (rw [MainStatements.Hodge.evL, Algebra.TensorProduct.lift_tmul]; simp [Algebra.ofId_apply])

theorem boxE_pull_boxL_boxR (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1)
    (hx : dn F 1 x = 0) :
    pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 ∧ pulln (boxE F T₀ ε) 1 (pulln (boxR F) 1 x) = x := by
  have h0 := GlobalTheory.CompanionTheory.HopfC.cocycle_const F T₀ x hx
  refine ⟨?_, ?_⟩
  · funext c
    calc _ = MainStatements.Hodge.evL F T₀ (c.obj (Fin.last 1)) ε
          (x ((Functor.const (Fin (1 + 1))).obj T₀) ⊗ₜ[R] 1) := rfl
      _ = algebraMap R _ (ε (x ((Functor.const (Fin (1 + 1))).obj T₀))) :=
          GlobalTheory.CompanionTheory.HopfC.evL_tmul_one F T₀ _ ε _
      _ = 0 := by rw [h0, map_zero, map_zero]
  · funext c
    calc _ = MainStatements.Hodge.evL F T₀ (c.obj (Fin.last 1)) ε (1 ⊗ₜ[R] x c) := rfl
      _ = x c := GlobalTheory.CompanionTheory.HopfC.evL_one_tmul F T₀ _ ε _

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianRepresentationsResidueStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitian_representations_residue : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E), cT τ S = S → IsUnit S.det → cT τ T = T → IsUnit T.det → (Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings | exact GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings | (intros; apply GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechStructureSheafComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

section

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of R)) [Algebra R Γ(X, ⊤)]

theorem secMap_eq_restrictGlobal
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    (W : X.Opens) (r : R) :
    (GlobalTheory.CechDR.secMap s W).hom r = GlobalTheory.restrictGlobal X W (algebraMap R Γ(X, ⊤) r) := by
  rw [← GlobalTheory.map_restrictGlobal (homOfLE (le_top : W ≤ ⊤)) (algebraMap R Γ(X, ⊤) r),
    GlobalTheory.restrictGlobal_top, hs]
  rfl

def secRes (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W ≤ U) : GlobalTheory.CechDR.Sec s U →ₗ[R] GlobalTheory.sectionsOn (GlobalTheory.structureModule X) W where
  toFun x := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (X.presheaf.map (homOfLE h).op (x : Γ(X, U)))
  map_add' x y := map_add (X.presheaf.map (homOfLE h).op).hom (x : Γ(X, U)) (y : Γ(X, U))
  map_smul' r x := by
    apply (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective
    rw [RingHom.id_apply, GlobalTheory.sectionsOn.toΓ_smul, ← secMap_eq_restrictGlobal s hs W r]
    have e : (GlobalTheory.CechDR.secMap s W).hom r =
        X.presheaf.map (homOfLE h).op ((GlobalTheory.CechDR.secMap s U).hom r) :=
      (congrArg (fun q ↦ q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (s.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)).symm
    have key : ∀ y : Γ(X, U), X.presheaf.map (homOfLE h).op ((GlobalTheory.CechDR.secMap s U).hom r * y) =
        (GlobalTheory.CechDR.secMap s W).hom r * X.presheaf.map (homOfLE h).op y := fun y ↦ by
      rw [e]
      exact map_mul (X.presheaf.map (homOfLE h).op).hom _ y
    exact key x

private theorem sectionsOn_toΓ_secRes_eq_presheaf_map
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W ≤ U) (x : GlobalTheory.CechDR.Sec s U) :
    GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W (secRes s hs h x) =
      X.presheaf.map (homOfLE h).op (x : Γ(X, U)) :=
  AddEquiv.apply_symm_apply _ _

theorem secRes_bijective
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U W : X.Opens} (h : W = U) : Function.Bijective (secRes s hs h.le) := by
  subst h
  have key : ∀ x : GlobalTheory.CechDR.Sec s W, secRes s hs (le_refl W) x =
      (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm (x : Γ(X, W)) := by
    intro x
    have hx : X.presheaf.map (homOfLE (le_refl W)).op (x : Γ(X, W)) = (x : Γ(X, W)) := by
      change (X.presheaf.map (𝟙 (op W))) (x : Γ(X, W)) = x
      rw [X.presheaf.map_id]
      rfl
    exact congrArg (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm hx
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · rw [key, key] at hxy
    exact (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm.injective hxy
  · refine ⟨(show GlobalTheory.CechDR.Sec s W from GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W y), ?_⟩
    rw [key]
    exact (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).symm_apply_apply y

private theorem sectionsOn_toΓ_res_eq_presheaf_map {U V : X.Opens} (h : V ≤ U)
    (y : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) U) :
    GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) V (GlobalTheory.sectionsOn.res R (GlobalTheory.structureModule X) h y) =
      (GlobalTheory.structureModule X).presheaf.map (homOfLE h).op (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) U y) :=
  GlobalTheory.WithAction.toBase_linearMap _ _ R _ _ y

theorem secRes_square
    (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
    {U V V' W : X.Opens} (a : V ≤ U) (b : W ≤ V) (c : V' ≤ U) (d : W ≤ V') (x : GlobalTheory.CechDR.Sec s U) :
    secRes s hs b (GlobalTheory.CechDR.Sec.res s a x) =
      GlobalTheory.sectionsOn.res R (GlobalTheory.structureModule X) d (secRes s hs c x) := by
  apply (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) W).injective
  rw [sectionsOn_toΓ_secRes_eq_presheaf_map, sectionsOn_toΓ_res_eq_presheaf_map, sectionsOn_toΓ_secRes_eq_presheaf_map]
  change (X.presheaf.map (homOfLE b).op) ((X.presheaf.map (homOfLE a).op) (x : Γ(X, U))) =
    (X.presheaf.map (homOfLE d).op) ((X.presheaf.map (homOfLE c).op) (x : Γ(X, U)))
  have h1 : X.presheaf.map (homOfLE a).op ≫ X.presheaf.map (homOfLE b).op =
      X.presheaf.map (homOfLE c).op ≫ X.presheaf.map (homOfLE d).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (fun f : X.presheaf.obj (op U) ⟶ X.presheaf.obj (op W) => f (x : Γ(X, U))) h1

end

section

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of R)) [Algebra R Γ(X, ⊤)]
  {P : Type} [SemilatticeInf P] (S : MainStatements.Hodge.Sys X P) {κ : Type} (e : κ → P)

theorem sys_inf' (t : Finset κ) (ht : t.Nonempty) :
    (S.u (t.inf' ht e)).1 = ⊤ ⊓ ⨅ i ∈ t, (S.u (e i)).1 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact absurd ht Finset.not_nonempty_empty
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · rw [Finset.inf'_insert hs, S.map_inf, ih hs, Finset.iInf_insert]
      simp only [top_inf_eq]
    · obtain rfl : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp

variable (hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))

def sysVertex (t : Finset κ) :
    (cubeOf e (toMod (MainStatements.Hodge.OSys s S))).obj t →ₗ[R]
      (GlobalTheory.cechCube R (GlobalTheory.structureModule X) ⊤ fun i ↦ (S.u (e i)).1).obj t :=
  if ht : t.Nonempty then
    (secRes s hs (sys_inf' S e t ht).ge) ∘ₗ
      LinearMap.proj (R := R) (φ := fun h : PLift t.Nonempty ↦
        ((toMod (MainStatements.Hodge.OSys s S)).obj (op (t.inf' h.down e)) : Type)) ⟨ht⟩
  else 0

theorem sysVertex_apply (t : Finset κ) (ht : t.Nonempty) (x : (cubeOf e (toMod (MainStatements.Hodge.OSys s S))).obj t) :
    sysVertex s S e hs t x = secRes s hs (sys_inf' S e t ht).ge (x ⟨ht⟩) := by
  unfold sysVertex
  rw [dif_pos ht]
  rfl

theorem sysVertex_of_not_nonempty (t : Finset κ) (ht : ¬ t.Nonempty) : sysVertex s S e hs t = 0 := by
  unfold sysVertex
  rw [dif_neg ht]

theorem sysVertex_bijective (t : Finset κ) (ht : t.Nonempty) : Function.Bijective (sysVertex s S e hs t) := by
  have hf : ⇑(sysVertex s S e hs t) = (secRes s hs (sys_inf' S e t ht).ge) ∘ (fun x => x ⟨ht⟩) :=
    funext fun x => sysVertex_apply s S e hs t ht x
  rw [hf]
  refine (secRes_bijective s hs (sys_inf' S e t ht).symm).comp ⟨fun x y hxy => ?_, fun y => ?_⟩
  · funext h
    obtain ⟨h⟩ := h
    exact hxy
  · exact ⟨fun _ => y, rfl⟩

def sysCube : cubeOf e (toMod (MainStatements.Hodge.OSys s S)) ⟶
    GlobalTheory.cechCube R (GlobalTheory.structureModule X) ⊤ fun i ↦ (S.u (e i)).1 :=
  GlobalTheory.Cube.homMk (sysVertex s S e hs) fun {t t'} h x ↦ by
    by_cases ht : t.Nonempty
    · have ht' : t'.Nonempty := ht.mono h
      rw [sysVertex_apply s S e hs t' ht', sysVertex_apply s S e hs t ht]
      have e1 := cubeRes_apply e (toMod (MainStatements.Hodge.OSys s S)) h x ht ⟨ht'⟩
      refine (congrArg (secRes s hs (sys_inf' S e t' ht').ge) e1).trans ?_
      exact secRes_square s hs _ _ _ _ (x ⟨ht⟩)
    · rw [sysVertex_of_not_nonempty s S e hs t ht, LinearMap.zero_apply, map_zero]
      by_cases ht' : t'.Nonempty
      · rw [sysVertex_apply s S e hs t' ht']
        have e1 := cubeRes_empty e (toMod (MainStatements.Hodge.OSys s S)) h x ht ⟨ht'⟩
        exact (congrArg (secRes s hs (sys_inf' S e t' ht').ge) e1).trans (map_zero _)
      · rw [sysVertex_of_not_nonempty s S e hs t' ht', LinearMap.zero_apply]

theorem isIso_sysCube [LinearOrder κ] : IsIso (GlobalTheory.cechComplexMap (sysCube s S e hs)) := by
  apply GlobalTheory.isIso_cechComplexMap
  intro t ht
  rw [sysCube, GlobalTheory.Cube.homMk_app, ModuleCat.hom_ofHom]
  exact sysVertex_bijective s S e hs t ht

end

theorem cech_OSys_homology_equiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) := by
  intro R _ X s P _ S κ _ e n
  letI := GlobalTheory.algebraΓOfHom s
  have hs : ∀ r : R, algebraMap R Γ(X, ⊤) r = s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) :=
    fun r => rfl
  haveI := isIso_sysCube s S e hs
  exact ⟨((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (asIso (GlobalTheory.cechComplexMap (sysCube s S e hs)))).toLinearEquiv⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_vanishing_from_cover : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS U S) j)) → ∀ j < s, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS U S) j)) → ∀ j, Subsingleton (CH.H F j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS U S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H F j)) := by
  first | exact @GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | exact GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover | (intros; apply GlobalTheory.CompanionTheory.CosieveMV.vanishing_of_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainHomotopyFiniteProjectorStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_homotopy_finite_projector : ∀ {R : Type} [CommRing R] (P : Type) [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R),
    ∃ (e : ∀ n, Cn F n →ₗ[R] Cn F n) (h : ∀ n, Cn F (n + 1) →ₗ[R] Cn F n) (B : ℕ),
      (∀ n, e n ∘ₗ e n = e n) ∧ (∀ n, e (n + 1) ∘ₗ dn F n = dn F n ∘ₗ e n) ∧
      e 0 = LinearMap.id + h 0 ∘ₗ dn F 0 ∧
      (∀ n, e (n + 1) = LinearMap.id + dn F n ∘ₗ h n + h (n + 1) ∘ₗ dn F (n + 1)) ∧
      ∀ n, B < n → e n = 0 := by
  first | exact @GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation | exact GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation | (intros; apply GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFil

section Rings

variable {R B : Type} [CommRing R] [CommRing B] {I : Ideal R} {J : Ideal B}

theorem dividedPowerFiltration_anti (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') : pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

theorem one_mem_pdP_zero (δ : DividedPowers J) : (1 : B) ∈ pdP δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem mul_mem_map (γ : DividedPowers I) (i : R →+* B) (r r' : ℕ) {x y : B}
    (hx : x ∈ (pdP γ r).map i) (hy : y ∈ (pdP γ r').map i) : x * y ∈ (pdP γ (r + r')).map i := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul] at h
  exact Ideal.map_mono (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le γ r r') h

theorem dpow_mem_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ (pdP γ n).map i := by
  have h0 : ∀ y ∈ J, δ.dpow 0 y ∈ (pdP γ 0).map i := fun y hy => by
    rw [δ.dpow_zero hy, ← map_one i]
    exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
  rw [hJ] at hx
  revert n
  refine Submodule.span_induction (p := fun x _ => ∀ n, δ.dpow n x ∈ (pdP γ n).map i) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩ n
    rw [hi.2 a ha]
    exact Ideal.mem_map_of_mem i (GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ n ha)
  · intro n
    by_cases hn : n = 0
    · subst hn
      exact h0 0 J.zero_mem
    · rw [δ.dpow_eval_zero hn]
      exact Ideal.zero_mem _
  · intro y z hy hz ihy ihz n
    have hy' : y ∈ J := hJ ▸ hy
    have hz' : z ∈ J := hJ ▸ hz
    rw [δ.dpow_add hy' hz']
    refine Ideal.sum_mem _ fun ab hab => ?_
    have e : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    rw [← e]
    exact mul_mem_map γ i _ _ (ihy _) (ihz _)
  · intro a y hy ihy n
    have hy' : y ∈ J := hJ ▸ hy
    rw [smul_eq_mul, δ.dpow_mul hy']
    exact Ideal.mul_mem_left _ _ (ihy n)

theorem dividedPowerFiltration_eq_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) (r : ℕ) : pdP δ r = (pdP γ r).map i := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map hi r hx)
  rintro _ ⟨l, hl, hr, rfl⟩
  have key : ∀ l : List (ℕ × B), (∀ q ∈ l, q.2 ∈ J) →
      (l.map fun q => δ.dpow q.1 q.2).prod ∈ (pdP γ (l.map Prod.fst).sum).map i := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [← map_one i]
      exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
    | cons a t ih =>
      intro h
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact mul_mem_map γ i _ _ (dpow_mem_map γ δ i hi hJ (h a (by simp)) _)
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
  exact Ideal.map_mono (dividedPowerFiltration_anti γ hr) (key l hl)

end Rings

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

theorem sub_mem_J (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (z : c.D.B) : f.φ z - g.φ z ∈ T.J := by
  obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
  have e := (hu _ f.pt).trans (hu _ g.pt).symm
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun e (Ideal.Quotient.mk _ z))

theorem sub_mem_pdP (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (n : ℕ) {x : c.D.B} (hx : x ∈ (pdP γ n).map c.D.i) : f.φ x - g.φ x ∈ pdP T.δ (n + 1) := by
  refine Submodule.span_induction (p := fun x _ => f.φ x - g.φ x ∈ pdP T.δ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, -, rfl⟩
    have e : f.φ (c.D.i a) - g.φ (c.D.i a) = 0 := by rw [f.comm, g.comm, sub_self]
    rw [e]
    exact Ideal.zero_mem _
  · rw [map_zero, map_zero, sub_zero]
    exact Ideal.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hy hz
  · intro a y hy ih
    have e : f.φ (a • y) - g.φ (a • y) = f.φ a * (f.φ y - g.φ y) + (f.φ a - g.φ a) * g.φ y := by
      rw [smul_eq_mul, map_mul, map_mul]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h1 : f.φ a - g.φ a ∈ pdP T.δ 1 := T.J_le_pdPow_one (sub_mem_J c hT f g a)
    have hm : (pdP γ n).map c.D.i ≤ pdP c.D.δ n :=
      Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map c.D.compat n hx
    have hy' : y ∈ pdP c.D.δ n := hm hy
    have h2 : g.φ y ∈ pdP T.δ n := dividedPowerFiltration_map g.dp n hy'
    have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ 1 n (Ideal.mul_mem_mul h1 h2)
    rwa [add_comm 1 n] at h3

theorem chart_grConst : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  intro O R _ _ I γ p X q κ V d c h Q hQ hD
  have h1 : ∀ r, c.D.pdPow r = (pdP γ r).map c.D.i := fun r =>
    dividedPowerFiltration_eq_map γ c.D.δ c.D.i c.D.compat c.J_eq r
  refine ⟨h1, ?_⟩
  intro n T σ σ' x hx
  have hx' : (show c.D.B from x) ∈ c.D.pdPow ((n : ℤ).toNat) := hx
  rw [Int.toNat_natCast, h1] at hx'
  change _ ∈ T.obj.pdPow (((n : ℤ) + 1).toNat)
  have e : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [e]
  exact sub_mem_pdP c (hQ _ T.property) σ.hom σ'.hom n hx'

end GlobalTheory.CompanionTheory.ChartFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChangeStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_empty_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d), ∃ (θ : R0 K n d ∅ →ₐ[K] C.R ∅) (hθ : ∀ b, θ (poly n K ∅ b) = toR C ∅ (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaEmpty.theta_empty <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartExtendBaseChangeStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_extend_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (θ₁ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ₁ : ∀ b, θ₁ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ₁ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) → IsBaseChange (Aa C) (thetaLin C θ₁ hθ₁) → ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc.theta_loc | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc.theta_loc | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc.theta_loc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSingletonBaseChangeStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_singleton_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (k : Fin d), ∃ (θ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) ∧ IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne.theta_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionUniversalSquareZeroStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_immersion_universal_square_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (P : Type) [CommRing P] (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R → (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) → j ≫ s = spMap α → spMap ε ≫ j = e → Mono j → (∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W) (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ := by
  first | exact @GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting | exact GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting | (intros; apply GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_along_ideal_filtration : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a : ℕ → IdF A),
    (∀ k T, (a (k + 1)).S T ≤ (a k).S T) → (∀ T, ∃ k, (a k).S T = ⊥) →
    (∀ k j, Subsingleton (CH.H (sq (a k) (a (k + 1))) j)) → ∀ j, Subsingleton (CH.H (sq (a 0) (IdF.bot A)) j) := by
  first | exact @GlobalTheory.CompanionTheory.TowerEnd.vanish | exact GlobalTheory.CompanionTheory.TowerEnd.vanish | (intros; apply GlobalTheory.CompanionTheory.TowerEnd.vanish <;> assumption)
end

