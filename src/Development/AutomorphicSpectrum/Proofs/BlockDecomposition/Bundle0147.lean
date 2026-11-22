import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0137
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainBaseChangeEquivalences
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CochainBC

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C]
    [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F'),
    ∃ (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F') (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F'),
      (∀ c, E₀ (1 ⊗ₜ c) = fun T ↦ m.α T (c T)) ∧ (∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ)) ∧
      (∀ c, E₂ (1 ⊗ₜ c) = fun T T' T'' φ ψ ↦ m.α T'' (c T T' T'' φ ψ)) ∧
      (∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x)) ∧ ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x) := by
  intro R R' _ _ _ C _ _ _ F F' m
  obtain ⟨E₀, hE₀⟩ := GlobalTheory.CompanionTheory.PerfExt.ext0 m
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.CompanionTheory.PerfExt.ext1 m
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.CompanionTheory.PerfExt.ext2 m
  refine ⟨E₀, E₁, E₂, hE₀, hE₁, hE₂, fun x => ?_, fun x => ?_⟩
  · have h := GlobalTheory.CompanionTheory.PerfExt.bc_ext (E₁.toLinearMap ∘ₗ (d0 F).baseChange R') ((d0 F') ∘ₗ E₀.toLinearMap) (by
      intro n
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, hE₁, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hE₀]
      funext T T' φ
      dsimp only
      rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, m.naturality])
    exact LinearMap.congr_fun h x
  · have h := GlobalTheory.CompanionTheory.PerfExt.bc_ext (E₂.toLinearMap ∘ₗ (d1 F).baseChange R') ((d1 F') ∘ₗ E₁.toLinearMap) (by
      intro n
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, hE₂, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hE₁]
      funext T T' T'' φ ψ
      dsimp only
      rw [d1_apply, d1_apply, map_add, map_sub, m.naturality])
    exact LinearMap.congr_fun h x

end GlobalTheory.CompanionTheory.CochainBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Low

variable {R : Type} [CommRing R]

theorem homology_equiv {A B D : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] [Module R A] [Module R B]
    [Module R D] (a : A →ₗ[R] B) (b : B →ₗ[R] D)
    (w : ModuleCat.ofHom a ≫ ModuleCat.ofHom b = 0) :
    Nonempty ((LinearMap.ker b ⧸ (LinearMap.range a).comap (LinearMap.ker b).subtype) ≃ₗ[R]
      (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).homology) := by
  have heq : (LinearMap.range a).comap (LinearMap.ker b).subtype =
      LinearMap.range (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).moduleCatToCycles := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ heq).trans
    (ShortComplex.mk (ModuleCat.ofHom a) (ModuleCat.ofHom b) w).moduleCatHomologyIso.symm.toLinearEquiv⟩

variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem d_eq (n : ℕ) : (nerveCx.obj (toMod F)).d n (n + 1) = ModuleCat.ofHom (MainStatements.Hodge.dn F n) :=
  nerveCx_d (toMod F) n

theorem d_zero : (nerveCx.obj (toMod F)).d 0 0 = ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0) := by
  rw [HomologicalComplex.shape _ 0 0 (by simp)]
  exact ModuleCat.ofHom_zero.symm

theorem comp_eq (n : ℕ) :
    ModuleCat.ofHom (MainStatements.Hodge.dn F n) ≫ ModuleCat.ofHom (MainStatements.Hodge.dn F (n + 1)) = 0 := by
  have h := HomologicalComplex.d_comp_d
    (GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.toMod F)) n (n + 1) (n + 1 + 1)
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Low.d_eq, GlobalTheory.CompanionTheory.Hodge.Nerve.Low.d_eq] at h
  exact h

theorem comp_zero_eq :
    ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0) ≫ ModuleCat.ofHom (MainStatements.Hodge.dn F 0) = 0 := by
  rw [ModuleCat.ofHom_zero, zero_comp]

def scIso (n : ℕ) : (nerveCx.obj (toMod F)).sc' n (n + 1) (n + 2) ≅
    ShortComplex.mk (ModuleCat.ofHom (MainStatements.Hodge.dn F n)) (ModuleCat.ofHom (MainStatements.Hodge.dn F (n + 1))) (comp_eq F n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((d_eq F n).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((d_eq F (n + 1)).symm.trans (Category.comp_id _).symm))

def scIso0 : (nerveCx.obj (toMod F)).sc' 0 0 1 ≅
    ShortComplex.mk (ModuleCat.ofHom (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0)) (ModuleCat.ofHom (MainStatements.Hodge.dn F 0))
      (comp_zero_eq F) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans ((d_zero F).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans ((d_eq F 0).symm.trans (Category.comp_id _).symm))

theorem homology_nerveCx :
    ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveCx.obj (toMod F)).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveCx.obj (toMod F)).homology (n + 1)) := by
  intro R _ C _ F
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨e⟩ := GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_equiv
      (0 : MainStatements.Hodge.Cn F 0 →ₗ[R] MainStatements.Hodge.Cn F 0)
      (MainStatements.Hodge.dn F 0) (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.comp_zero_eq F)
    have hbot : (LinearMap.range (0 : MainStatements.Hodge.Cn F 0 →ₗ[R]
        MainStatements.Hodge.Cn F 0)).comap
        (LinearMap.ker (MainStatements.Hodge.dn F 0)).subtype = ⊥ := by
      simp
    exact ⟨((Submodule.quotEquivOfEqBot _ hbot).symm.trans e).trans
      (((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.toMod F)).homologyIsoSc'
        0 0 1 (by simp) (by simp)) ≪≫
        ShortComplex.homologyMapIso (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.scIso0 F)).symm.toLinearEquiv⟩
  · obtain ⟨e⟩ := GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_equiv
      (MainStatements.Hodge.dn F n) (MainStatements.Hodge.dn F (n + 1))
      (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.comp_eq F n)
    exact ⟨e.trans
      (((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.toMod F)).homologyIsoSc'
        n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
        ShortComplex.homologyMapIso (GlobalTheory.CompanionTheory.Hodge.Nerve.Low.scIso F n)).symm.toLinearEquiv⟩

end GlobalTheory.CompanionTheory.Hodge.Nerve.Low
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedCechAcyclic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type}

abbrev BV (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) (s : Finset κ) : Type :=
  ∀ _ : PLift (∀ j ∈ s, b ≤ e j), M b

def bRes (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s t : Finset κ} (h : s ⊆ t) :
    BV e M b s →ₗ[R] BV e M b t where
  toFun x ht := x ⟨fun j hj ↦ ht.down j (h hj)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cubeB (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) : Cube.{0} κ R :=
  Cube.mk (fun s ↦ ModuleCat.of R (BV e M b s)) (fun h ↦ bRes e M b h) (fun _ _ ↦ rfl)
    (fun _ _ _ ↦ rfl)

theorem cubeB_bijective [DecidableEq κ] (e : κ → P) (M : P → ModuleCat.{0} R) {b : P} {i : κ} (hi : e i = b)
    (s : Finset κ) (_his : i ∉ s) :
    Function.Bijective (Cube.res (cubeB e M b) (Finset.subset_insert i s)) := by
  have key : ∀ hs : PLift (∀ j ∈ s, b ≤ e j), ∀ j ∈ insert i s, b ≤ e j := fun hs j hj ↦ by
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hi.ge
    · exact hs.down j hj
  constructor
  · intro x y h
    exact funext fun hs ↦ congrFun h ⟨key hs⟩
  · intro y
    exact ⟨fun hs ↦ (show BV e M b (insert i s) from y) ⟨key hs⟩, rfl⟩

abbrev AV (e : κ → P) (M : P → ModuleCat.{0} R) (s : Finset κ) : Type :=
  ∀ hs : PLift s.Nonempty, ∀ b : {b : P // b ≤ s.inf' hs.down e}, M b.1

def prj (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) (s : Finset κ) :
    (cubeOf e (coind M)).obj s →ₗ[R] (cubeB e M b).obj s where
  toFun x := fun h ↦ if hs : s.Nonempty then
    (show AV e M s from x) ⟨hs⟩ ⟨b, Finset.le_inf' hs e h.down⟩ else 0
  map_add' x y := funext fun h ↦ by
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs]; rfl
    · simp only [dif_neg hs]; exact (add_zero _).symm
  map_smul' r x := funext fun h ↦ by
    by_cases hs : s.Nonempty
    · simp only [dif_pos hs]; rfl
    · simp only [dif_neg hs]; show (0 : M b) = r • (0 : M b); exact (smul_zero r).symm

theorem prj_apply (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s : Finset κ} (hs : s.Nonempty)
    (x : (cubeOf e (coind M)).obj s) (h : PLift (∀ j ∈ s, b ≤ e j)) :
    (show BV e M b s from prj e M b s x) h =
      (show AV e M s from x) ⟨hs⟩ ⟨b, Finset.le_inf' hs e h.down⟩ :=
  dif_pos hs

theorem prj_empty (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) {s : Finset κ} (hs : ¬ s.Nonempty)
    (x : (cubeOf e (coind M)).obj s) : prj e M b s x = 0 :=
  funext fun _ ↦ dif_neg hs

def prjHom (e : κ → P) (M : P → ModuleCat.{0} R) (b : P) : cubeOf e (coind M) ⟶ cubeB e M b :=
  Cube.homMk (prj e M b) fun {s t} h x ↦ by
    by_cases hs : s.Nonempty
    · refine funext fun ht ↦ ?_
      have hs' : t.Nonempty := hs.mono h
      refine (prj_apply e M b hs' _ ht).trans ?_
      refine Eq.trans ?_ (prj_apply e M b hs x ⟨fun j hj ↦ ht.down j (h hj)⟩).symm
      have := cubeRes_apply e (coind M) h x hs ⟨hs'⟩
      exact congrFun this _
    · rw [prj_empty e M b hs, map_zero]
      by_cases ht : t.Nonempty
      · refine funext fun hh ↦ ?_
        refine (prj_apply e M b ht _ hh).trans ?_
        have := cubeRes_empty e (coind M) h x hs ⟨ht⟩
        exact congrFun this _
      · exact prj_empty e M b ht _

theorem term_ext (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ}
    (u v : Cube.Term (cubeOf e (coind M)) (q + 1))
    (h : ∀ b, Cube.termMap (prjHom e M b) (q + 1) u = Cube.termMap (prjHom e M b) (q + 1) v) :
    u = v := by
  funext s
  refine funext fun hs ↦ funext fun b ↦ ?_
  have hle : ∀ j ∈ s.1, b.1 ≤ e j := fun j hj ↦ b.2.trans (Finset.inf'_le e hj)
  have h1 := congrFun (congrFun (h b.1) s) ⟨hle⟩
  exact (prj_apply e M b.1 hs.down (u s) ⟨hle⟩).symm.trans (h1.trans (prj_apply e M b.1 hs.down (v s) ⟨hle⟩))

def asm (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ} (y : ∀ b, Cube.Term (cubeB e M b) (q + 1)) :
    Cube.Term (cubeOf e (coind M)) (q + 1) :=
  fun s ↦ (show AV e M s.1 from fun _ b ↦
    (show BV e M b.1 s.1 from y b.1 s) ⟨fun _ hj ↦ b.2.trans (Finset.inf'_le e hj)⟩)

theorem termMap_asm (e : κ → P) (M : P → ModuleCat.{0} R) {q : ℕ}
    (y : ∀ b, Cube.Term (cubeB e M b) (q + 1)) (b : P) :
    Cube.termMap (prjHom e M b) (q + 1) (asm e M y) = y b := by
  funext s
  refine funext fun h ↦ ?_
  have hs : s.1.Nonempty := Finset.card_pos.1 (by have := s.2; omega)
  exact prj_apply e M b hs (asm e M y s) h

variable [LinearOrder κ]

theorem exact_d (e : κ → P) (he : Function.Surjective e) (M : P → ModuleCat.{0} R) (p : ℕ) :
    Function.Exact (Cube.d (cubeOf e (coind M)) (p + 1)) (Cube.d (cubeOf e (coind M)) (p + 2)) := by
  intro x
  refine ⟨fun hx ↦ ?_, by rintro ⟨y, rfl⟩; exact Cube.d_d _ _ y⟩
  have hb : ∀ b, ∃ y : Cube.Term (cubeB e M b) (p + 1),
      Cube.d (cubeB e M b) (p + 1) y = Cube.termMap (prjHom e M b) (p + 2) x := by
    intro b
    obtain ⟨i, hi⟩ := he b
    refine (Cube.exact_d_of_bijective (cubeB e M b) i (cubeB_bijective e M hi) (p + 1) _).1 ?_
    rw [← Cube.termMap_d, hx, map_zero]
  choose y hy using hb
  refine ⟨asm e M y, term_ext e M _ _ fun b ↦ ?_⟩
  rw [Cube.termMap_d, termMap_asm, hy]

theorem isZero_homology (e : κ → P) (he : Function.Surjective e) (M : P → ModuleCat.{0} R) (n : ℕ) :
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((cechComplex_exactAt_succ_iff (cubeOf e (coind M)) n).2 (exact_d e he M n))

example : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Surjective e → ∀ (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) :=
  fun e he M n ↦ isZero_homology e he M n

end GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedNerveAcyclic
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]

theorem chain_ext {n : ℕ} {c c' : Fin (n + 1) ⥤ Pᵒᵖ} (h : ∀ i, c.obj i = c'.obj i) : c = c' :=
  CategoryTheory.Functor.ext h (fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _))

theorem chain_anti {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {i j : Fin (n + 1)} (h : i ≤ j) :
    (c.obj j).unop ≤ (c.obj i).unop :=
  leOfHom (c.map (homOfLE h)).unop

def snocObj {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) : Fin (n + 2) → Pᵒᵖ :=
  Fin.snoc (α := fun _ ↦ Pᵒᵖ) (fun i ↦ c.obj i) (op b)

@[simp] theorem snocObj_last {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) :
    snocObj c b (Fin.last _) = op b :=
  Fin.snoc_last (α := fun _ ↦ Pᵒᵖ) _ _

@[simp] theorem snocObj_castSucc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (i : Fin (n + 1)) :
    snocObj c b i.castSucc = c.obj i :=
  Fin.snoc_castSucc (α := fun _ ↦ Pᵒᵖ) _ _ _

theorem snocObj_anti {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {b : P} (hb : b ≤ (c.obj (Fin.last n)).unop)
    {i j : Fin (n + 2)} (h : i ≤ j) : (snocObj c b j).unop ≤ (snocObj c b i).unop := by
  induction j using Fin.lastCases with
  | last =>
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]
    induction i using Fin.lastCases with
    | last => exact le_of_eq (by rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last])
    | cast i =>
      rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
      exact hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last i))
  | cast j =>
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
    induction i using Fin.lastCases with
    | last => exact absurd h (not_le.mpr (Fin.castSucc_lt_last j))
    | cast i =>
      rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
      exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.castSucc_le_castSucc_iff.mp h)

def snoc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (hb : b ≤ (c.obj (Fin.last n)).unop) :
    Fin (n + 2) ⥤ Pᵒᵖ where
  obj := snocObj c b
  map h := (homOfLE (snocObj_anti c hb (leOfHom h))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem snoc_last_le {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (hb : b ≤ (c.obj (Fin.last n)).unop) :
    b ≤ ((snoc c b hb).obj (Fin.last _)).unop :=
  le_of_eq (congrArg Opposite.unop (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last c b)).symm

abbrev face {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) : Fin (n + 1) ⥤ Pᵒᵖ :=
  (Fin.succAboveOrderEmb i).toOrderHom.monotone.functor ⋙ c

theorem face_le {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) : b ≤ ((face i c).obj (Fin.last _)).unop :=
  hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last _))

theorem face_castSucc_snoc {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) :
    face i.castSucc (snoc c b hb) = snoc (face i c) b (face_le i c hb) := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext
  intro k
  induction k using Fin.lastCases with
  | last =>
    show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.last _)) =
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.last _)
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i)),
      Fin.succ_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]
  | cast k =>
    show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.castSucc k)) =
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.castSucc k)
    rw [Fin.castSucc_succAbove_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
    all_goals rfl

theorem face_last_snoc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) : face (Fin.last _) (snoc c b hb) = c := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext
  intro k
  show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.last _).succAbove k) = c.obj k
  rw [Fin.succAbove_last_apply, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]

def valL (M : P → ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) : NC (coind M) n →ₗ[R] M b where
  toFun f := f c ⟨b, hb⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem valL_congr (M : P → ModuleCat.{0} R) {n : ℕ} {c c' : Fin (n + 1) ⥤ Pᵒᵖ} (h : c = c') (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) (hb' : b ≤ (c'.obj (Fin.last n)).unop) (f : NC (coind M) n) :
    valL M c b hb f = valL M c' b hb' f := by
  subst h
  rfl

theorem valL_dNC (M : P → ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 2) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last _)).unop) (f : NC (coind M) n) :
    valL M c b hb (dNC (coind M) n f) =
      ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • valL M (face i c) b (face_le i c hb) f := by
  first
    | (simp only [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul];
        all_goals exact Finset.sum_congr rfl fun i _ => rfl)
    | (rw [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, map_sum];
        exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply, map_smul]; rfl)

def contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1)) : NC (coind M) n :=
  fun c b ↦ valL M (snoc c b.1 b.2) b.1 (snoc_last_le c b.1 b.2) f

theorem valL_contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1)) (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) :
    valL M c b hb (contr M f) = valL M (snoc c b hb) b (snoc_last_le c b hb) f := rfl

theorem NC_ext (M : P → ModuleCat.{0} R) {n : ℕ} {f g : NC (coind M) n}
    (h : ∀ c b hb, valL M c b hb f = valL M c b hb g) : f = g := by
  funext c b
  exact h c b.1 b.2

theorem dNC_contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1))
    (hf : dNC (coind M) (n + 1) f = 0) :
    dNC (coind M) n (((-1 : R) ^ (n + 1)) • contr M f) = f := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.NC_ext
  intro c b hb
  have hcoc : GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc c b hb) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc_last_le c b hb)
      (GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) f) = 0 := by
    rw [hf, map_zero]
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, Fin.sum_univ_castSucc] at hcoc
  have hsum : ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) •
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_le i c hb)
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M f) =
      -((-1 : R) ^ (n + 1 + 1) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M c b hb f) := by
    rw [eq_neg_iff_add_eq_zero, ← hcoc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_contr]
      exact congrArg ((-1 : R) ^ (i : ℕ) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_castSucc_snoc i c hb).symm b _ _ f)
    · rw [Fin.val_last]
      exact congrArg ((-1 : R) ^ (n + 1 + 1) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_last_snoc c hb).symm b _ _ f)
  have hp : (-1 : R) ^ (n + 1) * (-1 : R) ^ (n + 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [map_smul, map_smul, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, hsum, smul_neg, smul_smul,
    pow_succ (-1 : R) (n + 1), ← mul_assoc, hp, one_mul, neg_smul, one_smul, neg_neg]

end GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

open GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc in

theorem GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
    (M : P → ModuleCat.{0} R) (n : ℕ) : IsZero ((nerveCx.obj (coind M)).homology (n + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) x = 0 := by
    change ((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d (n + 1) (n + 1 + 1)).hom x = 0 at hx
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d] at hx
    exact hx
  refine ⟨((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x, ?_⟩
  change ((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d n (n + 1)).hom
    (((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x) = x
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d]
  exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.dNC_contr M x hx'
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLinearInFunctional
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem con_add_form {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (Ξ Ξ' : (∀ i, V i) →ₗ[R] R)
    (u : ∀ i, V i ⊗[R] M) : con V M (Ξ + Ξ') u = con V M Ξ u + con V M Ξ' u := by
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M
    (P := fun u => GlobalTheory.CompanionTheory.HopfC.con V M (Ξ + Ξ') u = GlobalTheory.CompanionTheory.HopfC.con V M Ξ u + GlobalTheory.CompanionTheory.HopfC.con V M Ξ' u)
    ?_ ?_ ?_ u
  · simp only [map_zero, add_zero]
  · intro f m
    simp only [GlobalTheory.CompanionTheory.HopfC.con_pure, LinearMap.add_apply, add_smul]
  · intro u v hu hv
    rw [map_add, map_add, map_add, hu, hv]
    abel

theorem con_smul_form {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (r : R) (Ξ : (∀ i, V i) →ₗ[R] R)
    (u : ∀ i, V i ⊗[R] M) : con V M (r • Ξ) u = r • con V M Ξ u := by
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M
    (P := fun u => GlobalTheory.CompanionTheory.HopfC.con V M (r • Ξ) u = r • GlobalTheory.CompanionTheory.HopfC.con V M Ξ u)
    ?_ ?_ ?_ u
  · simp only [map_zero, smul_zero]
  · intro f m
    simp only [GlobalTheory.CompanionTheory.HopfC.con_pure, LinearMap.smul_apply, smul_eq_mul, mul_smul]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, smul_add]

theorem Con_linear_form {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ Ξ' : Cn F p →ₗ[R] R) (r : R) (B : Bi F p q) :
    Con F (Ξ + Ξ') q B = Con F Ξ q B + Con F Ξ' q B ∧ Con F (r • Ξ) q B = r • Con F Ξ q B := by
  have key : ∀ (Θ : MainStatements.Hodge.Cn F p →ₗ[R] R) (b : Fin (q + 1) ⥤ C),
      GlobalTheory.CompanionTheory.HopfC.Con F Θ q B b =
        GlobalTheory.CompanionTheory.HopfC.con (fun a : Fin (p + 1) ⥤ C => (F.obj (a.obj (Fin.last p)) : Type))
          (F.obj (b.obj (Fin.last q)) : Type) Θ (fun a => B a b) := fun _ _ => rfl
  refine ⟨funext fun b => ?_, funext fun b => ?_⟩
  · rw [key, GlobalTheory.CompanionTheory.HopfC.con_add_form]
    rfl
  · rw [key, GlobalTheory.CompanionTheory.HopfC.con_smul_form]
    rfl

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDimStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_dim_eq_relative_dim : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n q] {V : X.Opens}, (V : Set X).Nonempty → ∀ {m : ℕ} (c : Coord q V m), m = n := by
  first | exact @GlobalTheory.CompanionTheory.CoordCard.main | exact GlobalTheory.CompanionTheory.CoordCard.main | (intros; apply GlobalTheory.CompanionTheory.CoordCard.main <;> assumption)
end

