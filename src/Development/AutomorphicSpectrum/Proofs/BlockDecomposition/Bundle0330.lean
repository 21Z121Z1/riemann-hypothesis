import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0009
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0044

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE.PSupp

def badSet {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) : Set X :=
  {x | ∀ V : X.affineOpens, secs S (V : X.Opens) = Set.univ → x ∉ (V : X.Opens)}

lemma badSet_compl_eq {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) :
    (badSet S)ᶜ = ⋃ V ∈ {V : X.affineOpens | secs S (V : X.Opens) = Set.univ}, ((V : X.Opens) : Set X) := by
  ext x
  simp only [badSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, exists_prop, Set.mem_iUnion]
  constructor
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hV, not_not.mp hx⟩
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hV, not_not.mpr hx⟩

lemma isClosed_badSet {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) : IsClosed (badSet S) := by
  rw [← isOpen_compl_iff, badSet_compl_eq]
  exact isOpen_biUnion fun V _ => (V : X.Opens).isOpen

theorem subset_of_closedFibre {A : Type} [CommRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens) (C : Set X)
    (hC : IsClosed C) (h : ∀ x ∈ C, I ≤ ((X ↘ Spec (.of A)).base x).asIdeal → x ∈ (O : Set X)) :
    C ⊆ O := by

  have hZ := GlobalTheory.CompanionTheory.ClosedFibre.closed_missing_closedFibre_empty A I hI
    (Over.mk (X ↘ Spec (.of A))) (inferInstanceAs (UniversallyClosed (X ↘ Spec (.of A))))
    (C ∩ (O : Set X)ᶜ) (hC.inter O.isOpen.isClosed_compl) (by
      rintro x ⟨hxC, hxO⟩ hIx
      exact hxO (h x hxC hIx))
  intro x hx
  by_contra hxO
  have hx' : x ∈ C ∩ (O : Set X)ᶜ := ⟨hx, hxO⟩
  rw [hZ] at hx'
  exact hx'

end GlobalTheory.CompanionTheory.GE.PSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMap
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem idx_self_eq {d : ℕ} (I : Idx d d) : I.1 = id := by
  have hs : Function.Surjective I.1 := Finite.injective_iff_surjective.1 I.2.injective
  exact (StrictMono.range_inj I.2 strictMono_id).1 (by rw [hs.range_eq, Set.range_id])

theorem sum_idx_self {M : Type*} [AddCommMonoid M] {d : ℕ} [Fintype (Idx d d)] (g : Idx d d → M) :
    ∑ I, g I = g ⟨id, strictMono_id⟩ := by
  letI : Unique (Idx d d) :=
    { default := ⟨id, strictMono_id⟩, uniq := fun I => Subtype.ext (idx_self_eq I) }
  exact Fintype.sum_unique g

section Form
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d j : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (I : Fin j → Fin d) (u : ComposableArrows C j)

theorem form_add_fun (x x' : Φ.A.obj E.D) : E.form σ I (x + x') u = E.form σ I x u + E.form σ I x' u := by
  simp only [Frame.form, map_add, mul_add]

theorem form_sub_fun (x x' : Φ.A.obj E.D) : E.form σ I (x - x') u = E.form σ I x u - E.form σ I x' u := by
  simp only [Frame.form, map_sub, mul_sub]

theorem form_alg_mul (a : R) (x : Φ.A.obj E.D) :
    E.form σ I (algebraMap R _ a * x) u = a • E.form σ I x u := by
  simp only [Frame.form, map_mul, AlgHom.commutes, Algebra.smul_def]
  ring

end Form

theorem coef_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  intro K _ _ X q W d t s E ε hL σ r hr hs
  letI := (strV q W).toAlgebra
  obtain ⟨hE, hU⟩ := GlobalTheory.T.local_graded_class_representative q t s E ε hL σ d r hr hs
  have ex : ∀ c : HQ (KS q s {W}) r (r + 1) d, ∃ y : Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c := by
    intro c
    obtain ⟨y, hy⟩ := hE c
    refine ⟨y ⟨id, strictMono_id⟩, ?_⟩
    have e : (fun u => ∑ I : Idx d d, E.form σ I.1 (ε (y I)) u) = E.form σ id (ε (y ⟨id, strictMono_id⟩)) :=
      funext fun u => sum_idx_self (fun I : Idx d d => E.form σ I.1 (ε (y I)) u)
    rwa [e] at hy
  have z0 : ∀ y : Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) 0 → y = 0 := by
    intro y h
    have e : (fun u => ∑ I : Idx d d, E.form σ I.1 (ε ((fun _ => y : Idx d d → Γ(X, W)) I)) u) = E.form σ id (ε y) :=
      funext fun u => sum_idx_self (fun I : Idx d d => E.form σ I.1 (ε y) u)
    exact congrFun (hU (fun _ => y) (by rwa [e])) ⟨id, strictMono_id⟩
  have uniq : ∀ (y y' : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c →
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y')) c → y = y' := by
    intro y y' c h h'
    have h2 := rep_add h (rep_smul (-1 : K) h')
    have e : (fun u => E.form σ id (ε y) u + (-1 : K) • E.form σ id (ε y') u) = E.form σ id (ε (y - y')) := by
      funext u
      rw [map_sub, form_sub_fun, neg_one_smul, sub_eq_add_neg]
    rw [e, neg_one_smul, add_neg_cancel] at h2
    exact sub_eq_zero.1 (z0 _ h2)
  choose φ hφ using ex
  refine ⟨{ toFun := φ, map_add' := ?_, map_smul' := ?_ }, ?_, fun y c h => uniq _ _ c (hφ c) h⟩
  · intro c c'
    refine uniq _ _ (c + c') (hφ _) ?_
    have h2 := rep_add (hφ c) (hφ c')
    have e : (fun u => E.form σ id (ε (φ c)) u + E.form σ id (ε (φ c')) u) = E.form σ id (ε (φ c + φ c')) := by
      funext u
      rw [map_add, form_add_fun]
    rwa [e] at h2
  · intro a c
    refine uniq _ _ (a • c) (hφ _) ?_
    have h2 := rep_smul a (hφ c)
    have e : (fun u => a • E.form σ id (ε (φ c)) u) = E.form σ id (ε (a • φ c)) := by
      funext u
      have e1 : a • φ c = strV q W a * φ c := Algebra.smul_def a (φ c)
      rw [e1, map_mul, hL.2.2.1 a, form_alg_mul]
    rwa [e] at h2
  · intro c c' h
    have h' : φ c = φ c' := h
    have h2 := hφ c'
    rw [← h'] at h2
    exact rep_unique (hφ c) h2

end GlobalTheory.CompanionTheory.ConeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE.Step

variable {X : Scheme.{0}} {P : X.Modules}

def lvl (S : ℕ → Subobject P) : ℕ → Subobject P
  | 0 => ⊤
  | e + 1 => S e

@[simp] lemma lvl_zero (S : ℕ → Subobject P) : lvl S 0 = ⊤ := rfl
@[simp] lemma lvl_succ (S : ℕ → Subobject P) (e : ℕ) : lvl S (e + 1) = S e := rfl

lemma lvl_succ_le {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    lvl S (e + 1) ≤ lvl S e := by
  cases e with
  | zero => exact le_top
  | succ e => exact hS e

def incl {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    (lvl S (e + 1) : X.Modules) ⟶ (lvl S e : X.Modules) :=
  Subobject.ofLE _ _ (lvl_succ_le hS e)

@[reassoc (attr := simp)]
lemma incl_arrow {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    incl hS e ≫ (lvl S e).arrow = (lvl S (e + 1)).arrow :=
  Subobject.ofLE_arrow _

def gr {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) : X.Modules :=
  cokernel (incl hS e)

def grπ {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    (lvl S e : X.Modules) ⟶ gr hS e :=
  cokernel.π _

@[reassoc (attr := simp)]
lemma incl_grπ {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) (e : ℕ) :
    incl hS e ≫ grπ hS e = 0 :=
  cokernel.condition _

def MapsDown (S : ℕ → Subobject P) (r : Γ(X, ⊤)) : Prop :=
  ∀ e, (lvl S (e + 1)).Factors ((lvl S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P r)

def mulLvl {S : ℕ → Subobject P} {r : Γ(X, ⊤)} (hr : MapsDown S r) (e : ℕ) :
    (lvl S e : X.Modules) ⟶ (lvl S (e + 1) : X.Modules) :=
  (lvl S (e + 1)).factorThru _ (hr e)

@[reassoc (attr := simp)]
lemma mulLvl_arrow {S : ℕ → Subobject P} {r : Γ(X, ⊤)} (hr : MapsDown S r) (e : ℕ) :
    mulLvl hr e ≫ (lvl S (e + 1)).arrow = (lvl S e).arrow ≫ GroundTheory.Arith.SchemeCoh.smulHom P r :=
  Subobject.factorThru_arrow _ _ _

lemma incl_mulLvl {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)}
    (hr : MapsDown S r) (e : ℕ) :
    incl hS e ≫ mulLvl hr e = mulLvl hr (e + 1) ≫ incl hS (e + 1) := by
  rw [← cancel_mono (lvl S (e + 1)).arrow]
  simp only [Category.assoc, mulLvl_arrow, incl_arrow, incl_arrow_assoc]

def grT {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)} (hr : MapsDown S r)
    (e : ℕ) : gr hS e ⟶ gr hS (e + 1) :=
  cokernel.desc _ (mulLvl hr e ≫ grπ hS (e + 1)) (by
    rw [← Category.assoc, incl_mulLvl, Category.assoc, incl_grπ, comp_zero])

@[reassoc (attr := simp)]
lemma grπ_grT {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r : Γ(X, ⊤)}
    (hr : MapsDown S r) (e : ℕ) :
    grπ hS e ≫ grT hS hr e = mulLvl hr e ≫ grπ hS (e + 1) :=
  cokernel.π_desc _ _ _

lemma grT_comm {S : ℕ → Subobject P} (hS : ∀ e, S (e + 1) ≤ S e) {r s : Γ(X, ⊤)}
    (hr : MapsDown S r) (hs : MapsDown S s) (e : ℕ) :
    grT hS hr e ≫ grT hS hs (e + 1) = grT hS hs e ≫ grT hS hr (e + 1) := by
  apply coequalizer.hom_ext
  change grπ hS e ≫ _ = grπ hS e ≫ _
  simp only [grπ_grT_assoc, grπ_grT]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (lvl S (e + 2)).arrow]
  simp only [Category.assoc, mulLvl_arrow, mulLvl_arrow_assoc]
  rw [smulHom_comp_smulHom, smulHom_comp_smulHom, mul_comm]

lemma anti {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A} [X.Over (Spec (.of A))]
    {S : ℕ → Subobject P} (hS : ClosedSys I P S) (e : ℕ) : S (e + 1) ≤ S e := by
  rw [hS.succ e]
  exact le_sup_left

lemma twist_smulHom_app (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (F : X.Modules) (r : Γ(X, ⊤))
    (V : X.Opens) (s : Γ(GlobalTheory.twist F L, V)) :
    (GlobalTheory.Twist.map L (GroundTheory.Arith.SchemeCoh.smulHom F r)).app V s = restrictTop V r • s := by
  ext i
  rw [GlobalTheory.Twist.coord_map_app, GlobalTheory.Twist.coord_smul, GroundTheory.Arith.SchemeCoh.smulHom_app_apply]
  congr 1
  exact (restrictTop_restrict (homOfLE inf_le_left) r).symm

def Lifts {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) {S : ℕ → Subobject P} (hS : ClosedSys I P S) (n : ℤ) (e : ℕ) :
    Prop :=
  ∀ y : Γ(GlobalTheory.twistZ (gr (anti hS) e) H n, ⊤), ∃ c : Γ(GlobalTheory.twistZ (lvl S e : X.Modules) H n, ⊤),
    (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) e)).app ⊤ c = y ∧
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (lvl S e).arrow).app ⊤ c ∈ twPow I H n P e

end GlobalTheory.CompanionTheory.GE.Step
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

lemma toFunctions_top_eq {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (a : A) :
    toFunctions (X := X) (A := A) ⊤ a = algebraMap A Γ(X, ⊤) a := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom _ = _
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

lemma twist_map_smulHom_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (P : X.Modules)
    (r : Γ(X, ⊤)) (c : Γ(GlobalTheory.twist P L, ⊤)) :
    (GlobalTheory.Twist.map L (GroundTheory.Arith.SchemeCoh.smulHom P r)).app ⊤ c = r • c := by
  apply GlobalTheory.Twist.sec_ext
  intro i
  rw [GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]

lemma smul_mem_twSecs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ)
    {a : A} (ha : a ∈ I ^ m) (c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    toFunctions (X := X) (A := A) ⊤ a • c ∈ twSecs H n (powSub I P m) := by
  let g : P ⟶ (powSub I P m : X.Modules) :=
    idealPowOfMem I P a ha ≫ (Subobject.underlyingIso (idealPowι I P m)).inv
  have hg : g ≫ (powSub I P m).arrow = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    simp only [g, powSub, Category.assoc]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Iso.inv_hom_id_assoc, idealPowOfMem_ι]
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) g).app ⊤ c, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp, hg,
    twist_map_smulHom_app, toFunctions_top_eq]

def twSecsSub {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    (S : Subobject P) : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) where
  carrier := twSecs H n S
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨x, rfl⟩
    exact ⟨r • x, Scheme.Modules.Hom.app_smul _ _ _⟩

theorem twPow_subset_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ),
      twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  intro A _ _ I X _ H _ P _ n m
  have key : (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ :
      Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ≤ twSecsSub H n (powSub I P m) := by
    rw [Submodule.smul_le]
    intro r hr c _
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact smul_mem_twSecs I H n P m ha c
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul x y _ hy => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ _ hy
  exact key

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsCauchyLimit
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

theorem exists_limit_of_finite {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (I : Ideal A) (hI : IsPrecomplete I A) (f : ℕ → M)
    (hf : ∀ m, f m - f (m + 1) ∈ (I ^ m • ⊤ : Submodule A M)) :
    ∃ L, ∀ m, f m - L ∈ (I ^ m • ⊤ : Submodule A M) :=
  _root_.UpperTheory.Reformulated.B.LimitOfFinite.exists_limit_of_finite I hI f hf

theorem finite_twisted_sections {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) {P : X.Modules} (hP : IsCoherent P) (n : ℤ)
    [Module A Γ(GlobalTheory.twistZ P H n, ⊤)]
    (hs : ∀ (a : A) (x : Γ(GlobalTheory.twistZ P H n, ⊤)), a • x = algebraMap A Γ(X, ⊤) a • x) :
    Module.Finite A Γ(GlobalTheory.twistZ P H n, ⊤) := by
  haveI : GlobalTheory.QCoh.IsFiniteQC P := ⟨hP.1, hP.2⟩
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.twistZ P H n) :=
    GlobalTheory.Twist.isFiniteQC_twist (F := P) (GlobalTheory.Twist.isLB_lbZPow hH.isLB n)
  have h0 : Module.Finite A (GlobalTheory.coh (GlobalTheory.twistZ P H n) 0) :=
    GlobalTheory.IsAmpleLB.finite_coh (R := A) (f := X ↘ Spec (.of A)) (fun _ => rfl) _ hH 0
  exact Module.Finite.equiv ((GlobalTheory.cohOn.zeroEquiv A (GlobalTheory.twistZ P H n) ⊤).trans
    (GlobalTheory.sectionsOn.equivOfSMul A (GlobalTheory.twistZ P H n) ⊤ fun a x => by
      rw [hs, GlobalTheory.restrictGlobal_top]))

theorem exists_limit_twPow : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (f : ℕ → Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ m, f m - f (m + 1) ∈ twPow I H n P m) → ∃ L : Γ(GlobalTheory.twistZ P H n, ⊤), ∀ m, f m - L ∈ twPow I H n P m := by
  intro A _ _ I hI X _ _ H hH P hP n f hf
  letI : Module A Γ(GlobalTheory.twistZ P H n, ⊤) := Module.compHom _ (algebraMap A Γ(X, ⊤))
  haveI : IsScalarTower A Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) :=
    ⟨fun a r x => by
      change (a • r) • x = algebraMap A Γ(X, ⊤) a • (r • x)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI := finite_twisted_sections (A := A) H hH hP n (fun _ _ => rfl)
  have hmem : ∀ (m : ℕ) (y : Γ(GlobalTheory.twistZ P H n, ⊤)),
      y ∈ twPow I H n P m ↔ y ∈ (I ^ m • ⊤ : Submodule A Γ(GlobalTheory.twistZ P H n, ⊤)) := by
    intro m y
    have hfun : toFunctions (X := X) (A := A) ⊤ = algebraMap A Γ(X, ⊤) := by
      ext a
      simp [toFunctions, restrictTop]
    have h := Ideal.smul_restrictScalars (R := A) (S := Γ(X, ⊤))
      (M := Γ(GlobalTheory.twistZ P H n, ⊤)) (I ^ m) ⊤
    rw [Submodule.restrictScalars_top] at h
    rw [← h]
    simp only [twPow, hfun]
    rfl
  obtain ⟨L, hL⟩ := exists_limit_of_finite I hI.toIsPrecomplete f fun m => (hmem m _).1 (hf m)
  exact ⟨L, fun m => (hmem m _).2 (hL m)⟩

end GlobalTheory.CompanionTheory.GE
end
end

