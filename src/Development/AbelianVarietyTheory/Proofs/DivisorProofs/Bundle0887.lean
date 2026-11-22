import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.GlobalFields.TateThesis.AdelicChar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory

namespace GlobalTheory.WhitBump

abbrev Idx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

abbrev Vp (E : Type) [Field E] (n : ℕ) : Type := Idx n → Cinf E

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def nu (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else if i = j then 1 else 0

def sdM {R : Type} [CommRing R] (x : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, x i j

theorem superDiag_eq_sdM {R : Type} [CommRing R] (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag g = sdM (g : Matrix (Fin n) (Fin n) R) := rfl

theorem nu_lower (t : Vp E n) {i j : Fin n} (h : j < i) : nu t i j = 0 := by
  simp [nu, not_lt_of_gt h, ne_of_gt h]

theorem nu_diag (t : Vp E n) (i : Fin n) : nu t i i = 1 := by
  simp [nu]

theorem det_nu (t : Vp E n) : (nu t).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [nu_diag]
  · intro i j h; exact nu_lower t h

def nuGL (t : Vp E n) : GL (Fin n) (Cinf E) :=
  Matrix.nonsingInvUnit (nu t) (by rw [det_nu]; exact isUnit_one)

@[simp] theorem nuGL_val (t : Vp E n) : (nuGL t : Matrix (Fin n) (Fin n) (Cinf E)) = nu t := rfl

theorem nuGL_mem (t : Vp E n) : nuGL t ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun _ _ h => nu_lower t h, nu_diag t⟩

variable [IsTotallyComplex E]

def psiInf (z : Cinf E) : ℂ := (GroundTheory.Global.adelicChar E (sInf E z) : ℂ)

def psiFin (a : Af E) : ℂ := (GroundTheory.Global.adelicChar E (sFin E a) : ℂ)

def bumpInf (f : Lie E n → ℝ) (x : Lie E n) : ℂ :=
  ∫ t : Vp E n, (f (toL (nu t * Matrix.of x)) : ℂ) * psiInf (-sdM (nu t))

open Classical in

def bumpFin (g : GL (Fin n) (Af E)) : ℂ :=
  if h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n then
    psiFin (GlobalTheory.Whittaker.superDiag h.choose) else 0

end GlobalTheory.WhitBump
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivOfIsLBSplitTorus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TorusPic

theorem triv_of_isLB_splitTorus : ∀ (A : Type) [CommRing A], IsField A → ∀ (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : LB (splitTorus (Sp A) X).left), N.IsLB → Triv N := by
  intro A _ hA X _ _ _ N hN
  letI := hA.toField
  have : IsAffine (splitTorus (Sp A) X).left := by
    have := Diag.isAffineHom_hom (Sp A) X
    exact isAffine_of_isAffineHom (splitTorus (Sp A) X).hom
  have := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus A X
  exact GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top hN

end GlobalTheory.TorusPic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ
open scoped Matrix

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

abbrev VA (F : Type) [Field F] [NumberField F] (N : ℕ) : Type := (Fin N → AF F) × (Fin N → AF F)

def symV (w w' : VA F N) : AF F := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def embR {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) 0

def IsRealLine (M : ℝ →+ VA F N) : Prop := Continuous M ∧ ∀ t, fin (M t).1 = 0 ∧ fin (M t).2 = 0

def half (F : Type) [Field F] (N : ℕ) : Fin N → F := fun _ => 1 / 2

variable [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)

def heisV (u : VA F N) (f : VA F N → ℂ) : VA F N → ℂ := fun w => ψ (⅟(2 : AF F) * symV w u) * f (w + u)

def thV (Φ : (Fin N → AF F) → ℂ) : VA F N → ℂ := fun w => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)

def invV (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) : (Fin N → AF F) → ℂ :=
  fun x => ∫ y in 𝓓, f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) ∂(muV N ν)

def QuasiV (f : VA F N → ℂ) : Prop :=
  ∀ (a b : Fin N → F) (w : VA F N), f ((rat a, rat b) + w) = ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) * f w

def LevelV (f : VA F N → ℂ) : Prop :=
  ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → heisV ψ u f = f

abbrev ratSub (F : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (Fin N → AF F) :=
  AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))

theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

omit [Invertible (2 : AF F)] in
theorem Bd_half (u u' : Fin N → AF F) : Bd (AF F) (half F N) u u' = u ⬝ᵥ u' := by
  simp [Bd, half, dotProduct]

omit [NumberField F] [Invertible (2 : AF F)] in
theorem half_ne_zero [CharZero F] (l : Fin N) : half F N l ≠ 0 := by
  simp [half]

theorem schr_eq_rho (w : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w Φ = rho ψ (half F N) w.1 w.2 Φ := by
  funext x
  rw [GlobalTheory.WeilM.schr, rho, Bd_half, Bd_half, invOf_two_eq]

theorem thV_eq_th (Φ : (Fin N → AF F) → ℂ) (w : VA F N) : thV ψ Φ w = th (rho ψ (half F N) w.1 w.2 Φ) := by
  rw [thV, schr_eq_rho]
  rfl

theorem two_mul_invOf (a : AF F) : ⅟(2 : AF F) * a + ⅟(2 : AF F) * a = a := by
  rw [← add_mul, invOf_two_add_invOf_two, one_mul]

theorem schr_schr (w u : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ u Φ) = ψ (⅟(2 : AF F) * symV w u) • GlobalTheory.WeilM.schr ψ (w + u) Φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination (-1 : AF F) * two_mul_invOf (w.1 ⬝ᵥ u.2)

theorem thV_schr (u : VA F N) (Φ : (Fin N → AF F) → ℂ) : thV ψ (GlobalTheory.WeilM.schr ψ u Φ) = heisV ψ u (thV ψ Φ) := by
  funext w
  rw [thV, schr_schr, heisV, thV]
  exact tsum_mul_left

theorem quasiV_thV (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) (Φ : (Fin N → AF F) → ℂ) : QuasiV ψ (thV ψ Φ) := by
  intro a b w
  simp only [thV, GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : Fin N → F => ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rat ξ + rat a := by
    funext i; simp [rat]
  have e2 : (fun i => algebraMap F (AF F) (ξ i)) = rat ξ := rfl
  have e3 : ∀ c d : Fin N → F, rat c ⬝ᵥ rat d = algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [rat, dotProduct]
  rw [e1, e2]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  rw [← mul_one (ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w) + _)), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add, map_mul, ← invOf_two_eq, ← e3, ← e3]
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination two_mul_invOf (rat a ⬝ᵥ w.2)

end GlobalTheory.ThetaTransform

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesCardAndResidueLe
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem typePlaces_card_and_residue_le : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → R.Pg.card = 2 * D.R.f ∧ ∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h
  obtain ⟨_, plg, iso, -⟩ := h
  refine ⟨?_, fun PP hPP => ?_⟩
  · rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_congr plg, Nat.card_sigma]
    have hk : ∀ k : Fin 2, Nat.card (D.nd.PlG k) = D.R.f := fun k => by
      rw [← D.nd.card_PlG k]
      exact @Nat.card_eq_fintype_card _ (_)
    simp only [hk, Fin.sum_univ_two, two_mul]
  · obtain ⟨kv, hkv⟩ := plg.surjective ⟨PP, hPP⟩
    have h1 : Nat.card (kP (plg kv).1) = D.host.g kv.1 := by
      rw [← Nat.card_congr (iso kv).toEquiv, Nat.card_zmod]
    rw [hkv] at h1
    change _ ≤ Nat.card (kP (⟨PP, hPP⟩ : R.Pg).1)
    rw [h1]
    generalize kv.1 = k
    fin_cases k
    · exact min_le_left _ _
    · exact min_le_right _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtCorrespondOfCartesian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UnifPull

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X}
  {φ : G'.left ⟶ G.left}

def push (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : Over.mk t ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = t
    rw [Category.assoc, hw, ← Category.assoc, Over.w x, ← ht]
    rfl)

theorem push_left (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t' ⟶ G') : (push hw ht x).left = x.left ≫ φ := rfl

def pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : Over.mk t' ⟶ G' :=
  Over.homMk (H.lift x.left t' ((Over.w x).trans ht.symm)) (H.lift_snd _ _ _)

theorem push_pull (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    (x : Over.mk t ⟶ G) : push H.w ht (pull H ht x) = x :=
  Over.OverMorphism.ext (H.lift_fst _ _ _)

theorem push_injective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Injective (push H.w ht) := fun x y h =>
  Over.OverMorphism.ext (H.hom_ext (congrArg (fun u => u.left) h) (by rw [Over.w x, Over.w y]))

theorem push_surjective (H : IsPullback φ G'.hom G.hom f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X}
    (ht : t' ≫ f = t) : Function.Surjective (push H.w ht) := fun x => ⟨_, push_pull H ht x⟩

theorem push_mul (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') (x y : Over.mk t' ⟶ G') :
    push hφ.1.w (t := t' ≫ f) rfl (x * y) = push hφ.1.w rfl x * push hφ.1.w rfl y :=
  Over.OverMorphism.ext (hφ.2 (Over.mk t') x y (push hφ.1.w rfl x) (push hφ.1.w rfl y) rfl rfl).symm

theorem push_one (hφ : IsGrpPullback G' G f φ) {T : Scheme.{0}} (t' : T ⟶ X') :
    push hφ.1.w (t := t' ≫ f) rfl (1 : Over.mk t' ⟶ G') = 1 := by
  have h := push_mul hφ t' 1 1
  rw [_root_.mul_one] at h
  exact mul_eq_left.1 h.symm

theorem push_comp (hw : φ ≫ G.hom = G'.hom ≫ f) {T : Scheme.{0}} {t' : T ⟶ X'} {t : T ⟶ X} (ht : t' ≫ f = t)
    {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) (x : Over.mk t' ⟶ G') :
    push hw ht (x ≫ a') = push hw ht x ≫ a :=
  Over.OverMorphism.ext (by
    show (x ≫ a').left ≫ φ = (push hw ht x ≫ a).left
    rw [Over.comp_left, Over.comp_left, push_left, Category.assoc, ha, Category.assoc])

theorem isDerivAt0_iff_comp (H : IsPullback φ G'.hom G.hom f) {g : ℕ} {y' : Sp ℂ ⟶ X'}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ G'.left)} (he : ∀ z, e z ≫ G'.hom = y')
    (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) (w : Fin g → ℂ) {v : Sp (DualNumber ℂ) ⟶ G'.left}
    (hv : v ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') :
    IsDerivAt0 e w v ↔ IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨fun h => FibreDeriv.isDerivAt0_comp h φ, fun h => ?_⟩
  have H₁ := (IsPullback.of_hasPullback G'.hom y').paste_horiz H
  let e₁ : (Fin g → ℂ) → (Sp ℂ ⟶ pullback G'.hom y') :=
    fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp])
  let v₁ : Sp (DualNumber ℂ) ⟶ pullback G'.hom y' := pullback.lift v (spMap (algebraMap ℂ (DualNumber ℂ))) hv
  have h1 : ∀ z, e₁ z ≫ pullback.fst _ _ = e z := fun z => pullback.lift_fst _ _ _
  have hv1 : v₁ ≫ pullback.fst _ _ = v := pullback.lift_fst _ _ _
  have hf1 : (fun z => e₁ z ≫ pullback.fst G'.hom y' ≫ φ) = fun z => e z ≫ φ :=
    funext fun z => by rw [← Category.assoc, h1]
  have key := FibreDeriv.isDerivAt0_of_isPullback H₁ (e := e₁) (fun z => pullback.lift_snd _ _ _)
    (by rw [hf1]; exact hol) (pullback.lift_snd _ _ _) (by rw [hf1, ← Category.assoc, hv1]; exact h)
  have := FibreDeriv.isDerivAt0_comp key (pullback.fst _ _)
  rw [hv1] at this
  simpa only [h1] using this

theorem spMap_fst_alg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem isExp_iff (hφ : IsGrpPullback G' G f φ) {g : ℕ} (y' : Sp ℂ ⟶ X') (e : (Fin g → ℂ) → (Over.mk y' ⟶ G')) :
    IsExp y' e ↔ IsExp (y' ≫ f) (fun z => push hφ.1.w rfl (e z)) := by
  have H := hφ.1
  have hpe : ∀ z, (push H.w (t := y' ≫ f) rfl (e z)).left = (e z).left ≫ φ := fun z => rfl
  have hes : ∀ z, (e z).left ≫ G'.hom = y' := fun z => Over.w (e z)
  have hol : IsHolTo Set.univ (fun z => (e z).left) ↔ IsHolTo Set.univ (fun z => (e z).left ≫ φ) :=
    ⟨fun h => HolFibre.isHolTo_comp h φ, fun h => HolFibre.isHolTo_of_isPullback H h
      (by simp only [hes]; exact HolFibre.isHolTo_const isOpen_univ y')⟩
  have ht : (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y') ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (y' ≫ f) :=
    Category.assoc _ _ _
  let pE : (epsPt y' ⟶ G') → (epsPt (y' ≫ f) ⟶ G) := push H.w ht
  have pEi : Function.Injective pE := push_injective H ht
  have pEs : Function.Surjective pE := push_surjective H ht
  have hd : IsHolTo Set.univ (fun z => (e z).left ≫ φ) → ∀ w (v : epsPt y' ⟶ G'),
      IsDerivAt0 (fun z => (e z).left) w v.left ↔ IsDerivAt0 (fun z => (push H.w (t := y' ≫ f) rfl (e z)).left) w (pE v).left :=
    fun h w v => isDerivAt0_iff_comp H hes h w (Over.w v)
  have hbase : ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (pE v).left =
      (push H.w (t := y' ≫ f) rfl (e 0)).left ↔ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left := by
    intro v
    refine ⟨fun h => H.hom_ext (by rw [Category.assoc]; exact h) ?_, fun h => ?_⟩
    · rw [Category.assoc, Over.w v, hes]
      show spMap _ ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y' = y'
      rw [← Category.assoc, spMap_fst_alg, Category.id_comp]
    · show spMap _ ≫ v.left ≫ φ = (e 0).left ≫ φ
      rw [← Category.assoc, h]
  have hinj : Function.Injective (push H.w (t := y' ≫ f) rfl (t' := y')) := push_injective H rfl
  constructor
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' := hol.1 hh
    refine ⟨fun z w => by dsimp only; rw [hadd, push_mul hφ], (push_surjective H rfl).comp hsurj, hh', fun w => ?_,
      fun v hv => ?_⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      refine ⟨pE v, (hd hh' w v).1 hv, fun v' hv' => ?_⟩
      obtain ⟨v', rfl⟩ := pEs v'
      rw [hu v' ((hd hh' w v').2 hv')]
    · obtain ⟨v, rfl⟩ := pEs v
      obtain ⟨w, hw, hu⟩ := hd2 v ((hbase v).1 hv)
      exact ⟨w, (hd hh' w v).1 hw, fun w' hw' => hu w' ((hd hh' w' v).2 hw')⟩
  · rintro ⟨hadd, hsurj, hh, hd1, hd2⟩
    have hh' : IsHolTo Set.univ (fun z => (e z).left ≫ φ) := hh
    refine ⟨fun z w => hinj (by have h := hadd z w; dsimp only at h; rw [h, push_mul hφ]), fun x => ?_, hol.2 hh', fun w => ?_, fun v hv => ?_⟩
    · obtain ⟨z, hz⟩ := hsurj (push H.w rfl x)
      exact ⟨z, hinj hz⟩
    · obtain ⟨v, hv, hu⟩ := hd1 w
      obtain ⟨v, rfl⟩ := pEs v
      exact ⟨v, (hd hh' w v).2 hv, fun v' hv' => pEi (hu _ ((hd hh' w v').1 hv'))⟩
    · obtain ⟨w, hw, hu⟩ := hd2 (pE v) ((hbase v).2 hv)
      exact ⟨w, (hd hh' w v).2 hw, fun w' hw' => hu w' ((hd hh' w' v).1 hw')⟩

end GlobalTheory.UnifPull

namespace GlobalTheory.UnifPull

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {R R' : Type} [CommRing R]
  [CommRing R'] {σ : R →+* ℂ} {σ' : R' →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {F' : Fam R' O Λ g} {N : ℕ}
  {f : F'.X ⟶ F.X} {φ : F'.A.left ⟶ F.A.left}

theorem unifAt_iff (hφ : IsGrpPullback F'.A F.A f φ) (hact : ∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left)
    (hL : LBIso F'.L (F.L.pull φ)) (heta : ∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) (D' : PLat O bar)
    (t : Λ → D'.La) (P : D'.La →+ (Fin g → ℂ)) (y' : Sp ℂ ⟶ F'.X) (hy' : y' ≫ F'.s = spMap σ')
    (hy : (y' ≫ f) ≫ F.s = spMap σ) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F'.A)) :
    UnifAt F' σ' ρ N D' t P y' e' ↔ UnifAt F σ ρ N D' t P (y' ≫ f) (fun z => push hφ.1.w rfl (e' z)) := by
  have hinj : Function.Injective (push hφ.1.w (t := y' ≫ f) rfl (t' := y')) := push_injective hφ.1 rfl
  have hker : ∀ z, push hφ.1.w (t := y' ≫ f) rfl (e' z) = 1 ↔ e' z = 1 := fun z => by
    rw [← push_one hφ y']
    exact hinj.eq_iff
  have hlin : ∀ a z, e' (ρ a *ᵥ z) = e' z ≫ F'.act a ↔
      push hφ.1.w (t := y' ≫ f) rfl (e' (ρ a *ᵥ z)) = push hφ.1.w rfl (e' z) ≫ F.act a := fun a z => by
    rw [← push_comp hφ.1.w rfl (hact a)]
    exact hinj.eq_iff.symm
  have hweil : ∀ (k : ℤ) (x x' : Over.mk y' ⟶ F'.A) (c : Γ(Sp ℂ, ⊤)ˣ), Out.WeilIs F'.A F'.L k x x' c ↔
      Out.WeilIs F.A F.L k (push hφ.1.w (t := y' ≫ f) rfl x) (push hφ.1.w rfl x') c := fun k x x' c =>
    GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ F.A F'.A f φ F.L F'.L F.isLB F'.isLB hφ hL (Over.mk y') k x x' _ _ c
      rfl rfl
  have hunit : ∀ a, push hφ.1.w (t := y' ≫ f) rfl (toUnit (Over.mk y') ≫ F'.eta a) =
      toUnit (Over.mk (y' ≫ f)) ≫ F.eta a := fun a => Over.OverMorphism.ext (by
    rw [push_left, Over.comp_left, Over.comp_left, Category.assoc, heta]
    simp)
  have heta' : ∀ a x, toUnit _ ≫ F'.eta a = x ↔ toUnit _ ≫ F.eta a = push hφ.1.w (t := y' ≫ f) rfl x :=
    fun a x => by
      rw [← hunit]
      exact hinj.eq_iff.symm
  constructor
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy, hP, (isExp_iff hφ y' e').1 hE, fun z => (hker z).trans (hK z), fun a z => (hlin a z).1 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).1 (hW k a b c hk hc), fun a => (heta' a _).1 (hT a)⟩
  · rintro ⟨-, hP, hE, hK, hA, hW, hT⟩
    exact ⟨hy', hP, (isExp_iff hφ y' e').2 hE, fun z => (hker z).symm.trans (hK z), fun a z => (hlin a z).2 (hA a z),
      fun k a b c hk hc => (hweil k _ _ _).2 (hW k a b c hk hc), fun a => (heta' a _).2 (hT a)⟩

end GlobalTheory.UnifPull

open GlobalTheory.UnifPull in

theorem GlobalTheory.unifAt_correspond_of_cartesian : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* ℂ) (σ' : R' →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (F' : Fam R' O Λ g) (N : ℕ) (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsGrpPullback F'.A F.A f φ → (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) → LBIso F'.L (F.L.pull φ) → (∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left) → ∀ (D' : PLat O bar) (t : Λ → D'.La) P (y' : Sp ℂ ⟶ F'.X), y' ≫ F'.s = spMap σ' → (y' ≫ f) ≫ F.s = spMap σ → (∀ e', UnifAt F' σ' ρ N D' t P y' e' → ∃ e, UnifAt F σ ρ N D' t P (y' ≫ f) e ∧ ∀ z, (e z).left = (e' z).left ≫ φ) ∧ ∀ e, UnifAt F σ ρ N D' t P (y' ≫ f) e → ∃ e', UnifAt F' σ' ρ N D' t P y' e' ∧ ∀ z, (e z).left = (e' z).left ≫ φ := by
  intro O _ bar g ρ R R' _ _ σ σ' Λ F F' N f φ hφ hact hL heta D' t P y' hy' hy
  refine ⟨fun e' he' => ⟨_, (unifAt_iff hφ hact hL heta D' t P y' hy' hy e').1 he', fun z => rfl⟩,
    fun e he => ⟨fun z => pull hφ.1 rfl (e z), ?_, fun z => (hφ.1.lift_fst _ _ _).symm⟩⟩
  have h : (fun z => push hφ.1.w (t := y' ≫ f) rfl (pull hφ.1 rfl (e z))) = e := funext fun z => push_pull hφ.1 rfl (e z)
  exact (unifAt_iff hφ hact hL heta D' t P y' hy' hy _).2 (by rw [h]; exact he)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIdeleCharTrivialCongruentOneModulo
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct Topology

namespace GlobalTheory.HeckeSplitGen

theorem integralFiniteAdelesTensor_eq_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    intAEF F E = GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  unfold intAEF GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_trivial_modSetF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : (AF F ⊗[F] E)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitGen.modSetF F E N, ν x = 1 := by
  intro F E _ _ _ _ _ ν hν
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (GlobalTheory.AdLat.RA F E) := ⟨rfl⟩
  haveI : ContinuousAdd (GlobalTheory.AdLat.RA F E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  have hsmall := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (by simp)).2
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.finite_order_of_small (infPartF F E) (finPartF F E) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (GlobalTheory.CharFin.hatRing F E) hsmall (GlobalTheory.CharFin.finite_quotient_hatRing F E) ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  rw [integralFiniteAdelesTensor_eq_adelicCompletion_integers] at hr h3
  have hNr : (N : Af F ⊗[F] E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPartF F E (x : AEF F E) ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    have : finPartF F E (x : AEF F E) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => one_mem _, _, ⟨1, rfl⟩,
      by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMinorLeOneAndHadamardColumnsStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns : (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n), ‖(u.1.submatrix I J).det‖ ≤ 1) ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ), ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
  first | exact @GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard | exact GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard | (intros; apply GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacksStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishingForms_iff_proportional_pullbacks : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔ ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  first | (exact @GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (exact GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (intros; apply GlobalTheory.HomFixUniv.formsOK_iff_exists_proport  <;> assumption)
end

