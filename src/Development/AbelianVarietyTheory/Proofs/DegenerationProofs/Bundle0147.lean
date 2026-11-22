import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormMulLeOfIrreducible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPosIsGreatestNormMulVecOnKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceIrreducibleResidue
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelCoordinatesLocalBasis
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Calc
open GlobalTheory.FrameGen GlobalTheory.ConstFam

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L' : LB G'.left}
  {L : LB G.left} {w : LB.Iso L' (L.pull φ)} {k : ℕ} {T' : Over S'} {T T₁ : Over S}

theorem prod_ext' {Z : Scheme.{0}} {a b : Z ⟶ (T ⊗ G).left} (h₁ : a ≫ (fst T G).left = b ≫ (fst T G).left)
    (h₂ : a ≫ (snd T G).left = b ≫ (snd T G).left) : a = b := pullback.hom_ext h₁ h₂

theorem exists_lift {Z : Scheme.{0}} (a : Z ⟶ T.left) (b : Z ⟶ G.left) (e : a ≫ T.hom = b ≫ G.hom) :
    ∃ H : Z ⟶ (T ⊗ G).left, H ≫ (fst T G).left = a ∧ H ≫ (snd T G).left = b :=
  ⟨pullback.lift a b e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem prod_w : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := (Over.w _).trans (Over.w _).symm

theorem exists_prod (hφ : φ ≫ G.hom = G'.hom ≫ f) {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ H : (T' ⊗ G').left ⟶ (T ⊗ G).left, H ≫ (fst T G).left = (fst T' G').left ≫ h ∧
      H ≫ (snd T G).left = (snd T' G').left ≫ φ :=
  exists_lift _ _ (by rw [Category.assoc, Category.assoc, hh, hφ, ← Category.assoc, ← Category.assoc, prod_w])

theorem thru_sv {h : T'.left ⟶ T.left} {s : LB.Sec (LPow G L (k : ℤ) T)} {s' : LB.Sec (LPow G' L' (k : ℤ) T')}
    (H : Thru w k h s s') {Z : Scheme.{0}} (r' : Z ⟶ (T' ⊗ G').left) (r : Z ⟶ (T ⊗ G).left)
    (h₁ : r ≫ (fst T G).left = r' ≫ (fst T' G').left ≫ h) (h₂ : r ≫ (snd T G).left = r' ≫ (snd T' G').left ≫ φ)
    (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sv G L k s r z J = (wVal w z J J' (r' ≫ (snd T' G').left) ^ k).val * sv G' L' k s' r' z J' := by
  rw [Units.val_pow_eq_pow_val]
  exact H Z r' r h₁ h₂ z J J' hJ hJ'

theorem existsUnique_thru (hφ : φ ≫ G.hom = G'.hom ≫ f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) (s : LB.Sec (LPow G L (k : ℤ) T)) :
    ∃! t : LB.Sec (LPow G' L' (k : ℤ) T'), Thru w k h s t := by
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hh
  obtain ⟨t, ht⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T' G').left)
    (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (h := H) hw hL hL' (fun _ => h₂.symm) s
  have key : Thru w k h s t := fun Z r' r e₁ e₂ z J J' hJ hJ' => by
    obtain rfl : r = r' ≫ H := prod_ext' (by rw [Category.assoc, h₁, e₁]) (by rw [Category.assoc, h₂, e₂])
    have a := ht.sval (fun _ => h₂.symm) r' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val] at a
  refine ⟨t, key, fun t' ht' => SecOps.sec_ext (sec_ext_val hL' fun y J' hJ' => ?_)⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e₁ : H ≫ (fst T G).left = 𝟙 _ ≫ (fst T' G').left ≫ h := by rw [Category.id_comp, h₁]
  have e₂ : H ≫ (snd T G).left = 𝟙 _ ≫ (snd T' G').left ≫ φ := by rw [Category.id_comp, h₂]
  exact (Units.mul_right_inj _).1 ((thru_sv ht' _ H e₁ e₂ y hJ hJ').symm.trans (thru_sv key _ H e₁ e₂ y hJ hJ'))

theorem cmb_iff (hL : L.IsLB) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (k : ℤ) T)) (a : Fin n → Γ(T.left, ⊤))
    (t : LB.Sec (LPow G L (k : ℤ) T)) :
    ((∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J) ∧
    ((∀ (z : (T ⊗ G).left) (J), Good L z J →
      sv G L k t (𝟙 _) z J = ∑ i, gT (𝟙 _ ≫ (fst T G).left) z (a i) * sv G L k (b i) (𝟙 _) z J) →
      ∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) := by
  have key : ∀ t : LB.Sec (LPow G L (k : ℤ) T), (∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J := fun t H Z r z J hJ =>
    (SectionScalarValuation.sval_lin (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (s := t)
      (fun i => (fst T G).left.appTop.hom (a i)) b H r z hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ((gs_top _ _ _).trans (gT_comp _ _ _ _)) rfl)
  refine ⟨key t, fun H j => ?_⟩
  let σ := SectionLimit.linSec (fun i => (fst T G).left.appTop.hom (a i)) b
  exact sec_ext_val (s := t) (s' := σ) hL (fun y J hJ => (H y J hJ).trans (key σ (fun _ => rfl) _ _ y J hJ).symm) j

theorem cmb_of_lin (hφ : φ ≫ G.hom = G'.hom ≫ f) (hL : L.IsLB) (hL' : L'.IsLB) {g : T'.left ⟶ T₁.left}
    (hg : g ≫ T₁.hom = T'.hom ≫ f) {h : T₁ ⟶ T} {p : T'.left ⟶ T.left} (hp : p = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {c : Fin n → Γ(T₁.left, ⊤)} {s : LB.Sec (LPow G L (k : ℤ) T₁)}
    {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')} {t : LB.Sec (LPow G' L' (k : ℤ) T')} (hl : Lin G L k h b c s)
    (hb : ∀ i, Thru w k p (b i) (b' i)) (ht : Thru w k g s t) :
    ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  subst hp
  refine (cmb_iff hL' b' _ t).2 fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL z
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hg
  have e := lin_all hL hl H z hJ
  rw [thru_sv ht (𝟙 _) H (by rw [Category.id_comp, h₁]) (by rw [Category.id_comp, h₂]) z hJ hJ'] at e
  refine (Units.mul_right_inj _).1 (e.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [thru_sv (hb i) (𝟙 _) (H ≫ (h ▷ G).left)
    (by rw [Category.id_comp, Category.assoc, wh_fst, ← Category.assoc, h₁, Category.assoc])
    (by rw [Category.id_comp, Category.assoc, wh_snd, h₂]) z hJ hJ', gT_comp, h₁, Category.id_comp,
    Category.id_comp, mul_left_comm]

theorem exists_thru_up (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _) :
    ∃ H : (T₁ ⊗ G).left ⟶ (T' ⊗ G').left, H ≫ (fst T' G').left ≫ g = (fst T₁ G).left ∧
      H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left ∧
      ∀ t : LB.Sec (LPow G' L' (k : ℤ) T'), ∃ s : LB.Sec (LPow G L (k : ℤ) T₁), Thru w k g s t := by
  have hp : (snd T₁ G).left ≫ G.hom = (((fst T₁ G).left ≫ p) ≫ T'.hom) ≫ f := by
    rw [Category.assoc, ← hg, Category.assoc, ← Category.assoc p, pg, Category.id_comp, prod_w]
  obtain ⟨H, h₁, h₂⟩ := exists_lift (T := T') (G := G') ((fst T₁ G).left ≫ p) (hφ.lift _ _ hp) (hφ.lift_snd _ _ hp).symm
  have h₃ : H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left := by rw [← Category.assoc, h₂, hφ.lift_fst]
  refine ⟨H, by rw [← Category.assoc, h₁, Category.assoc, pg, Category.comp_id], h₃, fun t => ?_⟩
  obtain ⟨t₁, ht₁⟩ := exists_sec_up (φ' := fun _ : Fin 1 => (snd T' G').left) (ε := fun _ => (k : ℤ))
    ((isGen_iff w).1 hw) hL hL' t
  obtain ⟨s, -, hs⟩ := SectionLimit.exists_pull t₁ H (fun _ : Fin 1 => (snd T₁ G).left) (fun _ => h₃)
  refine ⟨s, fun Z r' r e₁ e₂ z J J' hJ hJ' => ?_⟩
  have e₁' : r ≫ H ≫ (fst T' G').left = r' ≫ (fst T' G').left := by
    rw [h₁, ← Category.assoc, e₁, Category.assoc, Category.assoc, gp, Category.comp_id]
  have e : r ≫ H = r' := prod_ext' (by rw [Category.assoc, e₁']) (hφ.hom_ext
    (by rw [Category.assoc, Category.assoc, h₃, e₂, Category.assoc])
    (by rw [Category.assoc, Category.assoc, Category.assoc, ← prod_w, ← Category.assoc H, ← Category.assoc, e₁',
      Category.assoc]))
  have ST : SecThrough w (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T' G').left ≫ φ) (fun _ => (k : ℤ)) t t₁
      (𝟙 _) := fun Z r z p q hp hq => by
    rw [Category.comp_id]
    exact ht₁ Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  have a := ST.sval (fun _ => (Category.id_comp _).symm) r' hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, Category.comp_id] at a
  exact (hs Z r z J hJ).trans ((congrArg (fun q => sval t₁ q z J) e).trans a)

theorem basis_thru (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _)
    {h : T₁ ⟶ T} {q : T'.left ⟶ T.left} (hq : q = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')}
    (hB : BasisAlong G L k h b) (hb : ∀ i, Thru w k q (b i) (b' i)) (t : LB.Sec (LPow G' L' (k : ℤ) T')) :
    ∃! c : Fin n → Γ(T₁.left, ⊤), ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  obtain ⟨H, h₁, h₃, hs⟩ := exists_thru_up (k := k) hφ hw hL hL' hg gp pg
  obtain ⟨s, hst⟩ := hs t
  obtain ⟨c, hc, hu⟩ := hB s
  refine ⟨c, cmb_of_lin hφ.w hL hL' hg hq hc hb hst, fun c' hc' => hu c' fun z J hJ => ?_⟩
  subst hq
  obtain ⟨J', hJ'⟩ := exists_good' hL' z
  have a := thru_sv hst H (𝟙 _) ((Category.id_comp _).trans h₁.symm) ((Category.id_comp _).trans h₃.symm) z hJ hJ'
  refine a.trans ?_
  rw [(cmb_iff hL' b' _ t).1 hc' _ H z J' hJ', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have d := thru_sv (hb i) H (h ▷ G).left (by rw [wh_fst, ← h₁]; simp only [Category.assoc]) (by rw [wh_snd, h₃]) z hJ hJ'
  rw [mul_left_comm, ← d, gT_comp, Category.assoc, h₁]
  exact congrArg₂ (· * ·) (gs_top _ _ _).symm rfl

theorem appTop_fnR {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (c : R) :
    (spMap y).appTop.hom (fnR c) = fnR (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  intro Z G₀ _ L₀ hL R _ _ x A φ w gp hw F _ _ k
  refine ⟨fun T p hp s => existsUnique_thru (T' := TFK (R := R) F) gp.1.w hw hL A.isLB hp s,
    fun R' _ y T h ga e n b c s bF t hl hb ht j => ?_, fun K _ y ga e n τ τF hB hτ t => ?_⟩
  · have := cmb_of_lin (T' := TFK (R := R) F) (T₁ := Over.mk y) (g := spMap ga) gp.1.w hL A.isLB e rfl hl hb ht j
    exact this.trans (Finset.sum_congr rfl fun i _ =>
      congrArg (fun q => liftFun A.A _ q * (bF i).f j) (appTop_fnR ga (c i)))
  · obtain ⟨c, hc, hu⟩ := basis_thru (T' := TFK (R := R) F) (T₁ := Over.mk (jFK (R := R) F ≫ x)) (g := 𝟙 (Sp F))
      (p := 𝟙 (Sp F)) gp.1 hw hL A.isLB (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _).symm (hB F ga _ e) hτ t
    let ε := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm
    refine ⟨fun i => ε.symm (c i), fun j => (hc j).trans (Finset.sum_congr rfl fun i _ => ?_), fun a ha => funext fun i => ?_⟩
    · exact congrArg (fun q => liftFun A.A _ q * (τF i).f j) (ε.apply_symm_apply (c i)).symm
    · exact ε.eq_symm_apply.2 (congrFun (hu (fun i => ε (a i)) ha) i)

end GlobalTheory.OneBasis.Calc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitAllAndIsSemiAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.FibreSplit

theorem exists_residue_factor {K : Type} [Field K] {Z : Scheme.{0}} (s : Sp K ⟶ Z) [SurjectiveOnStalks s]
    (z : Z) (hz : s (IsLocalRing.closedPoint K) = z) :
    ∃ f : Sp (Z.residueField z) ⟶ Sp K, f ≫ s = Z.fromSpecResidueField z := by
  subst hz
  let ρ := Z.descResidueField (Scheme.stalkClosedPointTo s)
  have hs : Function.Surjective (Scheme.stalkClosedPointTo s).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp (s.stalkMap_surjective _)
  have hρ : Function.Surjective ρ.hom := by
    have h := congrArg CommRingCat.Hom.hom (Z.residue_descResidueField (Scheme.stalkClosedPointTo s))
    rw [← h] at hs
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at hs
    exact Function.Surjective.of_comp hs
  have : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).2 ⟨ρ.hom.injective, hρ⟩
  refine ⟨inv (Spec.map ρ), ?_⟩
  rw [IsIso.inv_comp_eq]
  exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z s).symm

theorem exists_splitExt_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (h : C.Split c) :
    ∃ E : SplitExt (Sp K), E.IsGt H := by
  obtain ⟨hc, i, hT⟩ := h
  obtain ⟨B, gB, q, hB, hq, hf, hs, ha, hk, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  exact GlobalTheory.exists_splitExt_isGt_of_torusExtension K H ⟨{
    X := Fin d → ℤ, B := B, grpB := gB, isAbelian := hB, i := i, q := q, i_hom := hT.hom, q_hom := hq,
    q_flat := hf, q_surjective := hs, q_quasiCompact := inferInstance, isKernel := hk }⟩

theorem splitAll_and_isSemiAbelian : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG := by
  intro C L hT hC
  let := L.grp
  let := L.comm
  obtain ⟨hsep, -, hqc, -⟩ := core_basic C
  have := L.smooth
  have hsm : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : SplitAll C.GG := by
    intro z
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hS, -⟩ := DenseSplit.exists_dense_splitOn C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd C.GG.hom t))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd C.GG.hom t))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd C.GG.hom t))
    have : Smooth ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (Smooth (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsSeparated ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (IsSeparated (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : QuasiCompact ((Over.pullback (Out.jK R)).obj ((Over.pullback t).obj C.GG)).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd ((Over.pullback t).obj C.GG).hom _))
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    obtain ⟨E, hE⟩ := exists_splitExt_of_split (FractionRing R) _ _ d _
      (GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hS)
    have : IsPreimmersion (Out.jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
    obtain ⟨f, hf⟩ := exists_residue_factor (Out.jK R ≫ t) z (by
      rw [← ht]
      refine (Scheme.Hom.comp_apply (Out.jK R) t _).trans (congrArg t (PrimeSpectrum.ext ?_))
      change Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)])
    have : IsMonHom (pullCompIso (Out.jK R) t C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (Out.jK R) t C.GG).inv)
    obtain ⟨D⟩ := isGt_of_iso (pullCompIso (Out.jK R) t C.GG).symm hE
    have : IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso f (Out.jK R ≫ t) C.GG).inv)
    have key : ∀ s : Sp (C.Z.residueField z) ⟶ C.Z, f ≫ Out.jK R ≫ t = s →
        ∃ E : SplitExt (Sp (C.Z.residueField z)), E.IsGt ((Over.pullback s).obj C.GG) := by
      rintro _ rfl
      exact ⟨_, isGt_of_iso (pullCompIso f (Out.jK R ≫ t) C.GG).symm (GtBaseChange.isGt_extBC f E _ D)⟩
    exact key _ hf
  exact ⟨h, (isSemiAbelian_of_splitAll C.Z C.GG h).1⟩

end GlobalTheory.ZJ.FibreSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StalkUnitsSymmGm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch GlobalTheory.ArcPull GlobalTheory.FrameValue

noncomputable section
namespace GlobalTheory.Ex.Arch.FibRos

theorem exists_ros_down {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (gp : IsGrpPullback A' A f Φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) {a b : A ⟶ A} {a' b' : A' ⟶ A'}
    (a₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ a' = 1) (b₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ b' = 1)
    (ha : a'.left ≫ Φ = Φ ≫ a.left) (hb : b'.left ≫ Φ = Φ ≫ b.left)
    {r : LB.Gen (LB.LinComb L (rosatiφ A a b) rosatiε)} (hr : TorusExt.IsRos L a b r) :
    ∃ t : LB.Gen (LB.LinComb L' (rosatiφ A' a' b') rosatiε), TorusExt.IsRos L' a' b' t ∧
      ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
        y'.left ≫ Φ = m ≫ (snd A A).left → ∀ (z : T'.left) J J', Good L z J → Good L' z J' →
        val r m z J = (∏ k, om w z J J' ((lift x' y').left ≫ rosatiφ A' a' b' k) ^ rosatiε k) *
          val t (lift x' y').left z J' := by
  let Φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left := (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
  have f₁ : (fst A' A').left ≫ Φ = Φ₂ ≫ (fst A A).left :=
    (congrArg (fun q => q.left) (lift_fst (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₂ : (snd A' A').left ≫ Φ = Φ₂ ≫ (snd A A).left :=
    (congrArg (fun q => q.left) (lift_snd (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₃ : (fst A' A' ≫ a').left ≫ Φ = Φ₂ ≫ (fst A A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, f₁, Category.assoc]
  have f₄ : (snd A' A' ≫ b').left ≫ Φ = Φ₂ ≫ (snd A A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, f₂, Category.assoc]
  have hψ : ∀ i, rosatiφ A' a' b' i ≫ Φ = Φ₂ ≫ rosatiφ A a b i := fun i => by
    fin_cases i
    exacts [mul_push gp Φ₂ f₃ f₂, f₃, f₂, mul_push gp Φ₂ f₁ f₄, f₁, f₄]
  have cmp : ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
      y'.left ≫ Φ = m ≫ (snd A A).left → (lift x' y').left ≫ Φ₂ = m := fun x' y' m hx hy => by
    apply pullback.hom_ext
    · refine Eq.trans ?_ hx
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₁.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · refine Eq.trans ?_ hy
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₂.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  obtain ⟨t, ht, vt⟩ := exists_down_om hw hL hL' Φ₂ hψ r hr.1
  refine ⟨t, ⟨ht, corr_of_val hL' fun y I' hI' => ?_⟩, fun x' y' m hx hy z J J' hJ hJ' => ?_⟩
  · obtain ⟨I, hI⟩ := DegPull.exists_good' hL y
    have o : lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A') = lift η[A'] η[A'] := by simp [Hom.one_def]
    have he : eSec A' ≫ Φ = f ≫ eSec A := (cubeMapOf gp).e_comm
    have o₁ : (1 : 𝟙_ (Over S') ⟶ A').left = eSec A' := Category.id_comp _
    have e := vt _ (lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A')).left y I I' hI hI'
    rw [prod_ros, cmp 1 1 (f ≫ zero2 A) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_fst]; rfl) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_snd]; rfl),
      a₁, b₁, _root_.mul_one, o] at e
    have e₁ := (val_pull hI _ _ _).symm.trans ((val_corr hI hr.2 f).trans (val_one _))
    rw [e₁] at e
    rw [val_pull hI', val_one, Category.id_comp]
    simpa using e.symm
  · have e := vt _ (lift x' y').left z J J' hJ hJ'
    rwa [cmp x' y' m hx hy] at e

theorem stalkUnits_symm_gm {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)ˣ) : (((TorusExt.stalkUnits z).symm (gm x z U a) : Fˣ) : F) = valF x U a.val := by
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (toStk_valF x U z h a).symm

theorem vF_eq_genVal {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    {u : HolUnif A L' g} (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {J : (Sp ℂ ⟶ X) → L.ι}
    (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ A.left)} {ε : K → ℤ}
    (r : LB.Gen (LB.LinComb L φ ε)) {t : LB.Gen (LB.LinComb L' φ' ε)} (ht : t.IsGen) (m : Sp ℂ ⟶ Y) {y : Sp ℂ ⟶ Y'}
    {z : K → Fin g → ℂ} (hz : IsLift u φ' y z)
    (h : ∀ (p : Sp ℂ) J', Good L' p J' → val r m p J = (∏ k, om w p J J' (y ≫ φ' k) ^ ε k) * val t y p J') :
    vF r m J = genVal u hL' t y z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : Good L p J := fun ψ => hJ ψ trivial
  have gJ' : Good L' p (chartAt hL') := fun ψ => le_chartAt hL' ψ trivial
  have e := congrArg (fun q => (((TorusExt.stalkUnits p).symm q : ℂˣ) : ℂ)) (h p _ gJ')
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val] at e ⊢
  have e₁ : (((TorusExt.stalkUnits p).symm (val r m p J) : ℂˣ) : ℂ) = vF r m J :=
    stalkUnits_symm_gm _ _ p (gJ.mem φ m) _
  have e₂ : (((TorusExt.stalkUnits p).symm (val t y p (chartAt hL')) : ℂˣ) : ℂ) =
      genVal u hL' t y z * frameProd u ε z fun k => chartAt hL' (y ≫ φ' k) :=
    (stalkUnits_symm_gm _ _ p (gJ'.mem φ' y) _).trans (valAt'_gen hL' ht hz (le_wchart_chartAt hL' φ' y))
  rw [e₁, e₂, mul_left_comm, frameProd, ← Finset.prod_mul_distrib] at e
  refine e.trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_))
  rw [← mul_zpow, hz k, hfr _ _ (le_chartAt hL' _)]
  refine congrArg (fun q => (q * _) ^ ε k) ?_
  have hm : (u.ex (z k)).left p ∈ (L.pull Φ).U (fun _ => J ((u.ex (z k)).left ≫ Φ)) ⊓
      L'.U (chartAt hL' (u.ex (z k)).left) := ⟨mem_pull.2 (gJ ((u.ex (z k)).left ≫ Φ)), gJ' _⟩
  exact stalkUnits_symm_gm _ _ p hm _

theorem fibRosSt : Laws → FibRosSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ f f' - - F G hF hG r hr
  have down : ∀ (a : D.P.A ⟶ D.P.A) (H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, ex (H z) = ex z ≫ a) →
      ∃ a' : P'.A ⟶ P'.A, a'.left ≫ φ = φ ≫ a.left ∧ (∀ z, u.ex (H z) = u.ex z ≫ a') ∧
        (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A) ≫ a' = 1 := fun a H hH => by
    let a' : P'.A ⟶ P'.A := Over.homMk (gp.1.lift (φ ≫ a.left) P'.A.hom
      (by rw [Category.assoc, Over.w, gp.1.w])) (gp.1.lift_snd _ _ _)
    have ha : a'.left ≫ φ = φ ≫ a.left := gp.1.lift_fst _ _ _
    have hu : ∀ z, u.ex (H z) = u.ex z ≫ a' := fun z =>
      Over.OverMorphism.ext (gp.1.hom_ext (by
        rw [← hex, hH, Over.comp_left, Over.comp_left, hex, Category.assoc, Category.assoc, ha]) (by rw [Over.w, Over.w]))
    refine ⟨a', ha, hu, ?_⟩
    have h0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
    rw [← h0, ← hu, map_zero]
  obtain ⟨a, ha, ua, a₁⟩ := down f F hF
  obtain ⟨b, hb, ub, b₁⟩ := down f' G hG
  obtain ⟨t, ht, vt⟩ := exists_ros_down gp D.P.isLB P'.isLB hw a₁ b₁ ha hb (r := r) hr
  obtain ⟨adj, one⟩ := genVal_rosati P'.isLB hAH ua ub t ht.1 ht.2
  refine ⟨adj, fun x z => ?_⟩
  have e := vF_eq_genVal P'.isLB hJ (fun z i hi => by rw [← hex]; exact hfr z i hi) r ht.1 (lift (ex x) (ex z)).left
    (isLift_rosati ua ub x z) (fun p J' hJ' => vt (u.ex x) (u.ex z) _
      ((hex x).symm.trans (congrArg (fun q => q.left) (lift_fst (ex x) (ex z)).symm))
      ((hex z).symm.trans (congrArg (fun q => q.left) (lift_snd (ex x) (ex z)).symm)) p J J'
      (fun ψ => hJ ψ trivial) hJ')
  rw [e, one, _root_.one_mul]
  simp only [Fin.prod_univ_six, rosatiLift, rosatiε, Matrix.cons_val, zpow_neg, zpow_one, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch.FibRos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

open TestSpan in

theorem testLattice_eq_span_sections : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → l.Match τ → u.Link σ b → b.det ≠ 0 → ∃ c : FractionRing u.V, c ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range ((c • b).map (algebraMap _ (PadicAlgCl p)))) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l τ σ cls md b hbig hint hmt hlink hdet
  obtain ⟨κ, hκ, hfr⟩ := FrameNorm.exists_pos_isGreatest_norm_mulVec_on_ker hLL o Ω S ρ p y₀ u l σ cls md b hbig hint hlink
  have hΛ := LatChar.mem_lattice_iff hLL o Ω S ρ p y₀ u l σ cls md b κ hbig hint hlink hdet hκ hfr
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  have hE := E_eq_bdd τ φ (fun _ => rfl) (EvCrd.ev_crd_act hLL o Ω S ρ).2
    (GlobalTheory.weightSpace_irreducible_residue hLL o Ω S ρ p φ _ τ.isoFree)
  have hker : ∀ a, a ∈ l.yy.ker ↔ a ∈ τ.yy.ker := fun a => by
    obtain ⟨e, -, he⟩ := hmt
    have h1 := he a 0
    rw [map_zero] at h1
    exact h1.symm
  obtain ⟨x, hx⟩ := τ.δ_max.1
  obtain ⟨i, hi⟩ := (hfr 0 (zero_mem _)).1
  let em := algebraMap (FractionRing u.V) (PadicAlgCl p)
  have hy : ∀ a, y₀ a = em (u.yK a) := fun a => (DFunLike.congr_fun u.fac a).symm
  let d : FractionRing u.V := u.yK ⟨S.th x, S.th_mem x⟩
  let k : FractionRing u.V := b.mulVec (fun i => u.yK ⟨S.ev 0 i, S.ev_mem 0 i⟩) i
  have hd : ‖em d‖ = τ.δ := (congrArg norm (hy _)).symm.trans hx
  have hk : ‖em k‖ = κ := by
    refine Eq.trans ?_ hi
    simp only [hy]
    exact congrArg norm (congrFun (map_mulVec' em b _) i).symm
  have hc : ‖em (d / k)‖ = τ.δ / κ := by rw [map_div₀, norm_div, hd, hk]
  have hc0 : em (d / k) ≠ 0 := norm_pos_iff.1 (hc ▸ div_pos τ.δ_pos hκ)
  refine ⟨d / k, fun h => hc0 (by rw [h, map_zero]), ?_⟩
  generalize d / k = c at hc hc0
  let m : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p) :=
    (LinearMap.lsmul (PadicAlgCl p) (S.J → PadicAlgCl p) (em c)).restrictScalars (OO p)
  have hm : ∀ e, m e = em c • e := fun _ => rfl
  have hr : Set.range ((c • b).map em) = m '' Set.range (b.map em) := by
    have h1 : ∀ i, (c • b).map em i = m (b.map em i) := fun i => by
      rw [hm]
      funext j
      simp only [Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (h1 i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, h1 i⟩
  clear_value m
  rw [hE]
  refine Eq.trans ?_ (congrArg (Submodule.span (OO p)) hr).symm
  rw [Submodule.span_image]
  ext e
  constructor
  · intro he
    refine ⟨(em c)⁻¹ • e, (hΛ _).2 fun a ha => ?_, by rw [hm, smul_inv_smul₀ hc0]⟩
    rw [smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, hc, inv_div, div_mul_eq_mul_div, div_le_iff₀ τ.δ_pos]
    exact mul_le_mul_of_nonneg_left (he a ((hker a).1 ha)) hκ.le
  · rintro ⟨e, he, rfl⟩ a ha
    rw [hm, smul_dotProduct, smul_eq_mul, norm_mul, hc, div_mul_eq_mul_div, div_le_iff₀ hκ]
    exact mul_le_mul_of_nonneg_left ((hΛ _).1 he a ((hker a).2 ha)) τ.δ_pos.le

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelCoordinatesLocalBasisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModel_coordinates_local_basis : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → BaseFacts S M U₀ EE → Z.Ab → (∀ l, ∀ z ∈ Q.W l, IsClosed ({z} : Set M.Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ M.Z), Set.range x = {z} ∧ ∀ c : S.J → K, (∀ (g : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (j), Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Q.G → g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = x → ∑ i, c i * valF g _ ((Q.σ l i).f j) = 0) → c = 0) → Z.SecO EE := by
  first | exact @GlobalTheory.ZH.SecCoord.secO | exact GlobalTheory.ZH.SecCoord.secO | (intros; apply GlobalTheory.ZH.SecCoord.secO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegralStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_test_power_integral : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC), ∃ k : ℕ, 1 ≤ k ∧ u.Int (a ^ k) := by
  first | exact @GlobalTheory.ZH.exists_int_pow | exact GlobalTheory.ZH.exists_int_pow | (intros; apply GlobalTheory.ZH.exists_int_pow <;> assumption)
end

