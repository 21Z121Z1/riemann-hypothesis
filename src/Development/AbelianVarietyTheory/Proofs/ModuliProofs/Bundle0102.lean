import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolDescent

theorem exists_gen_of_unique {Y : Scheme.{0}} [Subsingleton Y] (y₀ : Y) {M : LB Y} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  obtain ⟨i₀, hi₀⟩ := exists_chart hM y₀
  have h : ∀ y, y ∈ M.U i₀ := fun y => by rwa [Subsingleton.elim y y₀]
  have le : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i => le_inf le_rfl fun y _ => h y
  refine ⟨⟨fun i => res (le i) (M.g i i₀)⟩, fun i j => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans ?_))
  refine (congrArg _ ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _))).trans ?_
  exact gm_cocycle hM _ y hy.1 hy.2 (h y)

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem inv_left_comp (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h A') (𝟙 A'))
  simp only [Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))

theorem kTriv_of_pullback [Flat f] [Surjective f] [IsAffineHom f] (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : Out.KTriv A' L') : Out.KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let R' : Type := Γ(pullback t f, ⊤)
  let e : Spec (CommRingCat.of R') ⟶ pullback t f := (pullback t f).isoSpec.inv
  have : IsIso e := inferInstanceAs (IsIso (pullback t f).isoSpec.inv)
  have : Epi (pullback.fst t f) := Flat.epi_of_flat_of_surjective _
  obtain ⟨q, t', hq, sq⟩ : ∃ (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
      (t' : Spec (CommRingCat.of R') ⟶ S'), Epi q ∧ q ≫ t = t' ≫ f :=
    ⟨e ≫ pullback.fst t f, e ≫ pullback.snd t f, inferInstance, by
      rw [Category.assoc, Category.assoc, pullback.condition]⟩
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have sx : (q ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ sx) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = q ≫ x.left := h.1.lift_fst _ _ _
  have main : x' = toUnit _ ≫ η[A'] := by
    refine hK R' t' x' fun p => ?_
    obtain ⟨V, hV, c, hc⟩ := hx (q p)
    refine ⟨q ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ q)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ q :=
      congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (snd T' A').left ≫ φ = (lift a b).left ≫ (snd T A).left :=
      (congrArg (fun q => q.left) (lift_snd a b)).symm
    have k₃ : ((fst T' A' ≫ x') * snd T' A').left ≫ φ = (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left := by
      have e₀ : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₁ := h.2 (T' ⊗ A') (fst T' A' ≫ x') (snd T' A') (a ≫ x) b
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)) rfl
      rw [← e₀] at e₁
      exact e₁.symm
    obtain ⟨n, hn⟩ : ∃ n : ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ ((fst T A).left ⁻¹ᵁ V).toScheme,
        n ≫ ((fst T A).left ⁻¹ᵁ V).ι = ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left :=
      ⟨IsOpenImmersion.lift _ (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    let ψ : Fin 2 → (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ A'.left) := fun k =>
      ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫
        ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k => ψ k ≫ φ) _ _ n fun k => by
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
      fin_cases k
      exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ ψ fun _ => rfl) c₃ h₃
  let a : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk q sq
  have e₁ : pushPt h.1.w x' = 1 := (congrArg _ main).trans (map_one (pushHom h T'))
  have e₂ : a ≫ x = a ≫ (1 : T ⟶ A) :=
    (Over.OverMorphism.ext hx'.symm : a ≫ x = pushPt h.1.w x').trans (e₁.trans (MonObj.comp_one a).symm)
  exact Over.OverMorphism.ext ((cancel_epi q).1 (congrArg (fun z => z.left) e₂))

theorem sym_of_pullback [Subsingleton S'] (s' : S') (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (desc : ∀ M : LB A.left, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (hS : Out.Sym A' L') : Out.Sym A L := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨U, hU, c, hc⟩ := hS s'
  obtain ⟨e, he⟩ : ∃ e : A'.left ⟶ (A'.hom ⁻¹ᵁ U).toScheme, e ≫ (A'.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show A'.hom y ∈ U
      rwa [Subsingleton.elim (A'.hom y) s']), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullSame L' ![(GrpObj.inv : A' ⟶ A').left, 𝟙 _] _ _ e fun k => by
    fin_cases k
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) he).trans (Category.id_comp _))).symm
    · exact he.symm) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' c₁ h₁
  obtain ⟨c₃, h₃⟩ := desc _ (DVR.linComb_isLB L hL ![(GrpObj.inv : A ⟶ A).left, 𝟙 _] ![1, -1])
    (gen_chartPull (chartPullOut L _ _ φ _ fun k => by
      fin_cases k
      · exact inv_left_comp h
      · exact (Category.id_comp φ).trans (Category.comp_id φ).symm) c₂ h₂)
  intro s
  refine ⟨⊤, trivial, gen_chartPull (chartPullSame L _ _ _ (A.hom ⁻¹ᵁ ⊤).ι fun k => ?_) c₃ h₃⟩
  fin_cases k
  · rfl
  · exact (Category.comp_id _).symm

theorem rigidified_sym_kTriv_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → (Out.Rigidified A L → Out.Rigidified A₀ L₀) ∧ (Out.Sym A L → Out.Sym A₀ L₀) ∧ (Out.KTriv A L → Out.KTriv A₀ L₀) := by
  intro K₀ K _ _ i A₀ A _ _ φ L₀ L hA h hL₀ hL hw
  refine ⟨fun _ => ?_, fun hS => ?_, fun hK => ?_⟩
  · have : Subsingleton (𝟙_ (Over (Sp K₀))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
    exact exists_gen_of_unique (default : PrimeSpectrum K₀) (pull_isLB hL₀ _)
  · have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact sym_of_pullback (default : PrimeSpectrum K) h hL₀ hL hw
      (GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom A.hom φ hA.smooth hA.proper hA.geomConnected h.1).1 hS
  · have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    exact kTriv_of_pullback h hL₀ hL hw hK

end GlobalTheory.PolDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.CoordMove
open GlobalTheory.ZM.RepBC

theorem isUnit_cst_id {R : Type} [CommRing R] (p : Sp R) (a : R) : IsUnit (cst (𝟙 (Sp R)) p a) ↔ a ∉ p.asIdeal := by
  rw [cst, gs_eq _ _ ⊤ trivial]
  refine ((Sp R).mem_basicOpen (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) p trivial).symm.trans ?_
  have := basicOpen_eq_of_affine (R := CommRingCat.of R) a
  exact (congrArg (fun U : (Sp R).Opens => p ∈ U) this).to_iff

theorem secCoord_iff {X : Scheme.{0}} (M : LB X) {I : Type} (th : I → M.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (v : I → R) : SecCoord M th x v ↔ ∃ τ : (M.pull x).Gen, τ.IsGen ∧ ∀ (i : I) (j : PUnit → M.ι) (p : Sp R),
      p ∈ (M.pull x).U j → gs x p _ ((th i).f (j PUnit.unit)) =
        cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := by
  refine exists_congr fun τ => and_congr_right fun _ => forall₂_congr fun i j => ?_
  have l : ∀ (h : (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit)) (p : Sp R), p ∈ (M.pull x).U j →
      gs (𝟙 (Sp R)) p ((M.pull x).U j) ((x.appLE _ _ h).hom ((th i).f (j PUnit.unit))) =
        gs x p _ ((th i).f (j PUnit.unit)) := fun h p hp =>
    (gs_appLE x _ _ h (𝟙 _) p hp _).trans (by rw [Category.id_comp])
  have r : ∀ (p : Sp R), p ∈ (M.pull x).U j → gs (𝟙 (Sp R)) p ((M.pull x).U j)
      (resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) *
        (show Γ(Sp R, (M.pull x).U j) from (τ.s j).val)) =
      cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := fun p hp =>
    (gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_res _ p le_top hp _) (gs_unit _ p _ hp _))
  exact ⟨fun h p hp => (l (pull_le M x j) p hp).symm.trans ((congrArg _ (h _)).trans (r p hp)),
    fun h e => fn_ext fun p hp => (l e p hp).trans ((h p hp).trans (r p hp).symm)⟩

theorem secCoord_down {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (H : LBIso L' (L.pull F)) {I : Type} (th : I → L.Sec) :
    ∃ th' : I → L'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R),
      SecCoord L' th' x v ↔ SecCoord L th (x ≫ F) v := by
  obtain ⟨w, hw⟩ := H
  have hw' := (isGen_iff w).1 hw
  choose th' h' using fun i => sec_pull_down hw' hL hL' (th i)
  refine ⟨th', fun R _ x v => ?_⟩
  have e : ∀ (p : Sp R) (j : PUnit → L.ι) (k : PUnit → L'.ι),
      pw w (fun _ : PUnit => x) (fun _ => 1) (𝟙 _) p j k = gw w x p (j PUnit.unit) (k PUnit.unit) := fun p j k => by
    rw [pw, Fintype.prod_unique, zpow_one, Category.id_comp]
  rw [secCoord_iff, secCoord_iff]
  constructor
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := exists_up hw' hL hL' τ hτ
    refine ⟨t, ht, fun i j p hp => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hL' (x p)
    have hk' : p ∈ (L'.pull x).U (fun _ => k) := mem_pull.2 hk
    have h₁ := h' i _ x p (j PUnit.unit) k (mem_pull₂.1 hp) hk
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p j (fun _ => k) hp hk')
    rw [e, Units.val_mul] at h₂
    refine h₁.trans ((congrArg (_ * ·) (h i (fun _ => k) p hk')).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₂.symm)
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := CubTransport.exists_down_units hw' hL hL' (φ' := fun _ : PUnit => x) τ hτ
    refine ⟨t, ht, fun i k p hp => ?_⟩
    obtain ⟨j, hj⟩ := exists_chart hL (F (x p))
    have hj' : p ∈ (L.pull (x ≫ F)).U (fun _ => j) := mem_pull₂.2 hj
    have h₁ := h' i _ x p j (k PUnit.unit) hj (mem_pull.1 hp)
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p (fun _ => j) k hj' hp)
    rw [e, Units.val_mul] at h₂
    refine (Units.mul_right_inj (gw w x p j (k PUnit.unit))).1 (h₁.symm.trans ((h i (fun _ => j) p hj').trans ?_))
    exact (congrArg (_ * ·) h₂).trans (mul_left_comm _ _ _)

theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {R : Type} [CommRing R]
    {x : Sp R ⟶ X} {v : I → R} (i : I) (p : Sp R) (h : SecCoord M th x v) :
    x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal := by
  obtain ⟨τ, -, h⟩ := (secCoord_iff M th x v).1 h
  have key : ∀ k, x p ∈ M.U k → (IsUnit (gs (𝟙 X) (x p) _ ((th i).f k)) ↔ v i ∉ p.asIdeal) := fun k hk => by
    have e := h i (fun _ => k) p (mem_pull.2 hk)
    rw [gs_stalkMap x p _ hk] at e
    rw [← isUnit_cst_id, ← isUnit_map_iff (x.stalkMap p).hom]
    exact (congrArg IsUnit e).to_iff.trans (Units.isUnit_mul_units _ _)
  rw [mem_nonzeroLocus]
  refine ⟨fun ⟨k, hk, u⟩ => (key k hk).1 u, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  exact ⟨k, hk, (key k hk).2 u⟩

theorem secCoord_pull_iso_locus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  intro X M I th hM
  refine ⟨fun X' π => ⟨fun i => secPull M π (th i), fun R _ x v => secCoord_pull M th π x v⟩, fun M' hM' H => ?_,
    fun R _ x v i p h => mem_nonzeroLocus_iff hM i p h⟩
  obtain ⟨th', h⟩ := secCoord_down hM hM'
    (LBIso.chartPull (chartPullId M') (chartPullPull M (𝟙 X) (𝟙 X) rfl) (LBIso.symm H)) th
  refine ⟨th', fun R _ x v => ?_⟩
  have := h R x v
  rwa [Category.comp_id] at this

end GlobalTheory.ZM.CoordMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ZM.SiegPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem lbIso_pull_comp {X Y Y' : Scheme.{0}} {L : LB X} {A : LB Y} {F : Y ⟶ X} (H : LBIso A (L.pull F))
    (h : Y' ⟶ Y) : LBIso (A.pull h) (L.pull (h ≫ F)) := by
  refine LBIso.chartPull (chartPullPull A h h rfl) ⟨id, fun J x hx => ?_, fun y J J' hJ hJ' => ?_⟩ H
  · have hx' := (mem_pull (F := h ≫ F)).1 hx
    exact (mem_pull (F := F)).2 hx'
  · have a1 := (mem_pull (F := h ≫ F)).1 hJ
    have a2 := (mem_pull (F := h ≫ F)).1 hJ'
    rw [gm_pull_g L (h ≫ F) (𝟙 Y') y J J' hJ hJ', Category.id_comp]
    exact (gm_pull_g L F h y J J' ((mem_pull (F := F)).2 a1) ((mem_pull (F := F)).2 a2)).symm

theorem exists_isSquare {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left} (w : φ ≫ G.hom = G'.hom ≫ f) :
    ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ := by
  let T : Over S := Over.mk ((G' ⊗ G').hom ≫ f)
  have w₁ : ((fst G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (fst G' G')]
    rfl
  have w₂ : ((snd G' G').left ≫ φ) ≫ G.hom = T.hom := by
    rw [Category.assoc, w, ← Category.assoc, Over.w (snd G' G')]
    rfl
  let x : T ⟶ G := Over.homMk ((fst G' G').left ≫ φ) w₁
  let y : T ⟶ G := Over.homMk ((snd G' G').left ≫ φ) w₂
  refine ⟨(lift x y).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]
    rfl
  · rw [← Over.comp_left, lift_snd]
    rfl

theorem isSquare_tensor {G G' : Over S} (φ : G' ⟶ G) : IsSquare φ.left (φ ⊗ₘ φ).left := by
  constructor
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem isSquare_comp {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G'.left} {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) := by
  constructor
  · rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc]
  · rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]

theorem isSquare_unique {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') (e : φ = φ') : φ₂ = φ₂' := by
  subst e
  have w : φ₂' ≫ (G ⊗ G).hom = φ₂ ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, h'.1, ← Category.assoc, h.1]
  let a : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let b : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' w
  have hab : a = b := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (fst G G).left = φ₂' ≫ (fst G G).left
      rw [h.1, h'.1]
    · apply Over.OverMorphism.ext
      change φ₂ ≫ (snd G G).left = φ₂' ≫ (snd G G).left
      rw [h.2, h'.2]
  exact congrArg (fun m => m.left) hab

theorem lbIso_lam_pull {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (h : IsGrpPullback G' G f φ)
    (hw : LBIso L' (L.pull φ)) {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (hs : IsSquare φ φ₂) :
    LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain ⟨w, hw'⟩ := hw
  have hP : PGen w := by
    unfold PGen gw
    intro Y g y j j' k k' h1 h2 h3 h4
    have m1 : g y ∈ (L.pull φ).U (fun _ => j) := (mem_pull (F := φ)).2 h1
    have m2 : g y ∈ (L.pull φ).U (fun _ => j') := (mem_pull (F := φ)).2 h2
    have hV : g y ∈ (L.pull φ).U (fun _ => j) ⊓ L'.U k ⊓ ((L.pull φ).U (fun _ => j') ⊓ L'.U k') :=
      ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
    have e := congrArg (gm g y _) (hw' (fun _ => j, k) (fun _ => j', k'))
    unfold LB.div at e
    simp only [map_mul, map_inv] at e
    simp only [gm_res g y _ hV] at e
    rw [gm_pull_g L φ g y (fun _ => j) (fun _ => j') m1 m2] at e
    exact e
  have e : ∀ I : ULift (Finset (Fin 2)),
      (psum G' (x2 G') I.down).left ≫ φ = φ₂ ≫ (psum G (x2 G) I.down).left := by
    let T : Over S' := G' ⊗ G'
    have hj : φ₂ ≫ (G ⊗ G).hom = T.hom ≫ f := by
      rw [← Over.w (fst G G), ← Category.assoc, hs.1, Category.assoc, h.1.w, ← Category.assoc,
        Over.w (fst G' G')]
    let U : Over S := Over.mk (T.hom ≫ f)
    let j : U ⟶ G ⊗ G := Over.homMk φ₂ hj
    have hΦ : ∀ u : T ⟶ G', (u.left ≫ φ) ≫ G.hom = U.hom := fun u => by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u]
      rfl
    let Φ : (T ⟶ G') → (U ⟶ G) := fun u => Over.homMk (u.left ≫ φ) (hΦ u)
    have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y =>
      Over.OverMorphism.ext (h.2 T x y (Φ x) (Φ y) rfl rfl).symm
    let Φh : (T ⟶ G') →* (U ⟶ G) := MonoidHom.mk' Φ Φmul
    have key : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), Φ u = j ≫ v → u.left ≫ φ = φ₂ ≫ v.left :=
      fun u v hh => congrArg (fun m => m.left) hh
    have key' : ∀ (u : T ⟶ G') (v : G ⊗ G ⟶ G), u.left ≫ φ = φ₂ ≫ v.left → Φ u = j ≫ v :=
      fun u v hh => Over.OverMorphism.ext (by exact hh)
    have base : ∀ k : Fin 2, Φ (x2 G' k) = j ≫ x2 G k := by
      intro k
      fin_cases k
      · exact key' _ _ hs.1.symm
      · exact key' _ _ hs.2.symm
    have fold : ∀ l : List (Fin 2),
        Φ (List.foldr (fun k acc => padd G' (x2 G' k) acc) (pzero G' (G2 G')) l) =
          j ≫ List.foldr (fun k acc => padd G (x2 G k) acc) (pzero G (G2 G)) l := by
      intro l
      induction l with
      | nil =>
        change Φh 1 = j ≫ 1
        rw [map_one, comp_one]
      | cons k l ih =>
        change Φ (x2 G' k * _) = j ≫ (x2 G k * _)
        rw [Φmul, comp_mul, base k, ih]
    intro I
    exact key _ _ (fold _)
  exact LBIso.chartPull (chartPullId _) (chartPullOut L _ _ φ₂ _ e) (iso_linComb hP _ _)

theorem lev_comm_of_basis {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    {χ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f χ) {n : ℕ} {M : Type} [AddCommGroup M] (e : (Fin n → ℤ) ≃ₗ[ℤ] M)
    (l : M → (𝟙_ (Over S) ⟶ G)) (l' : M → (𝟙_ (Over S') ⟶ G')) (hl : ∀ a b, l (a + b) = l a * l b)
    (hl' : ∀ a b, l' (a + b) = l' a * l' b)
    (H : ∀ i, (l' (e (Pi.single i 1))).left ≫ χ = f ≫ (l (e (Pi.single i 1))).left) (a : M) :
    (l' a).left ≫ χ = f ≫ (l a).left := by
  let U : Over S := Over.mk ((𝟙_ (Over S')).hom ≫ f)
  have hΦ : ∀ x : 𝟙_ (Over S') ⟶ G', (x.left ≫ χ) ≫ G.hom = U.hom := fun x => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    rfl
  let Φ : (𝟙_ (Over S') ⟶ G') → (U ⟶ G) := fun x => Over.homMk (x.left ≫ χ) (hΦ x)
  have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y =>
    Over.OverMorphism.ext (h.2 _ x y (Φ x) (Φ y) rfl rfl).symm
  let Ψ : (𝟙_ (Over S) ⟶ G) → (U ⟶ G) := fun y => toUnit U ≫ y
  have Ψmul : ∀ x y, Ψ (x * y) = Ψ x * Ψ y := fun x y => comp_mul _ _ _
  have hT : (toUnit U).left = f := by
    simp [U]
  let F₁ : (Fin n → ℤ) →+ Additive (U ⟶ G) :=
    AddMonoidHom.mk' (fun v => Additive.ofMul (Φ (l' (e v)))) (fun v w => by
      simp only [map_add, hl', Φmul]
      rfl)
  let F₂ : (Fin n → ℤ) →+ Additive (U ⟶ G) :=
    AddMonoidHom.mk' (fun v => Additive.ofMul (Ψ (l (e v)))) (fun v w => by
      simp only [map_add, hl, Ψmul]
      rfl)
  have hF : F₁ = F₂ := by
    ext i
    change (l' (e (Pi.single i 1))).left ≫ χ = (toUnit U).left ≫ (l (e (Pi.single i 1))).left
    rw [hT, H i]
  have key := congrArg (fun F : (Fin n → ℤ) →+ Additive (U ⟶ G) => (Additive.toMul (F (e.symm a))).left) hF
  change (l' (e (e.symm a))).left ≫ χ = (toUnit U).left ≫ (l (e (e.symm a))).left at key
  rw [LinearEquiv.apply_symm_apply, hT] at key
  exact key

end GlobalTheory.ZM.SiegPull

open GlobalTheory.ZM.SiegPull in

theorem GlobalTheory.ZM.siegPB_iff_tSieg : ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s₁ : S ⟶ Sp B) (s' : S' ⟶ Sp o) (s₁' : S' ⟶ Sp B) (t : TObj g k J b s) (c : SiegPre g k ζ s₁) (t' : TObj g k J b s') (c' : SiegPre g k ζ s₁') (f : S' ⟶ S), TSieg bas bas' t c → TMap t' t f → (SiegPB c' c f ↔ TSieg bas bas' t' c') := by
  intro g k J La _ bas bas' o B _ _ b ζ S S' s s₁ s' s₁' t c t' c' f hc ht
  let _ := t.ab.comm
  let _ := t'.ab.comm
  obtain ⟨ψ, hψm, hψL, hψp⟩ := hc
  obtain ⟨χ, hχ, hχL, hχp, -⟩ := ht
  obtain ⟨χ₂, hχ₂⟩ := exists_isSquare (G := t.A) (G' := t'.A) (f := f) hχ.1.w
  have hLam : LBIso (abelian₂ t'.A t'.L) ((abelian₂ t.A t.L).pull χ₂) := lbIso_lam_pull hχ hχL hχ₂
  have hLt : (abelian₂ t.A t.L).IsLB := DVR.linComb_isLB _ t.isLB _ _
  have hLt' : (abelian₂ t'.A t'.L).IsLB := DVR.linComb_isLB _ t'.isLB _ _
  have hhi : ψ.hom.left ≫ ψ.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ψ.hom_inv_id, Over.id_left]
  have hih : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ψ.inv_hom_id, Over.id_left]
  constructor
  · rintro ⟨φ, φ₂, hφ, hsq, hP, hlev⟩
    have hψg : IsGrpPullback c.A t.A (𝟙 S) ψ.hom.left := isGrpPullback_of_iso ψ
    have h1 : IsGrpPullback c'.A t.A f (φ ≫ ψ.hom.left) :=
      (IsGrpPullback.comp hφ hψg).congr (Category.comp_id f) rfl
    obtain ⟨e, hem, heχ⟩ := grpPullback_iso h1 hχ
    have sq1 := isSquare_comp (isSquare_tensor e.hom) hχ₂
    have sq2 := isSquare_comp hsq (isSquare_tensor ψ.hom)
    have heq : (e.hom ⊗ₘ e.hom).left ≫ χ₂ = φ₂ ≫ (ψ.hom ⊗ₘ ψ.hom).left := isSquare_unique sq1 sq2 heχ
    refine ⟨e, hem, ?_, fun i => ?_⟩
    · have x1 := lbIso_pull_comp hψL φ₂
      have x2 := lbIso_pull_comp hLam (e.hom ⊗ₘ e.hom).left
      rw [heq] at x2
      exact LBIso.trans c'.isLB (pull_isLB c.isLB φ₂) (pull_isLB hLt' _) hP
        (LBIso.trans (pull_isLB c.isLB φ₂) (pull_isLB hLt _) (pull_isLB hLt' _) x1 x2.symm)
    · apply hχ.1.hom_ext
      · rw [Over.comp_left, Category.assoc, heχ, ← Category.assoc, hlev, Category.assoc, ← Over.comp_left,
          hψp i, hχp i]
      · rw [Over.w, Over.w]
        rfl
  · rintro ⟨ψ', hψ'm, hψ'L, hψ'p⟩
    have hψg : IsGrpPullback c.A t.A (𝟙 S) ψ.hom.left := isGrpPullback_of_iso ψ
    have hn : IsGrpPullback c'.A t.A (f ≫ 𝟙 S) ((ψ'.hom.left ≫ χ ≫ ψ.inv.left) ≫ ψ.hom.left) :=
      (IsGrpPullback.comp (isGrpPullback_of_iso ψ') hχ).congr (by rw [Category.id_comp, Category.comp_id])
        (by rw [Category.assoc, Category.assoc, hih, Category.comp_id])
    have hφ : IsGrpPullback c'.A c.A f (ψ'.hom.left ≫ χ ≫ ψ.inv.left) := by
      refine IsGrpPullback.cancel hψg hn ?_
      rw [Category.assoc, Category.assoc, Over.w ψ.inv, hχ.1.w, ← Category.assoc, Over.w ψ'.hom]
    obtain ⟨φ₂, hsq⟩ := exists_isSquare hφ.1.w
    have sq1 := isSquare_comp (isSquare_tensor ψ'.hom) hχ₂
    have sq2 := isSquare_comp hsq (isSquare_tensor ψ.hom)
    have heq : (ψ'.hom ⊗ₘ ψ'.hom).left ≫ χ₂ = φ₂ ≫ (ψ.hom ⊗ₘ ψ.hom).left :=
      isSquare_unique sq1 sq2 (by rw [Category.assoc, Category.assoc, hih, Category.comp_id])
    refine ⟨_, φ₂, hφ, hsq, ?_, ?_⟩
    · have x1 := lbIso_pull_comp hψL φ₂
      have x2 := lbIso_pull_comp hLam (ψ'.hom ⊗ₘ ψ'.hom).left
      rw [heq] at x2
      exact LBIso.trans c'.isLB (pull_isLB hLt' _) (pull_isLB c.isLB φ₂) hψ'L
        (LBIso.trans (pull_isLB hLt' _) (pull_isLB hLt _) (pull_isLB c.isLB φ₂) x2 x1.symm)
    · intro a
      refine lev_comm_of_basis hφ (bas.trans bas'.symm) c.lev c'.lev c.lev_add c'.lev_add (fun i => ?_) a
      change (c'.lev (bas'.symm (bas (Pi.single i 1)))).left ≫ ψ'.hom.left ≫ χ ≫ ψ.inv.left =
        f ≫ (c.lev (bas'.symm (bas (Pi.single i 1)))).left
      rw [← Category.assoc, ← Over.comp_left, hψ'p i, ← Category.assoc, hχp i, Category.assoc, ← hψp i,
        Over.comp_left, Category.assoc, hhi, Category.comp_id]

end
end

