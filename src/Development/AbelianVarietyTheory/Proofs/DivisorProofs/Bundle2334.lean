import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesMinimal
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.FinAffAmple

variable {X : Scheme.{0}} {M : LB X}

theorem mem_secAdd_iff_right {s t : M.Sec} {x : X} (ht : x ∉ nonzeroLocus t) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus s := by
  by_cases hc : ∃ k, x ∈ M.U k
  · obtain ⟨k, hk⟩ := hc
    rw [GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk, GlobalTheory.mem_nonzeroLocus_iff_basicOpen _ hk] at *
    change x ∈ X.basicOpen (s.f k + t.f k) ↔ _
    rw [Scheme.mem_basicOpen _ _ _ hk, Scheme.mem_basicOpen _ _ _ hk] at *
    rw [map_add]
    have hm : (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (t.f k) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).2 ht
    have := Ideal.add_mem_iff_left (IsLocalRing.maximalIdeal _)
      (a := (ConcreteCategory.hom (X.presheaf.germ (M.U k) x hk)) (s.f k)) hm
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff] at this
    exact not_iff_not.1 this
  · push_neg at hc
    exact ⟨fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc),
      fun h => absurd (GlobalTheory.exists_chart_of_mem_nonzeroLocus h) (by simpa using hc)⟩

theorem mem_secAdd_iff_left {s t : M.Sec} {x : X} (hs : x ∉ nonzeroLocus s) :
    x ∈ nonzeroLocus (DVR.SecOps.secAdd s t) ↔ x ∈ nonzeroLocus t := by
  have e : DVR.SecOps.secAdd s t = DVR.SecOps.secAdd t s := DVR.SecOps.sec_ext fun i => add_comm (s.f i) (t.f i)
  rw [e]
  exact mem_secAdd_iff_right hs

theorem exists_sec_forall_mem (T : Finset X) (t : X → M.Sec) (ht : ∀ x ∈ T, x ∈ nonzeroLocus (t x))
    (ht' : ∀ x ∈ T, ∀ y ∈ T, y ≠ x → y ∉ nonzeroLocus (t x)) :
    ∃ g : M.Sec, ∀ x ∈ T, x ∈ nonzeroLocus g := by
  classical
  suffices H : ∀ T' : Finset X, T' ⊆ T → ∃ g : M.Sec, ∀ x ∈ T, (x ∈ nonzeroLocus g ↔ x ∈ T') by
    obtain ⟨g, hg⟩ := H T subset_rfl
    exact ⟨g, fun x hx => (hg x hx).2 hx⟩
  intro T'
  induction T' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨DVR.SecOps.secZero, fun x _ => ?_⟩
    rw [GlobalTheory.nonzeroLocus_secZero]
    simp
  | insert a T' ha ih =>
    intro hsub
    obtain ⟨g, hg⟩ := ih ((Finset.subset_insert a T').trans hsub)
    have haT : a ∈ T := hsub (Finset.mem_insert_self a T')
    refine ⟨DVR.SecOps.secAdd g (t a), fun x hx => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      rw [mem_secAdd_iff_left (fun h => ha ((hg x hx).1 h))]
      simpa using ht x haT
    · rw [mem_secAdd_iff_right (ht' a haT x hx hxa), hg x hx, Finset.mem_insert]
      simp [hxa]

theorem exists_specializes_minimal {Z : Type*} [TopologicalSpace Z] [T0Space Z] (F : Finset Z) {x : Z}
    (hx : x ∈ F) : ∃ y ∈ F, x ⤳ y ∧ ∀ z ∈ F, y ⤳ z → z = y := by
  classical
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (F.filter (x ⤳ ·)) (fun y => (F.filter (y ⤳ ·)).card)
    ⟨x, Finset.mem_filter.2 ⟨hx, specializes_refl x⟩⟩
  obtain ⟨hyF, hxy⟩ := Finset.mem_filter.1 hy
  refine ⟨y, hyF, hxy, fun z hz hyz => ?_⟩
  have hsub : F.filter (z ⤳ ·) ⊆ F.filter (y ⤳ ·) := fun w hw => by
    obtain ⟨hwF, hzw⟩ := Finset.mem_filter.1 hw
    exact Finset.mem_filter.2 ⟨hwF, hyz.trans hzw⟩
  have hle := hmin z (Finset.mem_filter.2 ⟨hz, hxy.trans hyz⟩)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hzy : z ⤳ y := (Finset.mem_filter.1 (heq ▸ Finset.mem_filter.2 ⟨hyF, specializes_refl y⟩ :
    y ∈ F.filter (z ⤳ ·))).2
  exact (hyz.antisymm hzy).eq.symm

theorem finAff_of_isAmpleLB {Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f] {L : LB X}
    (h : IsAmpleLB L) : FinAff X := by
  classical
  intro F
  let F' := F.filter (fun x => ∀ z ∈ F, x ⤳ z → z = x)
  let V : X → X.Opens := fun x =>
    ⟨(⋃ y ∈ F'.erase x, closure ({y} : Set X))ᶜ, (isClosed_biUnion_finset fun _ _ => isClosed_closure).isOpen_compl⟩
  have hV : ∀ x ∈ F', x ∈ V x := by
    intro x hx hmem
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hmem
    obtain ⟨hyx, hyF'⟩ := Finset.mem_erase.1 hy
    have hyx' : y ⤳ x := specializes_iff_mem_closure.2 hxy
    exact hyx ((Finset.mem_filter.1 hyF').2 x (Finset.mem_filter.1 hx).1 hyx').symm
  have hV' : ∀ x ∈ F', ∀ y ∈ F', y ≠ x → y ∉ V x := fun x _ y hy hyx hmem =>
    hmem (Set.mem_iUnion₂.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hy⟩, subset_closure rfl⟩)
  choose n hn s hs hsV _ using fun x : F' => h.exists_affine_le (hV x.1 x.2)
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow n hn s
  let tt : X → (lbPow L N).Sec := fun x => if hx : x ∈ F' then t ⟨x, hx⟩ else DVR.SecOps.secZero
  have htt : ∀ x (hx : x ∈ F'), nonzeroLocus (tt x) = nonzeroLocus (s ⟨x, hx⟩) := fun x hx => by
    simp only [tt, dif_pos hx, ht]
  obtain ⟨g, hg⟩ := exists_sec_forall_mem F' tt (fun x hx => (htt x hx).symm ▸ hs ⟨x, hx⟩)
    (fun x hx y hy hyx hmem => hV' x hx y hy hyx (hsV ⟨x, hx⟩ ((htt x hx) ▸ hmem)))
  refine ⟨nonzeroLocus g, h.isAffineOpen_nonzeroLocus f hN g, fun x hx => ?_⟩
  obtain ⟨y, hyF, hxy, hmin⟩ := exists_specializes_minimal F hx
  exact hxy.mem_open (nonzeroLocus g).isOpen (hg y (Finset.mem_filter.2 ⟨hyF, hmin⟩))

theorem finAff_of_relAmple : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ L : LB B.left, L.IsLB → Out.RelAmple B L → FinAff B.left := by
  intro R _ B _ hB L hL hA
  have := hB.proper
  exact finAff_of_isAmpleLB B.hom (isAmpleLB_of_relAmple_of_isAffine B hL hA)

end GlobalTheory.DualCon.FinAffAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
noncomputable section
open scoped Matrix
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LogKSDiv.Spread

theorem stalk_loc {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    letI := (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom.toAlgebra
    IsLocalization.AtPrime (B.toScheme.presheaf.stalk y) (hU.primeIdealOf ⟨B.ι y, hy⟩).asIdeal := by
  letI := (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom.toAlgebra
  letI : Algebra Γ(X, U) (X.presheaf.stalk (B.ι y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨B.ι y, hy⟩
  have hloc := hU.isLocalization_stalk ⟨B.ι y, hy⟩
  have : IsIso (B.ι.stalkMap y) := inferInstance
  let e : X.presheaf.stalk (B.ι y) ≃+* B.toScheme.presheaf.stalk y :=
    (asIso (B.ι.stalkMap y)).commRingCatIsoToRingEquiv
  exact IsLocalization.isLocalization_of_algEquiv _ (AlgEquiv.ofRingEquiv (f := e) fun r => rfl)

theorem germ_pt {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    spMap (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom ≫ hU.fromSpec = B.toScheme.fromSpecStalk y ≫ B.ι := by
  show Spec.map (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

def cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom

theorem cst_apply {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a : R) :
    cst f U a = constFn f U a := rfl

theorem spMap_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) :
    spMap (cst f U) = hU.fromSpec ≫ f := by
  show Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)) = _
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU _

theorem spread_exact {R L : Type} [CommRing R] [CommRing L] [Algebra R L] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime L P] {n : ℕ} (B : Fin n → Fin n → L) (hB : IsUnit (Matrix.of fun i j => B j i).det)
    (Q : Fin n → Matrix (Fin n) (Fin n) R) (hQ : ∀ j, (Q j).map (algebraMap R L) *ᵥ B j = B j) :
    ∃ g ∈ P.primeCompl, ∃ (s : R) (B₀ : Fin n → Fin n → R), (∀ j, algebraMap R L ∘ B₀ j = algebraMap R L s • B j) ∧
      ∀ (S : Type) [CommRing S] (ψ : R →+* S), IsUnit (ψ g) → IsUnit (ψ s) ∧
        IsUnit (Matrix.of fun i j => ψ (B₀ j i)).det ∧ ∀ j, (Q j).map ψ *ᵥ (ψ ∘ B₀ j) = ψ ∘ B₀ j := by
  classical
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl Finset.univ (fun p : Fin n × Fin n => B p.1 p.2)
  choose B₀ hB₀ using fun j i => hs (j, i) (Finset.mem_univ _)
  have eB : ∀ j, algebraMap R L ∘ B₀ j = algebraMap R L s • B j := fun j => funext fun i => by
    simpa [Algebra.smul_def] using hB₀ j i
  have hdet : (Matrix.of fun i j => B₀ j i).det ∈ P.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff L P, RingHom.map_det]
    have : (algebraMap R L).mapMatrix (Matrix.of fun i j => B₀ j i) = algebraMap R L s • Matrix.of fun i j => B j i := by
      ext i j; exact congrFun (eB j) i
    rw [this, Matrix.det_smul]
    exact ((IsLocalization.map_units L s).pow _).mul hB
  have hq : ∀ (p : Fin n × Fin n), algebraMap R L ((Q p.1 *ᵥ B₀ p.1) p.2) = algebraMap R L (B₀ p.1 p.2) := fun p => by
    have h1 : ∀ j, algebraMap R L ∘ (Q j *ᵥ B₀ j) = (Q j).map (algebraMap R L) *ᵥ (algebraMap R L ∘ B₀ j) := fun j =>
      funext fun i => by simp [Matrix.mulVec, dotProduct, map_sum]
    have h2 := congrFun (h1 p.1) p.2
    rw [eB, Matrix.mulVec_smul, hQ] at h2
    exact h2.trans (congrFun (eB p.1) p.2).symm
  choose u hu using fun p => IsLocalization.exists_of_eq (M := P.primeCompl) (S := L) (hq p)
  refine ⟨s * (Matrix.of fun i j => B₀ j i).det * ∏ p, (u p : R),
    P.primeCompl.mul_mem (P.primeCompl.mul_mem s.2 hdet) (P.primeCompl.prod_mem fun p _ => (u p).2),
    s, B₀, eB, fun S _ ψ hψ => ?_⟩
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at hψ
  obtain ⟨⟨h1, h2⟩, h3⟩ := hψ
  refine ⟨h1, ?_, fun j => funext fun i => ?_⟩
  · rw [RingHom.map_det] at h2
    convert h2 using 2
    ext i j
    rfl
  · have hp : IsUnit (ψ (u (j, i))) :=
      isUnit_of_dvd_unit (map_dvd ψ (Finset.dvd_prod_of_mem (fun p => (u p : R)) (Finset.mem_univ (j, i)))) h3
    have := congrArg ψ (hu (j, i))
    rw [map_mul, map_mul] at this
    have e := hp.mul_left_cancel this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply] at e ⊢
    rw [← e, map_sum]
    simp [map_mul]

theorem basis_of_det {S : Type} [CommRing S] {n : ℕ} (w : Fin n → Fin n → S)
    (h : IsUnit (Matrix.of fun i j => w j i).det) (cc : Fin n → S) : ∃! a : Fin n → S, cc = ∑ j, a j • w j := by
  have hs : ∀ a : Fin n → S, ∑ j, a j • w j = (Matrix.of fun i j => w j i) *ᵥ a := fun a => by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨(Matrix.of fun i j => w j i)⁻¹ *ᵥ cc, ?_, fun a ha => ?_⟩
  · dsimp only
    rw [hs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]
  · rw [ha, hs, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]

end GlobalTheory.LogKSDiv.Spread

set_option maxHeartbeats 1000000 in
open GlobalTheory.LogKSDiv.Spread GlobalTheory.ShFam.EigSpread GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in

theorem GlobalTheory.LogKSDiv.spread_genFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ (GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι)), GlobalTheory.LogKSDiv.genPt TF Z ≫ s₀ TF.Y Z = spMap φ₀ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ τ i, f₀.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧ ∀ (a : 𝓞 E) (k : Fin n), IsCombAtG TF.Y.t (LogKS.chart U) v ((Matrix.diagonal fun j => constFn TF.Y.s U.1 (embK c (e.symm j).1 a)) k) (v k ≫ (TF.Y.t.act.act a).left) := by
  intro E _ _ _ H Dw l Xo c TF Z _ φ₀ f₀ hφ₀
  classical
  let ξ : X₀ TF.Y Z := genericPoint (X₀ TF.Y Z)
  let p : TF.Y.X := (barComp TF.Y Z).ι ξ
  obtain ⟨U₁, hU₁, hp₁, x₁, hx₁, C, n, xc, hx⟩ := exists_affine_chart TF.Y.t (𝟙 TF.Y.X) p
  obtain ⟨h, hhB, hph⟩ := hU₁.exists_basicOpen_le (V := barComp TF.Y Z) ⟨p, ξ.2⟩ hp₁
  let ρ₁ : Γ(TF.Y.X, U₁) →+* (X₀ TF.Y Z).functionField :=
    (TF.Y.X.presheaf.germ U₁ p hp₁ ≫ (barComp TF.Y Z).ι.stalkMap ξ).hom
  letI := ρ₁.toAlgebra
  have hloc : IsLocalization.AtPrime (X₀ TF.Y Z).functionField (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal :=
    stalk_loc (barComp TF.Y Z) ξ hU₁ hp₁
  have hK : spMap ρ₁ ≫ hU₁.fromSpec = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι := germ_pt (barComp TF.Y Z) ξ hU₁ hp₁
  let φ₁ := cst TF.Y.s U₁
  have hφ₁ : spMap φ₁ = hU₁.fromSpec ≫ TF.Y.s := spMap_cst _ hU₁
  have hρφ : ρ₁.comp φ₁ = φ₀ := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hK, ← hφ₀, Category.assoc])
  obtain ⟨xcK, hxK, hcK⟩ := vec_bc_of_chart C hx ρ₁ (x' := GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι)
    (by rw [hx₁, Category.comp_id, hK])
  obtain ⟨Pr, hPr⟩ := exists_projectors c φ₁ hx
  choose Bv hBv using fun τ i => vec_exists hxK _ (f₀.tan τ i)
  have hBe : ∀ τ i, Bv τ i ∈ eig c φ₀ hxK τ := fun τ i => (vec_eig_iff hxK _ _).1 (by rw [← hBv]; exact f₀.eig τ i)

  have hPK : ∀ τ i, (Pr τ).map ρ₁ *ᵥ Bv τ i = Bv τ i := fun τ i =>
    (hPr ρ₁ hxK hcK τ (Bv τ i)).2 (by rw [hρφ]; exact hBe τ i)
  letI : Algebra c.F (X₀ TF.Y Z).functionField := φ₀.toAlgebra
  have hEig : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c z.1) (Bv z.1 z.2) :=
    fun z => (ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).1 (hBe z.1 z.2)
  have hblk : ∀ τ w, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c τ) w →
      ∃! a : Fin (Dw.mult τ) → (X₀ TF.Y Z).functionField, ∑ i, a i • Bv τ i = w := fun τ w hw => by
    have := f₀.basis τ _ (vec_tan hxK w) ((vec_eig_iff hxK _ w).2 ((ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).2 hw))
    rw [show f₀.v τ = fun i => vec TF.Y.t _ xcK (Bv τ i) from funext (hBv τ)] at this
    simpa only [comb_iff hxK, eq_comm] using this
  have hglob := GlobalTheory.FlagEmb.EigSpread.global_basis (GlobalTheory.FlagEmb.EigSpread.splits c) (fun z => Bv z.1 z.2) hEig hblk
  obtain ⟨hli, hsp⟩ := (GlobalTheory.FlagEmb.EigSpread.existsUnique_iff _).1 hglob
  let bK := Module.Basis.mk hli hsp.ge
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hdet : IsUnit (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    show LinearIndependent _ ((fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => Bv z.1 z.2) ∘ e.symm)
    exact hli.comp _ e.symm.injective
  obtain ⟨g, hg, s0, B₀, hB₀, hψB⟩ := spread_exact (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal
    (fun j => Bv (e.symm j).1 (e.symm j).2) hdet (fun j => Pr (e.symm j).1) (fun j => hPK _ _)
  let g' := h * g
  have hU : IsAffineOpen (TF.Y.X.basicOpen g') := hU₁.basicOpen g'
  have hU' : TF.Y.X.basicOpen g' ∈ TF.Y.X.affineOpens := hU
  have hUB : TF.Y.X.basicOpen g' ≤ barComp TF.Y Z := by
    rw [Scheme.basicOpen_mul]; exact inf_le_left.trans hhB
  have hpU : p ∈ TF.Y.X.basicOpen g' := by
    rw [Scheme.basicOpen_mul]
    refine ⟨hph, ?_⟩
    letI : Algebra Γ(TF.Y.X, U₁) (TF.Y.X.presheaf.stalk p) :=
      TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨p, hp₁⟩
    have := hU₁.isLocalization_stalk ⟨p, hp₁⟩
    show p ∈ TF.Y.X.basicOpen g
    rw [Scheme.mem_basicOpen _ _ _ hp₁]
    exact IsLocalization.map_units (TF.Y.X.presheaf.stalk p) (⟨g, hg⟩ : (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal.primeCompl)
  let ψ : Γ(TF.Y.X, U₁) →+* Γ(TF.Y.X, TF.Y.X.basicOpen g') :=
    (TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g')).op).hom
  have hψg' : IsUnit (ψ g') := TF.Y.X.toRingedSpace.isUnit_res_basicOpen g'
  have hψg : IsUnit (ψ g) := isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hψg')
  obtain ⟨hs0, hdet0, hQ0⟩ := hψB _ ψ hψg
  have hmap : spMap ψ ≫ hU₁.fromSpec = hU.fromSpec := hU₁.map_fromSpec hU _
  obtain ⟨xcU, hxU, hcU⟩ := vec_bc_of_chart C hx ψ (x' := LogKS.chart ⟨_, hU'⟩)
    (by rw [hx₁, Category.comp_id]; exact hmap.symm)
  let ρ : Γ(TF.Y.X, TF.Y.X.basicOpen g') →+* (X₀ TF.Y Z).functionField :=
    (TF.Y.X.presheaf.germ _ p hpU ≫ (barComp TF.Y Z).ι.stalkMap ξ).hom
  have hρψ : ρ.comp ψ = ρ₁ := by
    show ((TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g')).op ≫ TF.Y.X.presheaf.germ _ p hpU) ≫
      (barComp TF.Y Z).ι.stalkMap ξ).hom = _
    rw [TopCat.Presheaf.germ_res]
  have hψφ : ψ.comp φ₁ = cst TF.Y.s (TF.Y.X.basicOpen g') := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hmap, spMap_cst _ hU])
  let u := hs0.unit
  let cU : Fin n → Fin n → Γ(TF.Y.X, TF.Y.X.basicOpen g') := fun j => (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) • (ψ ∘ B₀ j)
  have hdetU : IsUnit (Matrix.of fun i j => cU j i).det := by
    have : (Matrix.of fun i j => cU j i) = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) • Matrix.of fun i j => ψ (B₀ j i) := by
      ext i j; rfl
    rw [this, Matrix.det_smul]
    exact (u⁻¹.isUnit.pow _).mul hdet0
  have hcUd : ∀ j, cU j = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) • (ψ ∘ B₀ j) := fun j => rfl
  clear_value cU
  refine ⟨⟨_, hU'⟩, hUB, ρ, n, e, fun j => vec TF.Y.t _ xcU (cU j), germ_pt (barComp TF.Y Z) ξ hU hpU,
    fun j => vec_tan hxU _, fun w' hw' => ?_, fun τ i => ?_, fun a k => ?_⟩
  · obtain ⟨cc, rfl⟩ := vec_exists hxU w' hw'
    simp only [comb_iff hxU]
    exact basis_of_det cU hdetU cc
  · have hBj := hB₀ (e ⟨τ, i⟩)
    rw [Equiv.symm_apply_apply] at hBj
    have hρu : ρ (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) * ρ₁ s0 = 1 := by
      rw [← hρψ, RingHom.comp_apply, ← map_mul]
      have : (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) * ψ s0 = 1 := by
        rw [← hs0.unit_spec]; exact Units.inv_mul u
      rw [this, map_one]
    have key : Bv τ i = ρ (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g')) • (ρ₁ ∘ B₀ (e ⟨τ, i⟩)) := by
      have h2 : ρ₁ ∘ B₀ (e ⟨τ, i⟩) = ρ₁ s0 • Bv τ i := hBj
      rw [h2, smul_smul, hρu, one_smul]
    show f₀.v τ i = spMap (dualMap ρ) ≫ vec TF.Y.t _ xcU (cU (e ⟨τ, i⟩))
    rw [hcUd, hBv τ i, key, vec_smul hxK, hcK, vec_smul hxU, hcU, ← hρψ]
    simp only [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]
    congr 2
    refine RingHom.ext fun w => ?_
    ext <;> simp [dualMap, epsMul]
  · have hfix : (Pr (e.symm k).1).map ψ *ᵥ cU k = cU k := by
      rw [hcUd, Matrix.mulVec_smul, hQ0 k]
    have hmem := (hPr ψ hxU hcU (e.symm k).1 (cU k)).1
    rw [hfix, hψφ] at hmem
    have heig : vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU k) ≫ (TF.Y.t.act.act a).left =
        spMap (epsMul (cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a))) ≫
          vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU k) := (vec_eig_iff hxU (fun a => cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a)) (cU k)).2 hmem a
    have hrow : (Matrix.diagonal fun j => constFn TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm j).1 a)) k =
        Pi.single k (cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a)) := by
      funext j
      by_cases hjk : j = k
      · subst hjk; simp [cst_apply]
      · simp [Matrix.diagonal_apply, Pi.single_apply, hjk, Ne.symm hjk]
    have hc : IsCombAtG TF.Y.t (LogKS.chart ⟨_, hU'⟩) (fun j => vec TF.Y.t _ xcU (cU j))
        (Pi.single k (cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a)))
        (vec TF.Y.t _ xcU (cst TF.Y.s (TF.Y.X.basicOpen g') (embK c (e.symm k).1 a) • cU k)) := by
      rw [comb_iff hxU, Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same]
    rw [vec_smul hxU, ← heig] at hc
    rw [hrow]
    exact hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkMapIdentityModMaximalOfFixedPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.FixStalk

theorem fixes_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] (b : X ≅ X) (x : X), X.fromSpecResidueField x ≫ b.hom = X.fromSpecResidueField x → ∃ st : X.presheaf.stalk x →+* X.presheaf.stalk x, (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom = spMap st ≫ X.fromSpecStalk x ∧ (∀ a, IsLocalRing.residue (X.presheaf.stalk x) (st a) = IsLocalRing.residue (X.presheaf.stalk x) a) ∧ ∀ a, GlobalTheory.functionFieldMap b.hom (algebraMap (X.presheaf.stalk x) X.functionField a) = algebraMap (X.presheaf.stalk x) X.functionField (st a) := by
  intro X _ b x hb
  have hx : b.hom x = x := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (X.residueField x)) := ⟨IsLocalRing.closedPoint _⟩
    have h2 := Scheme.fromSpecResidueField_apply x p
    have h3 : b.hom (X.fromSpecResidueField x p) = X.fromSpecResidueField x p := by
      rw [← Scheme.Hom.comp_apply, hb]
    rwa [h2] at h3
  have hs : b.hom x ⤳ x := by rw [hx]
  have hs' : x ⤳ b.hom x := by rw [hx]
  let st : X.presheaf.stalk x ⟶ X.presheaf.stalk x :=
    X.presheaf.stalkSpecializes hs ≫ b.hom.stalkMap x
  have h0 : X.fromSpecStalk x ≫ b.hom = Spec.map st ≫ X.fromSpecStalk x := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h1 : (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom =
      spMap st.hom ≫ X.fromSpecStalk x := by
    simpa only [spMap, CommRingCat.ofHom_hom] using h0
  haveI : IsIso (X.presheaf.stalkSpecializes hs) :=
    ⟨⟨X.presheaf.stalkSpecializes hs', by simp, by simp⟩⟩
  haveI : IsLocalHom st.hom := by
    show IsLocalHom (X.presheaf.stalkSpecializes hs ≫ b.hom.stalkMap x).hom
    rw [CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom (X.residue x).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  haveI : IsLocalHom (st ≫ X.residue x).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  refine ⟨st.hom, h1, ?_, ?_⟩
  · have e : Spec.map (X.residue x) ≫ X.fromSpecStalk x =
        Spec.map (st ≫ X.residue x) ≫ X.fromSpecStalk x := by
      rw [Spec.map_comp, Category.assoc, ← h0, ← Category.assoc]
      exact hb.symm
    have e2 := (SpecToEquivOfLocalRing X (X.residueField x)).symm.injective
      (a₁ := ⟨x, ⟨X.residue x, inferInstance⟩⟩) (a₂ := ⟨x, ⟨st ≫ X.residue x, inferInstance⟩⟩) e
    obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] at e3
    intro a
    exact (congr($e3 a)).symm
  · intro a
    have e4 : algebraMap (X.presheaf.stalk x) X.functionField a =
        algebraMap (X.presheaf.stalk (b.hom x)) X.functionField (X.presheaf.stalkSpecializes hs a) := by
      simp only [RingHom.algebraMap_toAlgebra]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    rw [e4, GlobalTheory.functionFieldMap_algebraMap]
    rfl

end GlobalTheory.FixStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportMinimisersLatticeAutomorphismStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transport_minimisers_latticeAutomorphism : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ) (μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∃ σ : Equiv.Perm (Fin 8 → Fin r → ZMod N), (∀ c u i, ((e.symm (μ (σ c) u) i : ℤ) : ZMod N) = c u i) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b') ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W (pull e.toLinearMap b') α) := by
  first | exact @GlobalTheory.relabel_minimisers | exact GlobalTheory.relabel_minimisers | (intros; apply GlobalTheory.relabel_minimisers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedFibreOfFramedComplexPoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_isVecs_of_eigBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
    {S : Scheme.{0}} {t : SAB H S} {t' : SAB H (Sp ℂ)} {x : Sp ℂ ⟶ S} (m : SABMap t' t x) {g n : ℕ}
    (u : HolUnif t'.G t'.PP.L g) (hd : ∀ v, IsTangent v → ∃! z, u.IsDiff z v)
    (hd' : ∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) {χ : 𝓞 E →+* ℂ} {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) : ∃ V : Fin n → Fin g → ℂ, IsVecs u m.φ v V ∧ LinearIndependent ℂ V := by
  choose v' hv' using fun i => FlatRow.exists_lift m.cart (v i)
  have ix := FlatDegreeCompare.Indep.of_eigBasis (((FlatRow.fibre_iff m.cart hv').2 m.act χ).2 hv)
  choose V hV using fun i => (hd _ (ix.1 i)).exists
  exact ⟨V, fun i => ⟨v' i, hv' i, hV i⟩, FlatDegreeCompare.ArchExists.linearIndependent_of_indep u hd' ix hV⟩

theorem exists_unif_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  intro E _ _ _ H D l Xo c U τ e y v w h
  rw [← Category.assoc]
  obtain ⟨t', ⟨n⟩⟩ := exists_sab (y ≫ toX Xo c) Xo.univ.t
  obtain ⟨T, hT, -⟩ := CM.exists_pat_of_obj E H D l _ _ _ _ (ModelCompare.objOfSABMap Xo.univ n)
  obtain rfl : T.t = t' := hT
  obtain ⟨rig, hrig⟩ := T.pol.rigid
  obtain ⟨u, Hm, κ, -, hA, -, hd, hd', -⟩ := thetaUnifAV_all T.pol rig hrig
  obtain ⟨V, hV, iV⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.1
  obtain ⟨W, hW, iW⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.2
  exact ⟨ModelCompare.objOfSABMap Xo.univ n, ModelCompare.objMapOfSABMap Xo.univ n, _, u, Hm, κ, V, W, hA, hV, hW,
    iV, iW⟩

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFourStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), 1 ≤ Dw.p + Dw.q → ∃ K : (Rul Xo c)ˣ, (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) := by
  first | exact @GlobalTheory.KeyFourth.exists_unit_secZ_keyRule | exact GlobalTheory.KeyFourth.exists_unit_secZ_keyRule | (intros; apply GlobalTheory.KeyFourth.exists_unit_secZ_keyRule <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandGlueFlatArtinianFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ferrand_glue_flat_artinian_fibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  first | exact @GlobalTheory.FerrandGlue.ferrand_glue_artinian | exact GlobalTheory.FerrandGlue.ferrand_glue_artinian | (intros; apply GlobalTheory.FerrandGlue.ferrand_glue_artinian <;> assumption)
end

