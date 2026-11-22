import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3640
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3638
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusQuasiInverseScaling
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RedQuot

open Coalgebra Bialgebra

theorem semi_app_mulP {p : ℕ} {R R₀ : Type} [CommRing R] [CommRing R₀] {σ : R →+* R₀}
    {G : PDivGroup p R} {G₀ : PDivGroup p R₀} (s : SemiHom σ G₀ G) (n : ℕ) (a : G.A n) :
    s.app (n + 1) (G.mulP n a) = G₀.mulP n (s.app n a) := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [mulP_res, semi_mulBy, ← s.res_app, mulP_res]

theorem cancel (p : ℕ) [Fact p.Prime] (R R₀ : Type) [CommRing R] [CommRing R₀] [Algebra R R₀]
    (G' G : PDivGroup p R) (G₀ : PDivGroup p R₀) (s : SemiHom (algebraMap R R₀) G₀ G)
    (s' : SemiHom (algebraMap R R₀) G₀ G') (ψ : G ⟶ G') (χ : G' ⟶ G) (m N d e : ℕ)
    (hNe : N + e = m + d)
    (h1 : ∀ n a, s.app n (ψ.app n a) = s'.app n (Hom.app (((p : ℤ_[p]) ^ m) • 𝟙 G') n a))
    (h2 : ψ ≫ χ = ((p : ℤ_[p]) ^ N) • 𝟙 G) (n : ℕ) (a : G.A n) :
    s'.app n (χ.app n (Hom.app (((p : ℤ_[p]) ^ e) • 𝟙 G) n a)) =
      s.app n (Hom.app (((p : ℤ_[p]) ^ d) • 𝟙 G) n a) := by
  rw [smul_pow_app, smul_pow_app]

  let X : ∀ n, G.A n → G₀.A n := fun n a => s'.app n (χ.app n (mulBy R (G.A n) (p ^ e) a))
  let Y : ∀ n, G.A n → G₀.A n := fun n a => s.app n (mulBy R (G.A n) (p ^ d) a)
  have hX : ∀ n z, X (n + 1) (G.mulP n z) = G₀.mulP n (X n z) := fun n z => by
    simp only [X]
    rw [← map_mulBy (G.mulP n), app_mulP, semi_app_mulP]
  have hY : ∀ n z, Y (n + 1) (G.mulP n z) = G₀.mulP n (Y n z) := fun n z => by
    simp only [Y]
    rw [← map_mulBy (G.mulP n), semi_app_mulP]

  have base : ∀ n b, X n (mulBy R (G.A n) (p ^ m) b) = Y n (mulBy R (G.A n) (p ^ m) b) := by
    intro n b
    have h := ident s s' ψ χ m N h1 h2 n (mulBy R (G.A n) (p ^ e) b)
    simp only [X, Y]
    rw [mulBy_mulBy, ← pow_add, hNe, pow_add, mul_comm, ← mulBy_mulBy] at h
    rw [h, ← semi_mulBy (s'.app n), ← map_mulBy (χ.app n), mulBy_mulBy, mulBy_mulBy, mul_comm]

  have step : ∀ k, (∀ n b, X n (mulBy R (G.A n) (p ^ (k + 1)) b) =
      Y n (mulBy R (G.A n) (p ^ (k + 1)) b)) →
      ∀ n b, X n (mulBy R (G.A n) (p ^ k) b) = Y n (mulBy R (G.A n) (p ^ k) b) := by
    intro k hk n b
    obtain ⟨c, rfl⟩ := G.res_surjective n b
    apply GlobalTheory.PDivGroup.Test.mulP_injective G₀ n
    have e1 : G.mulP n (mulBy R (G.A n) (p ^ k) (G.res n c)) =
        mulBy R (G.A (n + 1)) (p ^ (k + 1)) c := by
      rw [map_mulBy, mulP_res, mulBy_mulBy, ← pow_succ]
    rw [← hX, ← hY, e1, hk]
  have all : ∀ j, j ≤ m → ∀ n b, X n (mulBy R (G.A n) (p ^ (m - j)) b) =
      Y n (mulBy R (G.A n) (p ^ (m - j)) b) := by
    intro j
    induction j with
    | zero => intro _; simpa using base
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      rw [show m - j = (m - (j + 1)) + 1 by omega] at h
      exact step _ h
  have e0 : ∀ k (z : G.A k), mulBy R (G.A k) 1 z = z := fun k z => by
    simp [mulBy]
  have h0 := all m le_rfl n a
  simp only [X, Y, Nat.sub_self, pow_zero, e0] at h0
  exact h0

end GlobalTheory.RedQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsDeRhamPairingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_deRham_pairing : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ := by
  first | exact @GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj | exact GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj | (intros; apply GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummand
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDeform

theorem connectedSpace_sp_of_local (C : Type) [CommRing C] [IsLocalRing C] : ConnectedSpace (Sp C) := by
  have : PreconnectedSpace (PrimeSpectrum C) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint C) fun y _ ↦
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  have : ConnectedSpace (PrimeSpectrum C) := ⟨inferInstance⟩
  exact this

theorem exists_lift_oAct : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) → (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) → ∃ (A : Over (Sp C)) (_ : GrpObj A) (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), IsAbelianScheme A ∧ liftFil (divided₂ hsq) h = E ∧ ∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ E hE hFil hstab
  have GD := GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.T.abelianScheme_firstDeRham_structure GlobalTheory.T.print_abelianLifting
  have hκ := isDPNilpotent_squareZero hsq
  obtain ⟨A₁, _, i₁, h₁, hA₁⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A o₀.ab
  haveI := hA₁.smooth
  haveI := hA₁.geomConnected
  haveI := connectedSpace_sp_of_local C
  haveI : ConnectedSpace A₁.left := GeometricallyConnected.connectedSpace A₁.hom A₁.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected A₁.hom (Classical.arbitrary _)
  obtain ⟨A, _, i, h, hA, hgA, hE'⟩ :=
    GlobalTheory.RMDeform.exists_lift_abelian GD GlobalTheory.T.abelianScheme_firstDeRham_structure (divided₂ hsq) hκ π hπ rfl h₁ hA₁ hg E hE hFil
  haveI : IsCommMonObj A := hA.comm
  have HL := (GD C _ (divided₂ hsq) hκ C₀ π hπ rfl).2.2
  have key : ∀ c : D.O, ∃! f : A ⟶ A, IsMonHom f ∧ i ≫ f.left = (o₀.act.act c).left ≫ i := fun c ↦ by
    haveI := o₀.act.hom c
    exact HL g o₀.A A i h hA hgA g o₀.A A i h hA hgA (o₀.act.act c) (fun d hd ↦ by
      rw [hE'] at hd ⊢; exact hstab c d hd)
  choose f hf huniq using key
  refine ⟨A, inferInstance, i, h, ⟨f, fun c ↦ (hf c).1, ?_, ?_, ?_⟩, hA, hE', fun c ↦ (hf c).2.symm⟩
  · refine (huniq 1 (𝟙 _) ⟨inferInstance, ?_⟩).symm
    rw [o₀.act.one]
    simp
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x * y) (f y ≫ f x) ⟨inferInstance, ?_⟩).symm
    rw [o₀.act.mul, Over.comp_left, Over.comp_left, ← Category.assoc, (hf y).2, Category.assoc, (hf x).2,
      Category.assoc]
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x + y) (f x * f y) ⟨GlobalTheory.OActLift.isMonHom_mul_of_comm _ _, ?_⟩).symm
    rw [o₀.act.add]
    let j : Over.mk (o₀.A.hom ≫ spMap π) ⟶ A := Over.homMk i h.1.w
    have e := h.2 o₀.A (o₀.act.act x) (o₀.act.act y) (j ≫ f x) (j ≫ f y) (hf x).2 (hf y).2
    rw [← MonObj.comp_mul] at e
    exact e

end GlobalTheory.HTDeform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionIdentityOfHodgeSummand
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTLieCrys

theorem isLieImage_sum {C : Type} [CommRing C] {A : Over (Sp C)} [GrpObj A] :
    ∀ (n : ℕ) (H : Fin n → HdR A) (u : Fin n → (epsR C ⟶ A)), (∀ i, IsLieImage (H i) (u i)) →
      IsLieImage (∑ i, H i) (List.ofFn u).prod
  | 0, H, u, _ => by
      simpa using (isLieImage_one_iff (A := A)).2 (zero_mem _)
  | n + 1, H, u, hu => by
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
      exact (hu 0).add (isLieImage_sum n _ _ fun i => hu i.succ)

theorem comp_listProd {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {M X Y : 𝒞} [MonObj M]
    (f : X ⟶ Y) : ∀ (n : ℕ) (u : Fin n → (Y ⟶ M)),
      f ≫ (List.ofFn u).prod = (List.ofFn fun i => f ≫ u i).prod
  | 0, u => by simp
  | n + 1, u => by
      rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_listProd f n, List.ofFn_succ,
        List.prod_cons]

theorem one_left_eq {C : Type} [CommRing C] (A : Over (Sp C)) [GrpObj A] (x : Sp C ⟶ Sp C) (hx : x = 𝟙 (Sp C)) :
    (1 : Over.mk x ⟶ A).left = η[A].left := by
  have w := Over.w (toUnit (Over.mk x))
  rw [Hom.one_def, Over.comp_left]
  have e1 : (toUnit (Over.mk x)).left = x := by
    simpa using w
  rw [e1, hx]
  exact Category.id_comp _

def overId {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) : Over.mk q ⟶ Over.mk q' :=
  Over.homMk (𝟙 P) ((Category.id_comp q').trans h)

theorem overId_rfl {P S : Scheme.{0}} (q : P ⟶ S) : overId q q rfl = 𝟙 _ :=
  Over.OverMorphism.ext rfl

theorem overId_comp {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) (h' : q = q') :
    overId q' q h' ≫ overId q q' h = 𝟙 _ := by
  subst h
  rw [overId_rfl, Category.id_comp]

theorem overId_comp_left {T P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (a : T ⟶ P) (b : T ⟶ A.left) (e : a ≫ f.left = b) :
    a ≫ (overId q q' h ≫ f).left = b := by
  subst h
  rw [overId_rfl, Category.id_comp]
  exact e

theorem overId_scal {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (g : A ⟶ A) (a : P ⟶ P) (e : Over.mk q ⟶ Over.mk q) (he : e.left = a)
    (hf : (f ≫ g).left = a ≫ f.left) : (overId q q' h ≫ f) ≫ g = e ≫ overId q q' h ≫ f := by
  subst h
  subst he
  rw [overId_rfl, Category.id_comp]
  exact Over.OverMorphism.ext hf

theorem overId_scal_left {P S : Scheme.{0}} (q q' : P ⟶ S) (h : q' = q) {A : Over S}
    (f : Over.mk q' ⟶ A) (g : A ⟶ A) (a : P ⟶ P) (e : Over.mk q' ⟶ Over.mk q') (he : e.left = a)
    (hf : f ≫ g = e ≫ f) : ((overId q q' h ≫ f) ≫ g).left = a ≫ (overId q q' h ≫ f).left := by
  subst h
  subst he
  rw [overId_rfl, Category.id_comp, hf]
  rfl

theorem epsPt_hq (C : Type) [CommRing C] :
    spMap (algebraMap C (DualNumber C)) ≫ spMap (RingHom.id C) = spMap (algebraMap C (DualNumber C)) := by
  rw [show spMap (RingHom.id C) = 𝟙 (Sp C) from Spec.map_id _, Category.comp_id]

theorem lieAt_id_of_liftFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) h → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h) → GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hyp
  obtain ⟨g, hg⟩ := GlobalTheory.SemiAbelianDim.exists_relDim_of_isSemiAbelian C A
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA)
  have ADR := GlobalTheory.T.abelianScheme_firstDeRham_structure
  obtain ⟨LE1, LE2⟩ : LieExact A := (ADR.2.1 C A g hA hg).1
  have bij : Function.Bijective (crysToDR (divided₂ hsq) h) :=
    GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective ADR.2.2.2.1 hA hg (isDPNilpotent_squareZero hsq) hπ rfl h
  have eqv : ∀ (c : D.O) (d : Crys (divided₂ hsq) (spMap π) o₀.A),
      (haveI := o₀.act.hom c; crysToDR (divided₂ hsq) h (push (divided₂ hsq) (spMap π) (o₀.act.act c) d)) =
      (haveI := act.hom c; push (dp0 C) (𝟙 _) (act.act c) (crysToDR (divided₂ hsq) h d)) := by
    intro c d
    haveI := o₀.act.hom c
    haveI := act.hom c
    exact crysToDR_push (divided₂ hsq) h h (o₀.act.act c) (act.act c) (hact c).symm d
  have hq := epsPt_hq C
  have one_left := one_left_eq A (spMap (RingHom.id C)) (Spec.map_id _)
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  let v' : epsR C ⟶ A := overId _ _ hq ≫ v
  have tan' : IsTangent v' := overId_comp_left _ _ hq v _ _ (hv1.trans one_left)
  obtain ⟨H0, hH0⟩ := LE2 v' tan'
  obtain ⟨d, rfl⟩ := bij.2 H0
  have scal : v' ≫ act.act (algebraMap (𝓞 D.F) D.O D.ω) = GlobalTheory.GrpTangent.epsScale (tR b.ρ) ≫ v' :=
    overId_scal _ _ hq v _ _ _ (GlobalTheory.GrpTangent.epsScale_left _) hv2
  have hmem : (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) - tR b.ρ • d ∈
      liftFil (divided₂ hsq) h := by
    haveI := act.hom (algebraMap (𝓞 D.F) D.O D.ω)
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, eqv]
    have h1 := hH0.push (act.act (algebraMap (𝓞 D.F) D.O D.ω))
    rw [scal] at h1
    exact h1.sub_mem (hH0.smul (tR b.ρ))
  obtain ⟨w, hw, hsum⟩ := hyp d hmem
  have ex : ∀ j, ∃ u : epsR C ⟶ A, IsLieImage (crysToDR (divided₂ hsq) h (w j)) u :=
    fun j => (LE1 _).exists
  choose u hu using ex
  have hu_scal : ∀ j (c : 𝓞 D.F), u j ≫ act.act (algebraMap (𝓞 D.F) D.O c) =
      GlobalTheory.GrpTangent.epsScale (tR (b.t j c)) ≫ u j := by
    intro j c
    haveI := act.hom (algebraMap (𝓞 D.F) D.O c)
    have m := hw j c
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, eqv] at m
    have k2 := ((hu j).smul (tR (b.t j c))).add (isLieImage_one_iff.2 m)
    rw [_root_.mul_one, add_sub_cancel] at k2
    exact (LE1 _).unique ((hu j).push _) k2
  have hprod : v' = (List.ofFn u).prod := by
    rw [liftFil, Submodule.mem_comap, map_sub, map_sum] at hsum
    have k2 := (isLieImage_sum _ _ _ hu).add (isLieImage_one_iff.2 hsum)
    rw [_root_.mul_one, add_sub_cancel] at k2
    exact (LE1 _).unique hH0 k2
  refine ⟨fun j => overId _ _ hq.symm ≫ u j, fun j c => ⟨?_, ?_⟩, ?_⟩
  · exact overId_comp_left _ _ hq.symm (u j) _ _ (Eq.trans (hu j).1 one_left.symm)
  · exact overId_scal_left _ _ hq.symm (u j) _ _ _ (GlobalTheory.GrpTangent.epsScale_left _) (hu_scal j c)
  · have e1 : v = overId _ _ hq.symm ≫ v' := by
      show v = overId _ _ hq.symm ≫ (overId _ _ hq ≫ v)
      rw [← Category.assoc, overId_comp, Category.id_comp]
    rw [e1, hprod, comp_listProd]
end GlobalTheory.HTLieCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionModHodgeFiltrationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_mod_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  first | (exact @GlobalTheory.HTSummand.lie_mod_fil) | (exact GlobalTheory.HTSummand.lie_mod_fil) | (intros; apply GlobalTheory.HTSummand.lie_mod_fil  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPairingSkewHodgeLagrangianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → FiniteDimensional k (HdR o₀.A) ∧ 2 * Module.finrank k (Fil o₀.A) = Module.finrank k (HdR o₀.A) ∧ (∀ x y, φ x y = -φ y x) ∧ ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, φ x y = 0 := by
  first | (exact @GlobalTheory.UPel.HT.FormFacts.formFacts) | (exact GlobalTheory.UPel.HT.FormFacts.formFacts) | (intros; apply GlobalTheory.UPel.HT.FormFacts.formFacts  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ x, (∀ y, φ x y = 0) → x = 0 := by
  first | exact @GlobalTheory.HTPolPair.nondeg | exact GlobalTheory.HTPolPair.nondeg | (intros; apply GlobalTheory.HTPolPair.nondeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackKernelLocusIsClopen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem isMonHom_id_npow {Y : Scheme.{0}} (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  have h := Grp.Hom.hom_hom_zpow (G := Grp.mk A) (H := Grp.mk A) (𝟙 _) (n : ℤ)
  have h' : IsMonHom ((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ (n : ℤ)).hom.hom := inferInstance
  rw [h, zpow_natCast] at h'
  exact h'

theorem polKer_locus_clopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ PolKerAt o ψ' c t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, hc⟩ hB hq
  have hpY : IsUnit ((p : ℕ) : Γ(Y, ⊤)) := by
    have := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  have hn : IsUnit ((c ^ 3 : ℕ) : Γ(Y, ⊤)) := by
    rw [hc, ← pow_mul, Nat.cast_pow]
    exact hpY.pow _
  obtain ⟨C, _, Q, h, hC, -, -, hh, -, hT⟩ := GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom p D R b N Y s o B ψ' hB hq.2.1
  haveI := isMonHom_id_npow B c
  have hcomp : ∀ {T : Over Y} (x : T ⟶ B), x ≫ (𝟙 B) ^ c = x ^ c := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  obtain ⟨W₁, o₁, c₁, H₁, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => C) (fun _ => h) B ((𝟙 B) ^ c) hB
    (fun _ => hC) hB (fun _ => hh) inferInstance hn
  obtain ⟨W₂, o₂, c₂, H₂, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => B) (fun _ => (𝟙 B) ^ c) C h hB
    (fun _ => hB) hC (fun _ => inferInstance) hh hn
  refine ⟨W₁ ∩ W₂, o₁.inter o₂, c₁.inter c₂, fun Tb t => ?_⟩
  rw [Set.subset_inter_iff, H₁, H₂]
  constructor
  · rintro ⟨h₁, h₂⟩ T σ hσ x hx
    rw [hT]
    refine ⟨fun hx' => ?_, fun hx' => ?_⟩
    · rw [← hcomp]; exact h₁ T σ hσ x hx fun _ => hx'
    · exact h₂ T σ hσ x hx fun _ => by rw [hcomp]; exact hx'
  · intro H
    refine ⟨fun T σ hσ x hx hx' => ?_, fun T σ hσ x hx hx' => ?_⟩
    · rw [hcomp]; exact ((H T σ hσ x hx).1 ((hT T x).2 (hx' ())))
    · exact (hT T x).1 ((H T σ hσ x hx).2 (by rw [← hcomp]; exact hx' ()))

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationLiftDeterminesModFilStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A' : Over (Sp (DualNumber k))) [GrpObj A'] (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i), IsAbelianScheme A' → ∀ x ∈ Fil A₀, ∀ y y' : HdR A₀, IsFilLift h x y → (IsFilLift h x y' ↔ y' - y ∈ Fil A₀) := by
  first | exact @GlobalTheory.KSGraph.isFilLift_iff_sub_mem | exact GlobalTheory.KSGraph.isFilLift_iff_sub_mem | (intros; apply GlobalTheory.KSGraph.isFilLift_iff_sub_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroCrys

theorem isBC_trivSqZeroExt : ∀ (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (h2 : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0)
      (m : GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀))), m.IsBC := by
  intro k _ V _ _ _ _ A₀ _ hA h2 m
  have := hA.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.SerreDim.exists_dim_of_grpObj A₀
  have e : (𝟙 _ : Sp k ⟶ Sp k) = spMap (RingHom.id k) := (Cris.spMap_id k).symm
  have h := (GlobalTheory.CrysConn.isGrpPullback_refl A₀).congr e rfl
  have key : ∀ (t : Sp k ⟶ Sp k), t = spMap (RingHom.id k) →
      ∀ m : GrpMor (dp0 k) t A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)), m.IsBC := by
    rintro _ rfl m
    exact GlobalTheory.CrysConn.isBC_of_lift GlobalTheory.T.abelianScheme_firstDeRham_structure hA hg (isDPNilpotent_bot k) Function.surjective_id
      ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id) h (isDPNilpotent_squareZero _)
      (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl m (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  exact key _ e m

end GlobalTheory.SqZeroCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedBlowupAmpleDivisorCompactification
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.PoincTop

theorem poinSt : PoinSt := by
  intro g hg n hn hodd F Z z i hth OZ hOZ hamp φ hφ
  obtain ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ := hth
  obtain ⟨d, J, hd, hJ, hval⟩ :=
    GlobalTheory.T.exists_fanOrder_ideal_thetaCompactification g hg n hn hodd F Z z i ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ φ hφ
  haveI := hoi
  let W : Z.Opens := i.opensRange
  have hWset : (W : Set Z) = Set.range i := by simp [W]
  obtain ⟨S, π, BD, hbl, hpS, hBD, hiso, hdS⟩ :=
    GlobalTheory.T.exists_normalised_blowup_cyclotomicAway_projective n Z z hproj (GlobalTheory.IsNormalScheme.pred Z) J W (by rw [hWset]; exact hdense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : F.X ⟶ (π ⁻¹ᵁ W).toScheme := i.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : F.X ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = i := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range i := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  refine ⟨d, J, S, π, j, BD, hd, hJ, hval, hbl, hpS, inferInstance, ?_, hjπ, hrj.symm, hBD, ?_, ?_⟩
  · rw [hrj, ← hWset]; exact hdS
  · intro T ξ hξ
    obtain ⟨a, ha, hid⟩ := hval T (ξ ≫ π) (by rw [← Category.assoc, hξ, Category.assoc, hjπ])
    refine ⟨a, ha, ?_⟩
    rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]
    exact hid
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
    haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
    obtain ⟨T₀, hT⟩ := GlobalTheory.T.ample_twist_normalisedBlowup_noetherian_domain (cycAway n) Z S₀ S z J π₀ ν BD hproj hb hfin
      (by rw [hνπ]; exact hBD) OZ hamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h

end GlobalTheory.PoincTop
end
end

