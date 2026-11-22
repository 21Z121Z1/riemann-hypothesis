import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0028
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0038
import Development.EtaleCohomology.EtaleSheaves.LeafVanBStalkPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.EtaleCohomology.EtaleSheaves.Bundle0079
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0034

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CurveCohomologyKilledByFiniteCover
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.curve_cohomology_killed_by_finite_cover

inductive AffU {C : Scheme.{0}} : ℕ → C.Opens → Prop
  | one (U : C.Opens) : IsAffineOpen U → Nonempty U → AffU 0 U
  | succ {k : ℕ} {W : C.Opens} (U : C.Opens) : AffU k W → IsAffineOpen U → Nonempty U → AffU (k + 1) (W ⊔ U)

theorem AffU.pre {C C' : Scheme.{0}} (γ : C' ⟶ C) [IsFinite γ] [Surjective γ] {k : ℕ} {W : C.Opens}
    (h : AffU k W) : AffU k (γ ⁻¹ᵁ W) := by
  induction h with
  | one U hU hn =>
    refine AffU.one _ (hU.preimage γ) ?_
    obtain ⟨⟨x, hx⟩⟩ := hn
    obtain ⟨y, rfl⟩ := Surjective.surj (f := γ) x
    exact ⟨⟨y, hx⟩⟩
  | @succ k W U h hU hn ih =>
    have e : γ ⁻¹ᵁ (W ⊔ U) = γ ⁻¹ᵁ W ⊔ γ ⁻¹ᵁ U := by
      ext x
      simp
    rw [e]
    refine AffU.succ _ ih (hU.preimage γ) ?_
    obtain ⟨⟨x, hx⟩⟩ := hn
    obtain ⟨y, rfl⟩ := Surjective.surj (f := γ) x
    exact ⟨⟨y, hx⟩⟩

theorem AffU.inter {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) {k : ℕ} {W V : C.Opens}
    (h : AffU k W) (hV : IsAffineOpen V) (hn : Nonempty V) : AffU k (W ⊓ V) := by
  induction h with
  | one U hU hn' =>
    refine AffU.one _ (CurveCut.CoverPf.inf_affine c hc hU hV) ?_
    obtain ⟨⟨a, ha⟩⟩ := hn'
    obtain ⟨⟨b, hb⟩⟩ := hn
    obtain ⟨x, hx⟩ := CurveCut.CoverPf.inf_nonempty c hc (U := U) (V := V) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨x, hx⟩⟩
  | @succ k W U h hU hn' ih =>
    rw [inf_sup_right]
    refine AffU.succ _ ih (CurveCut.CoverPf.inf_affine c hc hU hV) ?_
    obtain ⟨⟨a, ha⟩⟩ := hn'
    obtain ⟨⟨b, hb⟩⟩ := hn
    obtain ⟨x, hx⟩ := CurveCut.CoverPf.inf_nonempty c hc (U := U) (V := V) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨x, hx⟩⟩

theorem exists_affU {C : Scheme.{0}} [CompactSpace C] [Nonempty C] : ∃ k, AffU k (⊤ : C.Opens) := by
  classical
  let U : C → C.Opens := fun x => (C.affineCover.f (C.affineCover.idx x)).opensRange
  have hU : ∀ x, IsAffineOpen (U x) := fun x => isAffineOpen_opensRange _
  have hx : ∀ x, x ∈ U x := fun x => C.affineCover.covers x
  have hne : ∀ x, Nonempty (U x) := fun x => ⟨⟨x, hx x⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set C))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  have key : ∀ s : Finset C, s.Nonempty → ∃ k, AffU k (s.sup U) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      refine ⟨0, ?_⟩
      rw [Finset.sup_singleton]
      exact AffU.one _ (hU a) (hne a)
    | cons a s ha hs ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [Finset.sup_cons, sup_comm]
      exact AffU.succ _ hk (hU a) (hne a)
  obtain ⟨x0⟩ := ‹Nonempty C›
  have htne : t.Nonempty := by
    have := ht (Set.mem_univ x0)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, _⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := key t htne
  have htop : t.sup U = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hy⟩ := this
    exact (Finset.le_sup (f := U) hi) hy
  exact ⟨k, htop ▸ hk⟩

theorem pl_eq_zero_of_iso (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (e : Y ⟶ X) [IsIso e] (m : ℤ)
    (x : Ht q (sch.obj X) m i) (h : pl q i e m x = 0) : x = 0 := by
  have h2 := pl_comp q i (inv e) e m x
  rw [h, map_zero, IsIso.inv_hom_id] at h2
  simpa [pl, pull_id] using h2

theorem AffU.nonempty {C : Scheme.{0}} {k : ℕ} {W : C.Opens} (h : AffU k W) : Nonempty W := by
  induction h with
  | one U _ hn => exact hn
  | @succ k W U h hU hn ih =>
    obtain ⟨⟨x, hx⟩⟩ := ih
    exact ⟨⟨x, (le_sup_left : W ≤ W ⊔ U) hx⟩⟩

theorem res_sq {T S : Scheme.{0}} (f : T ⟶ S) {A B : S.Opens} (h : A ≤ B) (h' : f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B) :
    T.homOfLE h' ≫ (f ∣_ B) = (f ∣_ A) ≫ S.homOfLE h := by
  rw [← cancel_mono B.ι]
  simp [morphismRestrict_ι]

theorem pl_res_sq (q : ℕ) (i m : ℤ) {T S : Scheme.{0}} (f : T ⟶ S) {A B : S.Opens} (h : A ≤ B) (h' : f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B)
    (x : Ht q (sch.obj B.toScheme) m i) :
    pl q i (T.homOfLE h') m (pl q i (f ∣_ B) m x) = pl q i (f ∣_ A) m (pl q i (S.homOfLE h) m x) := by
  rw [← pl_comp, ← pl_comp, res_sq f h h']

theorem killAff (hy : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω))
    {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) (U : C.Opens) (hU : IsAffineOpen U) (hn : Nonempty U)
    (m i : ℤ) (hm : 0 < m) (x : Ht q (sch.obj U.toScheme) m i) :
    ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧ pl q i (γ ∣_ U) m x = 0 := by
  haveI : IsIntegral C := hc.1
  haveI : Nonempty U := hn
  haveI := functionField_isFractionRing_of_isAffineOpen C U hU
  have hqU : IsUnit (q : Γ(C, U)) := by
    have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ c.appLE ⊤ U (by simp)).hom
    simpa using this
  set x0 : Ht q (sp Γ(C, U)) m i := pl q i hU.isoSpec.inv m x with hx0
  obtain ⟨F, _, _, _, hST, hFD, hF⟩ := UpperTheory.exists_finite_ext_pullback_integralClosure_eq_zero hy q Γ(C, U) C.functionField hqU m i hm x0
  obtain ⟨C', γ, hγc, hγs, hγf, hγ⟩ := UpperTheory.exists_finite_surjective_curve_cover_of_functionField_extension Ω c hc hc.1 F
  obtain ⟨e, he⟩ := hγ U hU hn inferInstance hST
  refine ⟨C', γ, hγc, hγs, hγf, ?_⟩
  have hx : x = pl q i hU.isoSpec.hom m x0 := by
    rw [hx0, ← pl_comp, Iso.hom_inv_id]
    simp [pl, pull_id]
  have h0 : pl q i (Spec.map (CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)))) m x0 = 0 := hF
  rw [hx, ← pl_comp, he, pl_comp, h0, map_zero]

set_option maxHeartbeats 1000000 in
theorem kill (hy : Hyps) (hH0 : H0TwistOverClosedField) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω)) (k : ℕ) :
    ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ W : C.Opens, AffU k W → ∀ m i : ℤ, 0 < m →
    ∀ x : Ht q (sch.obj W.toScheme) m i,
    ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧ pl q i (γ ∣_ W) m x = 0 := by
  have pm : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) {A B : Y.Opens}, A ≤ B → f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B :=
    fun f _ _ h _ hy => h hy
  induction k with
  | zero =>
    intro C c hc W hW m i hm x
    cases hW with
    | one _ hU hn => exact killAff hy q Ω hq c hc _ hU hn m i hm x
  | succ k ih =>
    intro C c hc W' hW' m i hm x
    cases hW' with
    | @succ _ W U hW hU hn =>
      obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
      obtain ⟨C1, γ1, hc1, hs1, hf1, h1⟩ := ih c hc W hW (n + 1) i hm
        (pl q i (C.homOfLE (le_sup_left : W ≤ W ⊔ U)) (n + 1) x)
      haveI := hs1
      haveI := hf1
      obtain ⟨C2, γ2, hc2, hs2, hf2, h2⟩ := killAff hy q Ω hq (γ1 ≫ c) hc1 (γ1 ⁻¹ᵁ U) (hU.preimage γ1)
        (AffU.nonempty (AffU.pre γ1 (AffU.one U hU hn))) (n + 1) i hm
        (pl q i (C1.homOfLE (pm γ1 (le_sup_right : U ≤ W ⊔ U))) (n + 1) (pl q i (γ1 ∣_ (W ⊔ U)) (n + 1) x))
      haveI := hs2
      haveI := hf2
      have hcγ : IsCurve ((γ2 ≫ γ1) ≫ c) := by simpa only [Category.assoc] using hc2
      have hW2 : AffU k ((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U) := AffU.pre (γ2 ≫ γ1) (AffU.inter c hc hW hU hn)
      have hA : pl q i (C2.homOfLE (pm (γ2 ≫ γ1) (le_sup_left : W ≤ W ⊔ U))) (n + 1)
          (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 := by
        have e2 := pl_res_sq q i (n + 1) (γ2 ≫ γ1) (le_sup_left : W ≤ W ⊔ U) (pm _ le_sup_left) x
        have e3 := pl_comp q i (γ2 ∣_ (γ1 ⁻¹ᵁ W)) (γ1 ∣_ W) (n + 1)
          (pl q i (C.homOfLE (le_sup_left : W ≤ W ⊔ U)) (n + 1) x)
        rw [h1, map_zero, ← morphismRestrict_comp] at e3
        exact e2.trans e3
      have hB : pl q i (C2.homOfLE (pm (γ2 ≫ γ1) (le_sup_right : U ≤ W ⊔ U))) (n + 1)
          (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 := by
        have e1 := pl_res_sq q i (n + 1) γ2 (pm γ1 (le_sup_right : U ≤ W ⊔ U)) (pm γ2 (pm γ1 le_sup_right))
          (pl q i (γ1 ∣_ (W ⊔ U)) (n + 1) x)
        rw [h2, ← pl_comp q i (γ2 ∣_ (γ1 ⁻¹ᵁ (W ⊔ U))) (γ1 ∣_ (W ⊔ U)), ← morphismRestrict_comp] at e1
        exact e1
      obtain ⟨y, hyv⟩ := UpperTheory.exists_mayerVietoris_preimage_of_restrictions_vanish (ZMod q) (tw q i) ((γ2 ≫ γ1) ⁻¹ᵁ W) ((γ2 ≫ γ1) ⁻¹ᵁ U) n
        (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) hA hB
      have fin : ∀ (C3 : Scheme.{0}) (f : C3 ⟶ C2), IsCurve (f ≫ (γ2 ≫ γ1) ≫ c) → Surjective f → IsFinite f →
          pl q i (f ∣_ ((γ2 ≫ γ1) ⁻¹ᵁ W ⊔ (γ2 ≫ γ1) ⁻¹ᵁ U)) (n + 1)
            (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 →
          ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧
            pl q i (γ ∣_ (W ⊔ U)) (n + 1) x = 0 := by
        intro C3 f hc3 hs3 hf3 h3
        haveI := hs3
        haveI := hf3
        refine ⟨C3, f ≫ γ2 ≫ γ1, by simpa only [Category.assoc] using hc3, inferInstance, inferInstance, ?_⟩
        rw [morphismRestrict_comp f (γ2 ≫ γ1) (W ⊔ U)]
        exact (pl_comp q i (f ∣_ ((γ2 ≫ γ1) ⁻¹ᵁ (W ⊔ U))) ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x).trans h3
      rcases (show (0 : ℤ) < n ∨ n = 0 by omega) with hn0 | rfl
      · obtain ⟨C3, f, hc3, hs3, hf3, h3⟩ := ih ((γ2 ≫ γ1) ≫ c) hcγ _ hW2 n i hn0 y
        refine fin C3 f (by simpa only [Category.assoc] using hc3) hs3 hf3 ?_
        exact hyv f 0 0 (by rw [map_zero, map_zero, sub_zero]; exact h3)
      · haveI : IsIntegral C2 := hc2.1
        haveI : Nonempty (((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U : C2.Opens)) := AffU.nonempty hW2
        obtain ⟨z, hz⟩ := ((hH0 hy q Ω hq i).2
          (X := ((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U : C2.Opens).toScheme)
          (Scheme.Opens.ι _ ≫ (γ2 ≫ γ1) ≫ c)).2 y
        refine fin C2 (𝟙 C2) (by rw [Category.id_comp]; exact hcγ) inferInstance inferInstance ?_
        refine hyv (𝟙 C2) (pl q i ((𝟙 C2 ⁻¹ᵁ ((γ2 ≫ γ1) ⁻¹ᵁ W)).ι ≫ (γ2 ≫ γ1) ≫ c) 0 z) 0 ?_
        rw [map_zero, sub_zero, ← hz]
        change pl q i _ 0 (pl q i _ 0 z) = pl q i _ 0 (pl q i _ 0 z)
        rw [← pl_comp, ← pl_comp, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, Category.id_comp]

end UpperTheory.curve_cohomology_killed_by_finite_cover

theorem UpperTheory.Cb.curve_cohomology_killed_by_finite_cover :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.LeafKillCut.LeafOne := by
  intro hH0 hy q _ Ω _ _ hq C c hc m i hm x
  have hI := hc.1
  have hP := hc.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨k, hk⟩ := UpperTheory.curve_cohomology_killed_by_finite_cover.exists_affU (C := C)
  obtain ⟨C', γ, h1, h2, h3, h4⟩ := UpperTheory.curve_cohomology_killed_by_finite_cover.kill hy hH0 q Ω hq k c hc ⊤ hk m i hm (pl q i (⊤ : C.Opens).ι m x)
  refine ⟨C', γ, h1, h2, ?_⟩
  rw [← pl_comp] at h4
  rw [morphismRestrict_ι, pl_comp] at h4
  have hι : ∀ V : C'.Opens, V = ⊤ → IsIso V.ι := by
    rintro _ rfl
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI := hι (γ ⁻¹ᵁ (⊤ : C.Opens)) rfl
  exact UpperTheory.curve_cohomology_killed_by_finite_cover.pl_eq_zero_of_iso q i ((γ ⁻¹ᵁ (⊤ : C.Opens)).ι) m _ h4

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleStalkCohomologyStrictHenselianContinuity
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVanBPf LateralTheory.E.LeafVanBStalkPf

namespace UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity.SlopeTestRemainingChoices

section DiagramChase₂
variable (R : Type) [CommRing R]

private abbrev bd {Z E : Spc} (f : Z ⟶ E) (F : Shv R) (n : ℤ) : H R Z F n →+ Hrel R f F (n + 1) :=
  HK.pre R (mappingCone.fst ((chains R).map f)) F n (n + 1) (add_comm 1 n)

private theorem bd_nat {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (F : Shv R) (n : ℤ) (b : H R U F n) :
    rpull R f f' u e comm F (n + 1) (bd R f F n b) = bd R f' F n (pull R u F n b) := by
  obtain ⟨b, rfl⟩ := b.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.ofHom_coe, Cocycle.mk_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, rmap, LateralTheory.E.GlueRelPfNat.map_fst,
    Cochain.comp_assoc_of_second_is_zero_cochain]

private theorem bd_pull {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (a : H R E F n) :
    bd R f F n (pull R f F n a) = 0 :=
  (coneSeq_exact R ((chains R).map f) (res R F) n).2.1.apply_apply_eq_zero a

private theorem exists_pull {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (b : H R U F n)
    (h : bd R f F n b = 0) : ∃ a : H R E F n, pull R f F n a = b :=
  ((coneSeq_exact R ((chains R).map f) (res R F) n).2.1 b).1 h

private theorem exists_bd {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (y : Hrel R f F (n + 1))
    (h : fgt R f F (n + 1) y = 0) : ∃ b : H R U F n, bd R f F n b = y :=
  ((coneSeq_exact R ((chains R).map f) (res R F) n).2.2 y).1 h

private theorem relCont {J : Type} [SmallCategory J] [IsFiltered J] (F : Shv R) {Ei Zi : Spc} (fi : Zi ⟶ Ei)
    (E Z : J → Spc) (f : ∀ j, Z j ⟶ E j)
    (eM : ∀ {j j' : J}, (j ⟶ j') → (E j' ⟶ E j)) (zM : ∀ {j j' : J}, (j ⟶ j') → (Z j' ⟶ Z j))
    (sq : ∀ {j j' : J} (g : j ⟶ j'), f j' ≫ eM g = zM g ≫ f j)
    (fe : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j''), eM (g ≫ g') = eM g' ≫ eM g)
    (fz : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j''), zM (g ≫ g') = zM g' ≫ zM g)
    (te : ∀ j, Ei ⟶ E j) (tz : ∀ j, Zi ⟶ Z j) (sqt : ∀ j, fi ≫ te j = tz j ≫ f j)
    (ce : ∀ {j j' : J} (g : j ⟶ j'), te j' ≫ eM g = te j)
    (cz : ∀ {j j' : J} (g : j ⟶ j'), tz j' ≫ zM g = tz j)
    (CEi : ∀ (n : ℤ) (j : J) (y : H R (E j) F n), pull R (te j) F n y = 0 →
      ∃ (j' : J) (g : j ⟶ j'), pull R (eM g) F n y = 0)
    (CEs : ∀ (n : ℤ) (x : H R Ei F n), ∃ (j : J) (y : H R (E j) F n), pull R (te j) F n y = x)
    (CZi : ∀ (n : ℤ) (j : J) (y : H R (Z j) F n), pull R (tz j) F n y = 0 →
      ∃ (j' : J) (g : j ⟶ j'), pull R (zM g) F n y = 0)
    (n : ℤ) (j : J) (c : Hrel R (f j) F (n + 1))
    (hc : rpull R (f j) fi (tz j) (te j) (sqt j) F (n + 1) c = 0) :
    ∃ (j' : J) (g : j ⟶ j'), rpull R (f j) (f j') (zM g) (eM g) (sq g) F (n + 1) c = 0 := by

  have cmp1 : ∀ {j j' : J} (g : j ⟶ j') (y : Hrel R (f j) F (n + 1)),
      rpull R (f j') fi (tz j') (te j') (sqt j') F (n + 1) (rpull R (f j) (f j') (zM g) (eM g) (sq g) F (n + 1) y) =
        rpull R (f j) fi (tz j) (te j) (sqt j) F (n + 1) y := by
    intro j j' g y
    have c3 : fi ≫ (te j' ≫ eM g) = (tz j' ≫ zM g) ≫ f j := by
      rw [ce, cz, sqt]
    rw [← rpull_comp R (f j) (f j') fi (zM g) (eM g) (tz j') (te j') (sq g) (sqt j') c3]
    exact congrFun (congrArg _ rfl) y |>.trans (by
      rw [rpull_congr R (f j) fi (cz g) (ce g) c3 (sqt j)])
  have cmp2 : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j'') (y : Hrel R (f j) F (n + 1)),
      rpull R (f j') (f j'') (zM g') (eM g') (sq g') F (n + 1) (rpull R (f j) (f j') (zM g) (eM g) (sq g) F (n + 1) y) =
        rpull R (f j) (f j'') (zM (g ≫ g')) (eM (g ≫ g')) (sq (g ≫ g')) F (n + 1) y := by
    intro j j' j'' g g' y
    have c3 : f j'' ≫ (eM g' ≫ eM g) = (zM g' ≫ zM g) ≫ f j := by
      rw [← fe, ← fz, sq]
    rw [← rpull_comp R (f j) (f j') (f j'') (zM g) (eM g) (zM g') (eM g') (sq g) (sq g') c3]
    rw [rpull_congr R (f j) (f j'') (fz g g').symm (fe g g').symm c3 (sq (g ≫ g'))]

  have h1 : pull R (te j) F (n + 1) (fgt R (f j) F (n + 1) c) = 0 := by
    rw [← relNat R F (f j) fi (tz j) (te j) (sqt j) (n + 1) c, hc, map_zero]
  obtain ⟨j1, g1, h2⟩ := CEi (n + 1) j _ h1
  set c1 := rpull R (f j) (f j1) (zM g1) (eM g1) (sq g1) F (n + 1) c with hc1
  have h3 : fgt R (f j1) F (n + 1) c1 = 0 := by
    rw [hc1, relNat R F (f j) (f j1) (zM g1) (eM g1) (sq g1) (n + 1) c, h2]
  obtain ⟨b, hb⟩ := exists_bd R (f j1) F n c1 h3

  have h4 : bd R fi F n (pull R (tz j1) F n b) = 0 := by
    rw [← bd_nat R (f j1) fi (tz j1) (te j1) (sqt j1) F n b, hb, hc1, cmp1, hc]
  obtain ⟨ai, hai⟩ := exists_pull R fi F n _ h4
  obtain ⟨j2, a2, ha2⟩ := CEs n ai

  let j3 := IsFiltered.max j1 j2
  let g3 : j1 ⟶ j3 := IsFiltered.leftToMax j1 j2
  let g3' : j2 ⟶ j3 := IsFiltered.rightToMax j1 j2
  set a3 := pull R (eM g3') F n a2 with ha3
  set d := pull R (zM g3) F n b - pull R (f j3) F n a3 with hd
  have h5 : pull R (tz j3) F n d = 0 := by
    rw [hd, map_sub, ← pull_comp, ← pull_comp, cz, ← sqt, pull_comp, ha3, ← pull_comp R (te j3), ce, ha2, hai,
      sub_self]
  obtain ⟨j4, g4, h6⟩ := CZi n j3 d h5
  refine ⟨j4, g1 ≫ g3 ≫ g4, ?_⟩
  rw [← cmp2 g1 (g3 ≫ g4), ← hc1, ← hb, bd_nat, fz, pull_comp]
  have h7 : pull R (zM g4) F n (pull R (zM g3) F n b) = pull R (zM g4) F n (pull R (f j3) F n a3) := by
    rw [hd, map_sub, sub_eq_zero] at h6
    exact h6
  rw [h7, ← pull_comp, ← sq g4, pull_comp, bd_pull]

end DiagramChase₂

section Transport

private theorem injT (hB : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (c : Cocone D) (hc : IsColimit c) (X : J → Scheme.{0}) (ex : ∀ j, X j ≅ Spec (D.obj j))
    (tr : ∀ {j j' : J}, (j ⟶ j') → (X j' ⟶ X j))
    (htr : ∀ {j j' : J} (g : j ⟶ j'), (ex j').inv ≫ tr g ≫ (ex j).hom = Spec.map (D.map g))
    (tl : ∀ j, Spec c.pt ⟶ X j) (htl : ∀ j, tl j ≫ (ex j).hom = Spec.map (c.ι.app j))
    (hu : ∀ j, IsUnit (q : D.obj j)) (n : ℤ) (j : J) (y : Ht q (sch.obj (X j)) n i)
    (hy : pl q i (tl j) n y = 0) : ∃ (j' : J) (g : j ⟶ j'), pl q i (tr g) n y = 0 := by
  have h0 : pl q i (Spec.map (c.ι.app j)) n (pl q i (ex j).inv n y) = 0 := by
    rw [← pl_comp, ← htl, Category.assoc, Iso.hom_inv_id, Category.comp_id, hy]
  obtain ⟨j', g, h1⟩ := (hB q D c hc n i).2 j (pl q i (ex j).inv n y) (hu j) h0
  refine ⟨j', g, ?_⟩
  have h2 : pl q i (Spec.map (D.map g)) n (pl q i (ex j).inv n y) = 0 := h1
  rw [← pl_comp, ← htr, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id, pl_comp] at h2
  have h3 := congrArg (pl q i (ex j').hom n) h2
  rw [← pl_comp, Iso.hom_inv_id, map_zero] at h3
  simpa [pl, pull_id] using h3

private theorem surjT (hB : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (c : Cocone D) (hc : IsColimit c) (X : J → Scheme.{0}) (ex : ∀ j, X j ≅ Spec (D.obj j))
    (tl : ∀ j, Spec c.pt ⟶ X j) (htl : ∀ j, tl j ≫ (ex j).hom = Spec.map (c.ι.app j))
    (hu : IsUnit (q : c.pt)) (n : ℤ) (x : Ht q (sch.obj (Spec c.pt)) n i) :
    ∃ (j : J) (y : Ht q (sch.obj (X j)) n i), pl q i (tl j) n y = x := by
  obtain ⟨j, y, h⟩ := (hB q D c hc n i).1 x hu
  refine ⟨j, pl q i (ex j).hom n y, ?_⟩
  rw [← pl_comp, htl]
  exact h

private theorem unit_of {k : Type} [Field k] {q : ℕ} (hq : IsUnit (q : k)) (A : CommRingCat.{0})
    (f : Spec A ⟶ Sp k) : IsUnit (q : A) := by
  have g := Spec.preimage f
  simpa using hq.map g.hom

private theorem tr_comp_left {B : Scheme.{0}} {U : B.Etale} {x : U.left} (S : SHSys U x) {j j' j'' : S.J}
    (g : j ⟶ j') (g' : j' ⟶ j'') : (S.tr (g ≫ g')).left = (S.tr g').left ≫ (S.tr g).left := by
  have h := S.tr_spec (g ≫ g')
  rw [Functor.map_comp, Spec.map_comp, ← S.tr_spec g, ← S.tr_spec g'] at h
  have h2 : (S.e j'').inv ≫ (S.tr (g ≫ g')).left ≫ (S.e j).hom =
      (S.e j'').inv ≫ ((S.tr g').left ≫ (S.tr g).left) ≫ (S.e j).hom := by
    rw [h]; simp
  rw [cancel_epi, cancel_mono] at h2
  exact h2

end Transport

theorem main : LateralTheory.E.LeafVanBStalkPf.LeafSHCont := by
  intro hy q _ k _ hq i B W s ι _ U m c x S h0
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by ring⟩
  have hB : B1 := hy.2.2.2.2.2.2.2.2.2.2.1

  let tl : ∀ j, Spec S.c.pt ⟶ (S.V j).left := fun j => Spec.map (S.c.ι.app j) ≫ (S.e j).inv
  have htl : ∀ j, tl j ≫ (S.a j).left = S.t := fun j => by simp [tl, S.ht j]
  have htv : ∀ j, tl j ≫ (S.V j).hom = S.t ≫ U.hom := fun j => by
    have hw : (S.a j).left ≫ U.hom = (S.V j).hom := by simpa using (S.a j).w
    rw [← hw, ← Category.assoc, htl]
  let zl : ∀ j, pullback (S.t ≫ U.hom) ι ⟶ pullback (S.V j).hom ι := fun j =>
    pullback.map _ _ _ _ (tl j) (𝟙 W) (𝟙 B) (by simp [htv j]) (by simp)
  have hz1 : ∀ j, zl j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (S.c.ι.app j) ≫ (S.e j).inv :=
    fun j => pullback.lift_fst _ _ _
  have hz2 : ∀ j, zl j ≫ pullback.snd _ _ = pullback.snd _ _ := fun j =>
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  obtain ⟨D', c', hc', ez, ei, hD1, hD2⟩ := UpperTheory.exists_closedFiber_colimit_presentation ι U x S zl hz1 hz2

  have huD : ∀ j, IsUnit (q : S.D.obj j) := fun j => unit_of hq _ ((S.e j).inv ≫ (S.V j).hom ≫ s)
  have huD' : ∀ j, IsUnit (q : D'.obj j) := fun j =>
    unit_of hq _ ((ez j).inv ≫ pullback.snd _ _ ≫ ι ≫ s)
  have huc : IsUnit (q : S.c.pt) := unit_of hq _ (S.t ≫ U.hom ≫ s)
  have c3 : ∀ {j j' : S.J} (g : j ⟶ j'), prB ι (S.V j') ≫ (S.tr g).left = resBW ι (S.tr g) ≫ prB ι (S.V j) :=
    fun g => (pullback.lift_fst _ _ _).symm
  have c4 : ∀ j, pullback.fst (S.t ≫ U.hom) ι ≫ tl j = zl j ≫ prB ι (S.V j) := fun j => (pullback.lift_fst _ _ _).symm
  have ct : ∀ {j j' : S.J} (g : j ⟶ j'), tl j' ≫ (S.tr g).left = tl j := fun {j j'} g => by
    have h1 : Spec.map (S.c.ι.app j) = Spec.map (S.c.ι.app j') ≫ Spec.map (S.D.map g) := by
      rw [← Spec.map_comp, S.c.w g]
    simp only [tl]
    rw [h1, ← S.tr_spec g]
    simp
  obtain ⟨j0⟩ : Nonempty S.J := IsFiltered.nonempty
  have key := relCont (ZMod q) (tw q i) (sch.map (pullback.fst (S.t ≫ U.hom) ι))
    (fun j => sch.obj (S.V j).left) (fun j => sch.obj (pullback (S.V j).hom ι))
    (fun j => sch.map (prB ι (S.V j)))
    (fun g => sch.map (S.tr g).left) (fun g => sch.map (resBW ι (S.tr g)))
    (fun g => by rw [← Functor.map_comp, ← Functor.map_comp, c3 g])
    (fun g g' => by rw [tr_comp_left S g g', Functor.map_comp])
    (fun g g' => by
      rw [← Functor.map_comp]
      congr 1
      apply pullback.hom_ext <;> simp only [resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, tr_comp_left S g g'])
    (fun j => sch.map (tl j)) (fun j => sch.map (zl j))
    (fun j => by rw [← Functor.map_comp, ← Functor.map_comp, c4 j])
    (fun g => by rw [← Functor.map_comp, ct g])
    (fun {j j'} g => by
      rw [← Functor.map_comp]
      congr 1
      apply pullback.hom_ext <;> simp only [zl, resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, ct g])
    (fun n j y h => injT hB q i S.D S.c S.hc (fun j => (S.V j).left) S.e (fun g => (S.tr g).left) (fun g => S.tr_spec g)
      tl (fun j => by simp [tl]) huD n j y h)
    (fun n x => surjT hB q i S.D S.c S.hc (fun j => (S.V j).left) S.e tl (fun j => by simp [tl]) huc n x)
    (fun n j y h => by
      refine injT hB q i D' c' hc' (fun j => pullback (S.V j).hom ι) ez (fun g => resBW ι (S.tr g)) hD1
        (fun j => ei.inv ≫ zl j) (fun j => by simpa using hD2 j) huD' n j y ?_
      rw [pl_comp]
      exact (congrArg _ h).trans (map_zero _))
    n j0 (rB q i ι (S.a j0) (n + 1) c) ?_
  · obtain ⟨j', g, h⟩ := key
    refine ⟨j', ?_⟩
    rw [← S.tr_a g, rB_comp]
    exact h
  · have cu : sch.map (zl j0) ≫ sch.map (resBW ι (S.a j0)) = sch.map (pullback.map (S.t ≫ U.hom) ι U.hom ι S.t (𝟙 W) (𝟙 B)
        (by simp) (by simp)) := by
      rw [← Functor.map_comp]
      congr 1
      apply pullback.hom_ext <;> simp only [zl, resBW, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, htl j0]
    have ce0 : sch.map (tl j0) ≫ sch.map (S.a j0).left = sch.map S.t := by
      rw [← Functor.map_comp, htl]
    have c3' : sch.map (pullback.fst (S.t ≫ U.hom) ι) ≫ (sch.map (tl j0) ≫ sch.map (S.a j0).left) =
        (sch.map (zl j0) ≫ sch.map (resBW ι (S.a j0))) ≫ sch.map (prB ι U) := by
      rw [cu, ce0, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact (pullback.lift_fst _ _ _).symm
    refine (rpull_comp (ZMod q) (sch.map (prB ι U)) (sch.map (prB ι (S.V j0))) (sch.map (pullback.fst _ ι))
      (sch.map (resBW ι (S.a j0))) (sch.map (S.a j0).left) (sch.map (zl j0)) (sch.map (tl j0)) _ _ c3' (tw q i) (n + 1) c).symm.trans ?_
    exact (DFunLike.congr_fun (rpull_congr (ZMod q) _ _ cu ce0 c3' _ (tw q i) (n + 1)) c).trans h0

end UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity.SlopeTestRemainingChoices

theorem UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity :
    LateralTheory.E.LeafVanBStalkPf.LeafSHCont :=
  UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity.SlopeTestRemainingChoices.main
end
end

