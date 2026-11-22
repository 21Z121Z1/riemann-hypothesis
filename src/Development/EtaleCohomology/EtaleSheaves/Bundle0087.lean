import Development.EtaleCohomology.EtaleSheaves.Bundle0084
import Development.EtaleCohomology.EtaleSheaves.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafStalkOfAlgOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut TensorProduct

namespace LateralTheory.E.StalkOfAlgebra

theorem stalk_of_smoothAt {R A : CommRingCat.{0}} (φ : R ⟶ A) (p : PrimeSpectrum A)
    (h : letI := φ.hom.toAlgebra; Algebra.IsSmoothAt R p.asIdeal) :
    ((Spec.map φ).stalkMap p).hom.FormallySmooth := by
  letI := φ.hom.toAlgebra
  let P := (p.comap φ.hom).asIdeal
  haveI : p.asIdeal.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P p.asIdeal
  rw [RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ p)]
  have : Algebra.FormallySmooth (Localization.AtPrime P) (Localization.AtPrime p.asIdeal) :=
    (Algebra.FormallySmooth.iff_restrictScalars (R := R) (A := Localization.AtPrime P)).mp h
  exact this

theorem core (hA : LateralTheory.E.SpreadingOutSmoothness.LeafAlgDescend) (k : Type) [Field k] (Ω : Type) [Field Ω]
    [Algebra k Ω] (R : Subalgebra k Ω) {C : Scheme.{0}} {A : CommRingCat.{0}} (φ : CommRingCat.of R ⟶ A)
    (c : C ⟶ Sp Ω) (v : C ⟶ Spec A) [LocallyOfFinitePresentation (Spec.map φ)] (hs : Smooth c)
    (hv : IsPullback v c (Spec.map φ) (toR R)) (y : C) : v y ∈ (Spec.map φ).smoothLocus := by
  letI : Algebra R A := φ.hom.toAlgebra
  have hfp0 : φ.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp inferInstance
  have hfp : Algebra.FinitePresentation R A := hfp0
  have hpo := (CommRingCat.isPushout_tensorProduct R Ω A)
  have hφ : CommRingCat.ofHom (algebraMap R A) = φ := rfl
  rw [hφ] at hpo
  have hstd := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
  let e := hv.isoIsPullback _ _ hstd
  have h1 : e.hom ≫ Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeRight.toRingHom) = v :=
    hv.isoIsPullback_hom_fst _ _ hstd
  have h2 : e.hom ≫ Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom) = c :=
    hv.isoIsPullback_hom_snd _ _ hstd
  haveI := hs
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)) := by
    have : Spec.map (CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom) = e.inv ≫ c := by
      rw [← h2, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  have hrs := (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := CommRingCat.ofHom (S := Ω ⊗[R] A) Algebra.TensorProduct.includeLeftRingHom)).mp hsm
  have hinc : (Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[R] A) = algebraMap Ω (Ω ⊗[R] A) := by
    ext x; rfl
  have hsA : Algebra.Smooth Ω (Ω ⊗[R] A) := by
    rw [← RingHom.smooth_algebraMap, ← hinc]; exact hrs
  have key := hA k Ω R A hfp hsA (e.hom y)
  rw [← h1, Scheme.Hom.comp_apply]
  exact stalk_of_smoothAt φ _ key

theorem LeafStalkOfAlg_of : LateralTheory.E.SpreadingOutSmoothness.LeafStalkOfAlg := by
  intro hA k _ Ω _ _ R _ C D c q v hD _ hs hv y
  let e := D.isoSpec
  let φ := Spec.preimage (e.inv ≫ q)
  have hq : Spec.map φ = e.inv ≫ q := Spec.map_preimage _
  haveI : LocallyOfFinitePresentation (Spec.map φ) := by rw [hq]; infer_instance
  have hv' : IsPullback (v ≫ e.hom) c (Spec.map φ) (toR R) := by
    rw [hq]
    exact hv.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have key := core hA k Ω R φ c (v ≫ e.hom) hs.smooth hv' y
  have h2 := Scheme.Hom.preimage_smoothLocus_eq e.hom (Spec.map φ)
  have h3 : e.hom ≫ Spec.map φ = q := by rw [hq, Iso.hom_inv_id_assoc]
  have h4 : v y ∈ (e.hom ≫ Spec.map φ).smoothLocus := by
    rw [← h2]; simpa [Scheme.Hom.comp_apply] using key
  rw [Scheme.Hom.mem_smoothLocus] at h4 ⊢
  rwa [h3] at h4

end LateralTheory.E.StalkOfAlgebra

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTw0LocGenOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPf
open LateralTheory.E.LeafTw0LocGenPfA LateralTheory.E.LeafTw0LocGenPfB

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩

theorem loc_finset {ι : Type*} [DecidableEq ι] {U : Scheme.{0}} (s : Finset ι)
    {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  induction s using Finset.induction_on with
  | empty => exact loc_top fun _ _ i hi => by simp at hi
  | insert j s hj ih =>
    obtain ⟨S0, h0, hP0⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨S1, h1, hP1⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨S0 ⊓ S1, Scheme.etaleTopology.intersection_covering h0 h1, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hP0 V g hg.1
    · exact hP1 V g hg.2 i hi

theorem res_sec {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {W V : Scheme.{0}}
    (g : W ⟶ V) (x : M.obj Γ(V, ⊤)) :
    Sec.res g (ofRings.sec M V x) = ofRings.sec M W ((M.map g.appTop).hom x) := by
  have := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact this.symm

theorem relq {q : ℕ} {A : CommRingCat.{0}} (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 A) =
      Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩
  simp
  rfl

theorem mk_mapDomain {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (r : Prim q A →₀ ULift.{1} (ZMod q))
    (ζ0 : Prim q A)
    (hrel : ∀ ξ ∈ r.support, (Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ξ) 1) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) = Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1)) :
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) r) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) =
      (r.sum fun _ c => c) • Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1) := by
  classical
  rw [← Submodule.mkQ_apply, Finsupp.mapDomain, Finsupp.sum, map_sum, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  rw [← hrel ξ hξ, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]

theorem LeafTw0LocGen_of : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := by
  classical
  intro q _ U n a
  have hA : ∀ k, Loc U fun V g => ∃ t : (twF q 0).obj Γ(V, ⊤), ofRings.sec (twF q 0) V t = Sec.res g (a k) := by
    intro k
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) (U := op U) (a k), fun V g hg => hg⟩
  have hA' := loc_finset (U := U) Finset.univ (fun k _ => hA k)
  refine LateralTheory.E.LeafTensMonoPf.loc_trans hA' fun V g hg => ?_
  choose t ht using fun k => hg k (Finset.mem_univ k)
  obtain ⟨r, hr⟩ : ∃ r : Fin n → (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)),
      ∀ k, (Submodule.Quotient.mk (r k) : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤)) = t k :=
    ⟨fun k => (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose,
     fun k => (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose_spec⟩
  rcases isEmpty_or_nonempty (Prim q Γ(V, ⊤)) with hE | ⟨⟨ζ0⟩⟩
  · refine loc_top fun W h => ⟨0, fun _ => 0, fun k => ?_, Or.inl rfl⟩
    rw [zero_smul, LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k, Subsingleton.elim (r k) 0,
      Submodule.Quotient.mk_zero]
    unfold ofRings.sec
    have h0 := map_zero (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (op V)).hom)
    first
      | exact (congrArg (Sec.res h) h0).trans (map_zero _)
      | (erw [h0]; exact map_zero _)
  · obtain ⟨S, hS, hP⟩ := loc_finset (U := V) (Finset.univ.biUnion fun k => (r k).support) (fun ξ _ => geo V ζ0 ξ)
    refine ⟨S, hS, fun W h hh => ?_⟩
    have hrel := hP W h hh
    refine ⟨twGen 0 (Prim.map h.appTop.hom ζ0), fun k => (r k).sum fun _ c => c, fun k => ?_, Or.inr ⟨_, rfl⟩⟩
    rw [LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k]
    refine (res_sec (twF q 0) h _).trans ?_
    have e1 : ((twF q 0).map h.appTop).hom (Submodule.Quotient.mk (r k)) =
        Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map h.appTop.hom) (r k)) := rfl
    rw [e1, mk_mapDomain h.appTop (r k) ζ0 (fun ξ hξ => ?_)]
    · exact map_smul _ _ _
    · obtain ⟨b, hb⟩ := hrel ξ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hξ⟩)
      exact relq _ _ b hb

end LateralTheory.E.LeafTw0LocGenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.OpenSpreadingOut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut Topology

namespace LateralTheory.E.OpenSpreadingOut

lemma toR_apply_bot {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    (toR R) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R Ω) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R Ω)

theorem etale_open_spreading_out_over_finitely_generated_subalgebra : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafOpenSpread := by
  intro k _ Ω _ _ R hR C A c p v U hp sq hU
  obtain ⟨hfp, hqc, hqs⟩ := hp
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : LocallyOfFiniteType p := inferInstance
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian A := {}
  have hZ : IsConstructible ((U : Set A)ᶜ) := by
    rw [isConstructible_compl]
    exact IsRetrocompact.isConstructible U.isOpen
      (fun W _ _ => TopologicalSpace.NoetherianSpace.isCompact _)
  have hI : IsConstructible (p '' (U : Set A)ᶜ) := p.isConstructible_image hZ
  have hT : IsConstructible (p '' (U : Set A)ᶜ)ᶜ := isConstructible_compl.mpr hI
  have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ (p '' (U : Set A)ᶜ)ᶜ := by
    rintro ⟨a, ha, hpa⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := toR R) a
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω) (by rw [hpa, toR_apply_bot])
    apply ha
    have := hU (sq.isoPullback.inv z)
    rwa [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz] at this
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.exists_basicOpen_subset_of_isConstructible_of_bot_mem hT hη
  have hs' : (s : Ω) ≠ 0 := fun h => hs0 (Subtype.ext h)
  refine ⟨R ⊔ Algebra.adjoin k {(s : Ω)⁻¹}, le_sup_left, hR.sup ⟨{(s : Ω)⁻¹}, by simp⟩, ?_⟩
  intro R' hSR' hRR' E q' r sq' z
  by_contra hz
  have hw : p (r z) = (incl hRR') (q' z) := by
    rw [← Scheme.Hom.comp_apply, sq'.w, Scheme.Hom.comp_apply]
  have hmem := hs ((incl hRR') (q' z)) ?_
  · exact hmem ⟨r z, hz, hw⟩
  · intro hsp
    change Subalgebra.inclusion hRR' s ∈ (q' z).asIdeal at hsp
    have hinv : (s : Ω)⁻¹ ∈ R' := hSR' (le_sup_right (a := R) (Algebra.subset_adjoin rfl))
    have hu : IsUnit (Subalgebra.inclusion hRR' s) :=
      IsUnit.of_mul_eq_one ⟨(s : Ω)⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hs'))
    exact (q' z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hsp hu)

end LateralTheory.E.OpenSpreadingOut

end
end

