import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFreeSheafBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

namespace FreeSheafBasis

section Coproduct

variable {C : Type*} [Category C] [Preadditive C] (A : C) (n : ℕ)
  [HasCoproduct (fun _ : ULift.{u} (Fin n) => A)]

def projC (j : Fin n) : ∐ (fun _ : ULift.{u} (Fin n) => A) ⟶ A :=
  Sigma.desc (fun i : ULift.{u} (Fin n) => if i.down = j then 𝟙 A else 0)

lemma ι_projC (i j : Fin n) :
    Sigma.ι (fun _ : ULift.{u} (Fin n) => A) (ULift.up i) ≫ projC A n j =
      if i = j then 𝟙 A else 0 :=
  Sigma.ι_desc _ _

lemma sum_projC_ι :
    ∑ j : Fin n, projC A n j ≫ Sigma.ι (fun _ : ULift.{u} (Fin n) => A) (ULift.up j) = 𝟙 _ := by
  refine Sigma.hom_ext _ _ (fun ⟨i⟩ => ?_)
  simp only [Preadditive.comp_sum, ← Category.assoc, ι_projC, Category.comp_id]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

end Coproduct

variable (Y : Scheme.{u}) (n : ℕ)

def incl (i : Fin n) : structureModule Y ⟶ freeModule Y n :=
  SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i)

def proj (j : Fin n) : freeModule Y n ⟶ structureModule Y :=
  projC (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n j

lemma incl_proj (i j : Fin n) :
    incl Y n i ≫ proj Y n j = if i = j then 𝟙 (structureModule Y) else 0 :=
  ι_projC (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n i j

lemma sum_proj_incl : ∑ j, proj Y n j ≫ incl Y n j = 𝟙 (freeModule Y n) :=
  sum_projC_ι (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n

variable {Y} in

def evalHom {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) : (M ⟶ N) →+ Γ(N, V) where
  toFun φ := (φ.app V).hom x
  map_zero' := rfl
  map_add' _ _ := rfl

variable {Y} in
lemma evalHom_apply {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) (φ : M ⟶ N) :
    evalHom V x φ = (φ.app V).hom x := rfl

variable {Y n}

lemma incl_proj_app (V : Y.Opens) (i j : Fin n) (r : Γ(Y, V)) :
    ((proj Y n j).app V).hom (((incl Y n i).app V).hom r) = if i = j then r else 0 := by
  have := congrArg (fun φ => evalHom (M := structureModule Y) (N := structureModule Y) V
    (show Γ(structureModule Y, V) from r) φ) (incl_proj Y n i j)
  split_ifs at this ⊢ with hij <;> exact this

lemma sum_incl_proj_app (V : Y.Opens) (m : Γ(freeModule Y n, V)) :
    ∑ j, ((incl Y n j).app V).hom (((proj Y n j).app V).hom m) = m := by
  have := congrArg (fun φ => evalHom V m φ) (sum_proj_incl Y n)
  simp only [map_sum, evalHom_apply] at this
  exact this

end FreeSheafBasis

open FreeSheafBasis in

theorem FreeSheafBasis.proof : FreeSheafBasis.Statement.{u} := by
  intro Y n V h
  have h1 : ((structureModule Y).presheaf.map (homOfLE h).op).hom (1 : Γ(Y, ⊤)) = (1 : Γ(Y, V)) := by
    change (Y.presheaf.map (homOfLE h).op).hom 1 = 1
    exact map_one _
  have hres : ∀ i (r : Γ(Y, V)), r • ((freeModule Y n).presheaf.map (homOfLE h).op).hom
      (stdSection Y n i) = ((incl Y n i).app V).hom r := by
    intro i r
    have e := app_map_apply (incl Y n i) h (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤)))
    have h1' : ((structureModule Y).presheaf.map (homOfLE h).op).hom
        (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤))) =
        (show Γ(structureModule Y, V) from (1 : Γ(Y, V))) := h1
    rw [h1'] at e
    have e2 := Scheme.Modules.Hom.app_smul (incl Y n i) r
      (show Γ(structureModule Y, V) from (1 : Γ(Y, V)))
    have hr : r • (show Γ(structureModule Y, V) from (1 : Γ(Y, V))) =
        (show Γ(structureModule Y, V) from r) := mul_one r
    change r • ((freeModule Y n).presheaf.map (homOfLE h).op).hom
      (((incl Y n i).app ⊤).hom (show Γ(structureModule Y, ⊤) from (1 : Γ(Y, ⊤)))) = _
    rw [← e]
    exact e2.symm.trans (congrArg (fun x => (incl Y n i).app V x) hr)
  simp only [hres]
  refine Function.bijective_iff_has_inverse.mpr ⟨fun m j => ((proj Y n j).app V).hom m, ?_, ?_⟩
  · intro r
    funext j
    simp only [map_sum, incl_proj_app]
    change (∑ x, if x = j then r x else 0 : Γ(Y, V)) = r j
    simp
  · intro m
    exact sum_incl_proj_app V m

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericGermInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem GenericGermInjective.proof : GenericGermInjective.Statement := by
  intro X _ E hE U hU
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext ⟨E.presheaf, E.isSheaf⟩ U s 0 fun x hx => ?_
  change E.presheaf.germ U x hx s = E.presheaf.germ U x hx 0
  rw [map_zero]
  obtain ⟨Ux, -, hxUx, n, b, hb⟩ := hE x
  let V : X.Opens := U ⊓ Ux
  have hxV : x ∈ V := ⟨hx, hxUx⟩
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  let iVU : V ⟶ U := homOfLE inf_le_left
  let sV := E.presheaf.map iVU.op s
  obtain ⟨r, hr⟩ := (hb V inf_le_right).2 sV
  have hr0 : ∀ i, r i = 0 := by
    have h1 : E.presheaf.germ V (genericPoint X) hηV sV = E.presheaf.germ U (genericPoint X) hU 0 := by
      rw [TopCat.Presheaf.germ_res_apply, hs, map_zero]
    obtain ⟨W, hηW, iWV, iWU, e⟩ := E.presheaf.germ_eq (genericPoint X) hηV hU sV 0 h1
    have hWUx : W ≤ Ux := iWV.le.trans inf_le_right
    have key : (fun i => X.presheaf.map iWV.op (r i)) = 0 := by
      apply (hb W hWUx).1
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      rw [map_zero] at e
      rw [← e, ← hr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    intro i
    apply germ_injective_of_isIntegral X (U := V) (genericPoint X) hηV
    rw [map_zero, ← X.presheaf.germ_res_apply iWV (genericPoint X) hηW, congrFun key i,
      Pi.zero_apply, map_zero]
  have hsV : sV = 0 := by
    rw [← hr]
    simp [hr0]
  rw [← TopCat.Presheaf.germ_res_apply E.presheaf iVU x hxV s]
  change E.presheaf.germ V x hxV sV = 0
  rw [hsV, map_zero]

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

lemma exists_torsion_bound (A : Type*) [CommRing A] [IsNoetherianRing A] :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℤ) (a : A), n ≠ 0 → (n : A) * a = 0 → (N : A) * a = 0 := by
  let I : ℕ →o Ideal A :=
    ⟨fun j => LinearMap.ker (LinearMap.mulLeft A ((j.factorial : ℕ) : A)), by
      intro i j hij a ha
      simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply] at ha ⊢
      obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hij
      rw [hc, Nat.cast_mul, mul_right_comm, ha, zero_mul]⟩
  obtain ⟨N₀, hN₀⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian A A) I
  refine ⟨N₀.factorial, Nat.factorial_pos _, fun n a hn ha => ?_⟩
  have hM : a ∈ I (max N₀ n.natAbs) := by
    have hd : n ∣ (((max N₀ n.natAbs).factorial : ℕ) : ℤ) := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      exact Nat.dvd_factorial (Int.natAbs_pos.mpr hn) (le_max_right _ _)
    obtain ⟨c, hc⟩ := hd
    have hc' : (((max N₀ n.natAbs).factorial : ℕ) : A) = (n : A) * (c : A) := by
      exact_mod_cast congrArg (Int.cast : ℤ → A) hc
    show LinearMap.mulLeft A _ a = 0
    rw [LinearMap.mulLeft_apply, hc', mul_right_comm, ha, zero_mul]
  rw [← hN₀ _ (le_max_left _ _)] at hM
  exact hM

lemma torsion_bound_localization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B] {N : ℕ}
    (hN : ∀ (n : ℤ) (a : A), n ≠ 0 → (n : A) * a = 0 → (N : A) * a = 0)
    (n : ℤ) (b : B) (hn : n ≠ 0) (hb : (n : B) * b = 0) : (N : B) * b = 0 := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S b
  have key : ∀ z : ℤ, (z : B) * IsLocalization.mk' B a s = IsLocalization.mk' B ((z : A) * a) s := by
    intro z
    rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_intCast]
  rw [key, IsLocalization.mk'_eq_zero_iff] at hb
  obtain ⟨c, hc⟩ := hb
  have h := hN n ((c : A) * a) hn (by rw [← hc]; ring)
  have key' := key (N : ℤ)
  push_cast at key'
  rw [key', IsLocalization.mk'_eq_zero_iff]
  exact ⟨c, by rw [← h]; ring⟩

lemma invOpen_eq_basicOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ) :
    invOpen f k = X.basicOpen ((k : Γ(X, f ⁻¹ᵁ ⊤))) := by
  have h : invOpen f k = f ⁻¹ᵁ (SpecZ.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv k)) := by
    unfold invOpen
    exact congrArg (f ⁻¹ᵁ ·) (basicOpen_eq_of_affine (R := CommRingCat.of ℤ) k).symm
  rw [h, Scheme.preimage_basicOpen]
  congr 1
  simp only [eq_intCast]
  exact map_intCast (f.app ⊤).hom k

lemma isUnit_intCast_of_le_invOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ) {V : X.Opens}
    (hV : V ≤ invOpen f k) : IsUnit (k : Γ(X, V)) := by
  rw [invOpen_eq_basicOpen] at hV
  have hu := X.toRingedSpace.isUnit_res_basicOpen ((k : Γ(X, f ⁻¹ᵁ ⊤)))
  rw [map_intCast] at hu
  have := hu.map (X.presheaf.map (homOfLE hV).op).hom
  convert this using 1
  exact (map_intCast (X.presheaf.map (homOfLE hV).op).hom k).symm

lemma eq_zero_of_intCast_mul_eq_zero {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ)
    (hcov : ∀ x : X, ∃ (U : X.affineOpens) (N : ℕ), x ∈ (U : X.Opens) ∧ (N : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N : Γ(X, U)) * a = 0)
    {W : X.Opens} (hW : W ≤ invOpen f k) (n : ℤ) (hn : n ≠ 0) (s : Γ(X, W))
    (hs : (n : Γ(X, W)) * s = 0) : s = 0 := by
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨U, N, hxU, hNk, hN⟩ := hcov x
  obtain ⟨a, haW, hxa⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ hxU
  refine ⟨X.basicOpen a, haW, hxa, ?_⟩
  have := U.2.isLocalization_basicOpen a
  set t := X.presheaf.map (homOfLE haW).op s with ht_def
  have ht : (n : Γ(X, X.basicOpen a)) * t = 0 := by
    rw [ht_def, ← map_intCast (X.presheaf.map (homOfLE haW).op).hom n, ← map_mul, hs, map_zero]
  have hNt := torsion_bound_localization (Submonoid.powers a) hN n t hn ht
  have hk := isUnit_intCast_of_le_invOpen f k (haW.trans hW)
  have hNu : IsUnit (N : Γ(X, X.basicOpen a)) := by
    obtain ⟨c, hc⟩ := hNk
    have hkc : ((k : ℤ) : Γ(X, X.basicOpen a)) =
        ((N : ℤ) : Γ(X, X.basicOpen a)) * (c : Γ(X, X.basicOpen a)) := by
      rw [hc]; push_cast; ring
    rw [hkc] at hk
    exact_mod_cast isUnit_of_mul_isUnit_left hk
  rw [map_zero]
  exact hNu.mul_right_eq_zero.mp hNt

lemma flat_of_eq_zero_of_intCast_mul {Y : Scheme.{0}} (g : Y ⟶ SpecZ)
    (hT : ∀ (V : Y.Opens) (n : ℤ) (s : Γ(Y, V)), n ≠ 0 → (n : Γ(Y, V)) * s = 0 → s = 0) :
    Flat g := by
  have := HasRingHomProperty.HasAffineProperty @Flat
  rw [HasAffineProperty.iff_of_isAffine (P := @Flat) (Q := sourceAffineLocally RingHom.Flat)]
  intro V
  let e : ℤ ≃+* Γ(SpecZ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm
  have hφ : (g.appLE ⊤ V le_top).hom =
      (((g.appLE ⊤ V le_top).hom).comp e.toRingHom).comp e.symm.toRingHom :=
    by ext x; simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
  rw [hφ]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective) ?_
  generalize ((g.appLE ⊤ V le_top).hom).comp e.toRingHom = ψ
  have hψ : ψ = algebraMap ℤ Γ(Y, V) := RingHom.ext_int _ _
  rw [hψ, RingHom.flat_algebraMap_iff]
  have : Module.IsTorsionFree ℤ Γ(Y, V) := ⟨fun r hr b c hbc => by
    have hr0 : r ≠ 0 := hr.ne_zero
    simp only [zsmul_eq_mul] at hbc
    rw [← sub_eq_zero]
    exact hT V r _ hr0 (by rw [mul_sub, hbc, sub_self])⟩
  infer_instance

theorem GenericSectionsInj.proof : GenericSectionsInj.Statement := by
  intro X f _ _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  choose N hNpos hN using fun U : X.affineOpens =>
    haveI := IsLocallyNoetherian.component_noetherian U
    exists_torsion_bound Γ(X, U)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨∏ U ∈ t, N U, Finset.prod_pos fun U _ => hNpos U, fun k hk hmk W => ?_⟩
  have hcov : ∀ x : X, ∃ (U : X.affineOpens) (N' : ℕ), x ∈ (U : X.Opens) ∧ (N' : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N' : Γ(X, U)) * a = 0 := by
    intro x
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨U, N U, hxU, dvd_trans (by exact_mod_cast Finset.dvd_prod_of_mem N hUt) hmk, hN U⟩
  have hflat : Flat ((invOpen f k).ι ≫ f) := flat_of_eq_zero_of_intCast_mul _ fun V n s hn hs => by
    let e := ((invOpen f k).ι.appIso V).commRingCatIsoToRingEquiv
    have h0 := eq_zero_of_intCast_mul_eq_zero f k hcov ((invOpen f k).ι_image_le V) n hn (e.symm s)
      (by rw [← map_intCast e.symm, ← map_mul, hs, map_zero])
    simpa using congrArg e h0
  let φ : Spec (CommRingCat.of ℚ) ⟶ SpecZ := Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))
  have H : IsPullback (toInvOpen f ℚ k hk) (𝟙 _ ≫ pullback.snd f φ) ((invOpen f k).ι ≫ f) φ :=
    (IsOpenImmersion.isPullback_lift_id _ _ _).paste_vert (IsPullback.of_hasPullback _ _)
  have : IsDominant φ := by
    rw [isDominant_iff]
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (Int.cast_injective (α := ℚ))]
      exact bot_le)
  have : IsSchemeTheoreticallyDominant φ := .of_isDominant φ
  have : IsSchemeTheoreticallyDominant (toInvOpen f ℚ k hk) := .of_isPullback H.flip
  have : QuasiCompact (toInvOpen f ℚ k hk) := MorphismProperty.of_isPullback H.flip inferInstance
  exact (toInvOpen f ℚ k hk).app_injective W

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PInvOpenInside
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace InvOpenInside

lemma mem_range_baseChangeMap {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) (x : X)
    (hx : Disjoint ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl : Set ℤ) (f.base x).asIdeal) :
    x ∈ Set.range (baseChangeMap f (ZLoc p)) := by
  have hr := PrimeSpectrum.localization_comap_range (ZLoc p)
    (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
  obtain ⟨y, hy⟩ : f.base x ∈ Set.range (PrimeSpectrum.comap (algebraMap ℤ (ZLoc p))) := by
    rw [hr]; exact hx
  have e : algebraMap ℤ (ZLoc p) = Int.castRingHom (ZLoc p) := RingHom.ext_int _ _
  have hy' : f.base x = PrimeSpectrum.comap (Int.castRingHom (ZLoc p)) y :=
    hy.symm.trans (congrFun (congrArg PrimeSpectrum.comap e) y)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) x y hy'
  exact ⟨z, hz⟩

lemma exists_of_isAffineOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) (W : X.Opens)
    (hW : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ s ∈ (Ideal.span {((p : ℕ) : ℤ)}).primeCompl,
      ∀ x ∈ U, x ∉ W → s ∈ (f.base x).asIdeal := by
  set S := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl with hS
  set T : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec.base ⁻¹' (W : Set X)ᶜ with hTdef
  have hT : IsClosed T := W.isOpen.isClosed_compl.preimage hU.fromSpec.base.hom.continuous
  have hf : ∀ P : Spec Γ(X, U),
      (f.base (hU.fromSpec.base P)).asIdeal = P.asIdeal.comap (Int.castRingHom Γ(X, U)) := by
    intro P
    have h : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (Int.castRingHom Γ(X, U))) :=
      specZIsTerminal.hom_ext _ _
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  have hW' : ∀ x : X, Disjoint (S : Set ℤ) (f.base x).asIdeal → x ∈ W := by
    intro x hx
    have := hW (mem_range_baseChangeMap f p x hx)
    rwa [Scheme.Opens.range_ι] at this
  have hI : ¬ Disjoint (PrimeSpectrum.vanishingIdeal T : Set Γ(X, U))
      (S.map (Int.castRingHom Γ(X, U)) : Set Γ(X, U)) := by
    intro hd
    obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint _ _ hd
    obtain ⟨Q, rfl⟩ : ∃ Q : Spec Γ(X, U), Q.asIdeal = P := ⟨⟨P, hP⟩, rfl⟩
    have hQ : hU.fromSpec Q ∉ W := by
      change Q ∈ T
      rw [← hT.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact hIP
    apply hQ
    apply hW'
    rw [hf Q]
    refine Set.disjoint_left.mpr fun s hs hsP => ?_
    exact Set.disjoint_left.mp hPS hsP ⟨s, hs, rfl⟩
  obtain ⟨a, haI, ⟨s, hs, rfl⟩⟩ := Set.not_disjoint_iff.mp hI
  refine ⟨s, hs, fun x hxU hxW => ?_⟩
  have hxU' : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨Q, rfl⟩ := hxU'
  rw [hf]
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp haI Q hxW

theorem proof : InvOpenInside.Statement := by
  intro X f _ p W hW
  choose s hsS hs using fun U : X.affineOpens => exists_of_isAffineOpen f p W hW U.2
  have hZ : IsCompact (W : Set X)ᶜ := by
    have hX : IsCompact (Set.univ : Set X) := by
      simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ
    exact hX.of_isClosed_subset W.isOpen.isClosed_compl (Set.subset_univ _)
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun U : X.affineOpens => ((U : X.Opens) : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  set s₀ : ℤ := ∏ U ∈ t, s U with hs₀def
  have hs₀ : s₀ ∈ (Ideal.span {((p : ℕ) : ℤ)}).primeCompl :=
    Submonoid.prod_mem _ fun U _ => hsS U
  have hne : s₀ ≠ 0 := fun h => hs₀ (h ▸ Ideal.zero_mem _)
  refine ⟨s₀.natAbs, Int.natAbs_pos.mpr hne, fun h => ?_, fun x hx => ?_⟩
  · exact hs₀ (Ideal.mem_span_singleton.mpr (Int.ofNat_dvd_left.mpr h))
  · by_contra hxW
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht hxW)
    have h1 := hs U x hxU hxW
    have h2 : s₀ ∈ (f.base x).asIdeal := Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hUt) h1
    exact (mem_invOpen f _ x).mp hx (Ideal.mem_of_dvd _ (Int.dvd_natAbs.mpr dvd_rfl) h2)

end InvOpenInside

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PInvOpenInsideRat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

theorem isLocallyNoetherian_of_locallyOfFiniteType_specZ {X : Scheme.{0}} (f : X ⟶ SpecZ)
    [LocallyOfFiniteType f] : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  have hZ : IsNoetherianRing Γ(SpecZ, ⊤) :=
    IsLocallyNoetherian.component_noetherian (X := SpecZ) ⟨⊤, isAffineOpen_top _⟩
  have e : (U : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  have hφ := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨⊤, isAffineOpen_top _⟩ U e
  let _ := (f.appLE ⊤ U.1 e).hom.toAlgebra
  have : Algebra.FiniteType Γ(SpecZ, ⊤) Γ(X, U) := hφ
  exact Algebra.FiniteType.isNoetherianRing Γ(SpecZ, ⊤) Γ(X, U)

theorem mem_range_baseChangeMap_rat_of_asIdeal_eq_bot {X : Scheme.{0}} (f : X ⟶ SpecZ) (x : X)
    (hx : (f.base x).asIdeal = ⊥) : x ∈ Set.range (baseChangeMap f ℚ) := by
  let y : Spec (CommRingCat.of ℚ) := ⟨⊥, Ideal.isPrime_bot⟩
  have h : f.base x = (Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))).base y := by
    apply PrimeSpectrum.ext
    rw [hx]
    change ⊥ = Ideal.comap (Int.castRingHom ℚ) ⊥
    exact (Ideal.comap_bot_of_injective _ (Int.cast_injective (α := ℚ))).symm
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  exact ⟨z, hz⟩

theorem InvOpenInsideRat.proof : InvOpenInsideRat.Statement := by
  intro X f _ _ W hW
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isLocallyNoetherian_of_locallyOfFiniteType_specZ f
  have : IsNoetherian X := {}

  have hgen : ∀ x : X, x ∉ W → (f.base x).asIdeal ≠ ⊥ := by
    intro x hx h
    have h1 := hW (mem_range_baseChangeMap_rat_of_asIdeal_eq_bot f x h)
    rw [Scheme.Opens.range_ι] at h1
    exact hx h1
  obtain ⟨S, hSi, hS⟩ := NoetherianSpace.exists_finset_irreducible
    (⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ : Closeds X)
  have hSZ : ∀ k ∈ S, (k : Set X) ⊆ (W : Set X)ᶜ := by
    intro k hk
    have h1 : k ≤ S.sup id := Finset.le_sup (f := id) hk
    rw [← hS] at h1
    exact h1
  have claim : ∀ k ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ x ∈ (k : Set X), (n : ℤ) ∈ (f.base x).asIdeal := by
    intro k hk
    have hirr : IsIrreducible (k : Set X) := hSi ⟨k, hk⟩
    have hg : IsGenericPoint hirr.genericPoint (k : Set X) :=
      hirr.isGenericPoint_genericPoint k.isClosed
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (hgen _ (hSZ k hk hg.mem))
    refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun x hx => ?_⟩
    have hle : (f.base hirr.genericPoint).asIdeal ≤ (f.base x).asIdeal :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr ((hg.specializes hx).map f.base.hom.continuous)
    exact Ideal.mem_of_dvd _ (Int.dvd_natAbs.mpr dvd_rfl) (hle hn)
  choose! n hn using claim
  refine ⟨∏ k ∈ S, n k, Finset.prod_pos fun k hk => (hn k hk).1, ?_⟩
  intro x hx
  by_contra hxW
  have hxS : x ∈ ((S.sup id : Closeds X) : Set X) := by rw [← hS]; exact hxW
  rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hxS
  obtain ⟨k, hk, hxk⟩ := hxS
  apply (mem_invOpen f _ x).mp hx
  have hdvd : ((n k : ℕ) : ℤ) ∣ ((∏ k ∈ S, n k : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem n hk)
  exact Ideal.mem_of_dvd _ hdvd ((hn k hk).2 x hxk)

end

end GroundTheory.Heights₂.Heights.Model
end

