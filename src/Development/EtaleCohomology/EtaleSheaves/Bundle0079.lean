import Development.EtaleCohomology.EtaleSheaves.Bundle0078
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.EtaleCohomology.EtaleSheaves.Bundle0075
import Development.EtaleCohomology.EtaleSheaves.Bundle0054
import Development.EtaleCohomology.EtaleSheaves.Bundle0008
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.ResMapNsmulHomotopy
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuPf
import Development.EtaleCohomology.EtaleSheaves.KummerFields.H0Naturality
import Development.EtaleCohomology.EtaleSheaves.KummerFields.GmSecSurj
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.EtaleCohomology.EtaleSheaves.Bundle0076

-- bundled from Development.EtaleCohomology.EtaleSheaves.BridgeYfiPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.Bridge_yfiPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd
  LateralTheory.E.NeighbourhoodKilling LateralTheory.E.SecondDegreeKilling

structure Sys (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) (u : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  mem : ∀ j, u ∈ Set.range (a j).left
  tr : ∀ {j k : J}, (j ⟶ k) → (V k ⟶ V j)
  tr_id : ∀ j, tr (𝟙 j) = 𝟙 (V j)
  tr_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), tr (f ≫ g) = tr g ≫ tr f
  tr_a : ∀ {j k : J} (f : j ⟶ k), tr f ≫ a j = a k
  A : Type
  [ring : CommRing A]
  sh : SH A
  t : Sp A ⟶ U.left
  gY : ∀ j, pullback p (t ≫ U.hom) ⟶ YU p (V j)
  gW : ∀ j, pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι
  sq : ∀ j, prS p ι (t ≫ U.hom) ≫ gY j = gW j ≫ prU p ι (V j)
  gY_a : ∀ j, gY j ≫ resY p (a j) = tY p U t
  gW_a : ∀ j, gW j ≫ resYW p ι (a j) = tW p ι U t
  gY_tr : ∀ {j k : J} (f : j ⟶ k), gY k ≫ resY p (tr f) = gY j
  gW_tr : ∀ {j k : J} (f : j ⟶ k), gW k ≫ resYW p ι (tr f) = gW j
  injY : ∀ j (y : Ht q (sch.obj (YU p (V j))) m i), pull (ZMod q) (sch.map (gY j)) (tw q i) m y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resY p (tr f))) (tw q i) m y = 0
  surY : ∀ y : Ht q (sch.obj (pullback p (t ≫ U.hom))) (m - 1) i,
    ∃ (j : J) (y' : Ht q (sch.obj (YU p (V j))) (m - 1) i), pull (ZMod q) (sch.map (gY j)) (tw q i) (m - 1) y' = y
  injW : ∀ j (w : Ht q (sch.obj (pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι)) (m - 1) i),
    pull (ZMod q) (sch.map (gW j)) (tw q i) (m - 1) w = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resYW p ι (tr f))) (tw q i) (m - 1) w = 0

def Geo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Pack : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
  (u : U.left) (_ : Sys q i p ι U m u) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem Bridge_of_geo_pack (hG : Geo) (hP : Pack) : Bridge := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z u
  obtain ⟨S⟩ := hG hH q k hq i toK ι p hp U m u
  exact hP q i p ι U m u S z

end LateralTheory.E.Bridge_yfiPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FMrangePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf Topology

namespace LateralTheory.E.FMrangePf

def RRsub : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    RR w q ⊆ closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal})

theorem range_spec_atPrime {W : Type} [CommRing W] (q : PrimeSpectrum W) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))).base =
      {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal} := by
  have h := PrimeSpectrum.localization_comap_range (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  ext p
  change p ∈ Set.range (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal))) ↔ _
  rw [h]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hd x hx
    by_contra hq
    exact Set.disjoint_left.1 hd (show x ∈ (q.asIdeal.primeCompl : Set W) from hq) hx
  · intro hle
    exact Set.disjoint_left.2 fun x hx hp => hx (hle hp)

theorem mem_basicOpen_toNorm {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (s : Γ(w.normalization, ⊤)) (p : Spec (CommRingCat.of W)) :
    w.toNormalization p ∈ w.normalization.basicOpen s ↔ phi w s ∉ p.asIdeal := by
  change p ∈ w.toNormalization ⁻¹ᵁ w.normalization.basicOpen s ↔ _
  rw [Scheme.preimage_basicOpen_top, AlgebraicGeometry.basicOpen_eq_of_affine']
  rfl

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.appTop) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  exact h2.comp h1

theorem closure_sub_RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) :
    closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) ⊆ RR w q := by
  intro y hy s hs hsq
  have hid : IsIdempotentElem s := phi_injective w (by rw [map_mul]; exact hs.eq)
  have hcl : IsClosed (w.normalization.basicOpen s : Set w.normalization) := by
    rw [← isOpen_compl_iff]
    have : (w.normalization.basicOpen s : Set w.normalization)ᶜ = w.normalization.basicOpen (1 - s) := by
      ext x
      exact LateralTheory.E.SysFMPfSys.basicOpen_one_sub hid x
    rw [this]
    exact (w.normalization.basicOpen (1 - s)).isOpen
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨p, hp, rfl⟩
  exact (mem_basicOpen_toNorm w s p).2 fun h => hsq (hp h)

def IdemLift : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

def QcIdem : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ U : (Spec (CommRingCat.of W)).Opens,
  IsCompact (U : Set (Spec (CommRingCat.of W))) → ∃ e : W, IsIdempotentElem e ∧ ∀ p : Spec (CommRingCat.of W),
    p ∈ U ↔ e ∉ p.asIdeal

theorem RRsub_of (hI : IdemLift) (hQ : QcIdem) : RRsub := by
  intro P _ _ W _ w hW q y hy
  by_contra hc
  rw [mem_closure_iff] at hc
  push Not at hc
  obtain ⟨o, ho, hyo, hoT⟩ := hc
  obtain ⟨V, hV, hyV, hVo⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens w.normalization))
    (show y ∈ (⟨o, ho⟩ : TopologicalSpace.Opens w.normalization) from hyo)
  have hVc : IsCompact (w.toNormalization ⁻¹ᵁ V : Set (Spec (CommRingCat.of W))) :=
    QuasiCompact.isCompact_preimage _ V.isOpen (IsAffineOpen.isCompact hV)
  obtain ⟨e, he, hpe⟩ := hQ W hW _ hVc
  have heq : e ∈ q.asIdeal := by
    by_contra hnq
    have hmem : w.toNormalization q ∈ V := (hpe q).2 hnq
    have : w.toNormalization q ∈ o ∩ (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) :=
      ⟨hVo hmem, q, show q.asIdeal ≤ q.asIdeal from le_refl _, rfl⟩
    rw [hoT] at this
    exact this
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hfq : (1 - e) ∉ q.asIdeal := fun h => q.2.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.asIdeal.add_mem heq h))
  obtain ⟨s, hs⟩ := hI W w hW (1 - e) hf
  have hys : y ∈ w.normalization.basicOpen s := hy s (by rw [hs]; exact hf) (by rw [hs]; exact hfq)
  obtain ⟨_, ⟨hz1, hz2⟩, p, rfl⟩ := w.toNormalization.denseRange.inter_open_nonempty
    ((w.normalization.basicOpen s ⊓ V : w.normalization.Opens) : Set w.normalization)
    (w.normalization.basicOpen s ⊓ V).isOpen ⟨y, hys, hyV⟩
  have h1 : phi w s ∉ p.asIdeal := (mem_basicOpen_toNorm w s p).1 hz1
  have h2 : e ∉ p.asIdeal := (hpe p).1 hz2
  rw [hs] at h1
  have : e * (1 - e) ∈ p.asIdeal := by rw [mul_sub, mul_one, he.eq, sub_self]; exact p.asIdeal.zero_mem
  rcases p.2.mem_or_mem this with h | h
  · exact h2 h
  · exact h1 h

theorem FMrange_of (hC : RRsub) : FMrange := by
  intro P _ _ W _ w hW q m e1 e2
  set a := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have : IsIntegralHom (m ≫ w.fromNormalization) := by rw [e2]; infer_instance
  have : IsIntegralHom m := IsIntegralHom.of_comp m w.fromNormalization
  have hcl : IsClosedMap m.base := m.isClosedMap
  have hd : closure (Set.range (a ≫ w).toNormalization.base) = Set.univ :=
    (a ≫ w).toNormalization.denseRange.closure_range
  have himg : m.base '' Set.range (a ≫ w).toNormalization.base =
      w.toNormalization.base '' Set.range a.base := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext x
    simp only [Function.comp_apply]
    rw [← Scheme.Hom.comp_apply, ← e1, Scheme.Hom.comp_apply]
  rw [subset_antisymm (hC W w hW q) (closure_sub_RR w q), ← range_spec_atPrime q, ← Set.image_univ, ← hd,
    ← hcl.closure_image_eq_of_continuous m.continuous, himg]

theorem FMrange_of_leaves (hI : IdemLift) (hQ : QcIdem) : FMrange :=
  FMrange_of (RRsub_of hI hQ)

end LateralTheory.E.FMrangePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FiltrationLevelBase
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
  LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelBase

def Step0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
    rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
    ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
      LateralTheory.E.FiltGenPf.V ((chains R).map g) (-1) n ((z : Cochain _ _ n) - δ (n - 1) n c)

theorem Filt_of (h0 : Step0) : LateralTheory.E.FiltrationLevelInjectivity.Filt := by
  intro _ R _ F n Z' Z X' X g h a b comm ha hb hlev
  have hk : ∀ p : ℕ, 1 ≤ p → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map g).f (-(p : ℤ)))))
      (res R F) n) := by
    intro p hp
    refine LateralTheory.E.CechFiltPf.Piece_of LateralTheory.E.DiscLvlPf.DiscLvl_of LateralTheory.E.ShiftLvlPf.ShiftLvl_of R F g p n ?_
    obtain ⟨hi, hs⟩ := hlev p hp (n - p) (by omega)
    refine LateralTheory.E.RelativeTruncationSingleDegree.sub_of R F _ _ ⟨fun m hm => ?_, hi⟩ (LateralTheory.E.RelativeTruncationSingleDegree.pull_fgt R F _ _)
    obtain rfl : m = n - p - 1 := by omega
    exact hs
  have hk' : ∀ k : ℤ, k ≤ -1 → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) k).map (((chains R).map g).f k))) (res R F) n) := by
    intro k hk1
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact hk p (by omega)
  have claim : ∀ m : ℕ, ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
      rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
      ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
        LateralTheory.E.FiltGenPf.V ((chains R).map g) (-((m : ℤ) + 1)) n ((z : Cochain _ _ n) - δ (n - 1) n c) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      have e : (-(((0 : ℕ) : ℤ) + 1)) = -1 := by norm_num
      rw [e]
      exact h0 R F n g h a b comm ha hb z hz
    | succ m ih =>
      intro z hz
      obtain ⟨c, hc⟩ := ih z hz
      have hkm := hk' (-((m : ℤ) + 1)) (by omega)
      have hs1 := LateralTheory.E.FiltGenPf.step ((chains R).map g) (-((m : ℤ) + 1)) n hkm
      have hzz : δ n (n + 1) ((z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c) = 0 := by
        rw [δ_sub, δ_δ, sub_zero]; exact Cocycle.δ_eq_zero z (n + 1)
      have hs2 := hs1 _ hzz
      obtain ⟨c', hc'⟩ := hs2 hc
      refine ⟨c + c', ?_⟩
      have e : (-((((m + 1 : ℕ) : ℤ)) + 1)) = -((m : ℤ) + 1) - 1 := by push_cast; ring
      rw [e, δ_add, ← sub_sub]
      exact hc'
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨c, hc1, hc2⟩ := claim (n.toNat + 1) z hx
  change CohomologyClass.mk z = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨c, ?_⟩
  have hz0 : (z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c = 0 := by
    rw [mappingCone.ext_cochain_from_iff _ (n - 1) n (by omega)]
    constructor
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc1 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc2 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
  rw [sub_eq_zero] at hz0
  exact hz0.symm

theorem goal_of (h0 : Step0) : LateralTheory.E.RelDescPf.LevelInj :=
  LateralTheory.E.FiltrationLevelInjectivity.LevelInj_of (Filt_of h0) LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of

end LateralTheory.E.FiltrationLevelBase
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlueRelPfNat
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex AlgebraicGeometry LateralTheory.E.E4
  LateralTheory.E.LeafLocStalkPf

namespace LateralTheory.E.GlueRelPfNat
variable (R : Type) [CommRing R]

theorem map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) :
    (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff φ₁ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.map, mappingCone.inl_desc,
      Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inl_fst, ← Cochain.comp_assoc_of_third_is_zero_cochain,
      mappingCone.inl_fst]
    simp
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp [mappingCone.map]

theorem sq {Y X V : Scheme.{0}} (f : Y ⟶ X) (v : V ⟶ X) :
    cechAug (pullback.snd f v) ≫ sch.map v = LateralTheory.E.LocSurjPf.bcMap f v ≫ cechAug f := by
  ext n : 1
  simp only [NatTrans.comp_app]
  simp [cechAug, LateralTheory.E.LocSurjPf.bcMap, sch, Arrow.mapCechNerve, Arrow.augmentedCechNerve]
  exact (WidePullback.lift_base _ _ _ _).symm

def coneBC (q : ℕ) {Y X V : Scheme.{0}} (f : Y ⟶ X) (v : V ⟶ X) :
    mappingCone ((chains (ZMod q)).map (cechAug (pullback.snd f v))) ⟶ mappingCone ((chains (ZMod q)).map (cechAug f)) :=
  mappingCone.map _ _ ((chains (ZMod q)).map (LateralTheory.E.LocSurjPf.bcMap f v)) ((chains (ZMod q)).map (sch.map v))
    (by rw [← Functor.map_comp, ← Functor.map_comp, sq])

def RelInj : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X),
  (∀ (W : Scheme.{0}) (w : W ⟶ X), Etale w → ∀ m' < n, RelZS (ZMod q) (tw q i) m' (cechAug (pullback.snd f w))) →
  ∀ (V : Scheme.{0}) (v : V ⟶ X), Etale v → Surjective v → ∀ m : ℤ, m + 1 = n →
    Function.Injective (HK.pull (ZMod q) (coneBC q f v) (tw q i) (m + 1))

end LateralTheory.E.GlueRelPfNat
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IdemSecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.SysFMPf

namespace LateralTheory.E.IdemSecPf

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.app ⊤) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  intro a b h
  exact h1 (h2 h)

theorem phi_idem {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (e : W) (he : IsIdempotentElem e) : ∃ s, phi w s = e := by
  let t : Γ(Spec (CommRingCat.of W), w.toNormalization ⁻¹ᵁ ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv e
  have ht : (w.toNormalization.app ⊤).hom.IsIntegralElem t := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))
    · have : t * t = t := by
        show (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e * (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e = _
        rw [← map_mul, he.eq]
      rw [sq, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, this, sub_self]
  obtain ⟨s, hs⟩ := GlobalTheory.mem_range_toNormalization_app w ⊤ t ht
  refine ⟨s, ?_⟩
  show (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (w.toNormalization.app ⊤ s) = e
  rw [hs]
  show ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom e = e
  simp

theorem IdemSec_of : LateralTheory.E.SysFMPfSys.IdemSec := by
  intro P _ _ W _ w
  exact ⟨phi_injective w, fun e he => phi_idem w e he⟩

end LateralTheory.E.IdemSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KummerFields
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKumFieldPf

open LateralTheory.E.E4

theorem kumMu : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumMu := fun hy =>
  LateralTheory.E.H2CurveOrder.LeafKumMuPf.LeafKumMu_of hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2.2.1
    LateralTheory.E.H2CurveOrder.muUnits hy

theorem etale_kummer_sequence_degree_zero_global_sections : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.KummerUnitsSurjectH0 := fun hy =>
  LateralTheory.E.H2CurveOrder.KummerH0Surjection.etale_kummer_degree_zero_cohomology_of_sections_and_units_surjective LateralTheory.E.H2CurveOrder.kumSecSurj
    (LateralTheory.E.LeafKumFieldPf.H0Naturality.etale_degree_zero_cohomology_natural_in_sheaf hy.2.2.2.2.2.2.2.1)
    LateralTheory.E.LeafKumFieldPf.GmSecSurj.LeafGmSecSurj_of hy

theorem kumSeq : LateralTheory.E.LeafKumCut.LeafKumSeq :=
  LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumSeq_of kumMu etale_kummer_sequence_degree_zero_global_sections

end LateralTheory.E.LeafKumFieldPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPf
section
noncomputable section

namespace LateralTheory.E.LeafCoordsPointResPf

open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

def LeafResT : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∃ (t : Fin d → I),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤

def LeafResY : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → ∀ (t : Fin d → I),
    Submodule.span P.ResidueField (Set.range fun j => (1 : P.ResidueField) ⊗ₜ[B] t j) = ⊤ →
    ∃ (y : Fin e → B), Submodule.span P.ResidueField
      (Set.range fun i => (1 : P.ResidueField) ⊗ₜ[B] dyt (A := A) y (fun j => (t j : B)) i) = ⊤

theorem LeafCoordsPointRes_of (hT : LeafResT) (hY : LeafResY) : LeafCoordsPointRes := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  obtain ⟨t, ht⟩ := hT d e A B I hB hBI P hIP
  obtain ⟨y, hy⟩ := hY d e A B I hB hBI P hIP t ht
  exact ⟨t, y, ht, hy⟩

theorem pick {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (d : ℕ)
    (g : ι → V) (i0 : ι) (hs : Submodule.span K (Set.range g) = ⊤)
    (hd : Module.finrank K V ≤ d) : ∃ f : Fin d → ι, Submodule.span K (Set.range (g ∘ f)) = ⊤ := by
  classical
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent K (Set.range g)
  rw [hs] at hsp
  let bb : Module.Basis b K V := Module.Basis.mk hli (by rw [Subtype.range_coe]; exact hsp.ge)
  have : Finite b := Module.Finite.finite_basis bb
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b ≤ d := (Module.finrank_eq_card_basis bb).symm ▸ hd
  let e := Fintype.equivFin b
  have hpre : ∀ v : b, ∃ i, g i = v := fun v => hb v.2
  let f : Fin d → ι := fun j => if h : j.val < Fintype.card b then Classical.choose (hpre (e.symm ⟨j, h⟩)) else i0
  refine ⟨f, eq_top_iff.mpr ?_⟩
  rw [← hsp]
  apply Submodule.span_le.mpr
  intro v hv
  apply Submodule.subset_span
  refine ⟨⟨(e ⟨v, hv⟩).val, lt_of_lt_of_le (e ⟨v, hv⟩).2 hcard⟩, ?_⟩
  simp only [Function.comp_apply, f, (e ⟨v, hv⟩).2, dite_true]
  rw [Classical.choose_spec (hpre _)]
  simp

theorem span_one_tmul {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B) [P.IsPrime] :
    Submodule.span P.ResidueField (Set.range fun m : M => (1 : P.ResidueField) ⊗ₜ[B] m) = ⊤ := by
  rw [eq_top_iff]; rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k m =>
    have : k ⊗ₜ[B] m = k • ((1 : P.ResidueField) ⊗ₜ[B] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact add_mem hx hy

def LeafResDimI : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ (P : Ideal B) [P.IsPrime], I ≤ P → Module.finrank P.ResidueField (P.ResidueField ⊗[B] I) ≤ d

theorem LeafResT_of (hD : LeafResDimI) : LeafResT := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  have hfg := ideal_fg I _ _ hB hBI
  have : Module.Finite B I := Module.Finite.iff_fg.mpr hfg
  obtain ⟨f, hf⟩ := pick d (fun m : I => (1 : P.ResidueField) ⊗ₜ[B] m) 0 (span_one_tmul P) (hD d e A B I hB hBI P hIP)
  exact ⟨f, hf⟩

theorem LeafCoordsPointRes_of' (hD : LeafResDimI) (hY : LeafResY) : LeafCoordsPointRes :=
  LeafCoordsPointRes_of (LeafResT_of hD) hY

end LateralTheory.E.LeafCoordsPointResPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafInclDescendPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf

namespace LateralTheory.E.LeafInclDescendPf

def bcLift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R'' : Subalgebra k Ω} (h : R ≤ R'')
    {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D} (w : v ≫ q = g ≫ toR R) :
    Y ⟶ pullback q (incl h) :=
  pullback.lift v (g ≫ toR R'') (by rw [Category.assoc, toR_eq, w])

theorem bcLift_isPullback {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R'' : Subalgebra k Ω} (h : R ≤ R'')
    {Y D : Scheme.{0}} {g : Y ⟶ Sp Ω} {q : D ⟶ Sp R} {v : Y ⟶ D} (hp : IsPullback v g q (toR R)) :
    IsPullback (bcLift h hp.w) g (pullback.snd q (incl h)) (toR R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h))
  simp only [bcLift]
  rw [pullback.lift_fst, toR_eq]
  exact hp

def LeafInclPiece : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U W : X.Opens) (hWU : W ≤ U) (R : Subalgebra k Ω), R.FG →
    ∀ (DU DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qW : DW ⟶ Sp R) (vU : U.toScheme ⟶ DU) (vW : W.toScheme ⟶ DW),
    FP qU → FP qW → ∀ (hU : IsPullback vU (U.ι ≫ f) qU (toR R)) (hW : IsPullback vW (W.ι ≫ f) qW (toR R)),
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ ∀ (R'' : Subalgebra k Ω) (h : R ≤ R''), R' ≤ R'' →
      ∃ φ : pullback qW (incl h) ⟶ pullback qU (incl h), IsOpenImmersion φ ∧
        φ ≫ pullback.snd qU (incl h) = pullback.snd qW (incl h) ∧
        bcLift h hW.w ≫ φ = X.homOfLE hWU ≫ bcLift h hU.w

theorem LeafInclDescend_of (hP : LeafInclPiece) : LeafInclDescend := by
  intro k _ Ω _ _ X f hf U V R hR ⟨DU, qU, vU, hqU, pU⟩ ⟨DV, qV, vV, hqV, pV⟩ ⟨DW, qW, vW, hqW, pW⟩
  obtain ⟨R1, h1, hR1, H1⟩ := hP k Ω f hf U (U ⊓ V) inf_le_left R hR DU DW qU qW vU vW hqU hqW pU pW
  obtain ⟨R2, h2, hR2, H2⟩ := hP k Ω f hf V (U ⊓ V) inf_le_right R hR DV DW qV qW vV vW hqV hqW pV pW
  have hle : R ≤ R1 ⊔ R2 := h1.trans le_sup_left
  obtain ⟨φU, oU, sU, cU⟩ := H1 (R1 ⊔ R2) hle le_sup_left
  obtain ⟨φV, oV, sV, cV⟩ := H2 (R1 ⊔ R2) hle le_sup_right
  exact ⟨R1 ⊔ R2, hle, hR1.sup hR2, _, _, _, pullback.snd qU (incl hle), pullback.snd qV (incl hle),
    pullback.snd qW (incl hle), bcLift hle pU.w, bcLift hle pV.w, bcLift hle pW.w, φU, φV,
    fp_snd _ _ hqU, fp_snd _ _ hqV, fp_snd _ _ hqW, oU, oV, sU, sV,
    bcLift_isPullback hle pU, bcLift_isPullback hle pV, bcLift_isPullback hle pW, cU, cV⟩

end LateralTheory.E.LeafInclDescendPf
end
end

