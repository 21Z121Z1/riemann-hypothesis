import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3176
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3165
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertySemiAbelianFlatBaseChangeDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.GaussBC

theorem gp_comp_eq_spMap_cst : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R),
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  intro X _ R _ p
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

theorem cst_regAt_zeroAt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X), p x = closedPoint R → ∀ r : R, GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  intro R _ _ X _ p x hx r
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.GaussBC

namespace GlobalTheory.Desc.GaussBC

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

theorem zero_mem_spanBy (T : Set F₁) : (0 : F₁) ∈ spanBy c T := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy {T : Set F₁} {v w : F₁} (hv : v ∈ spanBy c T) (hw : w ∈ spanBy c T) :
    v + w ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

theorem mul_mem_spanBy {T : Set F₁} {v : F₁} (hv : v ∈ spanBy c T) (d : R₁) : c d * v ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  exact ⟨n, fun i => d * r i, t, ht, by rw [Finset.mul_sum]; simp only [map_mul, _root_.mul_assoc]⟩

theorem spanBy_induction {T : Set F₁} (p : F₁ → Prop) (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hmul : ∀ r, ∀ t ∈ T, p (c r * t)) : ∀ v ∈ spanBy c T, p v := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact Finset.sum_induction _ p hadd h0 fun i _ => hmul (r i) (t i) (ht i)

end Span

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem gauss_baseChange : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → GaussAt (GlobalTheory.Desc.cst H'.hom) (maximalIdeal D) θ (regSet y) (regSet y') ∧ θ ⁻¹' (regSet y') = regSet y ∧ LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hmT := hϖ.maximalIdeal_eq
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]

  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_eq_spMap_cst H.left T H.hom
    have e2 := gp_comp_eq_spMap_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  set c := cst H'.hom with hc
  set P := c (a ϖ) with hPdef
  have hP : P = θ (cst H.hom ϖ) := by rw [hPdef, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply]
  obtain ⟨hϖ0, hfac⟩ := GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser T H hH y hy hdy ϖ hmT
  have hP0 : P ≠ 0 := by rw [hP]; exact (map_ne_zero θ).2 hϖ0
  have hPz : GlobalTheory.Cartier.ZeroAt y' P :=
    (cst_regAt_zeroAt D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_regAt_zeroAt D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_regAt_zeroAt T H.left H.hom y hy t).1
  have hmod := GlobalTheory.T.thetaSpan_vanishing_eq_uniformiser_mul T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy' ϖ hmT
  set S := spanBy c (θ '' regSet y) with hS
  have hSreg : ∀ v ∈ S, GlobalTheory.Cartier.RegAt y' v :=
    spanBy_induction c _ (regAt_zero y') (fun _ _ h h' => h.add h') (by
      rintro r _ ⟨t, ht, rfl⟩; exact (hcreg r).mul (hreg t ht))
  have hSP : ∀ v ∈ S, ∀ N : ℕ, P ^ N * v ∈ S := by
    intro v hv N
    induction N with
    | zero => simpa using hv
    | succ N ih => rw [pow_succ', _root_.mul_assoc]; exact mul_mem_spanBy c ih _

  have hQ : ∀ v ∈ spanBy c (Set.range θ), ∃ N : ℕ, P ^ N * v ∈ S := by
    refine spanBy_induction c _ ⟨0, by simpa using zero_mem_spanBy c _⟩ ?_ ?_
    · rintro v w ⟨N, hN⟩ ⟨M, hM⟩
      refine ⟨N + M, ?_⟩
      have := add_mem_spanBy c (hSP _ hN M) (hSP _ hM N)
      convert this using 1; ring
    · rintro r _ ⟨u, rfl⟩
      by_cases hu : u = 0
      · exact ⟨0, by simpa [hu] using zero_mem_spanBy c _⟩
      obtain ⟨k, w, hw, rfl⟩ := hfac u hu
      refine ⟨(-k).toNat, ?_⟩
      have hk : ((-k).toNat : ℤ) + k = ((((-k).toNat : ℤ) + k).toNat : ℤ) :=
        (Int.toNat_of_nonneg (by omega)).symm
      have e : P ^ (-k).toNat * (c r * θ (cst H.hom ϖ ^ k * w)) =
          c r * θ (cst H.hom ϖ ^ (((-k).toNat : ℤ) + k).toNat * w) := by
        rw [hP, map_mul, map_mul, map_zpow₀, map_pow]
        have hq : θ (cst H.hom ϖ) ^ (-k).toNat * θ (cst H.hom ϖ) ^ k =
            θ (cst H.hom ϖ) ^ (((-k).toNat : ℤ) + k).toNat := by
          rw [← zpow_natCast, ← zpow_natCast _ (((-k).toNat : ℤ) + k).toNat, ← hk,
            zpow_add₀ ((map_ne_zero θ).2 hϖ0)]
        linear_combination (c r * θ w) * hq
      rw [e]
      exact mul_mem_spanBy c (subset_spanBy c (θ '' regSet y) (Set.mem_image_of_mem θ
        (show _ ∈ regSet y from (regAt_pow (hc0reg ϖ) _).mul hw.regAt))) r

  have hB : ∀ (N : ℕ) (t : H'.left.functionField), GlobalTheory.Cartier.RegAt y' t → P ^ N * t ∈ S → t ∈ S := by
    intro N
    induction N with
    | zero => intro t _ h; simpa using h
    | succ N ih =>
      intro t ht h
      rw [pow_succ', _root_.mul_assoc] at h
      obtain ⟨z₁, hz₁, e⟩ := hmod _ h (hPz.mul ((regAt_pow hPz.regAt N).mul ht))
      have : P ^ N * t = z₁ := mul_left_cancel₀ hP0 e
      exact ih t ht (this ▸ hz₁)
  refine ⟨fun v ⟨d, hd0, hdv⟩ => ⟨fun hv => ?_, fun ⟨s, hs, hsv⟩ => ?_⟩, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hQ _ hdv
    have hirr : Irreducible (a ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmD
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr
    have e : P ^ (N + n) * v = c (↑u⁻¹ : D) * (P ^ N * (c (↑u * a ϖ ^ n) * v)) := by
      rw [hPdef, map_mul, map_pow]
      have : c (↑u⁻¹ : D) * c ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(c (a ϖ) ^ (N + n) * v)) * this
    refine ⟨1, fun h => (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [map_one, _root_.one_mul]
    exact hB (N + n) v hv (e ▸ mul_mem_spanBy c hN _)
  · obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hs
    have e : v = c (↑u⁻¹ : D) * (c ↑u * v) := by rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    rw [e]; exact (hcreg _).mul (hSreg _ hsv)
  · ext u
    refine ⟨fun h => ?_, fun h => hreg u h⟩
    change GlobalTheory.Cartier.RegAt y' (θ u) at h
    change GlobalTheory.Cartier.RegAt y u
    by_cases hu : u = 0
    · rw [hu]; exact regAt_zero y
    obtain ⟨k, w, hw, rfl⟩ := hfac u hu
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [zpow_natCast]; exact (regAt_pow (hc0reg ϖ) k).mul hw.regAt
    · exfalso
      have hw0 := hw.ne_zero
      obtain ⟨hw1, hw2⟩ := (unitAt_iff hw0).1 hw
      have hθw : GlobalTheory.Cartier.UnitAt y' (θ w) :=
        (unitAt_iff ((map_ne_zero θ).2 hw0)).2 ⟨hreg w hw1, by rw [← map_inv₀]; exact hreg _ hw2⟩
      have hm1 : ((-(k + 1)).toNat : ℤ) = -(k + 1) := Int.toNat_of_nonneg (by omega)
      have e : P⁻¹ = θ (cst H.hom ϖ ^ k * w) * (θ w)⁻¹ * P ^ (-(k + 1)).toNat := by
        rw [map_mul, map_zpow₀, ← hP, _root_.mul_assoc (P ^ k), mul_inv_cancel₀ ((map_ne_zero θ).2 hw0),
          _root_.mul_one, ← zpow_natCast, hm1, ← zpow_add₀ hP0, show k + -(k + 1) = -1 by ring, zpow_neg_one]
      have hPi : GlobalTheory.Cartier.RegAt y' P⁻¹ := by
        rw [e]; exact (h.mul hθw.inv.regAt).mul (regAt_pow hPz.regAt _)
      exact (zeroAt_iff.1 hPz).2 ((unitAt_iff hP0).2 ⟨hPz.regAt, hPi⟩)
  · exact GlobalTheory.T.linearlyDisjoint_functionField_of_flat_baseChange T D a ha H H' π θ hpb ⟨_, hff.choose_spec⟩

end GlobalTheory.Desc.GaussBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreProjEmbeddingFixedGroupConnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibConn

theorem lfac {X P : Scheme.{0}} (j : X ⟶ P) [IsImmersion j] (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ P)
    (h : Set.range ν ⊆ Set.range j) : ∃ y₀ : Sp Ω ⟶ X, y₀ ≫ j = ν := by
  have h1 : Set.range ν ⊆ Set.range j.coborderRange.ι := by
    refine h.trans ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨j.liftCoborder x, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι]⟩
  let ν' := IsOpenImmersion.lift j.coborderRange.ι ν h1
  have hν' : ν' ≫ j.coborderRange.ι = ν := IsOpenImmersion.lift_fac _ _ _
  have h2 : Set.range ν' ⊆ Set.range j.liftCoborder := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := h ⟨q, rfl⟩
    refine ⟨x, j.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hx, ← Scheme.Hom.comp_apply, hν']
  haveI : Surjective (pullback.snd j.liftCoborder ν') := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h2 ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd j.liftCoborder ν')
  have key : pullback.fst j.liftCoborder ν' ≫ j = pullback.snd j.liftCoborder ν' ≫ ν := by
    have := congrArg (· ≫ j.coborderRange.ι) (pullback.condition (f := j.liftCoborder) (g := ν'))
    simp only [Category.assoc, Scheme.Hom.liftCoborder_ι, hν'] at this
    exact this
  refine ⟨inv (pullback.snd j.liftCoborder ν') ≫ pullback.fst j.liftCoborder ν', ?_⟩
  rw [Category.assoc, key, IsIso.inv_hom_id_assoc]

theorem lsurj {X Y W Z : Scheme.{0}} (l : W ⟶ X) (f : X ⟶ Y) (ν : Z ⟶ Y)
    (h : ∀ z : (pullback f ν : Scheme.{0}), pullback.fst f ν z ∈ Set.range l)
    (hc : ConnectedSpace (pullback (l ≫ f) ν : Scheme.{0})) : ConnectedSpace (pullback f ν : Scheme.{0}) := by
  haveI : ConnectedSpace (pullback l (pullback.fst f ν) : Scheme.{0}) :=
    (pullbackRightPullbackFstIso f ν l).hom.homeomorph.connectedSpace_iff.2 hc
  refine Function.Surjective.connectedSpace (f := pullback.snd l (pullback.fst f ν)) ?_
    (pullback.snd l (pullback.fst f ν)).continuous
  intro z
  obtain ⟨w, hw⟩ := h z
  obtain ⟨d, -, hd⟩ := Scheme.Pullback.exists_preimage_pullback w z hw
  exact ⟨d, hd⟩

theorem liso {W Y T P Z B : Scheme.{0}} (a : Y ⟶ B) (k : T ⟶ B) (e : W ⟶ pullback a k) [IsIso e]
    (j : Y ⟶ P) [Mono j] (y₀ : Z ⟶ Y) (hc : ConnectedSpace (pullback (y₀ ≫ a) k : Scheme.{0})) :
    ConnectedSpace (pullback (e ≫ pullback.fst a k ≫ j) (y₀ ≫ j) : Scheme.{0}) := by
  set F := e ≫ pullback.fst a k ≫ j with hF
  set G := y₀ ≫ j with hG
  have c0 : pullback.fst F G ≫ e ≫ pullback.fst a k = pullback.snd F G ≫ y₀ := by
    rw [← cancel_mono j]
    have := pullback.condition (f := F) (g := G)
    simp only [hF, hG, Category.assoc] at this ⊢
    exact this
  have c1 : (pullback.fst (y₀ ≫ a) k ≫ y₀) ≫ a = pullback.snd (y₀ ≫ a) k ≫ k := by
    rw [Category.assoc]; exact pullback.condition
  let m₀ : pullback (y₀ ≫ a) k ⟶ pullback a k := pullback.lift (pullback.fst _ _ ≫ y₀) (pullback.snd _ _) c1
  have c2 : (m₀ ≫ inv e) ≫ F = pullback.fst (y₀ ≫ a) k ≫ G := by
    simp only [hF, hG, m₀, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  let m : pullback (y₀ ≫ a) k ⟶ pullback F G := pullback.lift (m₀ ≫ inv e) (pullback.fst _ _) c2
  have c3 : pullback.snd F G ≫ y₀ ≫ a = (pullback.fst F G ≫ e ≫ pullback.snd a k) ≫ k := by
    rw [← Category.assoc, ← c0]
    simp only [Category.assoc, pullback.condition]
  let n : pullback F G ⟶ pullback (y₀ ≫ a) k := pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ e ≫ pullback.snd a k) c3
  let φ : pullback (y₀ ≫ a) k ≅ pullback F G :=
    { hom := m, inv := n
      hom_inv_id := by
        apply pullback.hom_ext
        · simp only [m, n, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
        · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc,
            Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [← cancel_mono e]
          apply pullback.hom_ext
          · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, IsIso.inv_hom_id_assoc,
              Category.id_comp]
            exact c0.symm
          · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc,
              Category.id_comp]
        · simp only [m, n, Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp] }
  haveI : IsIso φ.hom := Iso.isIso_hom φ
  exact φ.hom.homeomorph.connectedSpace_iff.1 hc

theorem lred {X Y Z W : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] (hs : Function.Surjective i)
    (s : Y ⟶ W) (h : Z ⟶ W) (hc : ConnectedSpace (pullback h s : Scheme.{0})) :
    ConnectedSpace (pullback h (i ≫ s) : Scheme.{0}) := by
  haveI : Surjective i := ⟨hs⟩
  let q := pullback.fst (pullback.snd h s) i
  have hq : Function.Surjective q := (inferInstance : Surjective q).surj
  haveI : Nonempty (pullback (pullback.snd h s) i : Scheme.{0}) :=
    ⟨(hq (Nonempty.some inferInstance)).choose⟩
  haveI : ConnectedSpace (pullback (pullback.snd h s) i : Scheme.{0}) := by
    refine connectedSpace_iff_univ.2 ⟨Set.univ_nonempty, ?_⟩
    refine (q.isClosedEmbedding.isInducing.isPreconnected_image).1 ?_
    rw [Set.image_univ, hq.range_eq]
    exact isPreconnected_univ
  exact (pullbackLeftPullbackSndIso h s i).hom.homeomorph.connectedSpace_iff.1 this

theorem fib_conn : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G'), (∀ (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback π (spMap (κ.comp (residue R))) : Scheme.{0})) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ PSpace R E.N), (∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) → ConnectedSpace (pullback E.f ν : Scheme.{0}) := by
  intro R _ _ _ S π hπ G' _ hG E hconn Ω _ _ ν hex
  obtain ⟨g, hg, p, hp⟩ := hex
  obtain ⟨y, hy⟩ := (GlobalTheory.Mum.Emb.range_closed R S π G' E).1 g hg
  haveI := E.imm
  have hrange : Set.range ν ⊆ Set.range E.j := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p, hp, hy]
    exact ⟨y, rfl⟩
  obtain ⟨y₀, hy₀⟩ := lfac E.j Ω ν hrange
  let κ₀ : ResidueField R →+* Ω := (Spec.preimage (y₀ ≫ E.Y.hom)).hom
  have hκ₀ : y₀ ≫ E.Y.hom = spMap κ₀ := by
    simp [κ₀, spMap]
  haveI := hπ
  let ρ := spMap (residue R)
  let S₀ := pullback π ρ
  haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π ρ)
  let T := S₀.nilradical.subscheme
  let i : T ⟶ S₀ := S₀.nilradical.subschemeι
  haveI : IsReduced T := GlobalTheory.RedFibreField.isReduced_nilradical_subscheme _
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian i
  have hi : Function.Surjective i := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
    rfl
  let t := i ≫ pullback.fst π ρ
  let kk := i ≫ pullback.snd π ρ
  obtain ⟨e, l, -, hl1, hl2⟩ := GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t kk inferInstance inferInstance
    (by show i ≫ pullback.fst π ρ ≫ π = (i ≫ pullback.snd π ρ) ≫ ρ; rw [pullback.condition, Category.assoc])
  apply lsurj l E.f ν
  · intro z
    have h1 : E.f (pullback.fst E.f ν z) = ν (pullback.snd E.f ν z) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 : ν (pullback.snd E.f ν z) = E.f g := by rw [Subsingleton.elim (pullback.snd E.f ν z) p, hp]
    have h4 : ∀ b : E.H.toScheme, PSpace.str R E.N (E.f b) = π (G'.hom (E.H.ι b)) := fun b => by
      rw [← Scheme.Hom.comp_apply, E.f_over]
      rfl
    have h2 : π (G'.hom (E.H.ι (pullback.fst E.f ν z))) = closedPoint R := by
      rw [← h4, h1, h3, h4, hg]
    have h5 : G'.hom (E.H.ι (pullback.fst E.f ν z)) ∈ Set.range (pullback.fst π ρ) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨closedPoint (ResidueField R), (IsLocalRing.comap_closedPoint (residue R)).trans h2.symm⟩
    obtain ⟨w, hw⟩ := h5
    obtain ⟨u, rfl⟩ := hi w
    obtain ⟨d, hd1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := t)
      (E.H.ι (pullback.fst E.f ν z)) u hw.symm
    refine ⟨d, E.H.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hl1, hd1]
  · rw [hl2, ← hy₀]
    apply liso E.Y.hom kk e.hom E.j y₀
    rw [hκ₀]
    apply lred i hi
    have hc := hconn Ω κ₀
    have hcomp : spMap (κ₀.comp (residue R)) = spMap κ₀ ≫ ρ := by
      simp only [ρ, spMap, ← Spec.map_comp]
      rfl
    rw [hcomp] at hc
    exact ((pullbackLeftPullbackSndIso π ρ (spMap κ₀)).symm ≪≫ pullbackSymmetry _ _).hom.homeomorph.connectedSpace_iff.1 hc

end GlobalTheory.Mum.FibConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliMapDescendsGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.MapDesc

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def objMapCongr {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {f g : S' ⟶ S} (m : ObjMap o' o f) (h : f = g) : ObjMap o' o g := h ▸ m

end GlobalTheory.UPel.HT.MapDesc

open GlobalTheory.UPel.HT.MapDesc GlobalTheory.UPel.HT.MapComp in

theorem GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
  (S S₁ Y : Scheme.{0}) (t : S ⟶ Sp R) (sY : Y ⟶ Sp R) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga]
  (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (o : Obj b N t) (o' : Obj b N (π₁ ≫ t)) (u : Obj b N sY),
  3 ≤ N → N.Coprime p → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → ObjMap o' o π₁ → ObjMap o' u (π₁ ≫ f) →
  Nonempty (ObjMap o u f) := by
  intro p _ D R _ b N S S₁ Y t sY π₁ Ga _ ρ₁ f o o' u hN hNp hG m₁ m₂
  have uniq : ∀ {T T' : Scheme.{0}} {sT : T ⟶ Sp R} {sT' : T' ⟶ Sp R} {x : Obj b N sT} {y : Obj b N sT'}
      {g g' : T ⟶ T'} (_ : g = g') (n : ObjMap x y g) (n' : ObjMap x y g'), n.φ = n'.φ := by
    rintro T T' sT sT' x y g g' rfl n n'
    exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique p D R b N hN hNp T' T sT' sT x y g n n'
  have hw : ∀ a, m₁.φ ≫ o.A.hom = (o'.A.hom ≫ ρ₁ a) ≫ π₁ := fun a => by
    rw [Category.assoc, hG.inv a]; exact m₁.cart.1.w
  let σ : Ga → (o'.A.left ⟶ o'.A.left) := fun a => m₁.cart.1.lift m₁.φ (o'.A.hom ≫ ρ₁ a) (hw a)
  have hσ₁ : ∀ a, σ a ≫ m₁.φ = m₁.φ := fun a => m₁.cart.1.lift_fst _ _ _
  have hσ₂ : ∀ a, σ a ≫ o'.A.hom = o'.A.hom ≫ ρ₁ a := fun a => m₁.cart.1.lift_snd _ _ _
  have hG' : GlobalTheory.ZM.IsGaloisCover Ga σ m₁.φ := hG.of_isPullback m₁.cart.1.flip hσ₂ hσ₁
  have hinv : ∀ a, σ a ≫ m₂.φ = m₂.φ := fun a => by
    obtain ⟨n⟩ := MapComp.cancel (f := ρ₁ a) (g := π₁) (objMapCongr m₁ (hG.inv a).symm) m₁
    have hn₁ : n.φ ≫ m₁.φ = m₁.φ := uniq (hG.inv a) (MapComp.comp n m₁) m₁
    have hn₂ : n.φ ≫ o'.A.hom = o'.A.hom ≫ ρ₁ a := n.cart.1.w
    have hnσ : n.φ = σ a := m₁.cart.1.hom_ext (by rw [hn₁, hσ₁]) (by rw [hn₂, hσ₂])
    rw [← hnσ]
    exact uniq (by rw [← Category.assoc, hG.inv a]) (MapComp.comp n m₂) m₂
  obtain ⟨φ, hφ, -⟩ := hG'.existsUnique_desc m₂.φ hinv
  have : Epi m₁.φ := by
    have := hG'.etale; have := hG'.onto
    exact Flat.epi_of_flat_of_surjective _
  have : Epi π₁ := by
    have := hG.etale; have := hG.onto
    exact Flat.epi_of_flat_of_surjective _
  have cart : IsGrpPullback o.A u.A f φ :=
    GlobalTheory.T.isGrpPullback_descent_along_galoisCover S S₁ Y π₁ Ga ρ₁ f o'.A o.A u.A m₁.φ m₂.φ φ hG m₁.cart m₂.cart hφ
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare cart.1.w
  have sq₂ : IsSquare m₂.φ (m₁.φ₂ ≫ φ₂) := by rw [← hφ]; exact MapComp.isSquare_comp m₁.sq sq
  have e₂ : m₂.φ₂ = m₁.φ₂ ≫ φ₂ := MapComp.isSquare_unique m₂.sq sq₂
  have hA₂ : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab
  have := hA₂.comm
  obtain ⟨r, hr⟩ : GlobalTheory.AbLaw.Triv (o.P.pull (eSec (G2 o.A))) :=
    GlobalTheory.AbLaw.CubeOpen.triv_comp (eSec o.A) (GlobalTheory.SquareDescent.eSec_lift_one o.A) o.rig₁
  obtain ⟨r', hr'⟩ : GlobalTheory.AbLaw.Triv (u.P.pull (eSec (G2 u.A))) :=
    GlobalTheory.AbLaw.CubeOpen.triv_comp (eSec u.A) (GlobalTheory.SquareDescent.eSec_lift_one u.A) u.rig₁
  let PA : RigLB (G2 o.A) := ⟨o.P, r, o.isLB, hr⟩
  let PB : RigLB (G2 u.A) := ⟨u.P, r', u.isLB, hr'⟩
  have c₁ : IsGrpPullback (G2 o'.A) (G2 o.A) π₁ m₁.φ₂ :=
    GlobalTheory.ShearLift.isGrpPullback_tensor m₁.cart m₁.cart m₁.sq.1 m₁.sq.2
  have c₂ : IsGrpPullback (G2 o.A) (G2 u.A) f φ₂ := GlobalTheory.ShearLift.isGrpPullback_tensor cart cart sq.1 sq.2
  have pol₂ : LBIso o'.P (u.P.pull (m₁.φ₂ ≫ φ₂)) := by rw [← e₂]; exact m₂.pol
  have pol : LBIso o.P (u.P.pull φ₂) :=
    GlobalTheory.T.rigidLineBundleIso_descent_along_galoisCover S S₁ Y π₁ Ga ρ₁ f (G2 o'.A) (G2 o.A) (G2 u.A) m₁.φ₂ φ₂ PA PB o'.P hA₂ hG c₁ c₂ o'.isLB m₁.pol pol₂
  refine ⟨{ φ := φ, φ₂ := φ₂, cart := cart, sq := sq, act := fun c => ?_, pol := pol, eta := fun y => ?_ }⟩
  · rw [← cancel_epi m₁.φ, ← Category.assoc, ← m₁.act c, Category.assoc, hφ, m₂.act c, ← hφ, Category.assoc]
  · rw [← cancel_epi π₁, ← Category.assoc, ← m₁.eta y, Category.assoc, hφ, m₂.eta y, Category.assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCoefficientsCongruenceScaled
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coefficients_congruence_scaled : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ v : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 g₂ : 𝟙_ (Over S) ⟶ G2 o.A)) v → v = 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom) | (exact GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeightStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p), gdeg (up L u) D = gdeg L D := by
  first | exact @GlobalTheory.GdegMetric.gdeg_up | exact GlobalTheory.GdegMetric.gdeg_up | (intros; apply GlobalTheory.GdegMetric.gdeg_up <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueDerivativesViaJets
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

theorem GlobalTheory.HilbFam.eValue_derivs : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I) (Ch : ℍ → ℂ), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * ∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), ((∏ j, rco (2 * s) (κ (e.symm j)) (μ j) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ j, (κ (e.symm j) - μ j)) * hfun (2 * s) L μ Ch τ := by
  intro hE E _ _ _ I _ _ φ e θ τ Λ L n s N g κ u Ch hf hs hN hL hφ hθ hn hLΛ hD hu
  have h1 := GlobalTheory.T.deformed_lattice_sum_derivatives_eq_eisenstein_jets hE E I φ e θ τ Λ L n s N g κ u hf hs hN hL hφ hθ hn hLΛ hD hu
  have h2 := GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion hE (FR E) hf s N L hs hN hL τ (fun j ↦ κ (e.symm j)) Ch
  have hsum : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
  rw [hsum] at h2
  unfold wt at h2
  rw [hsum] at h2
  rw [h1, ← h2]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormCombinationEqZeroIndependentStatement
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousFormCombination_eq_zero_independent : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ) (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  first | exact @GlobalTheory.HSAmp.homogComb_eq_zero | exact GlobalTheory.HSAmp.homogComb_eq_zero | (intros; apply GlobalTheory.HSAmp.homogComb_eq_zero <;> assumption)
end

