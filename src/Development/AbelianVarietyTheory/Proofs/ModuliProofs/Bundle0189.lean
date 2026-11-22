import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NatCastMemConj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

open CharZeroPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ} {J : Type}

theorem map_bas {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (v : Fin (2 * g) → ℤ) :
    u (bas v) = ∏ i, u (bas (Pi.single i 1)) ^ v i := by
  rw [LatticeTorsion.eq_prod_zpow ((Pi.basisFun ℤ (Fin (2 * g))).map bas) u hu]
  simp

theorem map_nsmul' {A : Type} [Group A] (u : D.La → A) (hu : ∀ x y, u (x + y) = u x * u y) (n : ℕ) (x : D.La) :
    u (n • x) = u x ^ n :=
  (MonoidHom.mk' (fun x : Multiplicative D.La => u x.toAdd) fun _ _ => hu _ _).map_pow (Multiplicative.ofAdd x) n

theorem existsUnique_coeff {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) {N : ℕ} (hN : 0 < N) (hk : ∀ x, u x = 1 ↔ ∃ y, x = N • y) (x : D.La) :
    ∃! c : Fin (2 * g) → ZMod N, ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u x := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨v, rfl⟩ := bas.surjective x
  have key : ∀ c : Fin (2 * g) → ZMod N,
      ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas v) ↔ c = fun i => (v i : ZMod N) := fun c => by
    have e₁ : ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas fun i => ((c i).val : ℤ)) := by
      rw [map_bas bas u hu]; simp only [zpow_natCast]
    have e₂ := hu (bas (v - fun i => ((c i).val : ℤ))) (bas fun i => ((c i).val : ℤ))
    rw [← map_add, sub_add_cancel] at e₂
    rw [e₁, e₂, right_eq_mul, hk]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, rfl⟩ := bas.surjective y
      rw [← map_nsmul] at hy
      funext i
      have := congrArg (fun z : ℤ => (z : ZMod N)) (congrFun (bas.injective hy) i)
      simp at this
      exact (sub_eq_zero.1 this).symm
    · intro hc
      have : ∀ i, ∃ w : ℤ, v i - ((c i).val : ℤ) = N * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp [hc])
      choose w hw using this
      refine ⟨bas w, ?_⟩
      rw [← map_nsmul]
      congr 1
      funext i
      simpa using hw i
  simp only [key]
  exact existsUnique_eq

theorem coe_rt (n N : ℕ) : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
  show ((2 : RZ H n N) : ℂ) * ((1 + H.rt0) / 2) - 1 = H.rt0
  have : ((2 : RZ H n N) : ℂ) = 2 := map_ofNat (RZ H n N).subtype 2
  rw [this]; ring

theorem rt_sq (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  push_cast
  rw [coe_rt, H.sqrt_neg_disc_sq]

theorem map_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (x : Sp K ⟶ S) (β : o →+* K)
    (h : x ≫ s = spMap β) (u : oˣ) (v : Kˣ) (hv : (v : K) = β u) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn v := by
  apply Units.ext
  show x.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) =
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom v
  have e := congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  have e' := congrArg (fun q : Sp K ⟶ Sp o => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) h
  rw [hv]
  exact e'.trans e.symm

set_option maxHeartbeats 800000 in

theorem exists_under (hL : Out.Laws) {n N : ℕ} (hN : 0 < N) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (hbas : IsSympBasis D bas) (b : TBase (RZ H n N) N) (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} [Flat s] {t : SAB H S} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)} (h : FullObj D s t lv) :
    ∃ T : TObj g N J b s, Under t lv a bas T ∧ IsPEL D a bas (RZ.rt H n N) T t := by
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, h.proper, t.semi.geomConnected⟩
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by
    have := bas.finrank_eq
    rw [datum_finrank_int, Module.finrank_fin_fun] at this
    omega
  have hdim : SmoothOfRelativeDimension g t.G.hom := by
    have := t.semi.smooth
    have := t.semi.geomConnected
    refine smoothOfRelativeDimension_of_generization _ g fun y => ?_
    obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization (t.G.hom ≫ s) y
    refine ⟨K, inferInstance, z, hz, fun m hm => ?_⟩
    refine (ObjDim.dim_eq_of_detCond D t.act (z ≫ t.G.hom) ?_
      (h.geom K _ β ((Category.assoc _ _ _).trans hβ)).1 hm).trans hg
    rw [← map_pow, rt_sq, map_neg, map_natCast]
  let pt : Fin (2 * g) → (Out.baseOver S ⟶ t.G) := fun i => toUnit _ ≫ lv (bas (Pi.single i 1))
  have hpt : ∀ i, pt i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← map_nsmul' lv h.add, h.ker, MonObj.comp_one]
  have hptx : ∀ {X : Scheme.{0}} (x : X ⟶ S) (i), toB x ≫ pt i = toUnit _ ≫ lv (bas (Pi.single i 1)) := fun x i => by
    rw [← Category.assoc, toUnit_unique (toB x ≫ toUnit _) (toUnit _)]
  have hu : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (RZ H n N))).inv.hom)
    rwa [map_natCast] at this
  have hζ : b.ζ ^ N = 1 := by
    apply Units.ext
    apply Subtype.val_injective
    exact (b.prim ℂ (RZ H n N).subtype).pow_eq_one
  let P : Out.PolAV S :=
    { A := t.G, isAb := hab, g := g, smoothDim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
      sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv }
  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  have hid : LBIso t.PP.L (t.PP.L.pull (Iso.refl t.G).hom.left) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ (𝟙 _) (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl t.PP.isLB)
  have hpl : ∀ i, (lv (bas (Pi.single i 1))).left ≫ (Iso.refl t.G).hom.left = (pt i).left := fun i => by
    have e : (toUnit (Out.baseOver S)).left = 𝟙 S := ObjPull.toUnit_left' _
    rw [Iso.refl_hom, Over.id_left, Category.comp_id, Over.comp_left, e]
    exact (Category.id_comp (X := S) _).symm
  refine ⟨{ A := t.G, ab := hab, dim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
            sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv, pt := pt, torsion := hpt,
            bij := torsion_basis_of_generization t.G N _ pt hab hN hu hpt fun p => ?_,
            pairing := fun i j => weilIs_of_generization hL P N _ _ _ hN hu (hpt i) (hpt j) ?_ fun p => ?_,
            act := fun j => t.act.act (a j), hom := fun j => t.act.hom _ },
    ⟨Iso.refl _, this, hid, fun j => by simp, hpl⟩,
    ⟨Iso.refl _, this, hid, fun j => by simp, fun K _ _ _ x β hx => ?_⟩⟩
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, -, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, inferInstance, z, hz, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := (I.onto N hN y).1 hy
    simp only [hptx, hI, Out.linComb, List.prod_ofFn]
    exact existsUnique_coeff bas (I.ev N) (I.add N) hN (I.ker N hN) x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, unitS, unitOn, ← map_pow, ← map_pow, hζ, map_one,
      map_one, one_zpow]
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, hIζ, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, z, hz, ?_⟩
    have hc : Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j) =
        unitOn (I.ζ N ^ Out.stdSymp g i j) := by
      rw [map_zpow, map_unitS s z β hβ b.ζ (I.ζ N) (by rw [hIζ, hb]), unitOn, unitOn, map_zpow]
    have e : Out.WeilIs t.G t.PP.L N (toB z ≫ pt i) (toB z ≫ pt j)
        (Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j)) := by
      rw [hc, hptx z i, hptx z j, hI, hI, ← hbas i j]
      exact I.isom N hN _ _
    exact e
  · obtain ⟨hd, I, hIζ, hI⟩ := h.geom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], fun i => ?_⟩
    have e : I.ev N (bas (Pi.single i 1)) ≫ 𝟙 t.G = toB x ≫ pt i := by rw [hptx, hI, Category.comp_id]
    exact e

theorem exists_level {n N : ℕ} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La}
    {b : TBase (RZ H n N) N} (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} {t : SAB H S} {T : TObj g N J b s} (h : IsPEL D a bas (RZ.rt H n N) T t) :
    ∃ lv : D.La → (𝟙_ (Over S) ⟶ t.G), Under t lv a bas T ∧ FullObj D s t lv := by
  obtain ⟨φ, hφ, hφL, hφa, hgeom⟩ := h
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (Category.id_comp _)
  let q : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.G) := fun i => j ≫ T.pt i ≫ φ.inv
  have hq : ∀ i, q i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← MonObj.pow_comp, T.torsion, MonObj.one_comp, MonObj.comp_one]
  let lv : D.La → (𝟙_ (Over S) ⟶ t.G) := fun x => ∏ i, q i ^ bas.symm x i
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => by
    simp only [lv, map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hlv : ∀ i, lv (bas (Pi.single i 1)) = q i := fun i => by
    simp only [lv, LinearEquiv.symm_apply_apply]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  obtain ⟨hab, hA, hK⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S T.A t.G _ _ T.L t.PP.L
    T.isLB t.PP.isLB T.ab (isGrpPullback_of_iso φ) hφL
  refine ⟨lv, ⟨φ, hφ, hφL, hφa, fun i => ?_⟩, hab.proper, hA T.ample, hK T.ktriv, hadd, fun x => ?_,
    fun K _ _ _ x β hx => ?_⟩
  · rw [hlv]
    show (𝟙 S ≫ (T.pt i).left ≫ φ.inv.left) ≫ _ = _
    rw [Category.assoc, Category.assoc, inv_hom_left]
    exact (Category.id_comp _).trans (Category.comp_id _)
  · rw [map_nsmul' lv hadd, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hq, one_zpow]
  · obtain ⟨hd, I, hIζ, hI⟩ := hgeom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], eq_of_basis bas (fun y => toUnit _ ≫ lv y) (I.ev N)
      (fun y y' => by rw [hadd, MonObj.comp_mul]) (I.add N) fun i => ?_⟩
    have e : toUnit (Over.mk x) ≫ j = toB x := Over.OverMorphism.ext
      ((Category.comp_id _).trans (ObjPull.toUnit_left' _))
    rw [hlv, ← Category.assoc, e, ← Category.assoc, Iso.comp_inv_eq]
    exact (hI i).symm

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : 0 < N) (h : N ∣ n ^ e) : ArBase (RZ H n N).subtype := by
  obtain ⟨l⟩ : Nonempty (Level H) := HostModel.instNonemptyLevel H
  exact ⟨BaseRing.isDedekindDomain_RZ { l with A := N, A_pos := hN } hn h, BaseRing.finiteType_RZ H n N,
    Subtype.val_injective⟩

end GlobalTheory.TripleTheta

namespace GlobalTheory

open TripleTheta CharZeroPts in

theorem exists_famCore_of_thetaFam : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  intro hL hL2 E _ _ _ H D n N' g J _ a bas b F τ hbas ha ⟨w, w', hw, hw'⟩ hb hP hsm hpq hn _ ⟨j, _, hj⟩
  have hN : 0 < N' ^ 2 := by rw [hj]; exact pow_pos (pow_pos hn.pos _) _
  have hbase : ArBase (RZ H n (N' ^ 2)).subtype := arBase_RZ H (e := j * 2) hn.pos hN (by rw [hj, pow_mul])
  obtain ⟨lev, hU, hF⟩ := exists_level hb hP
  refine ⟨lev, F.reduced, F.flat, F.qproj, SmoothOfRelativeDimension.smooth D.dim _, hF,
    fun S s t lv hS _ hs ho => ?_, fun k _ x t lv ν ν' hx hν hν' => ?_⟩
  · obtain ⟨T, hT, hTP⟩ := exists_under hL hN a bas hbas b hb ho
    obtain ⟨f, ⟨hf, hm⟩, huniq⟩ := F.rep S s T hS fun p => by
      obtain ⟨K, _, _, _, z, β, -, hz⟩ := exists_generization s p
      exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure (subset_closure ⟨K, inferInstance, z, ⟨_, rfl⟩,
        PELFrom.fromC_of_isPEL hL hL2 E H D g J a w w' bas hpq hbas hw hw' ha N' _ b _ _ (coe_rt n _) hbase S s T t hTP K z⟩)
    exact ⟨f, ⟨hf, sabMap_of_tmap hU hT hF.add ho.add ha hS ho.proper hm⟩,
      fun f' ⟨hf', ν, hν⟩ => huniq f' ⟨hf', tmap_of_sabMap hU hT ν hν⟩⟩
  · obtain ⟨T, hT⟩ := tObj_pull _ g _ J b _ _ F.s (x ≫ F.s) x F.univ rfl
    exact F.unram k x T hx hT (tmap_of_sabMap hU (under_of_tmap hU hT ν hν) ν' hν')

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteSurjectiveOfPoints
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckePoint GlobalTheory.CechPic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem splitPrime_iff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : IsSplitPrimeOff l p P ↔
    P.IsMaximal ∧ P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ P ∧ ¬ p ∣ l.M' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨h₂, h₂.coprime_of_ne (conj_isMaximal H P) (Ne.symm h₄), h₁, h₃, h₅⟩
  · rintro ⟨h₂, h₄, h₁, h₃, h₅⟩
    refine ⟨h₁, h₂, h₃, fun h => h₂.ne_top ?_, h₅⟩
    rw [← h₄, show P.map (H.bar : 𝓞 E →+* 𝓞 E) = P from h, sup_idem]

section Fibre

variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def ptAct {S : Scheme.{0}} (t : SAB H S) (T : Over S) (a : 𝓞 E) : (T ⟶ t.G) →* (T ⟶ t.G) :=
  haveI := t.act.hom a
  MonoidHom.mk' (fun x => x ≫ t.act.act a) fun x y => MonObj.mul_comp x y _

theorem isAct_ptAct {S : Scheme.{0}} (t : SAB H S) (T : Over S) : IsAct (ptAct t T) :=
  ⟨fun x => by show x ≫ _ = x; rw [t.act.one, Category.comp_id],
    fun a c x => by show x ≫ _ = (x ≫ _) ≫ _; rw [t.act.mul, Category.assoc],
    fun a c x => by show x ≫ _ = (x ≫ _) * (x ≫ _); rw [t.act.add, MonObj.comp_mul]⟩

abbrev ptWeil (t : SAB H (Sp k)) : ℕ → Pts t → Pts t → kˣ → Prop :=
  fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)

theorem ptWeil_one (t : SAB H (Sp k)) (n : ℕ) (x y : Pts t) : ptWeil t n x y 1 ↔ Out.WeilIs t.G t.PP.L n x y 1 :=
  iff_of_eq (congrArg (Out.WeilIs t.G t.PP.L n x y) unitOn_one)

theorem kerSet_eq (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) :
    kerSet (ptAct t _) (ptWeil t) p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ = heckeKernel t p P C₀ := by
  ext x
  constructor
  · rintro ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, fun c hc => (ptWeil_one t p _ _).1 (h₅ c hc)⟩
  · rintro ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, fun c hc => (ptWeil_one t p _ _).2 (h₅ c hc)⟩

abbrev objPol (o : Obj D l b s) : Out.PolAV (Sp k) :=
  polOf o.t o.proper o.ample o.ktriv (obj_isAbelianScheme_dim_rigidified_sym E H D l B b _ s o).2.1

theorem tate_facts [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) :
    Nonempty (TateIso D k (Pts o.t) (fun a x => ptAct o.t _ a x) (ptWeil o.t)) ∧ Uniq (ptWeil o.t) ∧
      ∀ p : ℕ, 0 < p → Nat.card {x : Pts o.t // x ^ p = 1} = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) := by
  obtain ⟨-, I, -⟩ := o.geom k (𝟙 _) (Spec.preimage s).hom (by simp [spMap])
  exact ⟨⟨I⟩, fun n z w c c' _ hz hw h h' =>
    (unitOn_bijective k).1 (((hL.weil _ (objPol o) n _).1 z w hz hw).unique h h'),
    fun p hp => (hL.mulN _ (objPol o) p hp).2.2.2.2 k (𝟙 _) (Nat.cast_ne_zero.2 hp.ne')⟩

theorem weil_sq (t : SAB H (Sp k)) (p : ℕ) (x y : Pts t) :
    ptWeil t (p * p) x y 1 ↔ Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) x y 1 := by
  rw [ptWeil_one, Nat.cast_mul, pow_two]

theorem card_tors (t : SAB H (Sp k)) (p : ℕ) :
    Nat.card (t.tors (𝟙_ _) (Ideal.span {(p : 𝓞 E)})) = Nat.card {x : Pts t // x ^ p = 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => (isAct_ptAct t _).kill_span_iff p x)

theorem card_inter_tors (t : SAB H (Sp k)) (p : ℕ) (C : Subgroup (Pts t)) :
    Nat.card ((C : Set (Pts t)) ∩ t.tors (𝟙_ _) (Ideal.span {(p : 𝓞 E)}) : Set (Pts t)) =
      Nat.card {x : Pts t // x ∈ C ∧ x ^ p = 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => and_congr_right' ((isAct_ptAct t _).kill_span_iff p x))

variable [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}
include hL

theorem exists_heckeKer_of_datum (h : IsSplitPrimeOff l p P) {i : ℕ} {C₀ : Subgroup (Pts o.t)}
    (h₀ : IsHeckeDatum o.t P i C₀) :
    ∃ C : Subgroup (Pts o.t), (C : Set (Pts o.t)) = heckeKernel o.t p P C₀ ∧ o.t.HeckeKer (𝟙_ _) D P p i C := by
  obtain ⟨hP, hco, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
  obtain ⟨⟨I⟩, hu, hc⟩ := tate_facts hL o
  have hf : Finite {x : Pts o.t // x ^ p = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc p hp.pos]; exact (pow_pos hp.pos _).ne')
  obtain ⟨C, e, c₁, c₂, c₃, c₄, c₅, c₆⟩ := exists_subgroup I hu (isAct_ptAct _ _) hco hp.pos hpP h₀.1 h₀.2.1 hf
  exact ⟨C, e.trans (kerSet_eq _ _ _ _), c₁, c₂, c₃, fun x hx y hy => (weil_sq _ _ _ _).1 (c₄ x hx y hy),
    c₅.trans (hc p hp.pos), by rw [card_tors, card_inter_tors, c₆, h₀.2.2.2]⟩

theorem heckeKer_iff (h : IsSplitPrimeOff l p P) (i : ℕ) (C : Subgroup (Pts o.t)) :
    o.t.HeckeKer (𝟙_ _) D P p i C ↔
      ∃ C₀, IsHeckeDatum o.t P i C₀ ∧ (C : Set (Pts o.t)) = heckeKernel o.t p P C₀ := by
  constructor
  · rintro ⟨c₁, -, c₃, c₄, c₅, c₆⟩
    obtain ⟨hP, hco, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
    obtain ⟨⟨I⟩, hu, hc⟩ := tate_facts hL o
    have hpos := pow_pos hp.pos (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))
    have hf : Finite {x : Pts o.t // x ^ p = 1} := Nat.finite_of_card_ne_zero (by rw [hc p hp.pos]; exact hpos.ne')
    obtain ⟨d₁, d₂, e⟩ := eq_kerSet I hu (isAct_ptAct _ _) hco hp.pos hpP hf C c₁ c₃
      (fun x hx y hy => (weil_sq _ _ _ _).2 (c₄ x hx y hy)) (c₅.trans (hc p hp.pos).symm)
    have hm := card_eq_tors_mul C p
    rw [card_tors, card_inter_tors, hc p hp.pos] at c₆
    rw [c₅] at hm
    have h₀ := mul_ne_zero_iff.1 (hm ▸ hpos.ne')
    exact ⟨_, ⟨d₁, d₂, Nat.finite_of_card_ne_zero h₀.2, mul_left_cancel₀ h₀.1 (hm.symm.trans c₆)⟩,
      e.trans (kerSet_eq _ _ _ _)⟩
  · rintro ⟨C₀, h₀, e⟩
    obtain ⟨C', e', h'⟩ := exists_heckeKer_of_datum hL o h h₀
    rwa [SetLike.coe_injective (e.trans e'.symm)]

end Fibre

section Isogeny

variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def IsIsogenyOnPoints (o o' : Obj D l b s) (p : ℕ) (C : Set (Pts o.t)) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.t.act.act a ≫ ψ = ψ ≫ o'.t.act.act a) ∧
  (∀ y : Pts o'.t, ∃ x, x ≫ ψ = y) ∧ (∀ x, x ≫ ψ = 1 ↔ x ∈ C) ∧
  (∀ (n : ℕ) (x x' : Pts o.t) (c : kˣ), n.Coprime p → Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) →
    Out.WeilIs o'.t.G o'.t.PP.L n (x ≫ ψ) (x' ≫ ψ) (unitOn (c ^ (p ^ 2)))) ∧
  ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a, o.eta (p' • a) ≫ ψ = o'.eta a ∧ o.etaA (p' • a) ≫ ψ = o'.etaA a

end Isogeny

section Transfer

variable {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} {k : Type} [Field k]
  {s : Sp k ⟶ Sp B}

theorem exists_fibre_equiv (u : Obj D l b sX) {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : Pts o.t ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      (∀ x, (ρ x).left = x.left ≫ m.cm.F) ∧
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c =>
      weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, hρ, m.cart.1.isoPullback_hom_snd, fun x => ?_,
    fun a x => Over.OverMorphism.ext ?_, fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'),
    fun a => Over.OverMorphism.ext ?_, fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

def SamePoints {u : Obj D l b sX} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) (C' : Set (Pts o.t))
    (C : Set (Over.mk y ⟶ u.t.G)) : Prop :=
  ∀ (x : Pts o.t) (x₀ : Over.mk y ⟶ u.t.G), x₀.left = x.left ≫ m.cm.F → (x ∈ C' ↔ x₀ ∈ C)

theorem heckeKer_transfer {u : Obj D l b sX} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y)
    {C' : Subgroup (Pts o.t)} {C : Subgroup (Over.mk y ⟶ u.t.G)} (h : SamePoints m C' C) (P : Ideal (𝓞 E))
    (p i : ℕ) : u.t.HeckeKer (Over.mk y) D P p i C ↔ o.t.HeckeKer (𝟙_ _) D P p i C' := by
  obtain ⟨ρ, -, e₀, -, -, e₃, e₄, -⟩ := exists_fibre_equiv u m
  have mem : ∀ x, x ∈ C' ↔ ρ x ∈ C := fun x => h x _ (e₀ x)
  have tor : ∀ J x, x ∈ o.t.tors (𝟙_ _) J ↔ ρ x ∈ u.t.tors (Over.mk y) J := fun J x =>
    forall₂_congr fun a _ => by rw [← e₃, map_eq_one_iff _ ρ.injective]
  have wl : ∀ (n : ℤ) x x', Out.WeilIs o.t.G o.t.PP.L n x x' 1 ↔ Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') 1 :=
    fun n x x' => (iff_of_eq (congrArg (Out.WeilIs o.t.G o.t.PP.L n x x') unitOn_one)).symm.trans ((e₄ n x x' 1).trans
      (iff_of_eq (congrArg (Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x')) unitOn_one)))
  have c₁ : Nat.card C' = Nat.card C := Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)
  have c₂ : ∀ J, Nat.card (o.t.tors (𝟙_ _) J) = Nat.card (u.t.tors (Over.mk y) J) := fun J =>
    Nat.card_congr (ρ.toEquiv.subtypeEquiv (tor J))
  have c₃ : ∀ J, Nat.card ((C' : Set (Pts o.t)) ∩ o.t.tors (𝟙_ _) J : Set (Pts o.t)) =
      Nat.card ((C : Set (Over.mk y ⟶ u.t.G)) ∩ u.t.tors (Over.mk y) J : Set (Over.mk y ⟶ u.t.G)) := fun J =>
    Nat.card_congr (ρ.toEquiv.subtypeEquiv fun x => and_congr (mem x) (tor J x))
  unfold SAB.HeckeKer
  rw [c₁, c₂, c₃]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl)))
  · rw [ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (mem x).symm (forall_congr' fun a => by rw [← e₃, mem])
  · refine forall₂_congr fun J _ => ?_
    rw [Set.subset_def, Set.subset_def, ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (tor J x).symm (mem x).symm
  · rw [Set.subset_def, Set.subset_def, ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (mem x).symm (tor _ x).symm
  · rw [ρ.surjective.forall]
    refine forall_congr' fun x => imp_congr (mem x).symm ?_
    rw [ρ.surjective.forall]
    exact forall_congr' fun x' => imp_congr (mem x').symm (wl _ x x').symm

def IsIsogenyOnFibres (u : Obj D l b sX) (y y'' : Sp k ⟶ X) (p : ℕ) (C : Subgroup (Over.mk y ⟶ u.t.G)) : Prop :=
  ∃ (ψ : pullback u.t.G.hom y ⟶ pullback u.t.G.hom y'') (ψp : (Over.mk y ⟶ u.t.G) →* (Over.mk y'' ⟶ u.t.G)),
    ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
    (∀ a x, ψp (x ≫ u.t.act.act a) = ψp x ≫ u.t.act.act a) ∧
    Function.Surjective ψp ∧ ψp.ker = C ∧
    (∀ (n : ℕ) (x x' : Over.mk y ⟶ u.t.G) (c : kˣ), n.Coprime p →
      Out.WeilIs u.t.G u.t.PP.L n x x' (unitOn c) →
      Out.WeilIs u.t.G u.t.PP.L n (ψp x) (ψp x') (unitOn (c ^ (p ^ 2)))) ∧
    ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
      ψp (toUnit _ ≫ u.eta (p' • a)) = toUnit _ ≫ u.eta a ∧ ψp (toUnit _ ≫ u.etaA (p' • a)) = toUnit _ ≫ u.etaA a

end Transfer

section Statements

variable {k : Type} [Field k]

theorem exists_fibre_obj (Xo : Moduli D l) (y y' : Sp k ⟶ Xo.X) (h : y' ≫ Xo.s = y ≫ Xo.s) :
    ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') :=
  obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl
    (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ

def HeckePointsAt (Xo : Moduli D l) : Prop :=
  ∀ (P : Ideal (𝓞 E)) (p i : ℕ), P.IsMaximal → P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ P →
    ¬ p ∣ l.M' → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X)
      (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Xo.univ.t.HeckeKer (Over.mk y) D P p i C →
      ∃! y'' : Sp k ⟶ Xo.X, y'' ≫ Xo.s = y ≫ Xo.s ∧ IsIsogenyOnFibres Xo.univ y y'' p C

end Statements

end GlobalTheory.HeckeCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfPolarisedAtEveryPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_polarised_at_every_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → (∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ t.G.left), IsPullback φ B.hom t.G.hom y → IsProjOver B.hom) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L) → Out.RelAmple t.G t.PP.L := by
  first | exact @GlobalTheory.AmpleGlobal.relAmple_of_polarised_at_points | exact GlobalTheory.AmpleGlobal.relAmple_of_polarised_at_points | (intros; apply GlobalTheory.AmpleGlobal.relAmple_of_polarised_at_points <;> assumption)
end

