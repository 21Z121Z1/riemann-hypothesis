import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTate

theorem torsion_card (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) {n : ℕ} (hn : 0 < n) {K : Type} [Field K]
    [IsSepClosed K] (t : Sp K ⟶ Sp ℂ) (z : Sp K) :
    Finite {x : Over.mk t ⟶ A // x ^ n = 1} ∧
      Nat.card {x : Over.mk t ⟶ A // x ^ n = 1} = (torsion A n).hom.finrank (t z) := by
  have hu : IsUnit (n : Γ(Sp ℂ, ⊤)) := GlobalTheory.SepClosedTorsion.isUnit_natCast_top (by exact_mod_cast hn.ne')
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hu
  let e2 : (Over.mk t ⟶ torsion A n) ≃ {x : Sp K ⟶ (torsion A n).left // x ≫ (torsion A n).hom = t} :=
    { toFun := fun y => ⟨y.left, Over.w y⟩
      invFun := fun x => Over.homMk x.1 x.2
      left_inv := fun y => Over.OverMorphism.ext rfl
      right_inv := fun x => rfl }
  let e : {x : Over.mk t ⟶ A // x ^ n = 1} ≃ {x : Sp K ⟶ (torsion A n).left // x ≫ (torsion A n).hom = t} :=
    (GlobalTheory.TorsionUnram.torsionEquiv A n (Over.mk t)).symm.trans e2
  obtain ⟨h1, h2⟩ := GlobalTheory.FinEt.card_points_eq_finrank (torsion A n).hom t z
  exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans h2⟩

def toC {k : Type} [Field k] (j : ℂ →+* k) : Over.mk (spMap j) ⟶ Over.mk (𝟙 (Sp ℂ)) :=
  Over.homMk (spMap j) (Category.comp_id _)

theorem toC_left {k : Type} [Field k] (j : ℂ →+* k) : (toC j).left = spMap j := rfl

theorem pre_injective {k : Type} [Field k] (j : ℂ →+* k) (A : Over (Sp ℂ)) [GrpObj A] :
    Function.Injective (preHom (G := A) (toC j)) := by
  intro x y h
  have hf : Flat (spMap j) := by
    rw [Flat.SpecMap_iff]
    letI := j.toAlgebra
    exact (inferInstance : Module.Flat ℂ k)
  have hs : Surjective (spMap j) := ⟨fun q => ⟨default, Subsingleton.elim (α := PrimeSpectrum ℂ) _ _⟩⟩
  have : Epi (spMap j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  have h' := congrArg (fun z => z.left) h
  simp only [preHom, MonoidHom.mk'_apply, Over.comp_left, toC_left] at h'
  exact (cancel_epi (spMap j)).1 h'

theorem pre_onto {k : Type} [Field k] [IsAlgClosed k] (j : ℂ →+* k) (A : Over (Sp ℂ)) [GrpObj A]
    (hA : IsAbelianScheme A) {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap j) ⟶ A) (hx : x ^ n = 1) :
    ∃ y : Over.mk (𝟙 (Sp ℂ)) ⟶ A, y ^ n = 1 ∧ preHom (toC j) y = x := by
  obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨f₁, c₁⟩ := torsion_card A hA hn (spMap j) z
  obtain ⟨f₀, c₀⟩ := torsion_card A hA hn (𝟙 (Sp ℂ)) (spMap j z)
  let F : {x : Over.mk (𝟙 (Sp ℂ)) ⟶ A // x ^ n = 1} → {x : Over.mk (spMap j) ⟶ A // x ^ n = 1} :=
    fun y => ⟨preHom (toC j) y.1, by rw [← map_pow, y.2, map_one]⟩
  have hF : Function.Injective F := fun y y' h => Subtype.ext (pre_injective j A (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (hF.bijective_of_nat_card_le (by rw [c₀, c₁]; rfl)).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

theorem unitOn_pull {k : Type} [Field k] (j : ℂ →+* k) (c : ℂˣ) :
    Units.map (toC j).left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) := by
  rw [toC_left]
  apply Units.ext
  exact (congrArg (fun q => q.hom (c : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem one_comp_hom {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] :
    (1 : T ⟶ G) ≫ φ = 1 := by
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]

end GlobalTheory.HTTate

namespace GlobalTheory.UPel.HT

open Classical in

theorem exists_tateIsoO_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (L : LB A.left) (D' : PLat D.O D.inv) t (Q : D'.La →+ (Fin D.g → ℂ)) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A)), 0 < N → N.Coprime p → IsAbelianScheme A → L.IsLB → Genus p N D.plat D' t → IsPeriod D' ρ Q → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A L k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (t a))) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ), ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y := by
  intro p _ D N ρ A _ _ act L D' t Q e eta hN hNp hA hL hG hP hadd hsurj hker hact hW heta k _ _ x
  obtain ⟨f, ν, rfl, htow, hgen⟩ := hG
  obtain ⟨j, rfl⟩ : ∃ j : ℂ →+* k, spMap j = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hGF : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let π := preHom (G := A) (GlobalTheory.HTTate.toC j)
  have hπ : Function.Injective π := GlobalTheory.HTTate.pre_injective j A
  let e' : Multiplicative (Fin D.g → ℂ) →* (Over.mk (𝟙 (Sp ℂ)) ⟶ A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin D.g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin D.g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • Q (a + n • c)) = e ((n : ℂ)⁻¹ • Q a) := by
    intro n hn a c
    rw [map_add, smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  let ev : ℕ → D.La → (Over.mk (spMap j) ⟶ A) := fun n a =>
    if 0 < n ∧ n.Coprime p then π (e ((n : ℂ)⁻¹ • Q (f n a))) else 1
  have hev : ∀ n, 0 < n → n.Coprime p → ∀ a, ev n a = π (e ((n : ℂ)⁻¹ • Q (f n a))) :=
    fun n hn hc a => if_pos ⟨hn, hc⟩
  have hev' : ∀ n, ¬ (0 < n ∧ n.Coprime p) → ∀ a, ev n a = 1 := fun n h a => if_neg h
  refine ⟨{ ζ := fun n => Units.map j.toMonoidHom (GlobalTheory.PeriodTate.rt n (ν n))
            ζ_prim := fun n hn hc => (GlobalTheory.PeriodTate.rt_prim hn (hgen n hn hc).1).map_of_injective
              (Units.map_injective j.injective)
            ζ_pow := fun n m hn hm hc => by
              rw [← map_pow, GlobalTheory.PeriodTate.rt_pow hm, GlobalTheory.PeriodTate.rt_congr hn (htow n m hn hm hc).1]
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn hc a => ?_
            onto := fun n hn hc q => ?_
            tower := fun n m hn hm hc a => ?_
            isom := fun n hn hc a b => ?_ }, fun y => ?_⟩
  · by_cases h : 0 < n ∧ n.Coprime p
    · have hf : f n (a + b) = f n a + f n b := (f n).map_add a b
      rw [hev n h.1 h.2, hev n h.1 h.2, hev n h.1 h.2, hf, map_add, smul_add, hadd, map_mul]
    · rw [hev' n h, hev' n h, hev' n h, _root_.mul_one]
  · by_cases h : 0 < n ∧ n.Coprime p
    · rw [hev n h.1 h.2, hev n h.1 h.2]
      obtain ⟨d, hd⟩ := (hgen n h.1 h.2).2.1 c a
      replace hd : f n (c • a) = c • f n a + n • d := hd
      show π _ = π _ ≫ _
      rw [hd, hshift n h.1, show π (e ((n : ℂ)⁻¹ • Q (f n a))) ≫ act.act c =
        π (e ((n : ℂ)⁻¹ • Q (f n a)) ≫ act.act c) from Category.assoc _ _ _, ← hact, hP.1, Matrix.mulVec_smul]
    · rw [hev' n h, hev' n h]
      haveI := act.hom c
      exact (GlobalTheory.HTTate.one_comp_hom (act.act c)).symm
  · rw [hev n hn hc, map_eq_one_iff π hπ, hker]
    have hk : (∃ e, f n a = n • e) ↔ ∃ e : D.La, a = n • e := (hgen n hn hc).2.2.1 a
    rw [← hk]
    constructor
    · rintro ⟨c, hc'⟩
      exact ⟨c, hP.2.1 (by rw [map_nsmul, hc', hsm n hn])⟩
    · rintro ⟨c, hc'⟩
      exact ⟨c, by rw [hc', map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := GlobalTheory.HTTate.pre_onto j A hA hn q hq
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hgen n hn hc).2.2.2.1 a'
      refine ⟨a, (hev n hn hc a).trans (congrArg π ?_)⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [hev n hn hc, ← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · have hn' : n.Coprime p := Nat.Coprime.coprime_dvd_left (Nat.dvd_mul_right n m) hc
    obtain ⟨c, hc'⟩ := (htow n m hn hm hc).2 a
    replace hc' : f (n * m) a = f n a + n • c := hc'
    rw [hev _ (Nat.mul_pos hn hm) hc, hev n hn hn', ← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul,
      hsm m hm, hc', hshift n hn]
  · show Out.WeilIs A L n (ev n a) (ev n b)
      (unitOn (Units.map j.toMonoidHom (GlobalTheory.PeriodTate.rt n (ν n)) ^ (2 * D.EF a b)))
    have h := GlobalTheory.CommPairing.weilIs_pull hGF hA hL (GlobalTheory.HTTate.toC j)
      (hW n (f n a) (f n b) (GlobalTheory.PeriodTate.rt n _) hn (GlobalTheory.PeriodTate.rt_val _ _))
    have e2 : D.plat.EF a b = 2 * D.EF a b := by
      show ((2 : ℤ) • D.EF) a b = _
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    have hν : (n : ℤ) ∣ D'.EF (f n a) (f n b) - ν n * (2 * D.EF a b) := by
      rw [← e2]; exact (hgen n hn hc).2.2.2.2 a b
    rw [GlobalTheory.HTTate.unitOn_pull, GlobalTheory.PeriodTate.rt_congr hn hν, GlobalTheory.PeriodTate.rt_mul, map_zpow] at h
    rw [hev n hn hc, hev n hn hc]
    exact h
  · show toUnit _ ≫ eta y = ev N y
    rw [hev N hN hNp]
    show _ = GlobalTheory.HTTate.toC j ≫ e _
    rw [← heta, ← Category.assoc]
    congr 1
end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relativeDimension_abelianVariety_field : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.AbVarRelDim.exists_relDim | exact GlobalTheory.AbVarRelDim.exists_relDim | (intros; apply GlobalTheory.AbVarRelDim.exists_relDim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortExactOfCompositionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shortExact_of_composition : ∀ (X : Scheme.{0}) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact), f ≫ g = u → ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0), (ShortComplex.mk l m w₃).ShortExact ∧ q₀ ≫ l = g ≫ q₂ ∧ q₂ ≫ m = q₁ := by
  first | exact @GlobalTheory.ThirdIso.modules | exact GlobalTheory.ThirdIso.modules | (intros; apply GlobalTheory.ThirdIso.modules <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BumpPts

theorem exists_finset_closure_eq_top {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k)
    [LocallyOfFiniteType p] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(X, W), Subring.closure (Set.range (constFn p W) ∪ ↑s) = ⊤ := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
  letI := (p.appLE ⊤ W (fun _ _ => trivial)).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Sp k, ⊤) Γ(X, W) := h
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := Γ(Sp k, ⊤)) (A := Γ(X, W))
  refine ⟨s, ?_⟩
  have e : Set.range (constFn p W) = Set.range (algebraMap Γ(Sp k, ⊤) Γ(X, W)) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b, ?_⟩
      have hb : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b) = b := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
      show (p.appLE ⊤ W (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom b)) = _
      rw [hb]
      rfl
  rw [e, ← Algebra.adjoin_eq_ring_closure, hs]
  rfl

theorem exists_cInf_bump (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (hp : IsProjOver p) (σ : k →+* ℂ) (y : CxPts p σ) (O : Set (CxPts p σ)) (hO : IsOpen O)
    (hy : y ∈ O) : ∃ χ : CxPts p σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧
      tsupport χ ⊆ O := by
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hp
  haveI : T2Space (CxPts p σ) := t2Space_cxPts_of_isProjOver σ hp
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top y.1)
  have hyW' : y ∈ ptsIn p σ W := hyW
  obtain ⟨s, hs⟩ := exists_finset_closure_eq_top p hW
  let φ : CxPts p σ → (s → ℂ) := fun z a => ev p σ W a.1 z

  obtain ⟨S, hS, hSO⟩ : ∃ S ∈ 𝓝 (φ y), ∀ z ∈ ptsIn p σ W, φ z ∈ S → z ∈ O := by
    let l := Filter.comap φ (𝓝 (φ y)) ⊓ 𝓟 (ptsIn p σ W)
    have hφl : Tendsto φ l (𝓝 (φ y)) := tendsto_comap.mono_left inf_le_left
    have ht : Tendsto (fun z => z) l (𝓝 y) := by
      refine (PtsOver.tendsto_iff_of_generators hW hyW hs).2 ⟨?_, fun f hf => ?_⟩
      · exact mem_inf_of_right (mem_principal_self _)
      · exact ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hφl
    have h : O ∈ l := ht (hO.mem_nhds hy)
    rw [mem_inf_principal] at h
    obtain ⟨S, hS, hSO⟩ := mem_comap.1 h
    exact ⟨S, hS, fun z hz hzS => hSO hzS hz⟩
  obtain ⟨F, hFS, hFc, hFd, hFr, hF1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hS
  let K : Set (CxPts p σ) := {z | z ∈ ptsIn p σ W ∧ φ z ∈ tsupport F}

  have hKc : IsCompact K := by
    refine isCompact_iff_ultrafilter_le_nhds.2 fun u hu => ?_
    have hKu : K ∈ u := le_principal_iff.1 hu
    have hWu : ∀ᶠ z in (u : Filter (CxPts p σ)), z ∈ ptsIn p σ W := mem_of_superset hKu fun z hz => hz.1
    obtain ⟨v, -, hv⟩ := hFc.ultrafilter_le_nhds (u.map φ)
      (le_principal_iff.2 (Ultrafilter.mem_map.2
        (mem_of_superset hKu fun z (hz : z ∈ K) => hz.2)))
    have hv' : Tendsto φ u (𝓝 v) := hv
    have hcst : ∀ a : k, ∀ z ∈ ptsIn p σ W, ev p σ W (constFn p W a) z = ev p σ W (constFn p W a) y :=
      fun a z hz => by
        show valR z.1 W _ = valR y.1 W _
        rw [valR_constFn p z.1 W hz, valR_constFn p y.1 W hyW, z.2, y.2]
    have hlim : ∀ f : Γ(X, W), ∃ c, Tendsto (fun z => ev p σ W f z) u (𝓝 c) := by
      intro f
      have hf : f ∈ Subring.closure (Set.range (constFn p W) ∪ ↑s) := hs ▸ Subring.mem_top f
      induction hf using Subring.closure_induction with
      | mem f hf =>
        rcases hf with ⟨a, rfl⟩ | hf
        · exact ⟨_, tendsto_const_nhds.congr' (hWu.mono fun z hz => (hcst a z hz).symm)⟩
        · exact ⟨v ⟨f, hf⟩, ((continuous_apply (⟨f, hf⟩ : s)).tendsto _).comp hv'⟩
      | zero =>
        exact ⟨0, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm)⟩
      | one =>
        exact ⟨1, tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm)⟩
      | add f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c + d, (hc.add hd).congr fun z => (ev_add f g z).symm⟩
      | neg f _ hf =>
        obtain ⟨c, hc⟩ := hf
        exact ⟨-c, hc.neg.congr' (hWu.mono fun z hz => by
          show -ev p σ W f z = ev p σ W (-f) z
          rw [ev_eq hz, ev_eq hz, map_neg])⟩
      | mul f g _ _ hf hg =>
        obtain ⟨c, hc⟩ := hf
        obtain ⟨d, hd⟩ := hg
        exact ⟨c * d, (hc.mul hd).congr fun z => (ev_mul f g z).symm⟩
    choose c hc using hlim
    let ψ : Γ(X, W) →+* ℂ :=
      { toFun := c
        map_one' := tendsto_nhds_unique (hc 1)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 1).trans (map_one _)).symm))
        map_mul' := fun f g => tendsto_nhds_unique (hc (f * g))
          (((hc f).mul (hc g)).congr fun z => (ev_mul f g z).symm)
        map_zero' := tendsto_nhds_unique (hc 0)
          (tendsto_const_nhds.congr' (hWu.mono fun z hz => ((ev_eq hz 0).trans (map_zero _)).symm))
        map_add' := fun f g => tendsto_nhds_unique (hc (f + g))
          (((hc f).add (hc g)).congr fun z => (ev_add f g z).symm) }
    have hψ : ∀ a, ψ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W a) = σ a := fun a => tendsto_nhds_unique (hc _)
      (tendsto_const_nhds.congr' (hWu.mono fun z hz => (ev_algX hz a).symm))
    let z' : CxPts p σ := ofHom hW ψ hψ
    have hz'W : z' ∈ ptsIn p σ W := ofHom_mem hW ψ hψ
    have hz'ev : ∀ f, ev p σ W f z' = c f := fun f => ev_ofHom hW ψ hψ f
    have ht : Tendsto (fun z => z) (u : Filter (CxPts p σ)) (𝓝 z') := by
      refine (PtsOver.tendsto_iff_of_generators hW hz'W hs).2 ⟨hWu, fun f _ => ?_⟩
      have := hc f
      rw [← hz'ev f] at this
      exact this
    have hφz' : φ z' = v := funext fun a =>
      (hz'ev a.1).trans (tendsto_nhds_unique (hc a.1) (((continuous_apply a).tendsto _).comp hv'))
    refine ⟨z', ⟨hz'W, ?_⟩, ht⟩
    rw [hφz']
    exact hFc.isClosed.mem_of_tendsto hv' (mem_of_superset hKu fun z hz => hz.2)
  have hKcl : IsClosed K := hKc.isClosed
  let χ : CxPts p σ → ℝ := (ptsIn p σ W).indicator fun z => F (φ z)
  have hsupp : Function.support χ ⊆ K := fun z hz => by
    rw [Function.mem_support, Set.indicator_apply_ne_zero] at hz
    exact ⟨hz.1, subset_tsupport _ hz.2⟩
  refine ⟨χ, fun z => ?_, fun z => Set.indicator_nonneg (fun w _ => (hFr ⟨_, rfl⟩).1) z, ?_, ?_⟩
  · by_cases hz : z ∈ ptsIn p σ W
    · refine ⟨W, s, inferInstance, fun a => a.1, F, Set.univ, hz, isOpen_univ, trivial,
        hFd.contDiffOn, ?_⟩
      filter_upwards [(isOpen_ptsIn W).mem_nhds hz] with w hw
      exact Set.indicator_of_mem hw _
    · have hzK : z ∉ K := fun h => hz h.1
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKcl.isOpen_compl.mem_nhds hzK] with w hw
      exact Function.notMem_support.1 fun h => hw (hsupp h)
  · show 0 < (ptsIn p σ W).indicator (fun z => F (φ z)) y
    rw [Set.indicator_of_mem hyW', hF1]
    exact one_pos
  · exact (closure_minimal hsupp hKcl).trans fun z hz => hSO z hz.1 (hFS hz.2)

end GlobalTheory.BumpPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemSpanOrbitOfNumberFieldLatticeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (O F : Type) [CommRing O] [Field F] [NumberField F] [Algebra O F] [IsFractionRing O F] (ρ : O →+* Module.End ℤ_[l] T), Module.finrank ℤ_[l] T = Module.finrank ℚ F → (∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => ρ (a i))) → ∃ (v : T) (c : ℤ_[l]), c ≠ 0 ∧ ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v) := by
  first | exact @GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit | exact GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit | (intros; apply GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceChartIndep
section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

theorem extTrace_midIn_indep {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} (T : HermSeq A 1 1)
    (a b : T.κ) (i : A.ι) {v : V n} (hv : v ∈ chartSet T a i ∩ chartSet T b i) :
    extTrace (midIn T a i) v = extTrace (midIn T b i) v := by
  have hh := trans_eventually T a b i hv
  have e : midIn T b i =ᶠ[𝓝 v] fun w => chg (gIn T a b i w) (midIn T a i w) := hh.mono fun w hw => hw.2.2.1
  have hK : MContDiffAt 1 (midIn T a i) v := (isPosFrame_midIn T a i).isHermFrame.one hv.1
  have hp : ∀ᶠ x in 𝓝 v, (midIn T a i x).PosDef :=
    mem_of_superset ((isOpen_chartSet T a i).mem_nhds hv.1) fun x hx => (isPosFrame_midIn T a i).posDef x hx
  have hg := holo_gIn T a b i hv
  have hA : MContDiffAt 1 (gIn T a b i) v := hg.1.of_le (by norm_cast)
  have hA0 : ∀ η, mdbar (gIn T a b i) v η = 0 := hg.2.self_of_nhds
  have ht : ∀ᶠ x in 𝓝 v, (gIn T a b i x).toBlocks₂₁ = 0 := hh.mono fun w hw => hw.2.2.2.2
  have hu : IsUnit (gIn T a b i v).det := by
    have ha : (A.e i).symm v ∈ T.U a := hv.1.2
    have hb : (A.e i).symm v ∈ T.U b := hv.2.2
    have h1 : T.g a b ((A.e i).symm v) * T.g b a ((A.e i).symm v) = 1 := by
      rw [T.g_mul a b a _ ⟨⟨ha, hb⟩, ha⟩, T.g_self a _ ha]
    exact Matrix.isUnit_det_of_right_inverse h1
  rw [extTrace_congr e, extTrace_chg hK hp hA hu hA0 ht]

end GlobalTheory.SecForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreLineOverSurjectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_spMap_mapRingHom_of_fibre_closedPoint : ∀ (R K : Type) [CommRing R] [Field K] (χ : R →+* K), Function.Surjective χ → ∀ (x : Sp (Polynomial R)), spMap (algebraMap R (Polynomial R)) x = spMap χ (IsLocalRing.closedPoint K) → x ∈ Set.range (spMap (Polynomial.mapRingHom χ)) := by
  first | exact @GlobalTheory.fibre_line_over_surjection | exact GlobalTheory.fibre_line_over_surjection | (intros; apply GlobalTheory.fibre_line_over_surjection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstant
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteGroupSchemeLength

theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  have h1 : Module.length R S = Module.length S S :=
    Module.length_eq_of_surjective (R := S) (M := S) (S := R) e.surjective
  let l : R ≃ₗ[R] S :=
    { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
      map_add' := e.map_add,
      map_smul' := fun r x => by
        simp only [smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
        rfl }
  rw [l.length_eq, h1]

theorem isClosed_singleton_of_isFinite {k : Type} [Field k] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of k)) [IsFinite f] (z : H) : IsClosed ({z} : Set H) := by
  have hz : f z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hc : IsClosed (f ⁻¹' {IsLocalRing.closedPoint k}) :=
    (IsLocalRing.isClosed_singleton_closedPoint k).preimage f.continuous
  have hd := (f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)).to_subtype
  have := hc.isClosedEmbedding_subtypeVal.isClosedMap {⟨z, hz⟩} (isClosed_discrete _)
  rwa [Set.image_singleton] at this

theorem length_stalk_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  intro k _ _ G _ hf x x'
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have hsurj : ∀ y : G.left, ∃ a : 𝟙_ (Over (Sp k)) ⟶ G, a.left pt = y := by
    intro y
    have hy := isClosed_singleton_of_isFinite G.hom y
    exact ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
      pointOfClosedPoint_apply G.hom y hy _⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨a', rfl⟩ := hsurj x'
  let φ := GrpObj.mulRight (a⁻¹ * a')
  have h : a ≫ φ.hom = a' := by
    have : a ≫ φ.hom = a * (a⁻¹ * a') := by
      simp [φ, comp_lift_assoc, Hom.mul_def]
    rw [this, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
  have hx : φ.hom.left (a.left pt) = a'.left pt := by
    rw [← h]; rfl
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso φ).hom)
  have hi : IsIso (φ.hom.left.stalkMap (a.left pt)) :=
    ((isIso_iff_isIso_stalkMap φ.hom.left).1 inferInstance).2 _
  let e := (asIso (φ.hom.left.stalkMap (a.left pt))).commRingCatIsoToRingEquiv
  rw [← length_self_eq_of_ringEquiv e]
  congr 1 <;> rw [hx]

end GlobalTheory.FiniteGroupSchemeLength
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageOfMapEqOneOnInfFiniteIndexStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_of_map_eq_one_on_inf_finiteIndex' : ∀ (G M : Type) [Group G] [Monoid M] (ρ : G →* M) (I H : Subgroup G), H.FiniteIndex → (∀ σ ∈ I, σ ∈ H → ρ σ = 1) → (ρ '' (I : Set G)).Finite := by
  first | exact @GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex | exact GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex | (intros; apply GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEquivariantHomEqAugmentationQuotientStatement
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_equivariantHom_eq_augmentation_quotient : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (χ : Idx → C →+* k), (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧ ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := by
  first | exact @GlobalTheory.HTRho.quotFacts | exact GlobalTheory.HTRho.quotFacts | (intros; apply GlobalTheory.HTRho.quotFacts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKsSubMapClsEqHomOStatement
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO : ∀ {k O H : Type*} [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z), Z ≤ G → finrank k ((ksSub σ 0 G Z).map (cls G)) = finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := by
  first | exact @GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | exact GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO | (intros; apply GlobalTheory.HTRho.finrank_ksSub_map_cls_eq_homO <;> assumption)
end

