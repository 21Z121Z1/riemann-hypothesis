import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitaryCharEqOneOfTrivialRationalSplitPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBLieMemHtLatIffOfPointOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
open GlobalTheory.KernelNoTorsion
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.IndepPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] {P P' : Point p v O Λ}

theorem corr_nilp {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] {x : specO O R ⟶ P.Gt}
    {y : specO O R ⟶ P.G} (h : Corr P x y) (φ : R →ₐ[O] R') (hR : IsNilpotent (p : R')) :
    P.cmp R' hR (ptMap φ ≫ x) = ptMap φ ≫ y := by
  obtain ⟨m, hm⟩ := id hR
  let ψ : (R ⧸ Ideal.span {(p : R) ^ m}) →ₐ[O] R' := Ideal.Quotient.liftₐ _ φ fun c hc => by
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    simp [hm]
  have e : ptMap φ = ptMap ψ ≫ ptMap (redR p O R m) := by
    rw [TangentPow.ptMap_comp_ptMap]
    rfl
  rw [e, Category.assoc, Category.assoc, h, P.cmp_nat _ _ (nilpR m)]

def ptsHom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (T : Over S) :
    (T ⟶ A) →* (T ⟶ B) :=
  MonoidHom.mk' (fun x => x ≫ f) fun x y => MonObj.mul_comp x y _

variable (p) in

def tateIso {A B : Out.PolAV (Sp C)} (α : A.A ≅ B.A) [IsMonHom α.hom] : TateA A p ≃ₗ[ℤ_[p]] TateA B p :=
  LinearEquiv.ofLinearMap (Tate.map p (ptsHom α.hom _)) (Tate.map p (ptsHom α.inv _))
    (LinearMap.ext fun t => Tate.ext fun n => by
      change (t.lev n ≫ α.inv) ≫ α.hom = t.lev n
      simp)
    (LinearMap.ext fun t => Tate.ext fun n => by
      change (t.lev n ≫ α.hom) ≫ α.inv = t.lev n
      simp)

theorem lev_tateIso {A B : Out.PolAV (Sp C)} (α : A.A ≅ B.A) [IsMonHom α.hom] (t : TateA A p) (n : ℕ) :
    (tateIso p α t).lev n = t.lev n ≫ α.hom := rfl

variable [IsAlgClosed C] [CharZero C]

theorem weil_iso {A B : Out.PolAV (Sp C)} (α : A.A ≅ B.A) [IsMonHom α.hom] (hL : LBIso A.L (B.L.pull α.hom.left))
    {k : ℕ} (hk : 1 ≤ k) {z s : ChTor.Pts A.A} (hz : z ^ k = 1) (hs : s ^ k = 1) :
    weil B k (z ≫ α.hom) (s ≫ α.hom) = weil A k z s := by
  have hl : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨w, hw⟩ := hL
  have h1 : (z ≫ α.hom) ^ k = 1 := by rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  have h2 : (s ≫ α.hom) ^ k = 1 := by rw [← MonObj.pow_comp, hs, MonObj.one_comp]
  exact (weilIs_iff hk hz hs _).1 ((GlobalTheory.weilIs_iso_iff hl.globalFns hl.cube A B α w hw k z s hz hs _).1
    ((weilIs_iff hk h1 h2 _).2 rfl))

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]

omit [Algebra ℤ_[p] O] in

theorem weilChar_tateIso (α : P.A.A ≅ P'.A.A) [IsMonHom α.hom] (hL : LBIso P.A.L (P'.A.L.pull α.hom.left))
    (g : P.G ⟶ P'.G) (hgen : α.hom.left ≫ P'.gen = P.gen ≫ g.left) (t : P.T) {n : ℕ}
    {d : torsion P.Gt (p ^ n) ⟶ torsion P'.Gt (p ^ n)}
    (hd : ∀ (R : Type) [CommRing R] [Algebra O R] (hR : IsNilpotent (p : R)) (w : specO O R ⟶ torsion P.Gt (p ^ n)),
      P'.cmp R hR (w ≫ d ≫ torsion.ι P'.Gt (p ^ n)) = P.cmp R hR (w ≫ torsion.ι P.Gt (p ^ n)) ≫ g) :
    (P.weilChar t).χ n = d ≫ (P'.weilChar (tateIso p α t)).χ n := P.char_ext fun w => by
  have e1 : P'.toG ((w ≫ d) ≫ torsion.ι P'.Gt (p ^ n)) = P.toG (w ≫ torsion.ι P.Gt (p ^ n)) ≫ g :=
    P.hom_ext_red fun m => by
      rw [Point.red_toG, ← Category.assoc _ (P.toG _), Point.red_toG, ← Category.assoc _ w, ← hd]
      simp only [Category.assoc]
  have e2 : P.toA (w ≫ torsion.ι P.Gt (p ^ n)) ≫ α.hom = P'.toA ((w ≫ d) ≫ torsion.ι P'.Gt (p ^ n)) := by
    rw [Point.eq_toA_iff, e1, Over.comp_left, Over.comp_left, Category.assoc, hgen, ← Category.assoc,
      (P.eq_toA_iff _ _).1 rfl, Category.assoc]
  rw [← Category.assoc, P.isWeilChar_weilChar, P'.isWeilChar_weilChar, ← e2, lev_tateIso]
  exact congrArg Units.val (weil_iso α hL (one_le_ppow p n) (P.toA_pow w) (t.lev_pow n)).symm

theorem al₀_tateIso (α : P.A.A ≅ P'.A.A) [IsMonHom α.hom] (hL : LBIso P.A.L (P'.A.L.pull α.hom.left))
    (g : P.G ⟶ P'.G) (hg : IsMonHom g) (hgen : α.hom.left ≫ P'.gen = P.gen ≫ g.left)
    {x : LieG P.Gt} {x' : LieG P'.Gt} {y : specO O (DualNumber O) ⟶ P.G} (hx : Corr P x.1 y)
    (hx' : Corr P' x'.1 (y ≫ g)) (t : P.T) : (P'.al₀ (tateIso p α t)).1 x' = (P.al₀ t).1 x := by
  have key : ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R], (p : R) ^ n = 0 →
      algebraMap O R ((dlogTv (P'.weilChar (tateIso p α t))).1 x') =
        algebraMap O R ((dlogTv (P.weilChar t)).1 x) := fun n R _ _ hR => by
    obtain ⟨d, hd⟩ := GlobalTheory.RaynaudTorsionMap.exists_torsion_map p C v O Λ P P' g hg (p ^ n) (one_le_ppow p n)
    have hn : IsNilpotent (p : DualNumber R) := ⟨n, by
      rw [← map_natCast (algebraMap R (DualNumber R)), ← map_pow, hR, map_zero]⟩
    have hw : _ = ptMap (dualBC (Algebra.ofId O R)) ≫ x.1 := HodgeTateImage.lift_ι hR x
    have h1 := isAl_dlogTv (P.weilChar t) n _ hR x _ hw
    have h2 := isAl_dlogTv (P'.weilChar (tateIso p α t)) n _ hR x' (HodgeTateImage.lift hR x ≫ d)
      ((P'.cmp _ hn).injective (by
        rw [Category.assoc, hd, hw, corr_nilp hx, corr_nilp hx', Category.assoc]))
    rw [Category.assoc, ← weilChar_tateIso α hL g hgen t hd, h1] at h2
    simpa [Algebra.algebraMap_eq_smul_one] using (congrArg TrivSqZeroExt.snd h2).symm
  exact HodgeTateImage.eq_of_forall (p := p) fun n => key n _ (HodgeTateImage.pow_quot n)

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (e : P.T ≃ₗ[ℤ_[p]] P'.T)

theorem exists_bLie_eq (he : ∀ s t, weilT P'.A p (e s) (e t) = weilT P.A p s t) :
    ∃ u : ℤ_[p], ∀ (x : LieG P.Gt) (x' : LieG P'.Gt), (∀ t, (P'.al₀ (e t)).1 x' = (P.al₀ t).1 x) →
      P'.bLie x' = u • e.toLinearMap.baseChange C (P.bLie x) := by
  let u : ℤ_[p] := P.eps.equiv.symm (P'.eps.equiv 1)
  have h1 : ∀ s t, pairT P.A P.eps s t = u * pairT P'.A P'.eps (e s) (e t) := fun s t => by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
    change P.eps.equiv.symm (weilT P.A p s t) =
      P.eps.equiv.symm (P'.eps.equiv (P'.eps.equiv.symm (weilT P'.A p (e s) (e t))))
    rw [LinearEquiv.apply_symm_apply, he]
  have h2 : ∀ (w : P.V) (t : P.T), P.pairV w (1 ⊗ₜ t) =
      P'.pairV (u • e.toLinearMap.baseChange C w) (1 ⊗ₜ e t) := fun w t => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, smul_add, LinearMap.add_apply, ha, hb]
    | tmul c s =>
      rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', Point.pairV_tmul, Point.pairV_tmul, h1, mul_comm u,
        mul_smul, smul_mul_assoc]
      rfl
  refine ⟨u, fun x x' h => P'.eq_of_pairV fun t => ?_⟩
  obtain ⟨t, rfl⟩ := e.surjective t
  rw [← h2, Point.pairV_bLie, Point.pairV_bLie, h]

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem map_latT_le : P.latT.map ((e.toLinearMap.baseChange C).restrictScalars O) ≤ P'.latT := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  | tmul c t => exact ⟨c ⊗ₜ e t, by rw [Point.inclT_tmul, Point.inclT_tmul]; rfl⟩

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C] in

theorem isEquivariant_baseChange (ha : ∀ a t, e (P.actT a t) = P'.actT a (e t)) :
    IsEquivariant P.actV P'.actV (e.toLinearMap.baseChange C) := fun a x => by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c t => exact congrArg (c ⊗ₜ ·) (ha a t)

omit [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem exists_corr {Y S : Scheme.{0}} {ψ : P.A.A.left ⟶ Y} {ψ' : P'.A.A.left ⟶ Y} {s : Y ⟶ S} {y : Sp C ⟶ S}
    (hψ : IsPullback ψ' P'.A.A.hom s y) (α : P.A.A ⟶ P'.A.A) (hα : α.left ≫ ψ' = ψ) (g : P.G ⟶ P'.G)
    (hgen : α.left ≫ P'.gen = P.gen ≫ g.left) {x : LieG P.Gt} {x' : LieG P'.Gt} {u : Sp (DualNumber C) ⟶ Y}
    (h : LieTie P ψ x u) (h' : LieTie P' ψ' x' u) : ∃ y, Corr P x.1 y ∧ Corr P' x'.1 (y ≫ g) := by
  obtain ⟨xG, w, h1, h2, h3⟩ := h
  obtain ⟨xG', w', h1', h2', h3'⟩ := h'
  have e1 : w.left ≫ α.left = w'.left := hψ.hom_ext (by rw [Category.assoc, hα, h2, h2'])
    ((Over.w (w ≫ α)).trans (Over.w w').symm)
  have : IsSchemeTheoreticallyDominant (spMap (dualMap (algebraMap O C))) :=
    (schemeDominant_specMap_iff _).2 fun a b hab => TrivSqZeroExt.ext
      (P.integers.hom_inj (by simpa [dualMap] using congrArg TrivSqZeroExt.fst hab))
      (P.integers.hom_inj (by simpa [dualMap, Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd hab))
  have := P'.semi.separated
  have e2 : xG.1 ≫ g = xG'.1 := Over.OverMorphism.ext (ext_of_schDom P'.G.hom
    ((Over.w (xG.1 ≫ g)).trans (Over.w xG'.1).symm) _ (by
      rw [← h3', ← e1, Over.comp_left, ← Category.assoc, ← h3, Category.assoc, Category.assoc, hgen]))
  exact ⟨xG.1, h1, e2 ▸ h1'⟩

end GlobalTheory.CompHt.IndepPoint

namespace GlobalTheory.CompHt

open IndepPoint

theorem sum_bLie_mem_htLat_of_pointOver {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ}
    [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C]
    [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] {T : CDVR} {x₀ : Sp T.Fr ⟶ Xo.X} {k : T.Fr →+* C}
    {kO kO' : T.V →+* O} {P P' : Point p v O (𝓞 E)} {ψ : P.A.A.left ⟶ Xo.univ.t.G.left}
    {ψ' : P'.A.A.left ⟶ Xo.univ.t.G.left} (h : PointOver P x₀ k kO ψ) (h' : PointOver P' x₀ k kO' ψ')
    (τ : E →+* ℂ) {n : ℕ} {u : Fin n → (Sp (DualNumber C) ⟶ Xo.univ.t.G.left)} {x : Fin n → LieG P.Gt}
    {x' : Fin n → LieG P'.Gt} (hx : ∀ j, LieTie P ψ (x j) (u j)) (hx' : ∀ j, LieTie P' ψ' (x' j) (u j))
    (a : Fin n → C) (ha : ∑ j, a j • P.bLie (x j) ∈ htLat c P τ) : ∑ j, a j • P'.bLie (x' j) ∈ htLat c P' τ := by
  classical
  obtain ⟨α, g, hα, hg, h1, h2, h3, h4⟩ := GlobalTheory.CompHt.pointOver_iso E H Dw l Xo p C v O T x₀ k kO kO' P P' ψ ψ' h h'
  let e : P.T ≃ₗ[ℤ_[p]] P'.T := tateIso p α
  obtain ⟨r, hr⟩ := exists_bLie_eq e fun s t => Tate.ext fun m =>
    weil_iso α h4 (one_le_ppow p m) (s.lev_pow m) (t.lev_pow m)
  have hb : ∀ j, P'.bLie (x' j) = r • e.toLinearMap.baseChange C (P.bLie (x j)) := fun j => hr _ _ fun t => by
    obtain ⟨y, hy, hy'⟩ := exists_corr h'.isGrpPullback.1 α.hom h1 g h2 (hx j) (hx' j)
    exact al₀_tateIso α h4 g hg h2 hy hy' t
  have he := isEquivariant_baseChange e fun b t => Tate.ext fun m => by
    change (t.lev m ≫ P.oA.act b) ≫ α.hom = (t.lev m ≫ α.hom) ≫ P'.oA.act b
    rw [Category.assoc, Category.assoc, h3]
  have hs : ∑ j, a j • P'.bLie (x' j) =
      algebraMap ℤ_[p] O r • e.toLinearMap.baseChange C (∑ j, a j • P.bLie (x j)) := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb, map_smul, smul_comm, ← algebraMap_smul C (algebraMap ℤ_[p] O r), ← IsScalarTower.algebraMap_apply,
      algebraMap_smul]
  rw [hs]
  refine Submodule.smul_mem _ _ ?_
  unfold htLat at ha ⊢
  split_ifs at ha ⊢
  · refine eigQuotLat_mono _ _ _ (map_latT_le e) ?_
    rw [← map_eigQuotLat _ _ he]
    exact Submodule.mem_map_of_mem ha
  · obtain ⟨ha1, ha2⟩ := (mem_eigSubLat _).1 ha
    refine (mem_eigSubLat _).2 ⟨map_latT_le e (Submodule.mem_map_of_mem ha1), mem_eigenSub.2 fun b => ?_⟩
    rw [← he, mem_eigenSub.1 ha2 b, map_smul]

theorem sum_bLie_mem_htLat_iff_of_pointOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (x₀ : Sp T.Fr ⟶ Xo.X) (k : T.Fr →+* C) (kO kO' : T.V →+* O) (P P' : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (ψ' : P'.A.A.left ⟶ Xo.univ.t.G.left), PointOver P x₀ k kO ψ → PointOver P' x₀ k kO' ψ' → ∀ (τ : E →+* ℂ) (n : ℕ) (u : Fin n → (Sp (DualNumber C) ⟶ Xo.univ.t.G.left)) (x : Fin n → LieG P.Gt) (x' : Fin n → LieG P'.Gt), (∀ j, LieTie P ψ (x j) (u j)) → (∀ j, LieTie P' ψ' (x' j) (u j)) → ∀ a : Fin n → C, ∑ j, a j • P.bLie (x j) ∈ htLat c P τ ↔ ∑ j, a j • P'.bLie (x' j) ∈ htLat c P' τ := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T x₀ k kO kO' P P' ψ ψ' h h' τ n u x x' hx hx' a
  exact ⟨sum_bLie_mem_htLat_of_pointOver h h' τ hx hx' a, sum_bLie_mem_htLat_of_pointOver h' h τ hx' hx a⟩

end GlobalTheory.CompHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormSqLeOfRootOfUnityAddCharCombination
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ParsevalRootsOfUnity

theorem isIntegral_of_pow_eq_one {R : Type} [CommRing R] (z : R) (m : ℕ) (hm : 0 < m)
    (h : z ^ m = 1) : IsIntegral ℤ z :=
  ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [h]⟩

theorem mem_Qbar_of_pow_eq_one (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : z ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact ((isIntegral_of_pow_eq_one z m hm h).tower_top (A := ℚ)).isAlgebraic

theorem norm_eq_one_of_pow_eq_one' (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : ‖z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg z) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity : ∀ {ι Q : Type} [Fintype ι] [Fintype Q] [AddCommGroup Q] (N k : ℕ) (c : ι → ℂ) (χ : ι → AddChar Q ℂ), 0 < N → (∀ i, ∃ m : ℕ, 0 < m ∧ c i ^ m = 1) → Function.Injective χ → Fintype.card Q = N ^ k → Fintype.card ι ≤ N ^ k → ∃ r : Q → Qbar, (∀ q, (r q : ℂ) = ((N : ℂ) ^ k)⁻¹ * ∑ i, c i * χ i q) ∧ (∀ q, IsIntegral ℤ ((N : Qbar) ^ k * r q)) ∧ ∀ ρ : Qbar →+* ℂ, (∑ q, ‖ρ (r q)‖) ^ 2 ≤ (N : ℝ) ^ k := by
  intro ι Q _ _ _ N k c χ hN hc hχ hQ hι
  classical
  choose m hm hcm using hc
  have hQpos : 0 < Fintype.card Q := Fintype.card_pos
  have hχq : ∀ i q, χ i q ^ Fintype.card Q = 1 := fun i q => by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  let cq : ι → Qbar := fun i => ⟨c i, mem_Qbar_of_pow_eq_one _ _ (hm i) (hcm i)⟩
  let xq : ι → Q → Qbar := fun i q => ⟨χ i q, mem_Qbar_of_pow_eq_one _ _ hQpos (hχq i q)⟩
  have hNQ : (N : Qbar) ≠ 0 := by exact_mod_cast hN.ne'
  let r : Q → Qbar := fun q => ((N : Qbar) ^ k)⁻¹ * ∑ i, cq i * xq i q
  refine ⟨r, ?_, ?_, ?_⟩
  · intro q
    simp [r, cq, xq]
  · intro q
    have : (N : Qbar) ^ k * r q = ∑ i, cq i * xq i q := by
      simp only [r]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hNQ), one_mul]
    rw [this]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
    · exact isIntegral_of_pow_eq_one _ (m i) (hm i) (Subtype.ext (by simpa [cq] using hcm i))
    · exact isIntegral_of_pow_eq_one _ _ hQpos (Subtype.ext (by simpa [xq] using hχq i q))
  · intro ρ
    let χ' : ι → AddChar Q Qbar := fun i =>
      { toFun := xq i
        map_zero_eq_one' := Subtype.ext (by simp [xq])
        map_add_eq_mul' := fun a b => Subtype.ext (by simp [xq, AddChar.map_add_eq_mul]) }
    let ψ : ι → AddChar Q ℂ := fun i => (ρ : Qbar →* ℂ).compAddChar (χ' i)
    have hψ : ∀ i q, ψ i q = ρ (xq i q) := fun i q => rfl
    let a : ι → ℂ := fun i => ρ (cq i)
    have ha : ∀ i, a i * (starRingEnd ℂ) (a i) = 1 := by
      intro i
      have h1 : a i ^ m i = 1 := by
        simp only [a]
        rw [← map_pow]
        have : cq i ^ m i = 1 := Subtype.ext (by simpa [cq] using hcm i)
        rw [this, map_one]
      rw [Complex.mul_conj', norm_eq_one_of_pow_eq_one' _ _ (hm i) h1]
      simp
    have hinj : Function.Injective ψ := by
      intro i j hij
      apply hχ
      ext q
      have h1 : ρ (xq i q) = ρ (xq j q) := by rw [← hψ, ← hψ, hij]
      have h2 := congrArg Subtype.val (ρ.injective h1)
      simpa [xq] using h2
    have horth : ∀ i j, ∑ q, ψ i q * (starRingEnd ℂ) (ψ j q) = if i = j then (Fintype.card Q : ℂ) else 0 := by
      intro i j
      have : ∀ q, ψ i q * (starRingEnd ℂ) (ψ j q) = (ψ i - ψ j) q := fun q => by
        rw [AddChar.sub_apply, AddChar.map_neg_eq_conj]
      simp_rw [this]
      rw [AddChar.sum_eq_ite]
      by_cases h : i = j
      · simp [h]
      · have : ψ i - ψ j ≠ 0 := fun h' => h (hinj (sub_eq_zero.1 h'))
        simp [h, this]
    let f : Q → ℂ := fun q => ∑ i, a i * ψ i q
    have hpars : ∑ q, ‖f q‖ ^ 2 = (Fintype.card Q : ℝ) * Fintype.card ι := by
      apply Complex.ofReal_injective
      push_cast
      simp_rw [← Complex.mul_conj']
      calc ∑ q, f q * (starRingEnd ℂ) (f q)
          = ∑ q, ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            simp only [f, map_sum, map_mul, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * ∑ q, (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            simp [Finset.mul_sum]
        _ = ∑ i, (Fintype.card Q : ℂ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [horth, ha]
        _ = (Fintype.card Q : ℂ) * Fintype.card ι := by
            simp [mul_comm]
    have hCS : (∑ q, ‖f q‖) ^ 2 ≤ (Fintype.card Q : ℝ) * ∑ q, ‖f q‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Q)) (f := fun q => ‖f q‖)
      simpa using this
    have hρr : ∀ q, ‖ρ (r q)‖ = ((N : ℝ) ^ k)⁻¹ * ‖f q‖ := by
      intro q
      simp only [r, map_mul, map_inv₀, map_pow, map_natCast, map_sum, norm_mul, norm_inv,
        norm_pow, Complex.norm_natCast, f, a, hψ]
    simp_rw [hρr]
    rw [← Finset.mul_sum, mul_pow]
    have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
    have hQr : (Fintype.card Q : ℝ) = (N : ℝ) ^ k := by exact_mod_cast hQ
    have hιr : (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ k := by exact_mod_cast hι
    calc (((N : ℝ) ^ k)⁻¹) ^ 2 * (∑ q, ‖f q‖) ^ 2
        ≤ (((N : ℝ) ^ k)⁻¹) ^ 2 * ((Fintype.card Q : ℝ) * ((Fintype.card Q : ℝ) * (Fintype.card ι : ℝ))) := by
          gcongr
          rw [← hpars]; exact hCS
      _ = (Fintype.card ι : ℝ) := by
          rw [hQr]; field_simp
      _ ≤ (N : ℝ) ^ k := hιr

end GlobalTheory.ParsevalRootsOfUnity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunOPosSigIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid (neg)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RallisBottom

variable {D : D7}

def posSig (A : HSp D) : HSp D := { A with sig := fun _ => (A.rank, 0) }

theorem posSig_sigOK {A : HSp D} (h : A.gram = 1) : (posSig A).SigOK := fun τ => by
  have e : (posSig A).gram.map τ = 1 := by
    show A.gram.map τ = 1
    rw [h]; exact Matrix.map_one _ (map_zero τ) (map_one τ)
  show Formalism.UG.HasSignature ((posSig A).gram.map τ) A.rank 0
  rw [e]
  exact GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef Matrix.PosDef.one

theorem thetaFunO_posSig_iff {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} (f : WO (neg A) WW → ℂ) :
    IsThetaFunO ψ (neg (posSig A)) WW f ↔ IsThetaFunO ψ (neg A) WW f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem isWeil_posSig {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} {χA χW : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep A WW}
    (h : GlobalTheory.Grid.IsWeil ψ true A WW χA χW ω) : GlobalTheory.Grid.IsWeil ψ true (posSig A) WW χA χW ω where
  std := h.std
  hecS := h.hecS
  hecT := h.hecT
  resS := h.resS
  resT := h.resT
  om_pres p f hf := (thetaFunO_posSig_iff (A := A) (WW := WW) _).2 (h.om_pres p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf))
  om_heis g k w f hf := h.om_heis g k w f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_aut γ hγ γ' hγ' f hf := h.om_aut γ hγ γ' hγ' f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_cont f hf := h.om_cont f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_unit μ 𝓕 h1 h2 p f hf := h.om_unit μ 𝓕 h1 h2 p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
  om_split e he g k h1 h2 x y h3 h4 :=
    (h.om_split e he g k h1 h2 x y h3 h4).imp fun _ hr => ⟨hr.1, fun ℓ hℓ f hf =>
      hr.2 ℓ (fun u hu f hf => hℓ u hu f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).2 hf)) f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)⟩

theorem isVacO_posSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A WW : HSp D} {sA sW LA LW} {f : WO (neg A) WW → ℂ}
    (h : IsVacO ψ θ (neg A) WW sA sW LA LW f) : IsVacO ψ θ (neg (posSig A)) WW sA sW LA LW f :=
  ⟨h.1, ⟨h.2.inf, (thetaFunO_posSig_iff (A := A) (WW := WW) f).2 h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩⟩

variable {T : Type}

def Tri.posSig {A A' WW : HSp D} (X : Tri T A A' WW) : Tri T (posSig A) A' WW :=
  ⟨⟨X.rA.Λ, X.rA.β, X.rA.s, X.rA.B⟩, X.rA', X.rW, X.ω, X.ω', X.vac, X.vac', X.e, X.c, X.f, X.f', X.m, X.fd, X.m', X.fd'⟩

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem isBottomTri_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    IsBottomTri W i j (Tri.posSig X) where
  rank := hX.rank
  rank' := hX.rank'
  std := hX.std
  std' := hX.std'
  stdW := hX.stdW
  is :=
    { rank := hX.is.rank
      rigA := hX.is.rigA
      rigA' := hX.is.rigA'
      rigW := hX.is.rigW
      weil := fun t => isWeil_posSig (hX.is.weil t)
      weil' := hX.is.weil'
      isVac := isVacO_posSig hX.is.isVac
      isVac' := hX.is.isVac'
      idem := hX.is.idem
      expo := hX.is.expo
      fst := hX.is.fst
      snd := hX.is.snd
      meas := hX.is.meas
      meas' := hX.is.meas' }

theorem sigOK_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    (posSig A).SigOK := posSig_sigOK hX.std.1

end GlobalTheory.RallisBottom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMem
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.NormUniq

theorem wd_rat_mem_TT : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {x : VC D N N'} {M : ℕ}, 0 < M → M • x ∈ La0 D (tor0 D cc δ) N N' → ∀ {F : VC D N N' → ℂ}, F ∈ TT D (tor0 D cc δ) N N' → Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  intro D cc δ hc N N' x M hM hx F hF
  obtain ⟨hd, m, hm, hFm⟩ := hF
  have hg := (GlobalTheory.InducedType.induced_type D).1
  have hint := (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D N) (GlobalTheory.NormSum.VacMove.moves_one D N'))).2.2.1
  refine ⟨GlobalTheory.FinWeil.RatTransl.differentiable_wd x hd, m * M, Nat.mul_pos hm hM, fun y hy => ?_⟩
  have h0 : Wd D (tor0 D cc δ) ((m * M) • y) F = F := by
    rw [mul_smul]; exact hFm _ (AddSubgroup.nsmul_mem _ hy M)
  obtain ⟨k, hk⟩ := hint _ (AddSubgroup.nsmul_mem _ hy m) _ hx
  have e : (m * M) • y = M • (m • y) := by rw [mul_comm, mul_smul]
  funext w
  exact GlobalTheory.FinWeil.RatTransl.wd_wd_of_int h0 k (by rw [e, GlobalTheory.FinWeil.RatTransl.hf_nsmul, hk]) w

end GlobalTheory.FunObj.NormUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingCharacterPhaseOriginValuationLeBoxStatement
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box : ∀ {k : Type} [Field k] [ValuativeRel k] (G : Grid k) (ϖ : kˣ) (a a' : ℤ) (e : Vars G), e ∈ box G ϖ a a' → valuation k (phase (0 : ColArgs G) e) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
  first | exact @GlobalTheory.OriginBox.phase_origin_le | exact GlobalTheory.OriginBox.phase_origin_le | (intros; apply GlobalTheory.OriginBox.phase_origin_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLatticeStatement
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_and_lintegral_unfold_of_lattice : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) (Λ : Subgroup G) [Countable Λ] (𝓑 : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ 𝓑 ν → ν 𝓑 ≠ ⊤ → ν.IsMulRightInvariant ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ b in 𝓑, ∑' γ : Λ, f (b⁻¹ * γ) ∂ν := by
  first | exact @GlobalTheory.ResLine.RightUnfold.unimodular_and_unfold | exact GlobalTheory.ResLine.RightUnfold.unimodular_and_unfold | (intros; apply GlobalTheory.ResLine.RightUnfold.unimodular_and_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharEqOneOfTrivialRationalSplitPlace
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.unitaryChar_eq_one_of_trivial_rational_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ ν : Formalism.IndefR.DatumF.GAF σ J →* Circle, Continuous ν → (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ν γ = 1) →
        (∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e → ∀ g, Formalism.IndefR.DatumF.SuppAtF σ e J g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @PositivityTheory.ThKW.character_trivial_of_rational_split | exact PositivityTheory.ThKW.character_trivial_of_rational_split | (intros; apply PositivityTheory.ThKW.character_trivial_of_rational_split <;> assumption)
end

