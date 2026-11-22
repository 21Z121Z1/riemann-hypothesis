import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
section
noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem eq_of_field_maps {S : Type} [CommRing S] [_root_.IsReduced S] {a b : S}
    (h : ∀ (L : Type) [Field L] (ψ : S →+* L), ψ a = ψ b) : a = b := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (mem_nilradical.1 ?_)
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  haveI : p.IsPrime := hp
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, h _ (algebraMap S p.ResidueField), sub_self]

theorem eq_of_field_algHoms {K S : Type} [CommRing K] [CommRing S] [Algebra K S] [_root_.IsReduced S] {a b : S}
    (h : ∀ (L : Type) [Field L] [Algebra K L] (ψ : S →ₐ[K] L), ψ a = ψ b) : a = b :=
  eq_of_field_maps fun L _ ψ =>
    letI : Algebra K L := (ψ.comp (algebraMap K S)).toAlgebra
    h L { ψ with commutes' := fun _ => rfl }

theorem ext_ev_field {Z : Scheme.{0}} [IsReduced Z] {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ev z V hz a = ev z V hz b) : a = b := by
  apply TopCat.Presheaf.section_ext Z.sheaf V
  intro p hp
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp V.isOpen
  have hWV : W ≤ V := hWV
  have e0 : ev (tau hW) V (tau_le hW hWV) a = ev (tau hW) V (tau_le hW hWV) b :=
    eq_of_field_maps fun L _ ψ => by
      have := h L (spMap ψ ≫ tau hW) (le_preimage_comp _ (tau_le hW hWV))
      rwa [ev_spMap ψ _ V (tau_le hW hWV)] at this
  rw [ev_tau hW hWV, ev_tau hW hWV] at e0
  have e1 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW a
  have e2 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW b
  exact e1.symm.trans ((congrArg _ e0).trans e2)

theorem glue_field {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → ∃ a : Γ(Z, W),
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a)) :
    ∃ a : Γ(Z, V), ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp V.isOpen
    exact ⟨⟨W, hW, hWV⟩, hpW⟩
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2)
    (fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)) a (fun i j => by
      refine ext_ev_field (a := resG Z inf_le_left (a i)) (b := resG Z inf_le_right (a j)) fun L _ z hz => ?_
      have hi := le_preimage_mono inf_le_left hz
      have hj := le_preimage_mono inf_le_right hz
      rw [ev_res z _ hz hi, ev_res z _ hz hj]
      exact uniq L z (le_preimage_mono i.2.2 hi) _ _ (ha i L z hi) (ha j L z hj))
  refine ⟨s, fun L _ z hz => ?_⟩
  obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
  have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
  have e : ev z V hz s = ev z i.1 hi' (a i) := (ev_res z i.2.2 hi' hz s).symm.trans (congrArg _ (hs i))
  exact e ▸ ha i L z hi'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

namespace FlagCover

theorem isReduced_Yo (hi : Function.Injective β) (hs : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (X : FlagCover Y) : IsReduced X.Yo := by
  letI := β.toAlgebra
  haveI : IsDomain O := hi.isDomain β
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hi
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, b, hb, h⟩ := hs x
    exact ⟨a, b, (eq_div_iff hb).2 h⟩
  have h1 : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (R := O) (S := c.F) (nonZeroDivisors O)
  have h2 : Flat (spMap β) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact IsLocalization.flat c.F (nonZeroDivisors O)
  have := Y.jQ_open
  have h3 : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have h4 : Flat Y.j := by unfold Model.j; infer_instance
  have h5 : IsPreimmersion X.inc :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h3
  have : ∀ x : X.Yo, _root_.IsReduced (X.Yo.presheaf.stalk x) := fun x => by
    have := (X.normal (X.inc x)).1
    let _ := (X.inc.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x) := Flat.stalkMap X.inc x
    have : IsLocalHom (algebraMap (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (X.inc.stalkMap x).hom)
    have : Module.FaithfullyFlat (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    let e := RingEquiv.ofBijective (X.inc.stalkMap x).hom
      ⟨FaithfulSMul.algebraMap_injective (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x),
        X.inc.stalkMap_surjective x⟩
    exact isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_isReduced_stalk _

theorem evR_frMap_of_isReduced {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    [_root_.IsReduced S] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, a, u, hu⟩ := (evLaws_genFr_atlas E H Dw l Xo c).1.test S y
  rw [FlagTan.evR_eq hf hu, FlagTan.evR_eq hf (PullbackSections.frMap_trans a φ hu h)]
  rfl

variable {X : FlagCover Y} {e : Ix Dw → ℤ}

theorem exists_alg_chartFr {S : Type} [CommRing S] (w : Sp S ⟶ X.Yo) :
    ∃ _ : Algebra c.F S, ∀ (k : X.F.J) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k),
      ∃ Q : FrPt Xo c S, X.F.ChartFr k (w ≫ X.inc) hz Q ∧ X.pt Q = w :=
  letI : Algebra c.F S :=
    ((ev (w ≫ pullback.snd X.π Y.j ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  ⟨this, fun k hz => X.exists_chartFr w (spMap_ev_top _).symm k hz⟩

theorem exists_coef [IsReduced X.Yo] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) (k : X.F.J) :
    ∃ a : Γ(X.Yo, ((X.F.LL e).pull X.inc).U (fun _ => k)), ∀ (L : Type) [Field L] (z : Sp L ⟶ X.Yo)
      (hz' : ⊤ ≤ z ⁻¹ᵁ ((X.F.LL e).pull X.inc).U (fun _ => k)) [Algebra c.F L]
      (hz : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c L), X.F.ChartFr k (z ≫ X.inc) hz Q → X.pt Q = z →
      ev z _ hz' a = evR Xo c f Q := by
  refine glue_field _ (fun L _ z x => ∀ [Algebra c.F L] (hz : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c L),
    X.F.ChartFr k (z ≫ X.inc) hz Q → X.pt Q = z → x = evR Xo c f Q) (fun L _ z hz' x y hx hy => ?_)
    fun W hW hle => ?_
  · obtain ⟨_, h⟩ := exists_alg_chartFr z
    obtain ⟨Q, hQ, ez⟩ := h k fun p hp => mem_pull.1 (hz' hp)
    exact (hx _ Q hQ ez).trans (hy _ Q hQ ez).symm
  · obtain ⟨_, h⟩ := exists_alg_chartFr (tau hW)
    obtain ⟨Q₀, hQ₀, e₀⟩ := h k fun p hp => mem_pull.1 (tau_le hW hle hp)
    refine ⟨evR Xo c f Q₀, fun L _ z hzW _ hz Q hQ ez => ?_⟩
    have e1 : spMap (ev z W hzW) ≫ tau hW = z := spMap_ev z hW hzW
    have e2 : spMap ((ev z W hzW).comp (algebraMap c.F Γ(X.Yo, W))) = spMap (algebraMap c.F L) := by
      rw [← spMap_comp', ← frX_snd Q₀, ← frX_snd Q, ← X.pt_snd Q₀, ← X.pt_snd Q, e₀, ez]
      simp only [← Category.assoc, e1]
    have e3 : (ev z W hzW).comp (algebraMap c.F Γ(X.Yo, W)) = algebraMap c.F L :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    let φ : Γ(X.Yo, W) →ₐ[c.F] L := { ev z W hzW with commutes' := fun r => DFunLike.congr_fun e3 r }
    obtain ⟨Q', hQ'⟩ := exists_frMap φ Q₀
    have e4 : spMap φ.toRingHom ≫ tau hW ≫ X.inc = z ≫ X.inc := by
      rw [← Category.assoc]; exact congrArg (· ≫ X.inc) e1
    rw [hQ.unique (hQ₀.frMap hQ' e4 hz)]
    exact (evR_frMap_of_isReduced hf hQ').symm

theorem exists_toRule_eq [IsReduced X.Yo] {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e) :
    ∃ s : X.SecO e, toRule s = f := by
  classical
  choose a ha using exists_coef (X := X) (e := e) hf.1
  let s : X.SecO e := ⟨fun j => a (j PUnit.unit), fun j j' => ext_ev_field fun L _ z hw => by
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
    obtain ⟨k', rfl⟩ : ∃ k, j' = fun _ => k := ⟨j' PUnit.unit, rfl⟩
    have hh : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') :=
      fun p hp => ⟨(mem_pull (F := X.inc)).1 (hw hp).1, (mem_pull (F := X.inc)).1 (hw hp).2⟩
    have hz := le_preimage_mono inf_le_left hh
    have hz' := le_preimage_mono inf_le_right hh
    obtain ⟨_, h⟩ := exists_alg_chartFr z
    obtain ⟨Q, hQ, ez⟩ := h k hz
    obtain ⟨Q', hQ', ez'⟩ := h k' hz'
    have hwt := FlagTan.evR_frBor hf (hQ.frBor hQ' hh)
    rw [map_mul]
    refine (ev_res z _ hw (le_pull hz) _).trans ((ha k L z _ hz Q hQ ez).trans (Eq.trans ?_
      (congrArg₂ (· * ·) ((ev_pull_g (X.F.LL e) X.inc (fun _ => k) (fun _ => k') z hw hh).trans
        (X.F.ev_LL_g e k k' _ hh)).symm
        ((ev_res z _ hw (le_pull hz') _).trans (ha k' L z _ hz' Q' hQ' ez')).symm)))
    rw [hwt, ← mul_assoc, ← Units.val_mul]
    have : (∏ ix, X.F.TAt k k' (z ≫ X.inc) hh ix ^ (-e ix)) * ∏ ix, X.F.TAt k k' (z ≫ X.inc) hh ix ^ e ix = 1 := by
      rw [← Finset.prod_mul_distrib]; simp
    rw [this, Units.val_one, one_mul]⟩
  refine ⟨s, funext fun p => funext fun P => ?_⟩
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  refine eq_of_field_algHoms (K := c.F) fun L _ _ ψ => ?_
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing X.F.cover (X.pt P' ≫ X.inc)
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor P' k hz
  have hc : coef s k (X.pt P') hz = evR Xo c f Q := ha k L _ _ hz Q hQ (X.pt_frBor ht)
  rw [← FlagTan.evR_eq hf.1 hP, FlagTan.evR_frBor hf ht, ← hc]
  refine (val_frMap s hP).symm.trans ?_
  convert val_eq s hQ ht

theorem toRule_injective [IsReduced X.Yo] {s s' : X.SecO e} (h : toRule s = toRule s') : s = s' := by
  refine TieUniq.sec_ext fun j => ext_ev_field fun S _ w hw => ?_
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
  have hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k := fun p hp => mem_pull.1 (hw hp)
  obtain ⟨_, h'⟩ := exists_alg_chartFr w
  obtain ⟨Q, hQ, rfl⟩ := h' k hz
  exact (val_chartFr s hQ).symm.trans (((evR_toRule_of_isReduced s Q).symm.trans
    ((congrArg (evR Xo c · Q) h).trans (evR_toRule_of_isReduced s' Q))).trans (val_chartFr s' hQ))

end FlagCover

end GlobalTheory.FlagMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.BCT.GlobLev GlobalTheory.SplitPts GroundTheory.Automorphic Topology

noncomputable section

namespace GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_one_entry {R : Type} [Ring R] (f : Ad E →+* R) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem sub_one_entry_mem {w : Pl E} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ w.adicCompletionIntegers E := by
  rw [mem_KGL_iff_val] at hg
  refine sub_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hg.1 i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

omit [IsCMField E] in

theorem af_ext {a b : Af E} (h : ∀ u : Pl E, pLoc E u a = pLoc E u b) : a = b := Subtype.ext (funext h)

omit [IsCMField E] in
theorem pLoc_singleNU_self (w : Pl E) (y : w.adicCompletion E) : pLoc E w (GlobalTheory.GLTwoHecke.singleNU w y) = y :=
  GlobalTheory.AdelicU.evalV_singleFin_self w y

omit [IsCMField E] in
theorem pLoc_singleNU_ne {u w : Pl E} (h : u ≠ w) (y : w.adicCompletion E) :
    pLoc E u (GlobalTheory.GLTwoHecke.singleNU w y) = 0 :=
  GlobalTheory.AdelicU.evalV_singleFin_ne h y

theorem entry_eq_one_add {w : Pl E} {N N' : Set (Af E)} (h0 : (0 : Af E) ∈ N')
    (hadd : ∀ a ∈ N', ∀ b ∈ N', a + b ∈ N)
    (hw : ∀ y ∈ w.adicCompletionIntegers E, GlobalTheory.GLTwoHecke.singleNU w y ∈ N')
    (hc : ∀ y ∈ (conjSrc (conjE E) w).adicCompletionIntegers E,
      GlobalTheory.GLTwoHecke.singleNU (conjSrc (conjE E) w) y ∈ N')
    (z : UA E n) (hz : z ∈ locU n w) (hK : cLoc w z ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    ∃ a ∈ N, ((z : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
      (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + (show Ad E from ((0 : InfiniteAdeleRing E), a)) := by
  have hKc := integral_conjSrc z w hK
  have hfin : z ∈ finU E n := (Subgroup.mem_inf.1 hz).1
  have hout : ∀ u : Pl E, u ≠ w → u ≠ conjSrc (conjE E) w → cLoc u z = 1 := by
    intro u huw huc
    have hne : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := fun h =>
      (eq_or_eq_conjSrc h).elim huw huc
    exact (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hz).2 u) hne)
  generalize conjSrc (conjE E) w = c at hc hKc hout
  refine ⟨GlobalTheory.GLTwoHecke.singleNU w ((cLoc w z).val i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
    (if c = w then 0 else GlobalTheory.GLTwoHecke.singleNU c ((cLoc c z).val i j - (1 : Matrix (Fin n) (Fin n) _) i j)),
    hadd _ (hw _ (sub_one_entry_mem hK i j)) _ ?_, ?_⟩
  · split_ifs
    · exact h0
    · exact hc _ (sub_one_entry_mem hKc i j)
  refine Prod.ext ?_ ?_
  · have h1 : GeneralLinearGroup.map (pInf E) (z : GA E n) = 1 := hfin
    have h2 : pInf E (((z : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) =
        pInf E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
      rw [map_one_entry]
      have := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) h1
      simpa using this
    have h3 := (infEq E).symm.injective h2
    change _ = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 + 0
    rw [add_zero]
    exact h3
  · apply af_ext
    intro u
    change (cLoc u z).val i j = ((pLoc E u).comp (pFin E)) ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      (show Ad E from ((0 : InfiniteAdeleRing E), _)))
    rw [map_add, map_one_entry]
    change _ = _ + pLoc E u (GlobalTheory.GLTwoHecke.singleNU w _ + _)
    rw [map_add]
    by_cases huw : u = w
    · subst huw
      rw [pLoc_singleNU_self]
      split_ifs with hcw
      · rw [map_zero]; abel
      · rw [pLoc_singleNU_ne (Ne.symm hcw)]; abel
    · rw [pLoc_singleNU_ne huw]
      by_cases huc : u = c
      · subst huc
        rw [if_neg huw, pLoc_singleNU_self]; abel
      · rw [hout u huw huc]
        split_ifs
        · simp
        · rw [pLoc_singleNU_ne huc]; simp

theorem eventually_locU_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU E n)),
    IsOpen (L : Set (finU E n)) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w n →
      ∀ h : x ∈ finU E n, (⟨x, h⟩ : finU E n) ∈ L := by
  intro E _ _ _ n L hL
  have h1 : (L : Set (finU E n)) ∈ 𝓝 (1 : finU E n) := hL.mem_nhds L.one_mem
  rw [nhds_subtype, Filter.mem_comap] at h1
  obtain ⟨V1, hV1, hV1L⟩ := h1
  rw [nhds_subtype, Filter.mem_comap] at hV1
  obtain ⟨V, hV, hVV1⟩ := hV1
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  let Φ : Af E → Ad E := fun a => show Ad E from ((0 : InfiniteAdeleRing E), a)
  have hΦ : Continuous Φ := continuous_const.prodMk continuous_id
  have hΦ0 : Φ 0 = 0 := rfl
  let ψ : (Bool × Fin n × Fin n → Af E) →
      Matrix (Fin n) (Fin n) (Ad E) × (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    fun y => (Matrix.of fun i j => (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + Φ (y (false, i, j)),
      MulOpposite.op (Matrix.of fun i j => (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + Φ (y (true, i, j))))
  have hψ : Continuous ψ := by
    refine Continuous.prodMk ?_ (MulOpposite.continuous_op.comp ?_) <;>
    exact continuous_pi fun i => continuous_pi fun j => continuous_const.add (hΦ.comp (continuous_apply _))
  have hψ0 : ψ 0 = Units.embedProduct _ (1 : GA E n) := by
    refine Prod.ext ?_ ?_
    · ext i j; simp [ψ, hΦ0]
    · refine MulOpposite.unop_injective ?_
      ext i j; simp [ψ, hΦ0]
  have hS : ψ ⁻¹' W ∈ 𝓝 (0 : Bool × Fin n × Fin n → Af E) :=
    hψ.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact hW)
  rw [nhds_pi, Filter.mem_pi'] at hS
  obtain ⟨I, t, ht, hIt⟩ := hS
  have hN : (⋂ i, t i) ∈ 𝓝 (0 : Af E) := Filter.iInter_mem.2 ht
  obtain ⟨N', hN', hadd⟩ := exists_nhds_zero_half hN
  have h0 : (0 : Af E) ∈ N' := mem_of_mem_nhds hN'
  have hev := GlobalTheory.GLTwoHecke.eventually_singleNU_mem hN'
  have hev2 := (conjSrc_injective (conjE E)).tendsto_cofinite.eventually hev
  filter_upwards [hev, hev2] with w hw hw2 x hxw hxK hx
  have hxw' : x⁻¹ ∈ locU n w := inv_mem hxw
  have hxK' : cLoc w x⁻¹ ∈ GlobalTheory.LFun.KGL w n := by rw [map_inv]; exact inv_mem hxK
  choose a ha hxa using entry_eq_one_add h0 hadd hw hw2 x hxw hxK
  choose b hb hxb using entry_eq_one_add h0 hadd hw hw2 x⁻¹ hxw' hxK'
  let y : Bool × Fin n × Fin n → Af E := fun p => if p.1 then b p.2.1 p.2.2 else a p.2.1 p.2.2
  have hy : y ∈ ψ ⁻¹' W := hIt fun p _ => by
    rcases p with ⟨_ | _, i, j⟩
    · exact Set.mem_iInter.1 (ha i j) _
    · exact Set.mem_iInter.1 (hb i j) _
  apply hV1L
  apply hVV1
  apply hWV
  have e : ψ y = Units.embedProduct _ ((x : GA E n)) := by
    refine Prod.ext ?_ ?_
    · ext i j
      exact (hxa i j).symm
    · refine MulOpposite.unop_injective ?_
      ext i j
      exact (hxb i j).symm
  show Units.embedProduct _ (x : GA E n) ∈ W
  rw [← e]
  exact hy

end GlobalTheory.BCT.GlobLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineGaloisCoverDualNumberEpi
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.DualCover

variable {A B : Type} [CommRing A] [CommRing B]

def dualMap (g : A →+* B) : DualNumber A →+* DualNumber B :=
  letI : Algebra A B := g.toAlgebra
  (DualNumber.lift ⟨(Algebra.ofId A (DualNumber B), DualNumber.eps), by simp, fun _ ↦ Commute.all _ _⟩).toRingHom

theorem dualMap_apply (g : A →+* B) (x : DualNumber A) :
    dualMap g x = TrivSqZeroExt.inl (g x.fst) + TrivSqZeroExt.inr (g x.snd) := by
  letI : Algebra A B := g.toAlgebra
  show (DualNumber.lift _ : DualNumber A →ₐ[A] DualNumber B) x = _
  rw [DualNumber.lift_apply_apply]
  ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]

@[simp] theorem dualMap_fst (g : A →+* B) (x : DualNumber A) : (dualMap g x).fst = g x.fst := by
  simp [dualMap_apply]

@[simp] theorem dualMap_snd (g : A →+* B) (x : DualNumber A) : (dualMap g x).snd = g x.snd := by
  simp [dualMap_apply]

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover
variable {A B : Type} [CommRing A] [CommRing B]

theorem isPushout_dualMap (g : A →+* B) :
    IsPushout (CommRingCat.ofHom (algebraMap A (DualNumber A))) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (dualMap g)) (CommRingCat.ofHom (algebraMap B (DualNumber B))) := by
  letI : Algebra A B := g.toAlgebra
  have hc : ∀ a : A, dualMap g (algebraMap A (DualNumber A) a) = algebraMap A (DualNumber B) a := by
    intro a
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let ψ₀ : DualNumber A →ₐ[A] DualNumber B := AlgHom.mk (dualMap g) hc
  have hψ₀ : ∀ x, ψ₀ x = dualMap g x := fun _ ↦ rfl
  let j : B →ₐ[A] DualNumber B := TrivSqZeroExt.inlAlgHom A B B
  let G : TensorProduct A (DualNumber A) B →ₐ[A] DualNumber B :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber B → TensorProduct A (DualNumber A) B := fun x ↦
    (1 : DualNumber A) ⊗ₜ[A] x.fst + (DualNumber.eps : DualNumber A) ⊗ₜ[A] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, G (h x) = x := by
    intro x
    simp only [h, G, map_add, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀, dualMap_apply]
  have hhg : ∀ x, h (G x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber A) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[A] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add, hadd, hx, hy]
  have hbij : Function.Bijective G := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  let eR : TensorProduct A (DualNumber A) B ≃+* DualNumber B := (AlgEquiv.ofBijective G hbij).toRingEquiv
  refine (CommRingCat.isPushout_tensorProduct A (DualNumber A) B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    eR.toCommRingCatIso (by simp) (by ext; simp [RingHom.algebraMap_toAlgebra]) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (x ⊗ₜ[A] 1) = dualMap g x
    simp [G, hψ₀]
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (1 ⊗ₜ[A] x) = algebraMap B (DualNumber B) x
    simp [G, j, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover

theorem epi_spMap_dualMap {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}
    (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (x : Sp A ⟶ Y) (x' : Sp B ⟶ X) (hsq : IsPullback (spMap g) x' x π) : Epi (spMap (dualMap g)) := by
  have h2 := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_dualMap g)
  have h3 : IsPullback (spMap (dualMap g)) (spMap (algebraMap B (DualNumber B)) ≫ x')
      (spMap (algebraMap A (DualNumber A)) ≫ x) π :=
    (IsPullback.paste_horiz h2.flip hsq.flip).flip
  have he := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG (spMap (algebraMap A (DualNumber A)) ≫ x)
  rw [← h3.isoPullback_hom_fst]
  exact epi_comp _ _

theorem exists_dualCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  intro X Y π Ga _ ρ hG R' _ x
  haveI : IsFinite π := hG.fin
  haveI : IsAffine (pullback x π) := isAffine_of_isAffineHom (pullback.fst x π)
  let X' := pullback x π
  let g₁ : R' →+* Γ(X', ⊤) := (Spec.preimage (X'.isoSpec.inv ≫ pullback.fst x π)).hom
  have hg₁ : spMap g₁ = X'.isoSpec.inv ≫ pullback.fst x π := Spec.map_preimage _
  let x'' : Sp Γ(X', ⊤) ⟶ X := X'.isoSpec.inv ≫ pullback.snd x π
  have hsq : IsPullback (spMap g₁) x'' x π := by
    rw [hg₁]
    exact IsPullback.of_iso_pullback ⟨by simp [x'', pullback.condition]⟩ X'.isoSpec.symm (by simp) (by simp [x''])
  refine ⟨Γ(X', ⊤), inferInstance, g₁, x'', dualMap g₁, hsq.w.symm, ?_, ?_, ?_, epi_spMap_dualMap hG g₁ x x'' hsq⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl']
  · refine RingHom.ext fun a ↦ ?_
    simp
  · intro r
    refine RingHom.ext fun a ↦ ?_
    ext <;> simp [epsScaleR, dualMap_apply] <;> ring

end GlobalTheory.DualCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedComplexPointOfFixedFieldPointStatement
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_complexPoint_of_fixed_fieldPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : Type) [Field k] (x : Sp k ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X), x ≫ ρ = x → ∃ x' : Sp ℂ ⟶ Xo.X, x' ≫ ρ = x' := by
  first | exact @GlobalTheory.FixedCx.exists_fixed_complex_point | exact GlobalTheory.FixedCx.exists_fixed_complex_point | (intros; apply GlobalTheory.FixedCx.exists_fixed_complex_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDetStatement
section
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatSection_valuation_at_finitePlace_eq_sub_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  first | exact @GlobalTheory.DefPt.rho_vw_eq_vAdd_sub | exact GlobalTheory.DefPt.rho_vw_eq_vAdd_sub | (intros; apply GlobalTheory.DefPt.rho_vw_eq_vAdd_sub <;> assumption)
end

