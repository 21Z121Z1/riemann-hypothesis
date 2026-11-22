import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSphericalUnit
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrb

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  rw [hR, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun q hq => absurd (Subsingleton.elim q 1) hq)]
  simp

theorem twOrb_unit_eventually : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ y : GLw n w, (nrmL n w y).val.charpoly = atPl w P → twOrb (thL n w) (GlobalTheory.LFun.KGL w n) y ((GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1) = if ∃ g : GLw n w, g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w n then 1 else 0 := by
  intro E _ _ _ hU n S _ P hP
  filter_upwards [GlobalTheory.T.eventually_bezout_separable_derivative_adicIntegers E P hP.2.2.1] with w hgood
  intro y hy
  obtain ⟨-, hinv, hKθ, hnrm, -⟩ := GlobalTheory.T.localTwist_continuous_involution_integral_properties E hU n w
  set K := GlobalTheory.LFun.KGL w n with hKdef
  set θ := thL n w with hθdef

  have hsumm : ∀ x : GLw n w, GlobalTheory.TwOrbConj.summand θ K y ((K : Set (GLw n w)).indicator 1) x =
      if x⁻¹ * y * θ x ∈ K then
        (((twCent θ y ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) else 0 := by
    intro x
    unfold GlobalTheory.TwOrbConj.summand
    have hc : (fun k : K => (K : Set (GLw n w)).indicator (1 : GLw n w → ℂ) ((x * k)⁻¹ * y * θ (x * k))) =
        fun _ => (K : Set (GLw n w)).indicator (1 : GLw n w → ℂ) (x⁻¹ * y * θ x) := by
      funext k
      have e : (x * (k : GLw n w))⁻¹ * y * θ (x * k) = (k : GLw n w)⁻¹ * (x⁻¹ * y * θ x) * θ k := by
        simp only [map_mul, _root_.mul_inv_rev]; group
      rw [e]
      by_cases hm : x⁻¹ * y * θ x ∈ K
      · rw [Set.indicator_of_mem (show _ ∈ (K : Set (GLw n w)) from
          K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) (hKθ _ k.2)), Set.indicator_of_mem (show _ ∈ (K : Set (GLw n w)) from hm)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (K : Set (GLw n w)) from hm), Set.indicator_of_notMem]
        intro h
        apply hm
        have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem (hKθ _ k.2))
        simpa [mul_assoc] using this
    rw [hc, avg_const]
    by_cases hm : x⁻¹ * y * θ x ∈ K
    · rw [Set.indicator_of_mem (show _ ∈ (K : Set (GLw n w)) from hm), if_pos hm]; simp
    · rw [Set.indicator_of_notMem (show _ ∉ (K : Set (GLw n w)) from hm), if_neg hm]; simp
  rw [GlobalTheory.TwOrbConj.twOrb_eq]
  by_cases hex : ∃ g : GLw n w, g⁻¹ * y * θ g ∈ K
  swap
  · rw [if_neg hex]
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    rw [hsumm, if_neg (fun h => hex ⟨_, h⟩)]
  rw [if_pos hex]
  obtain ⟨g₀, hg₀⟩ := hex
  set y₀ := g₀⁻¹ * y * θ g₀ with hy₀

  have hN₀ : nrmL n w y₀ = g₀⁻¹ * nrmL n w y * g₀ := hnrm g₀ y
  have hQ₀ : (nrmL n w y₀).val.charpoly = atPl w P := by
    rw [hN₀, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hy]
  have hgood₀ : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y₀).val.charpoly + v * derivative (nrmL n w y₀).val.charpoly = 1 := by
    rw [hQ₀]; exact hgood
  have hNK : nrmL n w y₀ ∈ K := by
    unfold nrmL
    split_ifs with hs
    · exact hg₀
    · have : thetaGL n (cj w) y₀ = θ y₀ := by rw [hθdef]; unfold thL; rw [if_neg hs]
      rw [this]; exact K.mul_mem hg₀ (hKθ _ hg₀)

  have huniq : ∀ g : GLw n w, g⁻¹ * y₀ * θ g ∈ K → ∃ t ∈ twCent θ y₀, ∃ k ∈ K, g = t * k := by
    intro g hg
    by_cases hs : IsSplitAt w
    · have hθ1 : θ = MonoidHom.id _ := by rw [hθdef]; unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w y₀ = y₀ := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood₀
      rw [hθ1] at hg ⊢
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL E n w y₀ g hg₀ hgood₀ hg
      exact ⟨t, ht, k, hk, rfl⟩
    · exact GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact E hU n w hs y₀ g hg₀ hgood₀ hg

  have hcomm : ∀ t ∈ twCent θ y₀, t * nrmL n w y₀ = nrmL n w y₀ * t := by
    intro t ht
    have ht' : t * y₀ = y₀ * θ t := ht
    by_cases hs : IsSplitAt w
    · have hθ1 : θ = MonoidHom.id _ := by rw [hθdef]; unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w y₀ = y₀ := by unfold nrmL; rw [if_pos hs]
      rw [hn1]; rw [hθ1] at ht'; simpa using ht'
    · have hn1 : nrmL n w y₀ = y₀ * θ y₀ := by
        unfold nrmL; rw [if_neg hs, hθdef]; unfold thL; rw [if_neg hs]
      rw [hn1]
      calc t * (y₀ * θ y₀) = y₀ * θ t * θ y₀ := by rw [← mul_assoc, ht']
        _ = y₀ * θ (t * y₀) := by simp only [map_mul, mul_assoc]
        _ = y₀ * θ (y₀ * θ t) := by rw [ht']
        _ = y₀ * θ y₀ * t := by simp only [map_mul, hinv, mul_assoc]
  have hcpt : cptPart (twCent θ y₀) ≤ twCent θ y₀ ⊓ K := by
    refine le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1) ((Subgroup.closure_le _).2 fun t ht => ?_)
    exact GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded E n w (nrmL n w y₀) t hNK hgood₀ (hcomm t ht.1) ht.2

  have hT : twCent θ y = (twCent θ y₀).map (MulAut.conj g₀).toMonoidHom := by
    rw [hy₀, GlobalTheory.TwOrbConj.twCent_conj, ← GlobalTheory.TwOrbConj.map_conj_mul, mul_inv_cancel,
      GlobalTheory.TwOrbConj.map_conj_self _ (Subgroup.one_mem _)]
  have hval : GlobalTheory.TwOrbConj.summand θ K y ((K : Set (GLw n w)).indicator 1) g₀ = 1 := by
    rw [hsumm, if_pos hg₀, GlobalTheory.TwOrbConj.relIndex_conj g₀ (twCent θ y₀) (twCent θ y) K _ hT rfl,
      (Subgroup.relIndex_eq_one).2 hcpt]
    simp
  rw [finsum_eq_single _ (DoubleCoset.mk (twCent θ y) K g₀)]
  · obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (twCent θ y) K (DoubleCoset.mk (twCent θ y) K g₀)).symm
    rw [he, GlobalTheory.TwOrbConj.summand_rep θ K y _ g₀ ht hk, hval]
  · intro q hq
    rw [hsumm]
    split_ifs with hm
    · exfalso
      apply hq
      have hm' : (g₀⁻¹ * Quotient.out q)⁻¹ * y₀ * θ (g₀⁻¹ * Quotient.out q) ∈ K := by
        have e : (g₀⁻¹ * Quotient.out q)⁻¹ * y₀ * θ (g₀⁻¹ * Quotient.out q) = (Quotient.out q)⁻¹ * y * θ (Quotient.out q) := by
          rw [hy₀]; simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]; group
        rw [e]; exact hm
      obtain ⟨t, ht, k, hk, he⟩ := huniq _ hm'
      have ht2 : g₀ * t * g₀⁻¹ ∈ twCent θ y := by
        rw [hT]; exact ⟨t, ht, by simp [MulAut.conj_apply]⟩
      symm
      conv_rhs => rw [← DoubleCoset.out_eq' (twCent θ y) K q]
      rw [DoubleCoset.eq]
      refine ⟨g₀ * t * g₀⁻¹, ht2, k, hk, ?_⟩
      calc Quotient.out q = g₀ * (g₀⁻¹ * Quotient.out q) := by group
        _ = g₀ * t * g₀⁻¹ * g₀ * k := by rw [he]; group
    · rfl

end GlobalTheory.UnitOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToOneOfStalkMap
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSResOnto

open GlobalTheory.HSCore.VanishNumberField

theorem vanishFrom_adj_of_nef_big : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (B₀ : LB G.Y), B₀.IsLB →
    IsNef K B₀ → IsBig K B₀ → VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle B₀)) 0 := by
  intro Q K _ _ G B₀ hB₀ hnef hbig j hj q hq
  lift j to ℕ using hj
  let Ω := AlgebraicClosure K
  let S := G.toLinSys
  have hV : S.IsVariety := G.geom.alg.variety
  have hV' := hV.baseChange Ω
  have hH := S.isPullback_baseChange Ω
  haveI : IsIntegral (S.baseChange Ω).Y := hV'.isIntegral
  haveI : SmoothOfRelativeDimension G.D (S.baseChange Ω).str := hV'.smooth
  obtain ⟨hprop, A₀, hA₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hV.proj
  haveI := hprop
  have hstr : strHom K G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom K G.Y) := hstr ▸ hV.proj
  haveI : IsProper (strHom K G.Y) := hstr ▸ hprop

  have hLnef : IsNef K G.L := IsGenerated.isNef_of_isProjOver (L := G.L) ⟨G.N, G.b, G.geom.alg.bpf⟩ hV.proj
  have hLj : IsNef K (lbPow G.L j) := hLnef.pow hA₀ j
  have hNnef : IsNef K (tens B₀ (lbPow G.L j)) := hnef.tens_of_isProjOver hLj hV.proj
  have hNbig : IsBig K (tens B₀ (lbPow G.L j)) := hbig.tens_nef Q.nef hproj hnef hLj

  haveI : IsIntegralHom (spMap (algebraMap K Ω)) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsIntegralHom (S.bcFst Ω) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hH.flip ‹_›
  let π := S.bcFst Ω

  have hN'nef : IsNef Ω ((tens B₀ (lbPow G.L j)).pull π) :=
    PosBaseChange.isNef_pull hNnef hA₀ (hA₀.pull_of_isAffineHom π) π π.isClosedMap
  have hN'big : IsBig Ω ((tens B₀ (lbPow G.L j)).pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hNbig.3
    have hD : topologicalKrullDim G.Y = G.D := topologicalKrullDim_eq_of_smooth G.str G.D hV.smooth
    obtain rfl : D₀ = G.D := by exact_mod_cast hD₀.symm.trans hD
    have hL := LB.isLB_pull hNbig.1 π
    refine (isBig_iff (f := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj
      (topologicalKrullDim_eq_of_smooth _ G.D hV'.smooth)).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hNbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hNbig.1, cls_pull (isLB_lbPow hNbig.1 m), cls_lbPow hNbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull hH (isLB_lbPow hNbig.1 m) 0).symm

  have hM' := LB.isLB_pull (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) π
  have hKV : Subsingleton (coh (twist (structureModule (S.baseChange Ω).Y) ((tw (tens G.K.bundle B₀) G.L j).pull π)) q) :=
    Q.kv.twist (k := Ω) (p := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj (G.K.baseChange hH) hN'nef hN'big hM'
      (by
        rw [cls_pull (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) π]
        erw [cls_pull G.K.isLB π, cls_pull hNnef.isLB π]
        rw [← map_add]
        congr 1
        erw [cls_tens (isLB_tens G.K.isLB hB₀) (Twist.isLB_lbZPow G.isLB j), cls_tens G.K.isLB hB₀,
          cls_tens hB₀ (isLB_lbPow G.isLB j)]
        exact add_assoc _ _ _) hq

  have hY : Subsingleton (coh (twist (structureModule G.Y) (tw (tens G.K.bundle B₀) G.L j)) q) :=
    subsingleton_coh_of_pull (f := G.str) (f' := (S.baseChange Ω).str) hH (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) q hKV
  have hB : (tens G.K.bundle B₀).IsLB := isLB_tens G.K.isLB hB₀
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule G.Y) hB (Twist.isLB_lbZPow G.isLB j)
    (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) rfl
  exact (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q
    ((twistFunctor (lbZPow G.L j)).mapIso (Twist.unitTwistIso (tens G.K.bundle B₀)).symm ≪≫ i)).toEquiv.subsingleton_congr.2 hY

section Comb

variable {K : Type} [Field K] [NumberField K] (G : Geo K)

theorem ger_comb_sum {ι : Type} [Fintype ι] (a : ι → K) (u : ι → Fin G.N → K) (j : G.L.ι) (y : G.Y) (hj : y ∈ G.L.U j) :
    ger y hj ((G.comb (∑ i, a i • u i)).f j) = ∑ i, H0.const G.str y (a i) * ger y hj ((G.comb (u i)).f j) := by
  have key (v : Fin G.N → K) : H0.ofSec G.str ⊤ (G.comb v) =
      Fintype.linearCombination K (fun c => H0.ofSec G.str ⊤ (G.b c)) v := G.ofSec_comb ⊤ v
  rw [← H0.germ_ofSec (p := G.str) j y (TopologicalSpace.Opens.mem_top y) hj, key, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, H0.germ_smul, ← key, H0.germ_ofSec]

theorem vanishesTo_of_isUnit (s : Fin G.D → Fin G.N → K) (g : Matrix (Fin G.D) (Fin G.D) K) (hg : IsUnit g.det)
    {B : LB G.Y} {O : G.Y.Opens} {f : Vanishing.H0 G.str B O} (hf : VanishesTo (G.ideal s) 1 f) :
    VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f := fun y _ hy c hc => by
  have h := vanishesTo_iff_forall.1 hf y hy c hc
  obtain ⟨j, hj⟩ := exists_chart G.isLB y
  rw [pow_one, stalkId_cutIdeal G.isLB _ j y hj] at h ⊢
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_) h
  have e : s a = ∑ i, g⁻¹ a i • ∑ j, g i j • s j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ger y hj ((G.comb (s a)).f j) ∈ Ideal.span _
  rw [e, ger_comb_sum]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Comb

section Germs
variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} {I : Y.IdealSheafData}

theorem vanishesTo_one_of_stalkMap {f : Vanishing.H0 p B O}
    (h : ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ O) (j : (B.pull I.subschemeι).ι)
      (hj : z ∈ (B.pull I.subschemeι).U j),
      (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) f) = 0) :
    VanishesTo I 1 f := by
  intro y hs hy i hi
  obtain ⟨z, rfl⟩ := exists_ι_eq hs
  rw [pow_one, ← ker_stalkMap]
  exact RingHom.mem_ker.2 (h z hy (fun _ => i) (mem_pull.2 hi))

theorem stalkMap_germ_eq_zero {f : Vanishing.H0 p B O} (hf : VanishesTo I 1 f) (z : I.subscheme)
    (hz : I.subschemeι z ∈ O) (i : B.ι) (hi : I.subschemeι z ∈ B.U i) :
    (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ i (I.subschemeι z) hz hi f) = 0 := by
  have := hf _ (ι_mem_support I z) hz i hi
  rw [pow_one, ← ker_stalkMap] at this
  exact RingHom.mem_ker.1 this

end Germs

theorem res_onto : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.L₂ → IsBig K G.L₂ →
    ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s), Function.Surjective fun f => hs.res 0 (G.mulE 0 f) := by
  intro Q K _ _ G hnef hbig s hs
  have hB : (tens G.K.bundle G.L₂).IsLB := isLB_tens G.K.isLB G.isLB₂
  have hB' : (G.adj₂ 0).IsLB := isLB_tw hB G.isLB _
  obtain ⟨g, hg, hreg⟩ := GlobalTheory.T.exists_basis_regular_sequence_of_common_zeros K G s hs _ hB
  have hproj : IsProjOver (GlobalTheory.strHom K G.Y) := by
    rw [GlobalTheory.strHom_eq (f := G.str) fun _ => rfl]
    exact G.geom.alg.variety.proj
  have hinv : ∀ {O : G.Y.Opens} {f : Vanishing.H0 G.str (G.adj₂ 0) O},
      VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f → VanishesTo (G.ideal s) 1 f := by
    intro O f hf
    have e : (fun a => ∑ i, g⁻¹ a i • ∑ j, g i j • s j) = s := funext fun a => by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h := vanishesTo_of_isUnit G (fun i => ∑ j, g i j • s j) g⁻¹ (Matrix.isUnit_nonsing_inv_det g hg) hf
    rwa [e] at h
  have key : ∀ y₀ : sectionsOnClosedSubscheme G.str (G.adj₂ 0) (G.ideal s), ∃ f, resTo suppIn_top f = y₀ := by
    intro y₀
    choose W hW b hb using fun y => GlobalTheory.T.exists_local_lift_sectionsOnClosedSubscheme K G.Y G.str (G.adj₂ 0) hB' (G.ideal s) y₀ y
    have hcomp : ∀ y z, VanishesTo (G.ideal s) 1 (Vanishing.H0.restr inf_le_left (b y) -
        Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 G.str (G.adj₂ 0) (W y ⊓ W z)) := by
      intro y z
      refine vanishesTo_one_of_stalkMap fun z' hz' j hj => ?_
      rw [map_sub, Vanishing.H0.germ_restr, Vanishing.H0.germ_restr, map_sub, ← hb y z' hz'.1 j hj,
        ← hb z z' hz'.2 j hj, sub_self]
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lift_sections_zeroScheme_regularSequence_lineBundle K G.Y hproj G.str _ G.L hB G.isLB G.D _ _ hreg
      (vanishFrom_adj_of_nef_big Q K G G.L₂ G.isLB₂ hnef hbig) (by simp) W b hW
      fun y z => vanishesTo_of_isUnit G s g hg (hcomp y z)
    refine ⟨σ, Vanishing.H0.ext_germ fun z _ => ?_⟩
    obtain ⟨c, hc⟩ := exists_chart hB' ((G.ideal s).subschemeι z)
    refine ⟨fun _ => c, mem_pull.2 hc, ?_⟩
    have h₁ := stalkMap_germ_eq_zero (hinv (hσ ((G.ideal s).subschemeι z))) z (hW _) c hc
    rw [map_sub, Vanishing.H0.germ_restr, map_sub, sub_eq_zero] at h₁
    refine (germ_resTo suppIn_top (fun _ => c) z (mem_pull.2 hc) σ).trans ?_
    rw [hb _ z (hW _) (fun _ => c) (mem_pull.2 hc)]
    exact h₁
  intro y₀
  obtain ⟨f, hf⟩ := key (Vanishing.mulDs G.K G.isLB G.isLB₂ (G.sec s) hs.etale rfl y₀)
  refine ⟨f, ?_⟩
  change hs.res 0 (G.mulE 0 f) = y₀
  rw [hs.res_mulE]
  exact (Vanishing.resDs_eq_iff G.K G.isLB G.isLB₂ (G.sec s) hs.etale suppIn_top rfl f y₀).2 hf

end GlobalTheory.HSResOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignature
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WittFrameSig

open Matrix

theorem Jpq_mul_self (r s : ℕ) : Formalism.UG.Jpq r s * Formalism.UG.Jpq r s = 1 := by
  simp [Formalism.UG.Jpq, fromBlocks_multiply]

theorem le_of_isotropic_diag {n r s k : ℕ} (hn : r + s = n) (J₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hA : Aᴴ * J₀ * A = Formalism.UG.Jpq r s)
    (X Y : Matrix (Fin n) (Fin k) ℂ) (hxx : Xᴴ * J₀ * X = 0) (hxy : Xᴴ * J₀ * Y = 1) : k ≤ r ∧ k ≤ s := by
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hn.symm).trans finSumFinEquiv.symm
  set B : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ := Formalism.UG.Jpq r s * Aᴴ * J₀ with hB
  have hBA : B * A = 1 := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Jpq_mul_self]
  have hAB : A * B = 1 := (Matrix.mul_eq_one_comm_of_equiv e).2 hBA
  have hJ : Bᴴ * Formalism.UG.Jpq r s * B = J₀ := by
    calc Bᴴ * Formalism.UG.Jpq r s * B = Bᴴ * (Aᴴ * J₀ * A) * B := by rw [hA]
      _ = (A * B)ᴴ * J₀ * (A * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J₀ := by rw [hAB]; simp
  refine GlobalTheory.WittSignature.le_of_isotropic_standard (B * X) (Yᴴ * J₀ᴴ * A) ?_ ?_
  · calc Yᴴ * J₀ᴴ * A * (B * X) = Yᴴ * J₀ᴴ * (A * B) * X := by simp only [Matrix.mul_assoc]
      _ = (Xᴴ * J₀ * Y)ᴴ := by rw [hAB]; simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hxy, conjTranspose_one]
  · calc (B * X)ᴴ * Formalism.UG.Jpq r s * (B * X) = Xᴴ * (Bᴴ * Formalism.UG.Jpq r s * B) * X := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hJ, hxx]

end GlobalTheory.WittFrameSig

namespace GlobalTheory.WittFrameSig

open Matrix

theorem wittFrame_le_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
      r₀ ≤ r ∧ r₀ ≤ s := by
  intro F E _ _ _ _ _ σ B n X r s hB hX r₀ Xf Yf hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hc : ∀ x, τ (σ x) = star (τ x) := hB.cm.2.2.2 τ
  obtain ⟨hrs, A, hA⟩ := hX.sig w
  have hmap : ∀ {a b : ℕ} (P : Matrix (Fin n) (Fin a) E) (Q : Matrix (Fin n) (Fin b) E),
      (Formalism.UG.cT (σ : E →+* E) P * ((1 : E) • X.J.map σ) * Q).map τ =
        (P.map τ)ᴴ * (X.J.map τ).map (starRingEnd ℂ) * Q.map τ := by
    intro a b P Q
    rw [one_smul, Matrix.map_mul, Matrix.map_mul]
    congr 2
    · ext i j
      simp [Formalism.UG.cT, conjTranspose_apply, hc]
    · ext i j
      simp [hc]
  have hA' : Aᴴ * (X.J.map τ).map (starRingEnd ℂ) * A = Formalism.UG.Jpq r s := by
    have h := congrArg (fun M => M.map (starRingEnd ℂ)) hA
    simp only [Matrix.map_mul] at h
    have hD : (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).map (starRingEnd ℂ) = fromBlocks 1 0 0 (-1) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
    rw [hD] at h
    rw [Formalism.UG.Jpq, ← h]
    congr 2 <;> ext i j <;> simp [conjTranspose_apply]
  refine le_of_isotropic_diag hrs _ A hA' (Xf.map τ) (Yf.map τ) ?_ ?_
  · rw [← hmap, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [← hmap, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.WittFrameSig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
section
noncomputable section

namespace GlobalTheory.ArchDecay

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infAd (a : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a)

def arch (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def dD (v : κ → mixedEmbedding.mixedSpace F) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  deriv (fun t : ℝ => f (x + fun i => infAd F (t • v i))) 0

def mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) : ℂ :=
  (l (arch F x) : ℂ) * f x

variable (κ) in

abbrev Op : Type := (κ → mixedEmbedding.mixedSpace F) ⊕ ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)

def app (o : Op F κ) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := Sum.elim (fun v => dD F v f) (fun l => mM F l f) o

def size (o : Op F κ) : ℝ := Sum.elim (fun v => ‖v‖) (fun l => ‖l‖) o

def word (w : List (Op F κ)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ := w.foldr (fun o g => app F o g) f

def wordD (w : List (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  word F (w.map Sum.inl) f

def Per (m : ℕ) (f : (κ → AF F) → ℂ) : Prop :=
  ∀ x z : κ → AF F, (∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    z i = (m : AF F) * a) → f (x + z) = f x

@[simp] theorem word_nil (f : (κ → AF F) → ℂ) : word F [] f = f := rfl

@[simp] theorem word_cons (o : Op F κ) (w : List (Op F κ)) (f : (κ → AF F) → ℂ) :
    word F (o :: w) f = app F o (word F w f) := rfl

theorem word_append (w w' : List (Op F κ)) (f : (κ → AF F) → ℂ) : word F (w ++ w') f = word F w (word F w' f) := by
  simp [word, List.foldr_append]

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordEqSmoothingOfReproduced
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AutGrowth

theorem word_eq_smoothing_of_reproduced : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ φ : Sm E a,
    smoothing ν α φ.1 = φ.1 → ∀ l : List (Lie E a), ∃ β : Lie E a → ℂ, IsTest (invSet E a) β ∧
      ((l.map (lie E a)).prod φ).1 = smoothing ν β φ.1 := by
  intro E _ _ _ a ν _ α hα φ hφ l
  induction l with
  | nil => exact ⟨α, hα, by simpa using hφ.symm⟩
  | cons X l ih =>
    obtain ⟨β, hβ, e⟩ := ih
    refine ⟨dens X β, isTest_dens X hβ, ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    funext g
    change lieD X ((l.map (lie E a)).prod φ).1 g = _
    rw [e]
    exact lieD_smoothing ν hβ φ.2 X g

end GlobalTheory.AutGrowth
end

