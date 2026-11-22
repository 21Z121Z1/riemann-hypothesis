import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0732
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0734
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0726
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0735
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSmulMemHatLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthBig

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem exists_modulBar_notMem (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0) :
    ∃ c : 𝓞 D.host.E, c ∈ G.pl.modulBar sc ∧ c ∉ (G.pl.w v).asIdeal := by
  classical
  have hne : ¬ G.pl.modul sc ≤ (GlobalTheory.IdemSupport.cP (G.pl.w v)).asIdeal := by
    intro h
    unfold Places.modul at h
    obtain ⟨v', hv', hle⟩ := (Ideal.IsPrime.prod_le (GlobalTheory.IdemSupport.cP (G.pl.w v)).isPrime).1 h
    have h1 := Ideal.IsPrime.le_of_pow_le (hP := (GlobalTheory.IdemSupport.cP (G.pl.w v)).isPrime) hle
    have h2 : G.pl.w v' = GlobalTheory.IdemSupport.cP (G.pl.w v) :=
      HeightOneSpectrum.ext ((G.pl.w v').isMaximal.eq_of_le (GlobalTheory.IdemSupport.cP (G.pl.w v)).isPrime.ne_top h1)
    have h3 : v' = v := by
      rw [← G.pl.under_w hv', h2, GlobalTheory.IdemSupport.under_cP, G.pl.under_w hv]
    subst h3
    obtain ⟨e, he⟩ := G.pl.w_split v' hv
    exact conjPrime_ne_of_isIdempotentAt he h2.symm
  obtain ⟨c₀, hc₀, hc₀'⟩ := Set.not_subset.1 hne
  refine ⟨D.host.conj • c₀, ?_, ?_⟩
  · unfold Places.modulBar
    exact Ideal.smul_mem_pointwise_smul _ _ _ hc₀
  · have e : D.host.conj • c₀ = GlobalTheory.IdemSupport.cO D c₀ := by
      apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
      rw [Formalism.L2.Pj.algebraMap_conj_smul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap,
        GlobalTheory.IdemSupport.cO_coe, bridge_star_holds D.R D.host]
    rw [e]
    exact hc₀'

theorem v_le_of_mem_shiftId (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0) {a : D.host.E}
    (ha : a ∈ shiftId G) :
    Valued.v (algebraMap D.host.E (Kw (G.pl.w v)) a) ≤ WithZero.exp (-(cosExp G (G.pl.w v) : ℤ)) := by
  obtain ⟨c, hc, hcw⟩ := exists_modulBar_notMem G hv
  have h0 : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc
  have hm : algebraMap (𝓞 D.host.E) D.host.E c * a ∈
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨c, hc, rfl⟩) ha
    rwa [shiftId, mul_left_comm, mul_inv_cancel₀ h0, mul_one] at this
  obtain ⟨o, ho, hoe⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 hm
  have hle : G.pl.modul sc ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := by
    unfold Places.modul
    exact Ideal.prod_le_inf.trans (Finset.inf_le hv)
  have h1 : (G.pl.w v).valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E o) ≤
      WithZero.exp (-(G.pl.depth sc v : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 (hle ho)
  have h2 : (G.pl.w v).valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E c) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm ((G.pl.w v).intValuation_le_one c)
      (not_lt.1 fun h => hcw (((G.pl.w v).intValuation_lt_one_iff_mem c).1 h))
  rw [hoe, map_mul, h2, one_mul] at h1
  rw [(depthAt_w G hv).1, Good.valued_alg]
  exact h1

end GlobalTheory.DepthBig

namespace GlobalTheory.DepthBig
open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames Formalism.L2.DIV

variable {D : D7} {S T : HSp D}

theorem genMap_add (s : Fin S.rank → D.host.E) (t t' : Fin T.rank → D.host.E) :
    GlobalTheory.LatVac.genMap S T 1 s (t + t') = GlobalTheory.LatVac.genMap S T 1 s t + GlobalTheory.LatVac.genMap S T 1 s t' := by
  ext i j
  simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  ring_nf

theorem genMap_smul (s : Fin S.rank → D.host.E) (r : D.host.E) (t : Fin T.rank → D.host.E) :
    GlobalTheory.LatVac.genMap S T 1 s (r • t) = r • GlobalTheory.LatVac.genMap S T 1 s t := by
  ext i j
  simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf

theorem genMap_zero (s : Fin S.rank → D.host.E) : GlobalTheory.LatVac.genMap S T 1 s 0 = 0 := by
  ext i j
  simp [GlobalTheory.LatVac.genMap]

end GlobalTheory.DepthBig

namespace GlobalTheory.DepthBig
open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RowLatChi

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

set_option maxHeartbeats 1000000 in

theorem v_le_of_mem_latO_idLat (hS : IsSelfDualC S ΛS) {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) (w : Pl D.host.E)
    (hw : ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1)
    {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {k : ℕ}
    (hI : ∀ a ∈ I, Valued.v (algebraMap D.host.E (Kw w) a) ≤ WithZero.exp (-(k : ℤ))) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (idLat I ΛT : Set _) fun _ => True) (a : Fin T.rank) (b : Fin S.rank) :
    Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ WithZero.exp (-(k : ℤ)) := by
  set B : WithZero (Multiplicative ℤ) := WithZero.exp (-(k : ℤ)) with hB
  let p : WO S T → Prop := fun u => ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ B
  have hadd : ∀ x y, p x → p y → p (x + y) := fun x y hx hy a b => by
    rw [Matrix.map_add _ (toEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]
    exact Valuation.map_add_le _ (hx a b) (hy a b)
  have hneg : ∀ x, p x → p (-x) := fun x hx a b => by
    rw [Matrix.map_neg _ (toEAf D).map_neg, fr_neg, Matrix.neg_apply, RingHom.map_neg, Valuation.map_neg]
    exact hx a b
  have hzero : p 0 := fun a b => by
    rw [Matrix.map_zero _ (toEAf D).map_zero, show Comparison₂.fr βT βS (0 : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) = 0 by
      rw [Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]
    simp

  have hY : ∀ s ∈ ΛS, ∀ t ∈ idLat I ΛT, ∀ a b,
      Valued.v (cpt (D := D) w (Comparison₂.fr βT βS ((GlobalTheory.LatVac.genMap S T 1 s t).map (eToEAf D)) a b)) ≤ B := by
    intro s hs t ht
    refine Submodule.span_induction (p := fun t _ => ∀ a b,
      Valued.v (cpt (D := D) w (Comparison₂.fr βT βS ((GlobalTheory.LatVac.genMap S T 1 s t).map (eToEAf D)) a b)) ≤ B) ?_ ?_ ?_ ?_ ht
    · rintro _ ⟨r, hr, y, hy, rfl⟩ a b
      have hY0 := genMap_one_mem_homLat hS hs hy
      obtain ⟨s', -, hs'⟩ := Comparison₂.fr_mem_idS hβS hβT (𝔪 := ⊤) (by rw [Submodule.top_smul]; exact hY0) a b
      have h4 := (mem_OA_iff _).1 s'.2 w
      rw [hs'] at h4
      rw [genMap_smul, show (r • GlobalTheory.LatVac.genMap S T 1 s y).map (eToEAf D) =
          eToEAf D r • (GlobalTheory.LatVac.genMap S T 1 s y).map (eToEAf D) from
          Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul],
        Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, Valuation.map_mul,
        show cpt (D := D) w (eToEAf D r) = algebraMap D.host.E (Kw w) r from Comparison₂.cpt_tmul w r]
      exact mul_le_of_le_of_le_one (hI r hr) h4
    · intro a b
      rw [genMap_zero, Matrix.map_zero _ (eToEAf D).map_zero, show Comparison₂.fr βT βS (0 : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) = 0 by
        rw [Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]
      simp
    · intro x y _ _ hx hy a b
      rw [genMap_add, Matrix.map_add _ (eToEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]
      exact Valuation.map_add_le _ (hx a b) (hy a b)
    · intro o x _ hx a b
      rw [show o • x = (algebraMap (𝓞 D.host.E) D.host.E o) • x from (algebraMap_smul _ _ _).symm, genMap_smul,
        show (algebraMap (𝓞 D.host.E) D.host.E o • GlobalTheory.LatVac.genMap S T 1 s x).map (eToEAf D) =
          eToEAf D (algebraMap (𝓞 D.host.E) D.host.E o) • (GlobalTheory.LatVac.genMap S T 1 s x).map (eToEAf D) from
          Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul],
        Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, Valuation.map_mul,
        show cpt (D := D) w (eToEAf D (algebraMap (𝓞 D.host.E) D.host.E o)) =
          algebraMap D.host.E (Kw w) (algebraMap (𝓞 D.host.E) D.host.E o) from Comparison₂.cpt_tmul w _, Good.valued_alg,
        HeightOneSpectrum.valuation_of_algebraMap]
      exact mul_le_of_le_one_of_le (w.intValuation_le_one o) (hx a b)
  refine GlobalTheory.LatVac.latO_induction (p := p) (fun α hα M hM => ?_) hzero hadd hneg hu a b
  induction hM using AddSubgroup.closure_induction with
  | mem M hM =>
    obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hM
    set Y := GlobalTheory.LatVac.genMap S T 1 s t
    have e1 : (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T c s t) : WO S T).map (toEAf D) =
        toEAf D ((pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c) • Y.map (eToEAf D) := by
      ext i j
      simp only [GlobalTheory.LatVac.finTens, Y, GlobalTheory.LatVac.genMap, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [show c * t i * ∑ k, star (s k) * HSpace.gram S k j = c * (1 * t i * ∑ k, star (s k) * HSpace.gram S k j) by ring,
        tmul_eq, RingHom.map_mul]
      rfl
    intro a b
    rw [e1, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      RingHom.map_mul, Valuation.map_mul]
    have h1 : Valued.v (cpt (D := D) w (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)))) ≤ 1 := by
      have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
      exact ((comp_toAd D).int (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E))).1 hi w
    have h2 : Valued.v (cpt (D := D) w (toEAf D (incA D c))) ≤ 1 := by
      rw [show cpt (D := D) w (toEAf D (incA D c)) = algebraMap D.host.E (Kw w) c from Comparison₂.cpt_tmul w c]
      exact hw c hc
    exact mul_le_of_le_one_of_le (mul_le_one' h1 h2) (hY s hs t ht a b)
  | zero => rw [GlobalTheory.LatVac.finTens_zero]; exact hzero
  | add x y _ _ hx hy => rw [GlobalTheory.LatVac.finTens_add]; exact hadd _ _ hx hy
  | neg x _ hx => rw [GlobalTheory.LatVac.finTens_neg]; exact hneg _ hx

end GlobalTheory.DepthBig

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.DepthBig in

theorem GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m →
    ∀ v : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)),
      v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _)
        (fun _ => True) → v ∈ latBig G i → ∀ e : AE D, IsIdemSum e G.pl.W0 →
      e • v ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  intro D hQ T L μ0 hL sc G W M _ i hi u _ hB e he
  have hV : ∀ X : Node, X.InRange D.R.m → IsSelfDualC (G.V X) (G.Λ X) := fun X hX => by
    by_cases h0 : ∀ j, X ≠ .grid 0 j
    · exact (G.isV hX h0).sd
    · push_neg at h0
      obtain ⟨j, rfl⟩ := h0
      exact (GlobalTheory.ChiGrid.colY_isV D T L μ0 hL j hX.2).sd
  have hS := hV (.grid (i + 1) 0) ⟨hi, Nat.zero_le _⟩
  have hT := hV (.grid i 0) ⟨hi.le, Nat.zero_le _⟩
  obtain ⟨βS, hβS⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ _ hS.1
  obtain ⟨βT, hβT⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ _ hT.1
  obtain ⟨e0, e1, e2⟩ := Comparison₂.cpt_idemSum he
  rw [Comparison₂.mem_hatMx_iff hβS hβT]
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, e0, zero_mul]
  · have hfr : Comparison₂.fr βT βS ((e • u).map (toEAf D)) a b = toEAf D e * Comparison₂.fr βT βS (u.map (toEAf D)) a b := by
      have hm : (e • u).map (toEAf D) = toEAf D e • u.map (toEAf D) := Matrix.ext fun i j => by
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      rw [hm, Comparison₂.fr_smul]
      rfl
    have hloc : ∀ w ∈ G.pl.W0, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤
        WithZero.exp (-(cosExp G w : ℤ)) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := (GlobalTheory.DepthFix.mem_orthogonal_frame_iff G).1 hw
      exact v_le_of_mem_latO_idLat hS hβS hβT _ (GlobalTheory.DepthFix.aa_int hL hQ G hw)
        (fun x hx => v_le_of_mem_shiftId G hv hx) hB a b
    have hint : Comparison₂.fr βT βS ((e • u).map (toEAf D)) a b ∈ OA D := by
      refine (mem_OA_iff _).2 fun Q => ?_
      rw [hfr, RingHom.map_mul]
      by_cases hQ : Q ∈ G.pl.W0
      · rw [e1 Q hQ, one_mul]
        exact (hloc Q hQ).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
      · rw [e2 Q hQ, zero_mul]
        exact zero_mem _
    refine ⟨⟨_, hint⟩, (Comparison₂.mem_idS_modul G _).2 fun w hw => ?_, rfl⟩
    show Valued.v (cpt (D := D) w (Comparison₂.fr βT βS ((e • u).map (toEAf D)) a b)) ≤ _
    rw [hfr, RingHom.map_mul, e1 w hw, one_mul]
    exact hloc w hw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtHalfExtensionLatticeIndicatorFn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow

section ThetaExt
variable {D : D7} {m n : ℕ}

theorem isHalf_add_right_iff {e : AE D} {t x : Mx D m n} (hx : IsHalf e x) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add] at h1
    linear_combination h1 - h2
  · intro h i j
    have h1 := h i j
    have h2 := hx i j
    simp only [Matrix.add_apply, mul_add]
    linear_combination h1 + h2

theorem smul_of_isHalf {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : e • x = x := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hx i j

theorem smul_eq_zero_of_isHalf {e e' : AE D} (h : e' * e = 0) {x : Mx D m n} (hx : IsHalf e x) : e' • x = 0 := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  rw [← hx i j, ← mul_assoc, h, zero_mul]

theorem isHalf_smul_idem {e : AE D} (he : e * e = e) (t : Mx D m n) : IsHalf e (e • t) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, he]

def extLin (e₀ e₁ : AE D) (Λ : AddSubgroup (Mx D m n)) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun := extFn e₀ e₁ Λ
  map_add' Φ Ψ := by
    funext t
    simp only [extFn, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c Φ := by
    funext t
    simp only [extFn, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem extFn_shift {e₀ e₁ : AE D} (h10 : e₁ * e₀ = 0) (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ)
    {x : Mx D m n} (hx : IsHalf e₀ x) :
    extFn e₀ e₁ Λ (fun t => Φ (t + x)) = fun t => extFn e₀ e₁ Λ Φ (t + x) := by
  funext t
  have hx' : IsHalf (e₀ + e₁) x := by
    rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
  simp only [extFn]
  rw [isHalf_add_right_iff hx', smul_add, smul_add, smul_of_isHalf hx, smul_eq_zero_of_isHalf h10 hx, add_zero]

theorem extFn_modul {e₀ e₁ : AE D} (Λ : AddSubgroup (Mx D m n)) (Φ : Mx D m n → ℂ) (g : Mx D m n → ℂ)
    (hg : ∀ t, IsHalf (e₀ + e₁) t → g t = g (e₀ • t)) :
    extFn e₀ e₁ Λ (fun t => g t * Φ t) = fun t => g t * extFn e₀ e₁ Λ Φ t := by
  funext t
  simp only [extFn]
  split_ifs with h
  · rw [hg t h]; ring
  · ring

theorem extFn_halfInd {e₀ e₁ : AE D} (h00 : e₀ * e₀ = e₀) (h11 : e₁ * e₁ = e₁) {Λ : AddSubgroup (Mx D m n)}
    (hΛ0 : ∀ u ∈ Λ, e₀ • u ∈ Λ) (hΛ1 : ∀ u ∈ Λ, e₁ • u ∈ Λ) :
    extFn e₀ e₁ Λ (halfInd e₀ Λ) = halfInd (e₀ + e₁) Λ := by
  funext t
  simp only [extFn, halfInd]
  by_cases ht : IsHalf (e₀ + e₁) t
  · have hdec : t = e₀ • t + e₁ • t := by
      rw [← add_smul, smul_of_isHalf ht]
    have hiff : (e₀ • t ∈ Λ ∧ e₁ • t ∈ Λ) ↔ t ∈ Λ := by
      constructor
      · rintro ⟨h0, h1⟩; rw [hdec]; exact Λ.add_mem h0 h1
      · intro h; exact ⟨hΛ0 t h, hΛ1 t h⟩
    have a0 := isHalf_smul_idem h00 t
    have a1 := isHalf_smul_idem h11 t
    rw [if_pos ht]
    by_cases h0 : e₀ • t ∈ Λ <;> by_cases h1 : e₁ • t ∈ Λ
    · rw [if_pos ⟨h0, a0⟩, if_pos ⟨h1, a1⟩, if_pos ⟨hiff.1 ⟨h0, h1⟩, ht⟩, one_mul]
    · rw [if_pos ⟨h0, a0⟩, if_neg (fun h => h1 h.1), if_neg (fun h => h1 (hiff.2 h.1).2), mul_zero]
    · rw [if_neg (fun h => h0 h.1), if_pos ⟨h1, a1⟩, if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h1 h.1), if_neg (fun h => h0 (hiff.2 h.1).1), zero_mul]
  · simp only [if_neg ht]
    rw [if_neg (fun h => ht h.2)]

theorem isThetaAt_extFn : ∀ {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {f₀ Φ f : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → (∀ t y, IsHalf (e₀ + e₁) t → IsHalf (cA D e₀) y → B t y = B (e₀ • t) y) → (∃ T, IsPlaceModel ψ B hs (e₀ + e₁) Λ 1 f₀ T) → IsThetaAt ψ B hs e₀ Λ 1 f₀ Φ f → IsThetaAt ψ B hs (e₀ + e₁) Λ 1 f₀ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) f := by
  intro D m n ψ B hs Λ e₀ e₁ f₀ Φ f h00 h11 h01 hΛ0 hΛ1 hB hex h
  have h10 : e₁ * e₀ = 0 := by rw [mul_comm]; exact h01
  have hsb : ∀ Ψ, IsSBHalf e₀ Λ Ψ → IsSBHalf (e₀ + e₁) Λ (extFn e₀ e₁ Λ Ψ) := fun Ψ hΨ =>
    GlobalTheory.T.isSBHalf_halfExtensionLatticeIndicatorFn h00 h11 h01 hΛ0 hΛ1 hΨ
  refine ⟨hex, fun T hT => ?_⟩
  have hT₀ : IsPlaceModel ψ B hs e₀ Λ 1 f₀ (T ∘ₗ extLin e₀ e₁ Λ) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · have hx' : IsHalf (e₀ + e₁) x := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_add_of_right h10 hx
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => Ψ (t + x))) = hs x (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_shift h10 Λ Ψ hx]
      exact hT.trans _ (hsb Ψ hΨ) x hx'
    · have hy' : IsHalf (cA D (e₀ + e₁)) y := by
        rw [add_comm]; exact GlobalTheory.VecProd.half_conj_add_of_right h10 hy
      simp only [LinearMap.comp_apply]
      change T (extFn e₀ e₁ Λ (fun t => ψ (B t y) * Ψ t)) = hs y (T (extFn e₀ e₁ Λ Ψ))
      rw [extFn_modul Λ Ψ (fun t => ψ (B t y)) (fun t ht => by simp only [hB t y ht hy])]
      exact hT.modul _ (hsb Ψ hΨ) y hy'
    · simp only [LinearMap.comp_apply, one_smul]
      change T (extFn e₀ e₁ Λ (halfInd e₀ Λ)) = f₀
      rw [extFn_halfInd h00 h11 hΛ0 hΛ1]
      simpa using hT.vac
  exact h.2 _ hT₀

end ThetaExt

end GlobalTheory.CosetRow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalSum
section
open NumberField IsDedekindDomain

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweSplitPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

theorem ker_thetaSub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hm : IsMatched Bs G Xc om om' R Rf) (v : Pl F) :
    GlobalTheory.Published.ThetaSub om v (LinearMap.ker (Rf.p v) ⊓ GlobalTheory.WeilM.SB _) := by
  refine ⟨le_inf (hm.fin.inv v) ?_, inf_le_right, ?_⟩
  · rw [augAt, Submodule.span_le]
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  · intro h hh φ hφ φ₁ hφ₁ hact
    refine ⟨?_, hφ₁⟩
    have h0 : Acts (evFin F v) (om' (1, h)) 0 0 := by
      intro r _
      have : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) r = 0 :=
        funext fun x => by simp [tens]
      rw [this, map_zero]
    have := hm.fin.equiv v h hh φ hφ.2 0 (Submodule.zero_mem _) φ₁ hφ₁ 0 (Submodule.zero_mem _) hact h0
      (by rw [map_zero]; exact hφ.1)
    rw [map_zero] at this
    exact this

theorem main : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0 := by
  intro hP hMin F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hm v hv
  obtain ⟨χ, ι, hχ, hbij, htr⟩ := GlobalTheory.T.exists_embedding_at_every_place hP F E σ Bs a a' G Xc om om' hm.triple v hv
  have ha : 1 ≤ a := by have := hm.triple.geo.lt; omega
  have hd : 1 ≤ a + a' := by omega
  have hSB : (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).map ι = GlobalTheory.SplitWeil.SB _ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hbij.mapsTo hx
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
      exact ⟨x, hx, rfl⟩
  have hinj : ∀ N N' : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      N ≤ GlobalTheory.WeilM.SB _ → N' ≤ GlobalTheory.WeilM.SB _ → N.map ι ≤ N'.map ι → N ≤ N' := by
    intro N N' hN hN' hle x hx
    obtain ⟨y, hy, hyx⟩ := hle ⟨x, hx, rfl⟩
    rw [hbij.injOn (hN' hy) (hN hx) hyx] at hy
    exact hy
  have hne : ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      N ≤ GlobalTheory.WeilM.SB _ → N ≠ GlobalTheory.WeilM.SB _ → N.map ι ≠ GlobalTheory.SplitWeil.SB _ := by
    intro N hN hN' he
    exact hN' (le_antisymm hN (hinj _ _ le_rfl hN (by rw [hSB, he])))
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL⟩ := GlobalTheory.T.theta_submodule_chain_bounded hP _ a (a + a') χ hχ
    refine ⟨L, fun r N hN hT => hL r (fun i => (N i).map ι) ?_ fun i => (htr _ (hT i).2.1).1 (hT i)⟩
    intro i j hij
    refine lt_of_le_of_ne (Submodule.map_mono (hN hij).le) fun heq => (hN hij).ne ?_
    exact le_antisymm (hN hij).le (hinj _ _ (hT j).2.1 (hT i).2.1 heq.ge)
  · intro N hN hNne φ hφ
    set K := LinearMap.ker (Rf.p v) ⊓ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) with hKdef
    have hK : GlobalTheory.Published.ThetaSub om v K := ker_thetaSub hm v
    have hKne : K ≠ GlobalTheory.WeilM.SB _ := by
      intro he
      haveI := hm.fin.nontriv v
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
      have hy' : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := by rw [hm.fin.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := hy'
      rw [← he] at hx
      exact hy hx.1
    have hNK : N ⊔ K ≤ GlobalTheory.WeilM.SB _ := sup_le hN.2.1 inf_le_right
    have hsub : GlobalTheory.Published.ThetaSub om v (N ⊔ K) := by
      refine (htr _ hNK).2 ?_
      rw [Submodule.map_sup]
      exact ((htr _ hN.2.1).1 hN).sup ((htr _ inf_le_right).1 hK)
    have hNKne : N ⊔ K ≠ GlobalTheory.WeilM.SB _ := by
      intro he
      have := GlobalTheory.T.theta_submodule_sup_ne_top hP hMin _ a (a + a') ha hd χ hχ _ _ ((htr _ hN.2.1).1 hN) ((htr _ inf_le_right).1 hK)
        (hne _ hN.2.1 hNne) (hne _ inf_le_right hKne)
      apply this
      rw [← Submodule.map_sup, he, hSB]
    have hmem : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
        Rf.p v x ∈ (N ⊔ K).map (Rf.p v) → x ∈ N ⊔ K := by
      intro x hx hpx
      obtain ⟨y, hy, hyx⟩ := hpx
      have hxy : x - y ∈ K := ⟨by simp [LinearMap.mem_ker, map_sub, hyx], Submodule.sub_mem _ hx (hNK hy)⟩
      have : x = y + (x - y) := by abel
      rw [this]
      exact Submodule.add_mem _ hy (Submodule.mem_sup_right hxy)
    rcases hm.fin.irred v ((N ⊔ K).map (Rf.p v)) (fun h hh x hx x₁ hx₁ hact hpx =>
        ⟨x₁, hsub.2.2 h hh x (hmem x hx hpx) x₁ hx₁ hact, rfl⟩) with hbot | htop
    · have : Rf.p v φ ∈ (N ⊔ K).map (Rf.p v) := ⟨φ, Submodule.mem_sup_left hφ, rfl⟩
      rw [hbot] at this
      exact this
    · exfalso
      apply hNKne
      refine le_antisymm hNK fun x hx => hmem x hx ?_
      rw [htop]
      trivial

end GlobalTheory.HoweSplitPlace
end

