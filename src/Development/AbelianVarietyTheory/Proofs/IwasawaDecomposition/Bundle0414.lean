import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0405
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Formalism.LocalToGlobal.Columns.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0010
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabCardOfStabTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCusp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.OSplitBig

theorem exists_big_oSplit : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∃ big : D.what₂.places.Pl → Finset ℂ, ∀ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), AutSpec A M tp.tup Sp.iq L.Y L.C → GlobalTheory.SplitCoef.OSplit (withLoc L) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb
  classical
  have hsys := fun w => GlobalTheory.T.galois_family_local_global D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb w
  choose FA Sy hSy using hsys
  have hexc := fun w : D.what₂.places.Pl => GlobalTheory.T.finite_exceptional_places_over_prime D (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)
  choose FB hFB using hexc
  let Fw : D.what₂.places.Pl → Finset (PlE D.host) := fun w => FA w ∪ FB w ∪ C.Q w
  let Pv : D.what₂.places.Pl → G D.host.E D.nd.Om → PlE D.host → Prop := fun w σ v =>
    v ∉ Fw w ∧ IsSplitPl D.host v ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ
  let pw : D.what₂.places.Pl → (PlE D.host → ℕ → ℂ) → G D.host.E D.nd.Om → ℂ[X] := fun w c σ =>
    if h : ∃ v, Pv w σ v then sysPol D c h.choose else 0
  have hcore := fun (w : D.what₂.places.Pl) (c : PlE D.host → ℕ → ℂ) =>
    GlobalTheory.T.exists_finite_splitting_set_frobeniusPolynomials (D.what₂.places.resChar w) (A.pl.ι w) D.host.E D.nd.Om D.R.nV (frobSet D (Fw w)) (pw w c)
      (dense_frobSet D hCheb (Fw w))
  choose SC hSC using hcore
  refine ⟨fun w => (Sy w).biUnion (SC w), ?_⟩
  intro L Sp hAut i x r hr
  obtain ⟨c, hcS, hc⟩ := hSy ((withLoc L).nd.w i) _ L Sp hAut i x rfl
  haveI : Fact ((withLoc L).nd.l i).Prime := (withLoc L).nd.lPrime i
  letI := (withLoc L).nd.dvrO i
  letI := (withLoc L).nd.algO i
  letI := (withLoc L).nd.finO i
  letI := (withLoc L).nd.topO i
  letI := (withLoc L).nd.trO i
  refine hSC ((withLoc L).nd.w i) c ((withLoc L).nd.l i) ((withLoc L).nd.w_l i) ((withLoc L).nd.O i) ((withLoc L).nd.O_adic i) (Sp.iq i) ?_ ?_ r
    hr.1 hr.2.1 ?_
  · exact fun z => Sp.iq_alg i z
  · intro z hz
    exact Sp.iq_big i z (Finset.mem_biUnion.2 ⟨c, hcS, hz⟩)
  · intro σ hσ
    have hex : ∃ v, Pv ((withLoc L).nd.w i) σ v := hσ
    have hspec := hex.choose_spec
    obtain ⟨hvF, hvs, B, hB, hFr⟩ := hspec
    have hvF' := hvF
    simp only [Fw, Finset.mem_union, not_or] at hvF'
    obtain ⟨⟨hvA, hvB⟩, hvQ⟩ := hvF'
    have hSO : SplitOut (withLoc L).nd i hex.choose := by
      have hQi : (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i) :=
        (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
      obtain ⟨h1, h2⟩ := hFB ((withLoc L).nd.w i) _ hvB
      refine ⟨hvs, ?_, ?_, ?_⟩
      · rw [← (withLoc L).nd.w_l i]; exact h1
      · intro hmem
        apply h2
        have := ((withLoc L).nd.S_def i _).1 hmem
        rw [← (withLoc L).nd.w_l i] at this
        exact this
      · show _ ∉ (withLoc L).nd.Q i
        rw [hQi]; exact hvQ
    refine (congrArg (Polynomial.map _) (hr.2.2 _ hSO B σ hB hFr)).trans ?_
    have hio : (qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i))).toRingHom.comp
        ((Sp.iq i).comp (algebraMap ((withLoc L).nd.O i) (FractionRing ((withLoc L).nd.O i)))) = iotaOC (withLoc L) i := by
      ext z
      simp only [iotaOC, RingHom.comp_apply]
      rw [show (withLoc L).naut.iotaQC i = L.Y.naut.iotaQC i from rfl, hAut.iotaQC i,
        show (withLoc L).naut.iotaQ i = L.Y.naut.iotaQ i from rfl, hAut.iotaQ i]
      rfl
    refine (congrArg (fun f => (heckePol (withLoc L).nd i x hex.choose).map f) hio).trans ?_
    rw [heckePol_map D L i x _ hSO]
    simp only [pw, dif_pos hex, sysPol]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc _ hvA k]

end GlobalTheory.OSplitBig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPureTensorsSeparateTensorProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothPureTensors_separate_tensorProduct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (x : SmT M), x ≠ 0 → ∃ w : M.Vec, ellT M (fun τ => (w τ : M.H τ)) (inclT M x) ≠ 0 := by
  first | exact @GlobalTheory.Mem.PureSep.exists_ellT_ne_zero | exact GlobalTheory.Mem.PureSep.exists_ellT_ne_zero | (intros; apply GlobalTheory.Mem.PureSep.exists_ellT_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatio
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_of_matEq {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) (y : GL (Fin b) A)
    (hm : MatEq x y) : y = castGL h x := by
  subst h
  ext i j
  simp only [castGL, Units.coe_mapEquiv, MulEquiv.coe_toMonoidHom]
  simp [Matrix.reindexAlgEquiv_apply]
  exact (hm.2 i j i j rfl rfl).symm

theorem matEq_castGL {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (x : GL (Fin a) A) : MatEq x (castGL h x) := by
  subst h
  refine ⟨rfl, fun i j i' j' hi hj => ?_⟩
  obtain rfl := Fin.ext hi
  obtain rfl := Fin.ext hj
  simp [castGL]

theorem castGL_mem_UA_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {a b : ℕ} (h : a = b) (x : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.UA hc 1) :
    castGL h x ∈ Formalism.L2.DIV.UA hc 1 := by
  subst h
  have e : castGL (rfl : a = a) x = x := by
    ext i j
    simp [castGL]
  rwa [e]

set_option maxHeartbeats 1000000 in

theorem brgStdV_of_readsStd_one : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m), L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∀ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) →
    ∀ P : ∀ t, LiftBrg.PresL X I hX U Xg tr L cV i t, (∀ t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 (P t)) →
      (∀ t v, (P t).coef v = c v) → BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (P t).extL φ) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i hβ hgram c hc P hR hcoef
  unfold BrgStdV StdSide
  refine ⟨c, ?_, ?_, ?_, X.toD7.sp.cm, ?_⟩
  · intro γ γE g hr hm v
    have hg : g = castGL (rkEq X i).symm γE := castGL_of_matEq _ γE g hm
    subst hg
    exact hc γ γE hr v
  · intro hcm t φ h x hm
    refine ((hR t _ h).trans (hcoef t _)).trans ?_
    congr 1
    rw [Formalism.L2.Col.decoPt_mk]
    unfold ptL
    congr 1
    rw [hβ] at hm
    have hx := castGL_of_matEq (rkEq X i).symm _ _ hm
    rw [hx]
    simp only [matIn, mul_one, inv_one, one_mul, Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  · have hli := (P (Formalism.L2.DIV.mu0F _)).coef_li
    simp only [hcoef] at hli
    exact hli
  · intro h
    obtain ⟨g, hg⟩ := h.2
    have h1 : Formalism.UG.bc (swapAE X.toD7) h.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
      rw [← hg]; exact GlobalTheory.LevSplit.finE_mem_UA _ g
    rw [hgram] at h1
    refine ⟨⟨castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1), castGL_mem_UA_std _ _ _ h1⟩, ?_⟩
    rw [hβ]
    have hm := matEq_castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) h.1)
    simp only [matIn, mul_one]
    exact hm

end GlobalTheory.Mem.R3.LiftBrg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdSideUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.StdUnique

theorem closed_eq_univ {D : D7} (V : HSp D) (C : Set (GA D V)) (hC : IsClosed C) (hQ : ∀ γ ∈ GQ V, γ ∈ C)
    (hf : ∀ h, ∀ k ∈ GfC V, h ∈ C → h * k ∈ C) (h : GA D V) : h ∈ C := by
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, (e h).2 = 1 → h ∈ GinfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))
  have hinf : ∀ h : GA D V, (e h).1 = 1 → h ∈ GfC V := fun h H =>
    MonoidHom.mem_ker.2 (Units.ext ((he h).2.symm.trans (by rw [H]; rfl)))
  have hu : e.symm ((e h).1, 1) ∈ C := by
    by_contra hn
    obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V _ (hfin _ (by rw [e.apply_symm_apply])) Cᶜ
      hC.isOpen_compl hn
    exact hU (hf γ k hk (hQ γ hγ))
  have hk : e.symm (1, (e h).2) ∈ GfC V := hinf _ (by rw [e.apply_symm_apply])
  have := hf _ _ hk hu
  rwa [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply] at this

variable {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is)
include hc

theorem bot_or_top (U : Submodule ℂ c.W) (hU : ∀ γ ∈ GQ V, ∀ w ∈ U, c.ρ γ w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  refine hc.2.2.2.2 U fun h => ?_
  rintro _ ⟨w, hw, rfl⟩
  refine closed_eq_univ V {h | c.ρ h w ∈ U} (U.closed_of_finiteDimensional.preimage (hc.2.2.1 w))
    (fun γ hγ => hU γ hγ w hw) (fun h k hk H => ?_) h
  show c.ρ (h * k) w ∈ U
  rw [map_mul, hc.1 k hk, mul_one]
  exact H

omit hc in

theorem exists_ratMat (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
  exact ⟨g, hg.symm⟩

omit hc

end GlobalTheory.Mem.StdUnique

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedAtConjPrimeIdempotentOfTrivialOffPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.SuppOffPlace

section Gen

variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

theorem prV_entry_eq_zero {n : ℕ} (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (w : HeightOneSpectrum (𝓞 F))
    (h : Formalism.UG.bc (Formalism.UG.prV (E := E) w) g = 1) (i j : Fin n) : Formalism.UG.prV (E := E) w ((g.val - 1) i j) = 0 := by
  have h1 : (Formalism.UG.bc (Formalism.UG.prV (E := E) w) g).val i j = (1 : GL (Fin n) (E ⊗[F] w.adicCompletion F)).val i j := by
    rw [h]
  rw [Formalism.UG.bc, Units.coe_map] at h1
  change Formalism.UG.prV (E := E) w (g.val i j) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] w.adicCompletion F)) i j at h1
  rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eps_mul_of_off (v : HeightOneSpectrum (𝓞 F)) {y : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hy : ∀ w, w ≠ v → Formalism.UG.prV (E := E) w y = 0) : Formalism.UG.P.afsplitEps E v * y = y := by
  rw [← sub_eq_zero]
  apply Formalism.UG.P.afsplit_inj
  intro w
  rw [map_sub, map_mul]
  by_cases h : w = v
  · subst h
    rw [Formalism.UG.P.afsplit_prV_eps, one_mul, sub_self]
  · rw [hy w h, mul_zero, sub_zero]

end Gen

variable {D : D7}

theorem belowPl_conjP {v : HeightOneSpectrum (𝓞 D.host.F)} {Pb : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.L2.Col.IsOver v Pb) : Formalism.IndefR.Fin.belowPl (D := D) (Formalism.L2.Col.conjPrime₂ Pb) = v := by
  apply HeightOneSpectrum.ext
  rw [h]
  ext x
  show Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ∈ Pb.asIdeal ↔
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ Pb.asIdeal
  have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
    rw [show ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) from rfl]
    exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  rw [this]

theorem afsplitI_one (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Formalism.UG.P.afsplitI v (1 : v.adicCompletion D.host.F) = Formalism.IndefR.Fin.sglV v 1 := by
  apply Formalism.IndefR.Fin.af_ext
  intro w
  by_cases hw : w = v
  · subst hw
    rw [Formalism.IndefR.Fin.sglV_same]
    exact Formalism.UG.P.afsplitI_self w 1
  · rw [Formalism.IndefR.Fin.sglV_ne v _ hw]
    exact Formalism.UG.P.afsplitI_ne v w hw 1

theorem swap_finPart_phiE (v : HeightOneSpectrum (𝓞 D.host.F)) :
    swapAE D (finPart D (Formalism.IndefR.Fin.phiE v 1)) = Formalism.UG.P.afsplitEps D.host.E v := by
  rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul, afsplitI_one]
  rfl

theorem suppAt_of_trivial_off : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → ∀ α : GA D V, α ∈ GfC V → (∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1) → SuppAt e V α := by
  intro D V v Pb e hO hI α hα hw
  rw [GlobalTheory.HeckeTrans.suppAt_iff e hα, Formalism.IndefR.Fin.below_of_idemAt hI, belowPl_conjP hO,
    ← GlobalTheory.HeckeTrans.finE_unswap]
  have hM : (finE V α).val.map
      (GlobalTheory.HeckeTrans.unswap D) - 1 =
      ((finE V α).val - 1).map
      (GlobalTheory.HeckeTrans.unswap D) := by
    rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  rw [hM]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  apply Function.LeftInverse.injective (GlobalTheory.HeckeTrans.unswap_swap (D := D))
  rw [map_mul, swap_finPart_phiE, GlobalTheory.HeckeTrans.swap_unswap]
  exact eps_mul_of_off v (fun w hw' => prV_entry_eq_zero _ w (hw w hw') i j)

end GlobalTheory.Mem.SuppOffPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeEqDecoratedLatticeReindexed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftLatStd

theorem hLat_eq_decoPt_N : ∀ (X : Stages) (i : Fin X.toD7.R.m) (Λ : Submodule (𝓞 X.toD7.host.E) (Fin (Vc X.toD7 i).rank → X.toD7.host.E)),
    IsSDFrame (Vc X.toD7 i) 1 Λ 1 → ∀ (SG : Finset (Pl X.toD7.host.E))
    (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Bridge.hLat (Vc X.toD7 i) (eG x) =
        (Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ SG (QuotientGroup.mk x)).1.N.map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap := by
  intro X i Λ hΛ SG eG hx x
  have hΛ' := hΛ
  obtain ⟨c, hfr, -⟩ := hΛ'
  rw [GlobalTheory.HLatMove.hLat_eq_span hΛ, Formalism.L2.Col.decoPt_mk]
  unfold Formalism.L2.Col.decoOf
  rw [dif_pos (Formalism.L2.Col.decorated_lattice_exists _ _ _ _ _ x.2)]
  set h := eG x with hh
  set g := Formalism.UG.bc (swapAE X.toD7) (h : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E)) with hg
  have hxg : (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) = LiftBrg.castGL (LiftBrg.rkEq X i).symm g := (hx x).symm
  have hL : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      (h.1⁻¹).1 *ᵥ (fun j => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y j) ∈
          GlobalTheory.AdLat.hat X.toD7.host.F (Λ : Set (Fin (Vc X.toD7 i).rank → X.toD7.host.E)) ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    have e : ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) =
        fun j => Algebra.TensorProduct.comm X.toD7.host.F _ X.toD7.host.E
          (((h.1⁻¹).1 *ᵥ (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F) ⊗ₜ[X.toD7.host.F] y k)) j) := by
      rw [hg, ← map_inv]
      funext j
      change _ = swapAE X.toD7 _
      rw [RingHom.map_mulVec (swapAE X.toD7)]
      rfl
    have e1 := hfr ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)))
    rw [inv_one, Units.val_one, Matrix.one_mulVec] at e1
    rw [← e1, e]
    constructor
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL Λ _ hz
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ hz
      simpa only [AlgEquiv.symm_apply_apply] using this
  have hR : ∀ y : Fin (Vc X.toD7 i).rank → X.toD7.host.E,
      y ∈ (Formalism.UG.CS.globLat (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (Formalism.L2.Col.stdLat X.toD7.host.E X.B.R.nV)).map
          (LinearEquiv.funCongrLeft (𝓞 X.toD7.host.E) X.toD7.host.E (finCongr (LiftBrg.rkEq X i)).symm).toLinearMap ↔
        ∀ j, ((g⁻¹).1 *ᵥ (fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k))) j ∈
          Formalism.L2.Herm.intAf X.toD7.host.F X.toD7.host.E := by
    intro y
    rw [Submodule.mem_map_equiv, LinearEquiv.funCongrLeft_symm, Formalism.L2.Col.mem_globLat]
    unfold Formalism.L2.Col.pullV
    rw [hxg, ← map_inv]
    simp only [LiftBrg.castGL, Units.coe_mapEquiv, Equiv.symm_symm, LinearEquiv.funCongrLeft_apply]
    simp only [LinearMap.funLeft_apply]
    have e2 : ∀ (M : Matrix (Fin (Vc X.toD7 i).rank) (Fin (Vc X.toD7 i).rank) (Lev.EAf X.toD7)),
        ((Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm)).toRingEquiv.toMulEquiv M) *ᵥ
          (fun a => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y (finCongr (LiftBrg.rkEq X i) a))) =
        fun a => (M *ᵥ fun k => Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E (y k)) (finCongr (LiftBrg.rkEq X i) a) := by
      intro M
      change Matrix.reindexAlgEquiv (Lev.EAf X.toD7) (Lev.EAf X.toD7) (finCongr (LiftBrg.rkEq X i).symm) M *ᵥ _ = _
      rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
      funext a
      simp [Function.comp_def]
    rw [e2]
    exact ⟨fun H j => by simpa using H ((finCongr (LiftBrg.rkEq X i)).symm j), fun H a => H _⟩
  refine le_antisymm (Submodule.span_le.2 fun y hy => (hR y).2 ((hL y).1 hy)) fun y hy => Submodule.subset_span ((hL y).2 ((hR y).1 hy))

end GlobalTheory.Mem.R3.LiftLatStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransportedClassSetPresentationReadsEquivariant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.TransportRead

theorem transport_ext_eq : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ G' Γ' : Type}
    [Group G] [Group Γ] [Group G'] [Group Γ'] {ι : Γ →* G} {J : Subgroup G} (A : Bridge.AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'} {χ' : J' →* ℂˣ}
    (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ)
    (hJ : J' = J.map eG.toMonoidHom) (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k)
    (f : (S.toCSD h).Forms) (g : G'),
    ((Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (eG.symm g))) := by
  intro K _ _ _ S G Γ G' Γ' _ _ _ _ ι J A h W _ _ σ ρ χ coef hli hspan hpair hK1 hgl ι' ρ' J' χ' eG eΓ hι hρ hJ hχ f g
  set P' := (Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ with hP'
  have hJ' : ∀ x, x ∈ J' ↔ eG.symm x ∈ J := fun x => by subst hJ; exact Subgroup.mem_map_equiv
  have hspec := P'.dec_spec g
  set γ' := P'.decG g
  set c := P'.decC g
  set k' := P'.decK g
  have hy : P'.y c = eG (A.y c) := rfl
  have hc : P'.coef = coef := rfl
  let k'' : J := ⟨eG.symm (k' : G'), (hJ' _).1 k'.2⟩
  have hg : eG.symm g = ι (eΓ.symm γ') * A.y c * (k'' : G) := by
    have e : ι (eΓ.symm γ') = eG.symm (ι' γ') := by
      rw [MulEquiv.eq_symm_apply, ← hι, MulEquiv.apply_symm_apply]
    rw [e, hspec, hy]
    simp only [map_mul, MulEquiv.symm_apply_apply, k'']
  have hq : A.q (eG.symm g) = A.gl (eΓ.symm γ', k''⁻¹) • S.outSec.rep c := by
    rw [hg, A.q_mul, A.q_y]
  set φ := (S.res h).symm f with hφ
  have hφc : ((φ : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
    have := Formalism.L2.Col.GSD.resOf_apply S h S.outSec φ c
    rw [← this]
    show (((S.res h) φ).1 : S.Cl → S.V) c = (f : S.Cl → S.V) c
    rw [hφ, LinearEquiv.apply_symm_apply]
  have hk : k' = ⟨eG (k'' : G), by simp only [k'', MulEquiv.apply_symm_apply]; exact k'.2⟩ :=
    Subtype.ext (by simp only [k'', MulEquiv.apply_symm_apply])
  rw [hq, φ.2, hφc, hgl]
  show (χ' k' : ℂ) • ρ' γ' (P'.coef ((f : S.Cl → S.V) c)) = _
  rw [hc, hk, hχ]
  have hγ : ρ' γ' = ρ (eΓ.symm γ') := by rw [← hρ, MulEquiv.apply_symm_apply]
  rw [hγ, map_inv, inv_inv, Units.smul_def]

end GlobalTheory.Mem.TransportRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimesDisjointTwistChosenPrimes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.LevDisj

theorem places_disjoint : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ t : TupU I U, Disjoint (X.B.primes px).vGs (Formalism.L2.Col.QE I.sel t.1) := by
  intro X px I U L hI _ _ t
  rw [Finset.disjoint_left]
  intro P hG hQ
  exact GlobalTheory.KFormsCmp.disj (GlobalTheory.BasePrimes.primes_ok X.B px).1 hI.sel_ok t.1 hI.g_mem hQ hG

end GlobalTheory.Mem.LevDisj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperUnipotentGenericCharacterMemIntegralFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperUnipotentGenericCharacter_mem_integralField : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (p : lev0 I), ((chr0 I p : B.LLˣ) : B.LL) ∈ B.Ks := by
  first | exact @GlobalTheory.Mem.R3.chr0_mem_Ks | exact GlobalTheory.Mem.R3.chr0_mem_Ks | (intros; apply GlobalTheory.Mem.R3.chr0_mem_Ks <;> assumption)
end

