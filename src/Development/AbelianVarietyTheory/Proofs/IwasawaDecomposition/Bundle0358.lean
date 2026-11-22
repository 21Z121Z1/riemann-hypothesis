import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0338

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.NefDescent

theorem fibre_point (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g] [LocallyOfFiniteType g] (z : Z)
    (hz : z ∈ Set.range g) : ∃ w, g w = z ∧ 0 < g.residueDegree w :=
  GlobalTheory.T.exists_preimage_positive_residue_degree W Z g z hz

theorem red_genericPoint (W : Scheme.{0}) (w : W) (Z : Closeds W) (hZ : (Z : Set W) = closure {w})
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme] :
    redι Z (genericPoint _) = w := by
  have h1 : closure {redι Z (genericPoint _)} = closure ({w} : Set W) := by
    rw [← Set.image_singleton, IsClosedMap.closure_image_eq_of_continuous (redι Z).isClosedMap
      (redι Z).continuous, (genericPoint_spec _).def, Set.image_univ, range_redι]
    exact hZ
  exact (inseparable_iff_closure_eq.2 h1).eq

theorem dim_eq_one (Z' Z : Scheme.{0}) [IsIntegral Z'] [IsIntegral Z] [IsNoetherian Z] (f : Z' ⟶ Z) [IsProper f]
    (hd : topologicalKrullDim Z = 1) (hη : f (genericPoint Z') = genericPoint Z)
    (hdeg : 0 < f.residueDegree (genericPoint Z')) : topologicalKrullDim Z' = 1 :=
  GlobalTheory.T.krullDim_one_of_finite_generic Z' Z f hd hη hdeg

theorem isFinite_of_dim (Z' Z : Scheme.{0}) [IsIntegral Z'] [IsIntegral Z] [IsNoetherian Z'] (f : Z' ⟶ Z) [IsProper f]
    (hd' : topologicalKrullDim Z' = 1) (hd : topologicalKrullDim Z = 1)
    (hη : f (genericPoint Z') = genericPoint Z) : IsFinite f := by
  have hsurj : Function.Surjective f := by
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hm : genericPoint Z ∈ Set.range f := ⟨_, hη⟩
    have : closure {genericPoint Z} ⊆ Set.range f := hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hm)
    rw [(genericPoint_spec Z).def] at this
    exact fun z => this (Set.mem_univ z)
  obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
  obtain ⟨x₀, rfl⟩ := hsurj x
  have := ProperCurve.locallyQuasiFinite_of_ne hd' f (x₀ := x₀) (by rw [hη]; exact hx)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

theorem nefFib_of_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), Function.Surjective π → ∀ (L : HermLB p), ArInt.NefFib (L.pull π hπ) → ArInt.NefFib L := by
  intro k _ _ X Y p q hp hq π hπ hsurj L hL
  refine GlobalTheory.T.nefFib_of_curve_degrees_nonneg k X p L ?_
  intro Z i _ _ r _ _ hd
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : Surjective π := ⟨hsurj⟩
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod r) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod r) f
  have h1 := hL _ i' (ZMod r) hd'
  have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have e1 : topSelfIntersection (ZMod r) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod r) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i')
      (fun _ => LB.isLB_pull hN f) fun _ => ?_
    show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))
    rw [← pull_comp, ← pull_comp, hcomm]
  have e2 : topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 = interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) :=
    (interNumOn_const_eq_topSelf (k := ZMod r) (fun _ => rfl) hN 1).symm
  have e3 : interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod r) f ![L.B.pull i] :=
    congrArg _ (funext fun j => by fin_cases j; rfl)
  have hproj : IsProjOver (strHom (ZMod r) Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod r) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod r)))
    exact ProperCurve.isProjOver_of_isProper _ hd
  have e4 := GlobalTheory.T.intersection_number_finite_pushforward (ZMod r) Z _ f hproj hd hη (L.B.pull i) hN
  have e5 : interNum (ZMod r) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [← e5, ← e4, ← e3, ← e2, ← e1]
    exact h1
  exact nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')

end GlobalTheory.NefDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySpec
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC

noncomputable section

namespace GlobalTheory.HeckeLocN

set_option synthInstance.maxHeartbeats 400000

section Transport

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {B : LocBase0 H what₂} {i : LocT B} {j : ℕ} {w : what₂.places.Pl}
  (h : jOf B i = j ∧ wOf B i = w)

def trO : OOf B i ≃+* B.Oc j w := by obtain ⟨rfl, rfl⟩ := h; exact RingEquiv.refl _

def trK : FractionRing (OOf B i) ≃+* FractionRing (B.Oc j w) := by obtain ⟨rfl, rfl⟩ := h; exact RingEquiv.refl _

theorem trK_alg (z : OOf B i) : trK h (algebraMap _ _ z) = algebraMap _ _ (trO h z) := by obtain ⟨rfl, rfl⟩ := h; rfl

theorem trK_ec (x : what₂.LL) : trK h (B.ec _ _ x) = B.ec j w x := by obtain ⟨rfl, rfl⟩ := h; rfl

variable (hC : PartCompl B) (hL : MtLoc B hC)

def trPsi : TensorProduct (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) →ₛₗ[(trK h).toRingHom] B.V j w := by
  obtain ⟨rfl, rfl⟩ := h
  exact { toFun := PsiC B hC hL i, map_add' := map_add _, map_smul' := fun c z => map_smul (PsiC B hC hL i) c z }

theorem trPsi_inj : Function.Injective (trPsi h hC hL) := by obtain ⟨rfl, rfl⟩ := h; exact PsiC_inj B hC hL i

theorem trPsi_range (y : B.V j w) : y ∈ NCov.part (heckeAlg0 B j w) (mxC B j w i) ↔ ∃ z, trPsi h hC hL z = y := by
  obtain ⟨rfl, rfl⟩ := h
  rw [mxC_self]
  exact PsiC_range B hC hL i y

theorem trPsi_pr (x : what₂.MtL (what₂.muTw (wOf B i)) (jOf B i)) (x' : what₂.MtL (what₂.muTw w) j) (hx : HEq x' x) :
    trPsi h hC hL (prMtC B hC hL i x) - B.iV j w x' ∈ NCov.off (heckeAlg0 B j w) (mxC B j w i) := by
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl := eq_of_heq hx
  rw [mxC_self]
  exact PsiC_pr B hC hL i _

def trX : XOf B i ≃ {ψ : heckeAlg0 B j w →ₐ[B.Oc j w] B.Oc j w //
    NCov.cls ψ = mxC B j w i ∧ NCov.W (heckeAlg0 B j w) (NCov.pt ψ) ≠ ⊥} := by
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨fun x => ⟨x.1, x.2.1.trans (mxC_self B i).symm, x.2.2⟩, fun x => ⟨x.1, x.2.1.trans (mxC_self B i), x.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem trX_hT (x : XOf B i) (v : PlE H) (k : ℕ) (hvk : GenAt0 H (what₂.places.resChar w) (B.Qw w) v k) :
    trO h ((hTOf B i v k : XOf B i → OOf B i) x) = (trX h x).1 ⟨B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
  obtain ⟨rfl, rfl⟩ := h
  exact ptX_val B i v k hvk x

theorem trPsi_act (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd))
    (hA : ActHK B hs hd hL hAct) (v : PlE H) (k : ℕ) (hvk : GenAt0 H (what₂.places.resChar w) (B.Qw w) v k) (z) :
    trPsi h _ hL (((actC B (partCompl_of hs hd) hAct i) (hTOf B i v k)).baseChange (FractionRing (OOf B i)) z) =
      B.hK j w v k (trPsi h _ hL z) := by
  obtain ⟨rfl, rfl⟩ := h
  exact hA i v k hvk z

include h in
theorem tr_max : (mxC B j w i).IsMaximal := by obtain ⟨rfl, rfl⟩ := h; exact mxC_max B i

end Transport

variable {D : D7}

def recBase (M : MtFam D) (B0 : LocBase0 D.host D.what₂)
    (hdef : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (B0.Qw w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (B0.hL j w v k x)) =
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)))
    (hO : ∀ w (v v' : PlE D.host), v ∈ B0.Qw w →
      (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ B0.Qw w)
    (hc : ∀ w (v v' : PlE D.host), v' ∈ B0.Qw w → IsConjPl D.host v v' → v ∈ B0.Qw w) : NLocBase D M where
  Oc := B0.Oc
  ec := B0.ec
  ec_w := B0.ec_w
  V := B0.V
  iV := B0.iV
  iV_basis := B0.iV_basis
  Qc _ w := B0.Qw w
  hL := B0.hL
  hL_def := hdef
  hK := B0.hK
  hK_def := B0.hK_def
  split := B0.split
  Qc_over _ := hO
  Qc_conj _ := hc

section Spec

variable (B0 : LocBase0 D.host D.what₂) (C : NChoice D) (hs : HeckeStd0 B0) (hd : FinDimV B0)
  (hL : MtLoc B0 (partCompl_of hs hd))
  (hMF : ∀ i, Module.Free (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hMFin : ∀ i, Module.Finite (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hTL : ∀ i, IsLocalRing (TOf B0 i)) (hAct : ActEx B0 (partCompl_of hs hd))
  (hEig : ∀ i x, heckeEig (TOf B0 i) (actC B0 (partCompl_of hs hd) hAct i) x ≠ ⊥)
  (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
  (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ)
  (hChi : ∀ i c, Continuous (fun g => ((chiN B0 C tw ps i c g : (OOf B0 i)ˣ) : OOf B0 i)))
  (hSQs : ∀ i v, v ∈ (exceptional_places_finite D.host (lOf B0 i)).toFinset ∨ v ∈ B0.Qw (wOf B0 i) → IsSplitPl D.host v)
  (hSQd : ∀ i, Disjoint (exceptional_places_finite D.host (lOf B0 i)).toFinset (B0.Qw (wOf B0 i)))
  (hQl : ∀ w v, v ∈ B0.Qw w → v ∉ placesOver D.host.E (D.what₂.places.resChar w))
  (hRam : ∀ i, ∀ v ∈ B0.Qw (wOf B0 i), ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chi1N B0 C tw ps i g ≠ 1)
  (hI : OsInt B0) (hBF : ∀ i, Module.Free (OOf B0 i) (BjC B0 hI i))

attribute [local instance] LocBase0.algOc

set_option maxHeartbeats 1000000 in

theorem nonempty_spec
    (hTwE : ∀ (a : LocT B0) (x : D.LL0) (y : D.ntw.O0 (C.twI (wOf B0 a))),
      algebraMap (D.ntw.O0 (C.twI (wOf B0 a))) (FractionRing (D.ntw.O0 (C.twI (wOf B0 a)))) y =
        (if C.sd (wOf B0 a) then D.ntw.emb0 (C.twI (wOf B0 a)) else D.ntw.emb0b (C.twI (wOf B0 a))) x →
      B0.ec (jOf B0 a) (wOf B0 a) (x : D.what₂.LL) = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y))
    (hOrd : ∀ a g, ∃ n : ℕ, ps a g ^ (lOf B0 a ^ n) = 1)
    (hOpen : ∀ a, IsOpen ((ps a).ker : Set (G D.host.E D.nd.Om)))
    (hAnti : ∀ a, AntiHom D.ntw.cc (ps a))
    (hRamP : ∀ a, RamExactly (ps a) (↑(B0.Qw (wOf B0 a)) : Set (HeightOneSpectrum (𝓞 D.host.E))))
    (hPl : ∀ a v, v ∈ placesOver D.host.E (lOf B0 a) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ ∈ Dec (F := D.host.E) A, ps a σ = 1)
    (pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ)
    (hdef : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (B0.Qw w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (B0.hL j w v k x)) =
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)))
    (hO : ∀ w (v v' : PlE D.host), v ∈ B0.Qw w →
      (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ B0.Qw w)
    (hc : ∀ w (v v' : PlE D.host), v' ∈ B0.Qw w → IsConjPl D.host v v' → v ∈ B0.Qw w)
    (hQ : ∀ w, B0.Qw w = C.Q w)
    (iq : ∀ j w, FractionRing (B0.Oc j w) →+* Qbar (D.what₂.places.resChar w))
    (hiA : ∀ j w (z : ℤ_[D.what₂.places.resChar w]), iq j w (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w))
      (algebraMap ℤ_[D.what₂.places.resChar w] (B0.Oc j w) z)) =
        algebraMap ℚ_[D.what₂.places.resChar w] (Qbar (D.what₂.places.resChar w)) (z : ℚ_[D.what₂.places.resChar w]))
    (hiL : ∀ j w x, pl.ι w (iq j w (B0.ec j w x)) = D.what₂.embLL x)
    (hBig : ∀ j w, ∀ z ∈ big w, ∃ x, pl.ι w (iq j w x) = z)
    (hAHK : ActHK B0 hs hd hL hAct) (hD : PlGwDisj D)
    (hψ : ∀ (a : LocT B0) (g : G D.host.E D.nd.Om) (y : D.what₂.LL), C.embW (wOf B0 a) y =
      algebraMap (C.Oe (wOf B0 a)) (FractionRing (C.Oe (wOf B0 a)))
        (algebraMap (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a))) (C.Oe (wOf B0 a))
          ((C.psi' (wOf B0 a) (D.ntw.art (C.twI (wOf B0 a)) (C.Q (wOf B0 a)) g) :
            (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a)))ˣ) : D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a)))) →
      B0.ec _ _ y = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) ((ps a g : (OOf B0 a)ˣ) : OOf B0 a))
    (hTwA : ∀ a : LocT B0, haveI : Fact (D.ntw.l (C.twI (wOf B0 a))).Prime := D.ntw.lPrime (C.twI (wOf B0 a))
      ∀ (z : ℤ_[D.ntw.l (C.twI (wOf B0 a))]) (z' : ℤ_[D.what₂.places.resChar (wOf B0 a)]), HEq z z' →
      tw a (@algebraMap _ (D.ntw.O0 (C.twI (wOf B0 a))) _ _ (D.ntw.algO0 (C.twI (wOf B0 a))) z) = algebraMap _ (OOf B0 a) z')
    (hTwR : ∀ a : LocT B0, ∃ (Ω : Type) (_ : Field Ω) (τ : FractionRing (OOf B0 a) →+* Ω)
      (ι : FractionRing (C.Oe (wOf B0 a)) →+* Ω),
      (∀ y, τ (algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y)) =
        ι (algebraMap (C.Oe (wOf B0 a)) (FractionRing (C.Oe (wOf B0 a)))
          (algebraMap (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a))) (C.Oe (wOf B0 a))
            (BlochKatoReduction.Gen.phiK D.ntw (C.twI (wOf B0 a)) (C.k' (wOf B0 a)) y)))) ∧
      ∀ x : D.what₂.LL, τ (B0.ec _ _ x) = ι (C.embW (wOf B0 a) x))
    (hBr : ∀ j w (u : PlE D.host), u ∈ placesOver D.host.E (D.what₂.places.resChar w) →
      ∃ Bw : LocBridge (D.what₂.places.resChar w) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 u)) (B0.Oc j w),
        (∀ x, x ∈ D.nd.plOm.1 u ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef D.host.condN Bw.LL ∧
        ∀ z : B0.Oc j w, iq j w (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w)) z) =
          ((Bw.toLL z : ↥Bw.LL.1) : Loc.Om (D.what₂.places.resChar w))) :
    Nonempty (NdSpec pl M C big (mkX B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF) (mkT B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF hTwE hOrd hOpen hAnti hRamP hPl)) := ⟨{
  iq i := iq (jOf B0 i) (wOf B0 i)
  iq_alg i := hiA _ _
  iq_LL i := hiL _ _
  iq_big i := hBig _ _
  B := recBase M B0 hdef hO hc
  Q_eq j w i h := congrArg B0.Qw ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h).2
  mx := mxC B0
  mx_max j w i h := tr_max ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  mx_inj := mxC_inj B0 (locsFin_of hs hd)
  mx_all := mxC_all B0 (locsFin_of hs hd)
  phO j w i h := trO ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK j w i h := trK ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK_alg j w i h := trK_alg ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK_emb j w i h := trK_ec ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  Psi j w i h := trPsi ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_inj j w i h := trPsi_inj ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_range j w i h := trPsi_range ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_pr j w i h x := trPsi_pr ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL x _ (cast_heq _ _)
  ptX j w i h := trX ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  ptX_hT j w i h := trX_hT ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  iotaC j w := (pl.ι w).toRingHom.comp ((iq j w).comp (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w))))
  iotaC_coh j w i h z := by
    obtain ⟨rfl, rfl⟩ := ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
    rfl
  Qc_eq _ := hQ
  std := hs
  act_hK j w i h := trPsi_act ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) hs hd hL hAct hAHK
  twOf_eq _ := rfl
  twSide_eq _ := rfl
  psi_eq := hψ
  twO_alg := hTwA
  tw_reads a := ⟨tw a, HEq.rfl, hTwR a⟩
  heckeLoc_gamma_places _ := gamN_tg D hD
  nbr i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose
  nbr_ind i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.1
  self_good i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.2.1
  nbr_iq i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.2.2
  bj := bjC B0 hI
  bj_span := bjC_span B0 hI
  bj_rel i s hs' c := by
    obtain rfl : s = sOfC B0 hI i := RingHom.ext fun y => IsFractionRing.injective (OOf B0 i) (FractionRing (OOf B0 i))
      ((hs' y).trans (congrArg Subtype.val ((fracRangeEquiv (OOf B0 i)).apply_symm_apply ⟨_, hI _ _ y⟩)).symm)
    exact bjC_rel B0 hI i c }⟩

end Spec

end GlobalTheory.HeckeLocN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadricFibreMeasureEqSmulNormalisedProduct
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.XbetaScale

theorem continuous_qR {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem units_inf (F : Type) [Field F] [NumberField F] :
    {c : Ainf F | ∀ w, c w ≠ 0} = {c | IsUnit c} := by
  ext c
  simp only [Set.mem_setOf_eq]
  refine Iff.trans ?_ (Pi.isUnit_iff (x := c)).symm
  simp only [isUnit_iff_ne_zero]

theorem units_fv (K : Type) [Field K] : {c : K | c ≠ 0} = {c | IsUnit c} := by
  ext c
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero]

theorem fib_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (hR : Nice R) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E))
    (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (r t : ℝ≥0) (ht : t ≠ 0)
    (hν : (t • ν).IsAddHaarMeasure) (hβ : IsUnit β) (hm : FibAt R σ J μ ν β m)
    (fib : R → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily (r • μ) (fun X => qR R σ J (X 0)) id Set.univ (t • ν) {c | IsUnit c} fib) :
    fib β = (r / t) • m := by
  obtain ⟨fib0, h0, rfl⟩ := hm
  exact (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR M J (r • μ) (t • ν) β _ hν hβ
    ⟨_, GlobalTheory.GramFibreRescale.isFibreFamily_smul h0 r t ht, rfl⟩).2.2 _ ⟨fib, hfib, rfl⟩

end GlobalTheory.GaugeEx.XbetaScale

namespace GlobalTheory.GaugeEx

open XbetaScale

theorem isXbetaMeasure_iff_smul_std : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∃ κ : ℕ → ℝ≥0, (∀ M, κ M ≠ 0) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F) (ψ : AddChar (AF F) ℂ) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), 1 ≤ M → IsHermND σ J → β ≠ 0 → IsCharAF F ψ → IsStdX s σ J β ν → ∀ νX, IsXbetaMeasure F E σ M J ψ β νX ↔ νX = κ M • ν := by
  intro F E _ _ _ _ _ σ hσ d b s
  choose κ hκ0 hκ using GlobalTheory.T.exists_selfDualMeasure_global_const_rank_only F E σ hσ d b s
  refine ⟨κ, hκ0, ?_⟩
  intro M J β ψ ν hM hJ hβ hψ hν
  obtain ⟨mi, mv, hmi, hmv, hprod⟩ := hν
  obtain ⟨nI, nV⟩ := GlobalTheory.GaugeEx.nice_ainf_fv F
  have hβi : IsUnit (algebraMap F (Ainf F) β) := (isUnit_iff_ne_zero.2 hβ).map _
  have hβv : ∀ v : HeightOneSpectrum (𝓞 F), IsUnit (algebraMap F (Fv F v) β) :=
    fun v => (isUnit_iff_ne_zero.2 hβ).map _

  have key : ∀ μi, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi →
      ∀ νi, SdR (Ainf F) (psiInf F ψ) νi →
      ∀ μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) →
      ∀ νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v),
      (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) →
      ∀ fibInf : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi
        {c : Ainf F | ∀ w, c w ≠ 0} fibInf →
      ∀ fibV : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
        {c | c ≠ 0} (fibV v)) →
      IsProd b (κ M • ν) (fibInf (algebraMap F (Ainf F) β))
        (fun v => fibV v (algebraMap F (Fv F v) β)) := by
    intro μi hμi νi hνi μv hμv νv hνv fibInf hfi fibV hfv
    obtain ⟨ri, ti, r, t, e1, e2, e3, e4, -, hti, -, ht, hfin, hk⟩ :=
      hκ M ψ J hψ hJ μi νi μv νv hμi hνi hμv hνv
    have a1 : fibInf (algebraMap F (Ainf F) β) = (ri / ti) • mi := by
      refine fib_eq_smul σ (Ainf F) nI J _ _ _ mi ri ti hti (e2 ▸ hνi.1) hβi hmi fibInf ?_
      rw [← e1, ← e2, ← units_inf]
      exact hfi
    have a2 : (fun v => fibV v (algebraMap F (Fv F v) β)) = fun v => (r v / t v) • mv v := by
      funext v
      refine fib_eq_smul σ (Fv F v) (nV v) J _ _ _ (mv v) (r v) (t v) (ht v) (e4 v ▸ (hνv v).1)
        (hβv v) (hmv v) (fibV v) ?_
      rw [← e3, ← e4, ← units_fv]
      exact hfv v
    rw [a1, a2, ← hk]
    exact GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 1 M ν mi mv (ri / ti) (fun v => r v / t v) hprod hfin

  obtain ⟨⟨νi0, hνi0, -⟩, hWi⟩ := GlobalTheory.T.existsUnique_selfDual_haar_measure_infinite_adeles F E σ hσ ψ hψ
  obtain ⟨μi0, hμi0, -⟩ := hWi M J hJ
  choose νv0 hνv0 using fun v => (GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hσ ψ hψ v).1.exists
  choose μv0 hμv0 using fun v => ((GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hσ ψ hψ v).2 M J hJ).exists
  have exI : ∀ μi, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi →
      ∀ νi, SdR (Ainf F) (psiInf F ψ) νi →
      ∃ fibInf : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi
        {c : Ainf F | ∀ w, c w ≠ 0} fibInf :=
    fun μi hμi νi hνi => GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hσ M J μi νi hM hJ hμi.1 hνi.1
  have exV : ∀ μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) →
      ∀ νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v),
      (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) →
      ∃ fibV : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
        {c | c ≠ 0} (fibV v)) := by
    intro μv hμv νv hνv
    choose fibV hfibV using fun v =>
      (GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM hJ (μv v) (hμv v).1 (νv v) (hνv v).1).2
    exact ⟨fibV, hfibV⟩
  intro νX
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨fi, hfi⟩ := exI μi0 hμi0 νi0 hνi0
    obtain ⟨fv, hfv⟩ := exV μv0 hμv0 νv0 hνv0
    have h1 := (((((h.2 μi0 hμi0).2 νi0 hνi0).2 μv0 hμv0).2 νv0 hνv0).2 fi hfi).2 fv hfv
    have h2 := GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b 1 M _ _ _ (key μi0 hμi0 νi0 hνi0 μv0 hμv0 νv0 hνv0 fi hfi fv hfv)
    refine GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals F E d b 1 M _ _ fun Φ Φinf Φf Φv c1 c2 c3 c4 => ?_
    obtain ⟨p1, -, p3⟩ := h1 d b Φ Φinf Φf Φv c1 c2 c3 c4
    obtain ⟨q1, -, q3⟩ := h2 d b Φ Φinf Φf Φv c1 c2 c3 c4
    exact ⟨p1, q1, p3.trans q3.symm⟩
  · rintro rfl
    refine ⟨?_, ⟨μi0, hμi0⟩, fun μi hμi => ⟨⟨νi0, hνi0⟩, fun νi hνi => ⟨⟨μv0, hμv0⟩, fun μv hμv =>
      ⟨⟨νv0, hνv0⟩, fun νv hνv => ⟨exI μi hμi νi hνi, fun fi hfi => ⟨exV μv hμv νv hνv, fun fv hfv =>
      GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b 1 M _ _ _ (key μi hμi νi hνi μv hμv νv hνv fi hfi fv hfv)⟩⟩⟩⟩⟩⟩
    have hz := (GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν mi mv hprod).2.2.2
      {Y | qR (Ainf F) σ J (Y 0) = algebraMap F _ β}
      (fun v => {Y | qR (Fv F v) σ J (Y 0) = algebraMap F _ β})
      (isClosed_eq (continuous_qR _ σ J) continuous_const).measurableSet
      (fun v => (isClosed_eq (continuous_qR _ σ J) continuous_const).measurableSet)
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ _ nI M J _ _ _ mi s.haar_nuI hβi hmi).1
      (fun v => (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ _ (nV v) M J _ _ _ (mv v) (s.haar_nuV v) (hβv v) (hmv v)).1)
    have hs : {X : Fin 1 → Fin M → AF F ⊗[F] E | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} =
        {X | ¬ (projInf X ∈ {Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
            qR (Ainf F) σ J (Y 0) = algebraMap F _ β} ∧
          ∀ v, projV v (projFin X) ∈ {Y : Fin 1 → Fin M → Fv F v ⊗[F] E |
            qR (Fv F v) σ J (Y 0) = algebraMap F _ β})} := by
      ext X
      exact not_congr ((GlobalTheory.GaugeEx.q_and_unitary_local_components F E σ M J).1 (X 0) β)
    rw [Measure.smul_apply, hs, hz, smul_zero]

end GlobalTheory.GaugeEx
end

