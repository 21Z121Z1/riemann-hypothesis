import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleOfOrdOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.AdjCodimTwo

theorem irreducible_of_ord_one {k K : Type} [Field k] [Field K] {c : k →+* K} (P : Place c)
    (x : P.ring) (hx : P.ord (x : K) = 1) : Irreducible x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hv0 : ((v : P.ring) : K) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
  have e : P.ord (((v : P.ring) * π ^ n : P.ring) : K) = n := by
    push_cast
    rw [P.ord_mul hv0 (pow_ne_zero _ hπ0), P.ord_eq_zero v.isUnit, P.ord_pow, P.ord_irreducible hπ]
    simp
  rw [e] at hx
  obtain rfl : n = 1 := by exact_mod_cast hx
  rw [pow_one]
  exact (irreducible_isUnit_mul v.isUnit).2 hπ

theorem disc_residue_eq : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q)
  (S E : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
  ringKrullDim Q = 2 → S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : L) = 1 → E.ord (u : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
    P.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) = 0) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    F.disc (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) =
      E.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
        (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n Q hQ t u S E ψ f w θ hm hd hS hE hSt hEu hψ hc hf hw hθ hP
  classical
  obtain ⟨hA1, hA2⟩ := GlobalTheory.T.twoDimLocalModel_primePlaces_along_parameters cL Q hQ t u hm hd
  obtain ⟨m, z, hzU, hzG⟩ := GlobalTheory.T.isFreeModuleGenerator_kaehlerWedge_regularPair_cons cL Q hQ t u hm hd
  have hxe : (fun i => ((Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q) i : L)) =
      (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => rfl) j
  have hzT := GlobalTheory.T.isTranscendenceBasis_of_kaehlerWedge_freeGenerator cL Q hQ _ _ (by omega) hzG
  have hzO := GlobalTheory.T.formOrd_freeTopForm_eq_zero_of_isPrimeOf cL Q hQ _ _ hzG
  rw [hxe] at hzT hzO
  obtain ⟨F, hFr, hFu⟩ := GlobalTheory.T.exists_residuePlace_of_twoDimLocalModel cL cK Q hQ t u hm hd S ψ hS hSt hψ hc
  have hQS : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let us : S.ring := ⟨u, hQS u⟩
  let ts : S.ring := ⟨t, hQS t⟩
  let zs : Fin m → S.ring := fun i => ⟨z i, hQS (z i)⟩
  have hF1 : F.ord (ψ us) = 1 := hFu us rfl
  have hB4 := GlobalTheory.T.residuePlace_eval_ne_zero_inv_mem_of_isUnit cL cK Q hQ S ψ F hS.1 hc hFr m z zs (fun _ => rfl) hzU
  have hzF : ∀ i, ψ (zs i) ∈ F.ring := fun i => (hFr _).2 ⟨zs i, (z i).2, rfl⟩
  have hTK := GlobalTheory.T.isTranscendenceBasis_residueField_uniformiser_cons cL cK S ψ hψ hc F m (ψ us) (fun i => ψ (zs i)) ⟨_, hzT⟩ hF1 hzF hB4
  have hFO := GlobalTheory.T.formOrd_kaehlerWedge_uniformiser_residueIndependent_eq_zero cK F m (ψ us) (fun i => ψ (zs i)) hF1 hzF hB4 hTK
  obtain rfl : n = m + 1 := by
    letI := cK.toAlgebra
    have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hw
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hTK
    rw [Cardinal.mk_fin] at h1 h2
    exact_mod_cast h1.trans h2.symm
  let v : Fin (m + 1) → S.ring := Fin.cons us zs
  have hv : (fun i => ψ (v i)) = (Fin.cons (ψ us) (fun i => ψ (zs i)) : Fin (m + 1) → K) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have htv : (Fin.cons (ts : L) (fun i => (v i : L)) : Fin (m + 2) → L) =
      (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  set Ω0 := (dForm cL (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L)) with hΩ0
  set η := dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (m + 1 + 1) → L) with hη
  have hfreeL := (GlobalTheory.T.dvrPlace_topForm_orders_api cL (m + 2) _ hzT).1
  obtain ⟨H, hH⟩ := hfreeL.2 η
  have ht_irr : Irreducible ts := irreducible_of_ord_one S ts hSt
  obtain ⟨h, hhf, hhw⟩ := GlobalTheory.T.residue_topForm_along_primeDivisor_adjunction cL cK (m + 1) S ψ hψ hc ts f v w H ht_irr hf (hv ▸ hTK)
    (htv ▸ hzT) (by rw [htv]; exact hH.symm)
  rw [hv] at hhw
  have hne : ∀ {A M : Type} [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] {ω : M},
      IsFreeGen A ω → ω ≠ 0 := fun hω h0 => one_ne_zero (hω.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  have hIK := GlobalTheory.T.dvrPlace_topForm_orders_api cK (m + 1) _ hTK
  have hIL := GlobalTheory.T.dvrPlace_topForm_orders_api cL (m + 2) _ hzT
  have hwne := hne (GlobalTheory.T.dvrPlace_topForm_orders_api cK (m + 1) _ hw).1
  have hvne := hne hIK.1
  have hΩne : Ω0 ≠ 0 := hne hfreeL
  have hψh : ψ h ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hhw
    exact hwne hhw
  have hh0 : (h : L) ≠ 0 := fun h0 => hψh (by rw [show h = 0 from Subtype.ext h0, map_zero])
  have hf0 : (f : L) ≠ 0 := fun h0 => hf.ne_zero (Subtype.ext h0)
  have ht0 : (t : L) ≠ 0 := fun h0 => ht_irr.ne_zero (Subtype.ext h0)
  have hH0 : H ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hhf
    exact mul_ne_zero hh0 hf0 hhf
  have hFw : F.formOrd (dForm cK (fun i => ψ (w i))) = F.ord (ψ h) := by
    rw [hhw, (hIK.2 F).2.2.1 _ _ hvne hψh, hFO, add_zero]
  have hPη : ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd η = P.ord H := by
    intro P hPQ
    rw [← hH, (hIL.2 P).2.2.1 Ω0 H hΩne hH0, hzO P hPQ, add_zero]
  have hPo : ∀ P : Place cL, P.ord (h : L) + P.ord (f : L) = P.ord H + P.ord (t : L) := by
    intro P
    rw [← P.ord_mul hh0 hf0, ← P.ord_mul hH0 ht0, hhf]
  have hEt : E.ord (t : L) = 0 := (hA2 E hE).resolve_right (by rw [hEu]; norm_num)
  have hSu : S.ord (u : L) = 0 := (hA2 S hS).resolve_left (by rw [hSt]; norm_num)
  have hu0 : (u : L) ≠ 0 := by
    intro h0
    rw [h0] at hEu
    simp [Place.ord] at hEu
  have hE1 := GlobalTheory.T.eq_unit_mul_zpow_regularLocalModel_dimTwo cL Q hQ t u hm hd E hE hEu
  set θ' := Finsupp.mapDomain (fun g : S.ring => (g : L)) θ with hθ'
  have hφs : ∀ g ∈ (Finsupp.single h 1 - θ).support, ψ g ≠ 0 := by
    intro g hg
    rcases Finset.mem_union.1 (Finsupp.support_sub hg) with hg | hg
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
      exact hψh
    · exact hθ g hg
  have hmc : Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.single h 1 - θ) =
      Finsupp.single (h : L) 1 - θ' := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hmψ : Finsupp.mapDomain ψ (Finsupp.single h 1 - θ) =
      Finsupp.single (ψ h) 1 - Finsupp.mapDomain ψ θ := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hφP : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.single h 1 - θ)) = 0 := by
    intro P hPQ hPS hPE
    have h1 := hP P hPQ hPS hPE
    rw [Place.disc, map_add, Place.ordQ_single, hPη P hPQ] at h1
    have hPt : P.ord (t : L) = 0 := by
      by_contra hne'
      have h0 : 0 ≤ P.ord (t : L) := (P.ord_nonneg_iff ht0).2 (hPQ.1 t t.2)
      exact hPS (hA1 P S hPQ hS (lt_of_le_of_ne h0 (Ne.symm hne')) (by rw [hSt]; norm_num))
    have h2 := hPo P
    rw [hPt, add_zero] at h2
    rw [hmc, map_sub, Place.ordQ_single]
    have h3 : ((P.ord (h : L) : ℤ) : ℚ) = (P.ord H : ℚ) - (P.ord (f : L) : ℚ) := by
      rw [← h2]; push_cast; ring
    rw [h3]
    linarith
  have hE2 := GlobalTheory.T.ordQ_mapDomain_residuePlace_transport cL cK Q u S E ψ F hS.1 hSu hu0 hψ hFr hFu hE1 _ hφs hφP
  rw [hmc, hmψ, map_sub, map_sub, Place.ordQ_single, Place.ordQ_single] at hE2
  refine ⟨F, hFr, ?_⟩
  rw [Place.disc, Place.disc, hFw, map_add, Place.ordQ_single, hPη E hE]
  have h2 := hPo E
  rw [hEt, add_zero] at h2
  have h3 : ((E.ord H : ℤ) : ℚ) = (E.ord (h : L) : ℚ) + (E.ord (f : L) : ℚ) := by
    rw [← h2]; push_cast; ring
  rw [h3]
  linarith

end GlobalTheory.AdjCodimTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLineBundlePullbackOfTranslates
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isAmpleLB_pull_fst_of_translates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (c : Pic A.left) (V : A.left.Opens), cls L hL = c → IsAffineOpen V → IsLocus c V → ∀ (T : Over (Sp R)) [IsAffine T.left] (n : ℕ) (a : Fin n → (T ⟶ A)), ⨆ i, ((fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ → (∀ i, GlobalTheory.CechPic.pull (a i).left c + GlobalTheory.CechPic.pull ((a i)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0) → GlobalTheory.IsAmpleLB (L.pull (fst A T).left) := by
  intro R _ _ A _ hA L hL c V hc hV hloc T _ n a hcov hrel
  haveI : IsProper A.hom := hA.proper
  have hL' : (L.pull (fst A T).left).IsLB := LB.isLB_pull hL _
  have h2 : (lbPow (L.pull (fst A T).left) 2).IsLB := GlobalTheory.isLB_lbPow hL' 2
  have hcls : cls _ h2 = 2 • CechPic.pull (fst A T).left c := by
    rw [cls_lbPow hL' 2 h2, cls_pull hL _ hL', hc]
  have hsec : ∀ i, ∃ s : (lbPow (L.pull (fst A T).left) 2).Sec, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s =
      (fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V := fun i =>
    IsLocus.exists_sec h2 (hcls ▸ GlobalTheory.T.translate_mul_inv_isNonvanishingLocus_square (Sp R) A hA c V hloc T (a i) (hrel i))
  choose s hs using hsec
  exact isAmpleLB_of_cover hL' (by norm_num) s (by simp only [hs]; exact hcov)
    fun i => (hs i).symm ▸ GlobalTheory.T.isAffineOpen_preimage_add_inf_preimage_sub_grpScheme R A V hV T (a i)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} →
      IsClosed ((snd G G).left '' N) := by
  intro R _ _ G _ hG x hx hxc N hN hNZ
  have hlft : LocallyOfFiniteType G.hom := by
    haveI := hG.smooth; infer_instance
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) :=
    GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G hlft x hx hxc
  set k := G.left.fromSpecResidueField x
  set f := G.hom
  let i := pullback.snd k (pullback.fst f f)
  have hrange : Set.range i = (pullback.fst f f) ⁻¹' {x} := by
    simp only [i, Scheme.Pullback.range_snd, k, Scheme.range_fromSpecResidueField]
  have hcomp : i ≫ pullback.snd f f =
      (pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f :=
    (pullbackRightPullbackFstIso_hom_snd f f k).symm
  have hcl : IsClosedMap (i ≫ pullback.snd f f) := by
    rw [hcomp]
    haveI := hfin
    haveI : IsFinite (pullback.snd (k ≫ f) f) := inferInstance
    exact ((pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f).isClosedMap
  have hNi : (snd G G).left '' N = (i ≫ pullback.snd f f) '' (i ⁻¹' N) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_of_subset]
    · rfl
    · rw [hrange]; exact hNZ
  rw [hNi]
  exact hcl _ (hN.preimage i.continuous)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSpecialOfLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj
open MonObj
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibre

open GlobalTheory.SplitTorus (torusMap bcIso)

theorem isClosedImmersion_special_of_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Type) [Field K] [Algebra R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G], IsSemiAbelian G →
    ∀ (r : ℕ) (u : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r ⟶ G), IsMonHom u →
    Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u) →
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left := by
  intro R _ _ _ K _ _ G _ hG r u hu hmono
  let k := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure k
  refine GlobalTheory.T.closedImmersion_of_baseChange_field_ext R k Ω (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r) G u ?_
  let p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  obtain ⟨E⟩ := hG.fibres Ω p
  let v := (bcIso p (Fin r → ℤ)).hom ≫ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u
  have hv : IsClosedImmersion v.left := by
    refine GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension Ω _ E r v inferInstance fun q hq φ hφ h => hφ ?_
    have hsep : IsSeparated G.hom := hG.separated
    have e1 : torusMap _ φ ≫ (bcIso p (Fin r → ℤ)).hom =
        (bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ) :=
      (GlobalTheory.SplitTorus.comm_bcMap_iff p _ _).1 (GlobalTheory.SplitTorus.torusMap_bcMap p φ)

    have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map (torusMap _ φ ≫ u) =
        (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map 1 := by
      rw [Functor.map_comp, Functor.map_one, ← cancel_epi (bcIso p (ZMod q)).hom, MonObj.comp_one,
        ← Category.assoc]
      change ((bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ)) ≫ _ = _
      rw [← e1, Category.assoc]
      exact h

    have hk := GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension R k Ω _ _ _ _ hΩ
    have hf : torusMap _ φ ≫ u = 1 :=
      GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow R (ZMod q) G hsep _ _ (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one R (ZMod q) G _ inferInstance hk)

    let pK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    have hK' : (Over.pullback pK).map (torusMap _ φ) = (Over.pullback pK).map (torusMap _ 0) := by
      rw [← cancel_mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u)]
      change (Over.pullback pK).map (torusMap _ φ) ≫ (Over.pullback pK).map u =
        (Over.pullback pK).map (torusMap _ 0) ≫ (Over.pullback pK).map u
      rw [← Functor.map_comp, ← Functor.map_comp, hf, GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]
    rw [GlobalTheory.SplitTorus.pullback_map_torusMap, GlobalTheory.SplitTorus.pullback_map_torusMap,
      cancel_epi, cancel_mono] at hK'
    exact GlobalTheory.SplitTorus.torusMap_injective hK'
  have : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u = (bcIso p (Fin r → ℤ)).inv ≫ v := by
    simp [v]
  rw [this, Over.comp_left]
  haveI : IsIso (bcIso p (Fin r → ℤ)).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (bcIso p (Fin r → ℤ)).inv))
  exact IsClosedImmersion.comp _ _

end GlobalTheory.TorusFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam.Pad GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps

namespace GlobalTheory.BdFib

attribute [local instance] Over.cartesianMonoidalCategory

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def FibAt {k : Type} [Field k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G) : Prop :=
  IsGrpPullback φ.G t.G x m.F ∧ m.e = x ∧ m.IsPullCubical φ.cub t.cub

def IsCochFrame {R : Type} [CommRing R] (x : Sp R ⟶ X) {r : ℕ} (ε : Fin r → TanM x t.G) : Prop :=
  ∃ u : torus R r ⟶ (Over.pullback x).obj t.G, IsMonHom u ∧ IsClosedImmersion u.left ∧
    ∀ i, ∃ e : LieG (torus R r), lieCoord e = Pi.single i 1 ∧
      (tv (ε i)).left = e.1.left ≫ u.left ≫ pullback.fst t.G.hom x

def TorRk {k : Type} [Field k] (x : Sp k ⟶ X) (r : ℕ) : Prop :=
  ∀ T : TorusExtension ((Over.pullback x).obj t.G), @Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _ = r

variable {t}

def IsAbMap {k : Type} [Field k] {x : Sp k ⟶ X} (φ : Fib k) (m : CubeMap φ.G t.G) {n : ℕ} (v : Fin n → (epsR k ⟶ φ.P.A))
    (q : TanM x t.G →ₗ[k] (Fin n → k)) : Prop :=
  ∀ w : TanM x t.G, ∃ w' : epsR k ⟶ φ.G, w'.left ≫ m.F = (tv w).left ∧ IsLieComb (q w) v (w' ≫ φ.q)

def AbLe {z : Sp ℂ ⟶ X} (g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ) (C : ℝ) : Prop :=
  ∀ (φ : Fib ℂ) (m : CubeMap φ.G t.G), FibAt t z φ m → ∀ (n : ℕ), φ.P.g = n → ∀ (u : HolUnif φ.P.A φ.P.L n)
    (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    ∀ (v : TanM z t.G) (v' : epsR ℂ ⟶ φ.G) (W : Fin n → ℂ), v'.left ≫ m.F = (tv v).left → u.IsDiff W (v' ≫ φ.q) →
      Real.pi * (hermForm Hm W W).re ≤ C * (g v v).re

theorem AbLe.mono {z : Sp ℂ ⟶ X} {g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ} (hg : IsBlockMetric g) {C C' : ℝ}
    (h : AbLe g C) (hC : C ≤ C') : AbLe g C' := fun φ m hφ n e u Hm χ hA v v' W h₁ h₂ => by
  refine (h φ m hφ n e u Hm χ hA v v' W h₁ h₂).trans (mul_le_mul_of_nonneg_right hC ?_)
  by_cases hv : v = 0
  · simp [hv]
  · exact (hg.2.1 v hv).le

end Fibre

def HasModel {K : Type} [Field K] [NumberField K] (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (G : Over (Sp (𝓞 K))) (_ : GrpObj G) (θ : A.left ⟶ G.left), IsSemiAbelian G ∧
    IsGrpPullback A G (spMap (algebraMap (𝓞 K) K)) θ

section Large

variable {Y : Scheme.{0}}

def Large (y : Sp Qb ⟶ Y) (Q : ∀ (K : Type) [Field K] [NumberField K], (Sp K ⟶ Y) → Prop) : Prop :=
  ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb),
    ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ →
      ∀ yK : Sp K ⟶ Y, spMap io ≫ yK = y → Q K yK

theorem exists_common {K₁ K₂ : Type} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] (i₁ : K₁ →+* Qb)
    (i₂ : K₂ →+* Qb) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (i : K →+* Qb) (j₁ : K₁ →+* K) (j₂ : K₂ →+* K),
      i.comp j₁ = i₁ ∧ i.comp j₂ = i₂ := by
  let a₁ : K₁ →ₐ[ℚ] Qb := i₁.toRatAlgHom
  let a₂ : K₂ →ₐ[ℚ] Qb := i₂.toRatAlgHom
  haveI : FiniteDimensional ℚ a₁.fieldRange := a₁.toLinearMap.finiteDimensional_range
  haveI : FiniteDimensional ℚ a₂.fieldRange := a₂.toLinearMap.finiteDimensional_range
  let K : IntermediateField ℚ Qb := a₁.fieldRange ⊔ a₂.fieldRange
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField K := ⟨⟩
  refine ⟨K, inferInstance, inferInstance, algebraMap K Qb,
    i₁.codRestrict K.toSubfield fun a => (le_sup_left : a₁.fieldRange ≤ K) ⟨a, rfl⟩,
    i₂.codRestrict K.toSubfield fun a => (le_sup_right : a₂.fieldRange ≤ K) ⟨a, rfl⟩, rfl, rfl⟩

variable {y : Sp Qb ⟶ Y} {Q Q' : ∀ (K : Type) [Field K] [NumberField K], (Sp K ⟶ Y) → Prop}

theorem Large.and (h : Large y Q) (h' : Large y Q') : Large y fun K _ _ yK => Q K yK ∧ Q' K yK := by
  obtain ⟨K₁, _, _, i₁, h₁⟩ := h
  obtain ⟨K₂, _, _, i₂, h₂⟩ := h'
  obtain ⟨K₀, _, _, i, j₁, j₂, e₁, e₂⟩ := exists_common i₁ i₂
  refine ⟨K₀, _, inferInstance, i, fun K _ _ io j hj yK hy => ⟨h₁ K io (j.comp j₁) ?_ yK hy, h₂ K io (j.comp j₂) ?_ yK hy⟩⟩
  · rw [← RingHom.comp_assoc, hj, e₁]
  · rw [← RingHom.comp_assoc, hj, e₂]

theorem epi_spMap {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  have h₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact inferInstanceAs (Module.Flat K L)
  have h₂ : Surjective (spMap f) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem Large.of_point {K₀ : Type} [Field K₀] [NumberField K₀] (io₀ : K₀ →+* Qb) (y₀ : Sp K₀ ⟶ Y)
    (hy : spMap io₀ ≫ y₀ = y)
    (h : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ → Q K (spMap j ≫ y₀)) :
    Large y Q := by
  refine ⟨K₀, _, inferInstance, io₀, fun K _ _ io j hj yK hK => ?_⟩
  have := epi_spMap io
  have e : yK = spMap j ≫ y₀ := by
    rw [← cancel_epi (spMap io), hK, ← hy, ← hj, ← Category.assoc, ← Spec.map_comp]
    rfl
  exact e ▸ h K io j hj

end Large

end GlobalTheory.BdFib

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompleteDVRCharZero_of_finiteInjectiveExtension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  first | exact @GlobalTheory.Mum.cDvr_of_finExt | exact GlobalTheory.Mum.cDvr_of_finExt | (intros; apply GlobalTheory.Mum.cDvr_of_finExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundlePullFlag
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.FlagBaseChange

theorem isFlagBundle_pullFlag : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (g : B' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => GlobalTheory.FlagBaseChange.pullFlag π g (fl a)) :=
  fun B Y B' π g ι E r fl H => GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange B Y B' π g ι E r fl H

end GlobalTheory.FlagBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaBoundFromMeasureStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_bound_from_measure : Hypotheses2 → Gram → Meas → abelian₂ := by
  first | exact @GlobalTheory.CovTop.LamAll.lam | exact GlobalTheory.CovTop.LamAll.lam | (intros; apply GlobalTheory.CovTop.LamAll.lam <;> assumption)
end

