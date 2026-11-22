import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SphNonSplit

theorem not_split_of_overPl (D : D7) {w w' : PlE D.host} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hw : NG.OverPl w v) (hw' : NG.OverPl w' v) (hs : ¬ IsSplitPl D.host w) : ¬ IsSplitPl D.host w' := by
  intro hs'
  have hu : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w =
      HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' :=
    HeightOneSpectrum.ext (hw.trans hw'.symm)
  have hr : Module.finrank (maximalRealSubfield D.host.E) D.host.E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj D.host.E) hr
      (IsCMField.complexConj_ne_one D.host.E) w' w).1 hu with h | h
  · exact hs (h ▸ hs')
  · have hc : (IsCMField.complexConj D.host.E).toRingEquiv = D.host.conj.toRingEquiv := by
      refine RingEquiv.ext fun x => ?_
      apply D.host.φ₀.injective
      show D.host.φ₀ (IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
      rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [hc] at h
    exact hs (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hs' ((GlobalTheory.Mem.Chr.conjPl_main.2.1 _ _ w' w).2 h))

theorem split_of_over_g (D : D7) (k : Fin 2) {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  obtain ⟨u, h | h⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · rw [h]; exact GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u
  · exact GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u) h

theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v)
    (w0 : D.what₂.places.Pl) (j : Fin D.R.m) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hw : NG.OverPl w v) (hs : ¬ IsSplitPl D.host w) :
    v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w0) j) := by
  have hg : v ∉ gPl D := by
    rintro ⟨w', hw', k, hk⟩
    exact not_split_of_overPl D hw hw' hs (split_of_over_g D k hk)
  rintro (h | h)
  · exact hg h
  · rw [qPl_tup] at h
    obtain ⟨-, w', hw', hr⟩ := h
    apply not_split_of_overPl D hw hw' hs
    rw [tp.xi_tw] at hr
    by_contra hns
    apply hr
    have hpsi : (tp.psi w0).UnrAt w' := by
      obtain ⟨Q, hQ⟩ := tp.psi_gen w0
      exact (hQ.ram w').2 fun hq => hns (hQ.split w' hq)
    by_cases hl : D.what₂.places.resChar w0 = D.host.pde
    · have hd : cf.del'.UnrAt w' := cf.isDel'.unr w' fun hp => hns (hsp w' (Or.inr hp))
      intro x hx
      simp [Host.CharFrame.delAt, hl, hd x hx, hpsi x hx]
    · have hd : cf.del.UnrAt w' := cf.isDel.unr w' fun hp => hns (hsp w' (Or.inl hp))
      intro x hx
      simp [Host.CharFrame.delAt, hl, hd x hx, hpsi x hx]

end GlobalTheory.SphNonSplit

namespace GlobalTheory.SphNonSplit

theorem sphAU_of_not_split : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), ¬ IsSplitPl D.host w → D.nbc.sphAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _hCS hMI _hstar _hE hsp _hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hns
  set v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w with hv
  have hover : NG.OverPl w v := rfl
  rw [A.au.sph (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 _ w v hns hover]
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = X.nd.j i := by simp only [j]; omega
  have hvB := not_mem_bad D cf C tp hsp (X.nd.w i) j w v hover hns
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
    have key : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
        NG.HypOutside (M μ jj k1 k2).J (M μ jj k1 k2).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
      rintro μ jj k1 k2 rfl rfl
      exact hMI.hyp (X.nd.w i) j
    exact key _ _ _ _ (X.nd.mu_w i) hj.symm
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (hne P)
  have hry : (mlX M X i).real y ≠ 0 := fun h0 =>
    hy0 ((mlX M X i).real_inj (h0.trans (map_zero (mlX M X i).real).symm))
  have hT : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.T.fixed_vector_of_mem_isotypic_component (mlX M X i).wt.ρ (F P)
    {κ | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {v} κ} (irr P) _ hy hry (by
      rintro κ ⟨hU, htr⟩
      have ht : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))ᶜ κ := fun u hu =>
        htr u (by rintro rfl; exact hu hvB)
      have hJ : κ ∈ (mlX M X i).J := ((hyp κ ht).1).2 hU
      rw [hT.2 ⟨κ, hJ⟩, (hyp κ ht).2 hJ, Units.val_one, one_smul])
  exact ⟨f, hfS, hf0, fun κ hU htr => hfix κ ⟨hU, htr⟩⟩

end GlobalTheory.SphNonSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyResidualImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.ChiOneRead

theorem localIdele_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Neutral.B1.localIdele E P u = Units.map (Formalism.L2.NC.locM P) u := by
  classical
  apply Units.ext
  rfl

theorem sqrt_zpow (q : ℕ) (r : ℕ) (t nV : ℕ) (h : nV = r + t) :
    ((Real.sqrt q : ℝ) : ℂ) ^ (-(r : ℤ)) = ((q : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 + (1 - (nV : ℝ)) / 2) : ℝ) : ℂ) := by
  subst h
  have e : (((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2) = -(r : ℝ) / 2 := by push_cast; ring
  rw [e]
  rw [show ((q : ℕ) : ℂ) = ((q : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast; ring

theorem chiOne_read : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∃ Bf : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ Bf, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P ∧ ∀ σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om, IsFrob (F := D.host.E) (X.nd.plOm.1 P) (normV P) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val P)⁻¹ : ℂˣ).1 * ((normV P : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i j hj
  classical
  obtain ⟨B1, h1⟩ := Bs.chi.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) (X.nd.j_range i).1 (X.nd.j_range i).2
  have hpsi := tp.psi_is (X.nd.w i) (X.nd.w_tw i)
  have hfin := Formalism.L2.NC.finite_placesOver (E := D.host.E) (X.nd.l i)
  refine ⟨B1 ∪ C.Q (X.nd.w i) ∪ hfin.toFinset, fun P hP => ?_⟩
  have hP1 : P ∉ B1 := fun h => hP (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hPQ : P ∉ C.Q (X.nd.w i) := fun h => hP (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hPl : P ∉ placesOver D.host.E (X.nd.l i) := fun h => hP (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  obtain ⟨α, hα, x, hx, hσ⟩ := h1 P hP1
  have hxi : tp.xi (X.nd.mu i) = cf.delAt (X.nd.l i) * tp.psi (X.nd.w i) := by
    rw [X.nd.mu_w i, tp.xi_tw, X.nd.w_l i]
  have hl' : D.ntw.l (T.twOf i) = X.nd.l i := T.twOf_l i
  have key : ∀ z : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ, (Bs.chiD.firstHeckeCharacter (T.twOf i) (X.nd.j i)).χ z =
      (cf.mu0 j).1 z * (cf.delAt (X.nd.l i)).1 z * (cf.eta.1 z)⁻¹ := by
    intro z
    simp only [Formalism.L2.NC.NChiData.firstHeckeCharacter, Formalism.L2.NC.HC.mul_χ, Formalism.L2.NC.HC.inv_χ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [← hj, Bs.ringSpec_normalisedCharacter_eq j z, Bs.eta_eq]
    have hd := Bs.del_eq (T.twOf i) z
    rw [hl'] at hd
    erw [hd]
  have hloc : ∀ (χ : HChar D.host.E) (u : (P.adicCompletion D.host.E)ˣ),
      χ.loc P u = χ.1 (Units.map (Formalism.L2.NC.locM P) u) := fun χ u => by
    rw [← localIdele_eq]; rfl
  have hunr : (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P := by
    intro u hu
    have e1 := hα.1 u hu
    rw [key] at e1
    have e2 : (tp.psi (X.nd.w i)).loc P u = 1 := ((hpsi.ram P).2 hPQ) u hu
    rw [hloc] at e2
    rw [hloc]
    show (cf.mu0 j * tp.xi (X.nd.mu i) * cf.eta⁻¹).1 _ = 1
    rw [hxi]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.mul_apply, MonoidHom.inv_apply] at e1 e2 ⊢
    rw [e2, mul_one]
    exact e1
  refine ⟨hunr, fun σ hσF => ?_⟩
  have hϖ : IsUnifAt P (atFin P (unif P)) := unif_spec P
  have hαv : α = ((cf.mu0 j).val P : ℂ) * ((cf.delAt (X.nd.l i)).val P : ℂ) * ((cf.eta.val P : ℂˣ) : ℂ)⁻¹ := by
    rw [← hα.2 _ hϖ, key]
    simp only [HChar.val, HChar.locK, HChar.loc, MonoidHom.comp_apply, localIdele_eq, Units.val_mul,
      Units.val_inv_eq_inv_val]
  have hc : ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i) =
      T.twist₂ i (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i)) *
        (T.psiL i σ : X.nd.O i) := by
    rw [T.chi_tw i]; rfl
  have hR1 : (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.twist₂ i (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i))))) =
      D.what₂.embLL (x : D.what₂.LL) := by
    have e := T.twO_emb i x (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i)) (hσ σ hσF)
    rw [← e, Sp.iq_LL]
  obtain ⟨ψ0, -, h2, -⟩ := hCS.nct.psi_eq
  have hR2 : (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.psiL i σ : X.nd.O i))) = D.what₂.embLL ((ψ0 (X.nd.w i) σ : (D.what₂.LL)ˣ) : D.what₂.LL) := by
    have e3 := Sp.psi_eq i σ _ (h2 (X.nd.w i) σ)
    rw [← e3, Sp.iq_LL]
  obtain ⟨y, hy⟩ := hψ (X.nd.w i) (X.nd.w_tw i) P ((hpsi.ram P).2 hPQ)
  have hy' : D.what₂.embLL y⁻¹ = ((((tp.psi (X.nd.w i)).val P)⁻¹ : ℂˣ) : ℂ) := by
    rw [map_inv₀, hy]
    simp [HChar.valTw]
  have hl2 : P ∉ placesOver D.host.E (D.what₂.places.resChar (X.nd.w i)) := by rw [X.nd.w_l i]; exact hPl
  have e4 := hCS.psi (X.nd.w i) (X.nd.w_tw i) P hPQ hl2 (X.nd.plOm.1 P) σ (X.nd.plOm.2 P) hσF y⁻¹ hy'
  have e5 : ((ψ0 (X.nd.w i) σ : (D.what₂.LL)ˣ) : D.what₂.LL) = y⁻¹ :=
    (C.embW (X.nd.w i)).injective (by rw [e4]; exact h2 _ σ)
  rw [hc, map_mul, map_mul, map_mul, hR1, hR2, e5, hy']
  have hx' : D.what₂.embLL (x : D.what₂.LL) = α⁻¹ * ((Real.sqrt (normV P) : ℝ) : ℂ) ^ (-(D.R.r : ℤ)) := hx
  rw [hx', ← sqrt_zpow (normV P) D.R.r D.R.t D.R.nV rfl, hαv]
  simp only [TupTied.tup, hxi, HChar.val_mul, HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  ring
end GlobalTheory.ChiOneRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariantAction_smoothVectors_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (k : ℕ), ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k w = c • w := by
  first | exact @GlobalTheory.SmVec.GelfScalar.gelfH_scalar | exact GlobalTheory.SmVec.GelfScalar.gelfH_scalar | (intros; apply GlobalTheory.SmVec.GelfScalar.gelfH_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantsActKernelFamilyShiftedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ (Y M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (Y → GA D V → ℂ)), (∀ f y, κ f y ∈ SmFun θ V) → ∀ (τ : D.what₂.Tau) (Q : Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Module.End ℂ M), Formalism.REAL.GlRel (fun i j => Q (Matrix.single i j 1)) → (∀ X ∈ lieAt V τ, ∃ lam : ℂ, ∀ f y g, HasDerivAt (fun t : ℝ => κ f y (g * oneP θ V τ X t)) (κ (Q X f + lam • f) y g) 0) → ∃ c : ℂ, ∀ k f y, gelf θ V τ k (κ f y) = κ (GlobalTheory.SmoothForms.gelfA (fun i j => Q (Matrix.single i j 1) + if i = j then algebraMap ℂ (Module.End ℂ M) c else 0) k f) y := by
  first | exact @GlobalTheory.Mem.Lift.OneSide.gelf_kernel | exact GlobalTheory.Mem.Lift.OneSide.gelf_kernel | (intros; apply GlobalTheory.Mem.Lift.OneSide.gelf_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointsEquivFibre
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ClosurePts

theorem lift_closed {K : Type} [Field K] {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z)
    (y : Sp K ⟶ X) (h : below y = i z) : ∃ y' : Sp K ⟶ Z, y' ≫ i = y := by
  obtain ⟨ψ, rfl⟩ := ExtConj.factor y _ h
  have hbij : Function.Bijective (i.residueFieldMap z).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have : IsIso (i.residueFieldMap z) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  refine ⟨Spec.map (inv (i.residueFieldMap z) ≫ ψ) ≫ Z.fromSpecResidueField z, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id_assoc]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X) (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ M.X) [IsClosedImmersion i], IsArithVar (i ≫ M.p) 0 → i (genericPoint Z) = M.j x → ∀ (K : Type) [Field K] (σ : F →+* K), ∃ E : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} ≃ {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap σ} // below y.1 = x}, ∀ y, (E y).1.1 ≫ M.j = y.1 ≫ i ∧ below y.1 = genericPoint Z := by
  intro F _ _ Y M x Z _ i _ hZ hx K _ σ
  have : CharZero K := charZero_of_injective_ringHom σ.injective
  have hgen (y : Sp K ⟶ Z) : below y = genericPoint Z :=
    SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField K Z y).2.hom.charZero
  have hpre : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F)) (S := F)
  have hj : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip hpre
  have hs : spMap (σ.comp (algebraMap (𝓞 F) F)) = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Spec.map_comp]
    rfl
  have hw (y : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))}) :
      (y.1 ≫ i) ≫ M.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [Category.assoc, y.2, hs]
  let f : {y : Sp K ⟶ Z // y ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F))} →
      {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap σ} // below y.1 = x} := fun y =>
    ⟨⟨M.pb.lift (y.1 ≫ i) (spMap σ) (hw y), M.pb.lift_snd _ _ _⟩, by
      apply M.j.isEmbedding.injective
      rw [← hx, ← hgen y.1]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun t : Sp K ⟶ M.X => below t) (M.pb.lift_fst _ _ (hw y))).trans
          (Scheme.Hom.comp_apply _ _ _))⟩
  have hf (y) : (f y).1.1 ≫ M.j = y.1 ≫ i := M.pb.lift_fst _ _ _
  refine ⟨Equiv.ofBijective f ⟨fun a b h => ?_, ?_⟩, fun y => ⟨hf y, hgen y.1⟩⟩
  · apply Subtype.ext
    rw [← cancel_mono i, ← hf, ← hf, h]
  · rintro ⟨⟨y, hy⟩, hyx⟩
    obtain ⟨y', hy'⟩ := lift_closed i (genericPoint Z) (y ≫ M.j)
      ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg M.j hyx).trans hx.symm))
    have h1 : y' ≫ (i ≫ M.p) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
      rw [← Category.assoc, hy', Category.assoc, M.pb.w, ← Category.assoc, hy, hs]
    refine ⟨⟨y', h1⟩, Subtype.ext (Subtype.ext (M.pb.hom_ext ((hf _).trans hy') ?_))⟩
    exact (f ⟨y', h1⟩).1.2.trans hy.symm

end GlobalTheory.TrueGeo.ClosurePts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodAtOfFixRed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7}

def FixRed (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd)
    (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) : Prop :=
  ∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsRedBasis X (D.naut.plGw kv.1 kv.2) (b kv) ∧ ∀ k ∈ X.B.I.Kset, ∀ i,
    X.B.I.fmat k *ᵥ incl X.B.I (b kv i) -
      ∑ j, (((((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) •
        incl X.B.I (b kv j) ∈ wLf X (D.naut.plGw kv.1 kv.2)

theorem goodAt_of_fixRed {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (hf : FixRed X red b) :
    ∀ k ∈ X.B.I.Kset, GoodAt X k (red k) :=
  fun k hk kv => ⟨b kv, (hf kv).1, (hf kv).2 k hk⟩

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodOperatorSpectrumStatement
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_operator_spectrum : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (fc X.zs).Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin ((fc X.zs).Dc.a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (R.wU u) = u) → (fc X.zs).Sp = spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (R.wU u) i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) → ∀ (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (sEEc : X.EE →ₗ⋆[ℂ] Tw s (HHX St)), HEq sEE sEEc → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (κ₀ : ℂ), κ₀ ≠ 0 → (∀ F, Tw.out (sEEc (M.eR F)) = κ₀ • conjHH St G (j F)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu St u hK), colDictL St (pw u).Tr hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR F), (fc X.zs).Sp.Pu (R.wU u) (cjv s (M.cφ u φ))⟫_ℂ = cj s (κ * ⟪((conjHH St G (j F) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T⟫_ℂ) := by
  first | exact @GlobalTheory.Mem.SJ.PairMain.pair_step | exact GlobalTheory.Mem.SJ.PairMain.pair_step | (intros; apply GlobalTheory.Mem.SJ.PairMain.pair_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharConjSelfDualInfinityInfinitesimalIffFieStatement
section
open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_conjSelfDual_infinity_infinitesimal_iff_field : ∀ {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H; (∀ z, dchi χ (-star z) = dchi χ z) ↔ ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹ := by
  first | exact @GlobalTheory.CuspRep.csdInf_iff | exact GlobalTheory.CuspRep.csdInf_iff | (intros; apply GlobalTheory.CuspRep.csdInf_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeMultiplicityEqFinrankJointEigenspace
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  NumberField IsDedekindDomain Polynomial Module Module.End

section Gen
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem heckeEig_mem_iff_gens (N : NData R H what₂) (i : N.Loc) (x : N.X i)
    (y : TensorProduct (N.O i) (FractionRing (N.O i)) (N.Mt i)) :
    y ∈ heckeEig (N.T i) (N.act i) x ↔ ∀ v k, SplitOut N i v → 1 ≤ k → k ≤ R.nV →
      ((N.act i (N.hT i v k)).baseChange (FractionRing (N.O i))) y =
        algebraMap (N.O i) (FractionRing (N.O i)) ((N.hT i v k : N.X i → N.O i) x) • y := by
  constructor
  · intro hy v k _ _ _
    exact mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy (N.hT i v k))
  · intro hy
    refine (Submodule.mem_iInf _).2 fun f => mem_eigenspace_iff.2 ?_
    obtain ⟨f, hf⟩ := f
    have hf' := hf
    rw [← N.T_gen i] at hf'
    suffices key : ∀ g (hg' : g ∈ Algebra.adjoin (N.O i) {g : N.X i → N.O i | ∃ v k, IsSplitPl H v ∧
        v ∉ placesOver H.E (N.l i) ∧ v ∉ N.S i ∧ v ∉ N.Q i ∧ 1 ≤ k ∧ k ≤ R.nV ∧
        g = (N.hT i v k : N.X i → N.O i)}), ∀ hg : g ∈ N.T i,
        ((N.act i ⟨g, hg⟩).baseChange (FractionRing (N.O i))) y =
          algebraMap (N.O i) (FractionRing (N.O i)) (g x) • y from key f hf' hf
    intro g hg'
    induction hg' using Algebra.adjoin_induction with
    | mem g hg0 =>
      intro hg
      obtain ⟨v, k, h1, h2, h3, h4, h5, h6, rfl⟩ := hg0
      exact hy v k ⟨h1, h2, h3, h4⟩ h5 h6
    | algebraMap r =>
      intro hg
      have e : (⟨algebraMap (N.O i) (N.X i → N.O i) r, hg⟩ : N.T i) =
          algebraMap (N.O i) (N.T i) r := rfl
      rw [e, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul,
        LinearMap.baseChange_one]
      simp [algebraMap_smul]
    | add g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ N.T i := N.T_gen i ▸ hg1
      have m2 : g' ∈ N.T i := N.T_gen i ▸ hg2
      have e : (⟨g + g', hg⟩ : N.T i) = ⟨g, m1⟩ + ⟨g', m2⟩ := rfl
      rw [e, map_add, LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2, Pi.add_apply, map_add,
        add_smul]
    | mul g g' hg1 hg2 ih1 ih2 =>
      intro hg
      have m1 : g ∈ N.T i := N.T_gen i ▸ hg1
      have m2 : g' ∈ N.T i := N.T_gen i ▸ hg2
      have e : (⟨g * g', hg⟩ : N.T i) = ⟨g, m1⟩ * ⟨g', m2⟩ := rfl
      rw [e, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1,
        smul_smul, Pi.mul_apply, map_mul, mul_comm]

end Gen

section Spec
variable {D : D7} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
  {X : LocNd (lay0 D)} {T : LocTw X}

theorem genAt_iff_splitOut (Sp : NdSpec Pl M C big X T) {j : ℕ} {w : D.what₂.places.Pl} {i : X.nd.Loc}
    (h : i ∈ X.nd.locs j w) (v : PlE D.host) (k : ℕ) :
    (SplitOut X.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) ↔ GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by
  obtain ⟨-, h2⟩ := (X.nd.locs_mem j w i).1 h
  have hl : X.nd.l i = D.what₂.places.resChar w := by rw [← X.nd.w_l i, h2]
  have hS : v ∈ X.nd.S i ↔ v ∈ placesS D (D.what₂.places.resChar w) := by
    rw [X.nd.S_def, hl]; rfl
  unfold SplitOut GenAt
  rw [hS, ← Sp.Q_eq j w i h, hl]
  tauto

theorem mult_eq_finrank_jointEig (D : D7) (Pl : PlSide D) (M : MtFam D) (C : NChoice D)
    (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (j : ℕ)
    (w : D.what₂.places.Pl) (i : X.nd.Loc) (h : i ∈ X.nd.locs j w) (x : X.nd.X i) :
    X.nd.mult i x = Module.finrank (FractionRing (Sp.B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ)
      (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) := by
  set Fam := (⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      Module.End.eigenspace (Sp.B.hK j w v k) (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)))) with hFam_def
  have hFam : ∀ e, e ∈ Fam ↔ ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      Sp.B.hK j w v k e = algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)) • e := by
    intro e
    simp only [Fam, Submodule.mem_iInf, mem_eigenspace_iff]
  have hval : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))
        (Sp.phO j w i h ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x)) =
      NCov.pt (Sp.ptX j w i h x).1 ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
    intro v k hvk
    simp only [NCov.pt]
    rw [Sp.ptX_hT j w i h x v k hvk]
  have hE : ∀ e, e ∈ Fam ↔ e ∈ NCov.E (Formalism.L2.heckeAlg Sp.B j w) (Sp.ptX j w i h x).1 := by
    intro e
    rw [hFam, NCov.mem_E_iff]
    constructor
    · rintro hy _ ⟨v, k, hvk, rfl⟩
      rw [← hval v k hvk]
      exact hy v k hvk
    · intro hy v k hvk
      rw [hval v k hvk]
      exact hy _ ⟨v, k, hvk, rfl⟩
  have hpsi : ∀ y, y ∈ heckeEig (X.nd.T i) (X.nd.act i) x ↔ Sp.Psi j w i h y ∈ Fam := by
    intro y
    rw [heckeEig_mem_iff_gens, hFam]
    constructor
    · intro hy v k hvk
      obtain ⟨hso, hk1, hk2⟩ := (genAt_iff_splitOut Sp h v k).2 hvk
      have e := congrArg (Sp.Psi j w i h) (hy v k hso hk1 hk2)
      rw [Sp.act_hK j w i h v k hvk, LinearMap.map_smulₛₗ] at e
      rw [e]
      congr 1
      exact Sp.phK_alg j w i h _
    · intro hy v k hso hk1 hk2
      have hvk := (genAt_iff_splitOut Sp h v k).1 ⟨hso, hk1, hk2⟩
      apply Sp.Psi_inj j w i h
      rw [Sp.act_hK j w i h v k hvk, LinearMap.map_smulₛₗ, hy v k hvk]
      congr 1
      exact (Sp.phK_alg j w i h _).symm
  let f : ↥(heckeEig (X.nd.T i) (X.nd.act i) x) →ₛₗ[(Sp.phK j w i h).toRingHom] Sp.B.V j w :=
    (Sp.Psi j w i h).comp (heckeEig (X.nd.T i) (X.nd.act i) x).subtype
  change Module.finrank _ ↥(heckeEig (X.nd.T i) (X.nd.act i) x) = _
  refine finrank_eq_of_semilinear (Sp.phK j w i h) f Fam ?_ ?_
  · intro a b hab
    exact Subtype.ext (Sp.Psi_inj j w i h hab)
  · intro e
    constructor
    · intro he
      have hp : e ∈ NCov.part (Formalism.L2.heckeAlg Sp.B j w) (Sp.mx j w i) := by
        have := NCov.E_le_part (Formalism.L2.heckeAlg Sp.B j w) (Sp.ptX j w i h x).1 ((hE e).1 he)
        rwa [(Sp.ptX j w i h x).2.1] at this
      obtain ⟨z, rfl⟩ := (Sp.Psi_range j w i h e).1 hp
      exact ⟨⟨z, (hpsi z).2 he⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact (hpsi z).1 hz

end Spec

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianColumnChoicesOfFormsLevelsClassesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianColumnChoices_of_formsLevelsClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)) (hf : ∀ u i, Finite (Ch u i)) (hm : ∀ u, Nonempty (Unique (Ch u B.R.m))), (∀ u, I.StdF l Z u (F u)) → ∃ lev0 lev cls vT Fv, CarH (D := (I.rec7 l Z)) { lev0 := lev0, Ch := Ch, ChFin := hf, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv } F := by
  first | exact @GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms | exact GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms | (intros; apply GlobalTheory.Mem.Col2.TC.hermColsCh_of_forms <;> assumption)
end

