import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

variable {R : Type} [CommRing R] [IsDomain R]

abbrev SecF (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) : Type :=
  GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) F) A.A).left
    (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (N : ℤ)))

def baseEm {F : Type} [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) :
    TFK (R := R) F ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom em.toRingHom)) (by
    show Spec.map (CommRingCat.ofHom em.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R))) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact em.commutes r)

def famExt (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ) :
    Fam D (Kb R) N →ₛₗ[em.toRingHom] Fam D F N :=
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  GlobalTheory.FieldBaseChange.famPull D (Kb R) F GlobalTheory.allSixLaws.1.globalFns N

def secExt (A : PolAV (Sp (FractionRing R))) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) (N : ℕ) : SecF A (Kb R) N →ₛₗ[em.toRingHom] SecF A F N :=
  GlobalTheory.FieldBaseChange.pullOver A.L (fun _ => (N : ℤ))
    (p := (baseEm em ▷ A.A).left)
    (congrArg (fun q => q.left) (whiskerRight_fst (baseEm em) A.A))
    (fun _ => (congrArg (fun q => q.left) (whiskerRight_snd (baseEm em) A.A)).symm)

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGeneratedSubringLocalisedBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closure_pow_lift {L L' : Type*} [CommRing L] [CommRing L'] (ρ : L →+* L') (C : Subring L) (u : L)
    (hu : u ∈ C) (G : Set L') (hG : ∀ g ∈ G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * g) :
    ∀ z ∈ Subring.closure G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * z := by
  intro z hz
  induction hz using Subring.closure_induction with
  | mem g hg => exact hG g hg
  | zero => exact ⟨0, 0, C.zero_mem, by simp⟩
  | one => exact ⟨0, 1, C.one_mem, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, u ^ l * w + u ^ k * v,
      C.add_mem (C.mul_mem (C.pow_mem hu _) hw) (C.mul_mem (C.pow_mem hu _) hv), ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, e, e']
    ring
  | neg a _ ha =>
    obtain ⟨k, w, hw, e⟩ := ha
    exact ⟨k, -w, C.neg_mem hw, by rw [map_neg, e]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, w * v, C.mul_mem hw hv, ?_⟩
    rw [map_mul, e, e']
    ring

theorem exists_pow_mul_res {S : Scheme.{0}} {U : S.Opens} (hc : IsCompact (U : Set S))
    (hq : IsQuasiSeparated (U : Set S)) (g : Γ(S, U)) (U' : S.Opens) (hle : U' ≤ U) (hU' : U' = S.basicOpen g)
    (a : Γ(S, U')) : ∃ (k : ℕ) (b : Γ(S, U)), (S.presheaf.map (homOfLE hle).op).hom b =
      (S.presheaf.map (homOfLE hle).op).hom g ^ k * a := by
  subst hU'
  letI := (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom.toAlgebra
  have := isLocalization_basicOpen_of_qcqs hc hq g
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers g) a
  refine ⟨k, y, ?_⟩
  rw [← map_pow, mul_comm]
  simpa [RingHom.algebraMap_toAlgebra] using hy.symm

theorem presheaf_map_bijective_of_eq {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (e : A = B) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 A := Subsingleton.elim _ _
  simpa [this] using Function.bijective_id

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finFam_basicOpen_loc : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens), IsAffineOpen W → ∀ (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ finFam gp V t (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ W)), y ∈ finFam gp V t W ∧
      resK gp (S.basicOpen_le f) y = resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ k * x := by
  intro S K _ gp _ r V t W hW f x hx
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : Sp K := (IsLocalRing.closedPoint K : PrimeSpectrum K)
  have pre : ∀ U U' : S.Opens, (gp.base p ∈ U ↔ gp.base p ∈ U') → gp ⁻¹ᵁ U = gp ⁻¹ᵁ U' := by
    intro U U' h
    ext q
    rw [Subsingleton.elim q p]
    exact h
  have bij : ∀ {U U' : S.Opens} (h : U' ≤ U), (gp.base p ∈ U ↔ gp.base p ∈ U') →
      Function.Bijective (resK gp h) := fun h e => presheaf_map_bijective_of_eq _ (pre _ _ e)
  by_cases hs : gp.base p ∈ S.basicOpen f
  swap
  · have e : gp ⁻¹ᵁ S.basicOpen f = ⊥ := by
      ext q
      rw [Subsingleton.elim q p]
      exact ⟨fun h => (hs h).elim, fun h => by simp at h⟩
    haveI : Subsingleton Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f) := by rw [e]; infer_instance
    exact ⟨0, 0, Subring.zero_mem _, Subsingleton.elim _ _⟩
  have hsW : gp.base p ∈ W := S.basicOpen_le f hs
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hNW : TopologicalSpace.NoetherianSpace (W : Set S) := noetherianSpace_of_isAffineOpen W hW
  have hcpt : ∀ T ⊆ (W : Set S), IsCompact T := (TopologicalSpace.noetherianSpace_set_iff _).mp hNW
  have hle : ∀ i, S.basicOpen f ⊓ V i ≤ W ⊓ V i := fun i => inf_le_inf_right _ (S.basicOpen_le f)
  rw [mem_finFam] at hx
  have step : ∀ i, ∃ k : ℕ, ∃ w ∈ Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
      resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)),
      resK gp (hle i) w = resK gp (hle i) (resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f)) ^ k *
        resK gp (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f) x := by
    intro i
    refine closure_pow_lift _ _ _ ?_ _ ?_ _ (hx i)
    · rw [resK_app]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    rintro _ (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
    · have hU' : S.basicOpen f ⊓ V i =
          S.basicOpen ((S.presheaf.map (homOfLE (inf_le_left : W ⊓ V i ≤ W)).op).hom f) := by
        rw [Scheme.basicOpen_res]
        exact le_antisymm (le_inf (le_inf (inf_le_left.trans (S.basicOpen_le f)) inf_le_right) inf_le_left)
          (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      have hWi : (↑(W ⊓ V i) : Set S) ⊆ W := fun z hz => hz.1
      obtain ⟨k, b, e⟩ := exists_pow_mul_res (hcpt _ hWi)
        (fun A B hA _ _ hB _ _ => hcpt _ ((Set.inter_subset_left.trans hA).trans hWi)) _ _ (hle i) hU' a
      refine ⟨k, (gp.app (W ⊓ V i)).hom b, Subring.subset_closure (Or.inl ⟨_, rfl⟩), ?_⟩
      rw [resK_app, resK_app, resK_app, e, map_mul, map_pow, ← CommRingCat.comp_apply]
    · refine ⟨0, resK gp (inf_le_right : W ⊓ V i ≤ V i) c, Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩), ?_⟩
      rw [pow_zero, _root_.one_mul, resK_resK]
  choose k w hw e using step
  let N := Finset.univ.sup k
  obtain ⟨y, hy⟩ := (bij (S.basicOpen_le f) ⟨fun _ => hs, fun _ => hsW⟩).2
    (resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ N * x)
  refine ⟨N, y, ?_, hy⟩
  rw [mem_finFam]
  intro i
  have hki : k i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hmem : resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f) ^ (N - k i) * w i ∈
      Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
        resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)) := by
    refine Subring.mul_mem _ (Subring.pow_mem _ ?_ _) (hw i)
    rw [resK_app]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  have inj := (bij (hle i) (by simp [hs, hsW])).1
  convert hmem using 1
  apply inj
  rw [map_mul, map_pow, e i, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hki, resK_resK, resK_resK,
    ← resK_resK gp (S.basicOpen_le f) (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f), hy, map_mul, map_pow,
    resK_resK]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupRepresentationTwist
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem typeSubspace_eq_iInf_ker {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] {n : ℕ}
    {Wσ : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) :
    A.typeP J0 lam0 = ⨅ p : J0, LinearMap.ker (A.ρ p - ((A.chi p * lam0 p : LLˣ) : LL) • LinearMap.id) := by
  ext F
  simp [Formalism.IndefR.Arith.FormsL.mem_typeP, Submodule.mem_iInf, sub_eq_zero]

set_option maxHeartbeats 1000000 in

theorem point_read (p : PtAt ex Csz) (i : Fin D.R.m) (hp : RowsT p) (hg : GramAt p i)
    (hfree : ∀ k : Fin 2, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH D k) X)
      (A : X → Submodule ℂ (VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), ∀ v ∈ A y, repAt p i (h : G0g D.nd) v ∈ A (h • y)) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (π : Γ →* G0g D.nd) (s : G0g D.nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ)
      (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ)
      (H : Fin 2 → Subgroup (G0g D.nd)), IsSplit π s ∧ IsWhit D Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧
      (∀ k, IsHalf D k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X)
        (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
        ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧
      Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧
      Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) := by
  classical
  obtain ⟨lam, ψ, hW, hlam, -⟩ := GlobalTheory.ShareOn.baseLevel_isWhit D L hT Gi Gl Kc Y0 cX ex Csz p hp.1
  have hfin : Finite (G0g D.nd) := Finite.of_equiv _ (p.R.eG.trans p.cG).toEquiv
  let e := p.R.eG.trans p.cG
  let Pb := p.P.P0.map e.toMonoidHom
  let lamb : Pb.comap (MonoidHom.id (G0g D.nd)) →* ℂˣ :=
    lam.comp (MulEquiv.subgroupCongr (Subgroup.comap_id Pb)).toMonoidHom

  have hEig : eig (repAt p i) (Pb.comap (MonoidHom.id (G0g D.nd))) lamb =
      eig (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi) (p.F.lv2.lvl false).P
        ((Units.map D.what₂.embLL.toMonoidHom).comp (p.F.lv2.lvl false).ψ⁻¹) := by
    ext v
    rw [mem_eig, mem_eig]
    constructor
    · intro h g
      have hm : e g ∈ Pb := ⟨g, g.2, rfl⟩
      have := h ⟨e g, hm⟩
      rw [repAt_apply] at this
      simp only [e, MulEquiv.symm_apply_apply] at this
      rw [this]
      congr 2
      exact Units.ext (hlam g hm)
    · intro h γ
      obtain ⟨g, hg, hge⟩ := γ.2
      have := h ⟨g, hg⟩
      rw [repAt_apply]
      have h1 : (p.R.eG.trans p.cG).symm (γ : G0g D.nd) = g := by
        rw [MulEquiv.symm_apply_eq]; exact hge.symm
      rw [h1, this]
      congr 2
      apply Units.ext
      have h2 := hlam ⟨g, hg⟩ ⟨g, hg, rfl⟩
      have h3 : lamb γ = lam ⟨e g, ⟨g, hg, rfl⟩⟩ := by
        show lam ⟨(γ : G0g D.nd), _⟩ = _
        congr 1
        exact Subtype.ext hge.symm
      rw [h3, h2]
      rfl
  refine ⟨G0g D.nd, inferInstance, hfin, VAt p i, inferInstance, inferInstance, inferInstance, MonoidHom.id _, MonoidHom.id _,
    repAt p i, Pb, lam, ψ, lamb, GlobalTheory.BadCount.Inh.halfH D, ⟨fun g => rfl, fun g γ hγ => ?_⟩, hW, fun γ => rfl,
    fun k => GlobalTheory.BadCount.Inh.isHalf_halfH D k, fun k => ?_, ?_, ?_⟩
  · have : γ = 1 := hγ
    subst this; simp
  · obtain ⟨X, hX, hXd, hact, A, hf, hA, hc⟩ := hfree k
    let f : (GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd)) →* GlobalTheory.BadCount.Inh.halfH D k :=
      { toFun := fun h => ⟨h.1, h.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    letI : MulAction ((GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd))) X := MulAction.compHom X f
    refine ⟨X, hX, hXd, this, A, fun h y hy => ?_, hA, fun h y v hv => hc (f h) y v hv⟩
    have := hf (f h) y hy
    exact Subtype.ext (congrArg Subtype.val this)
  · have hC := GlobalTheory.T.gram_lattice_span_eq_top p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _) = _
    rw [hB.1, typeSubspace_eq_iInf_ker, hA.1, hEig]
  · have hC := GlobalTheory.T.gram_lattice_span_eq_top p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    obtain ⟨-, -, -, hc, -, -⟩ := p.grpRecPin
    have hsum : ∀ x : MonoidAlgebra ℂ (G0g D.nd), x = ∑ h, MonoidAlgebra.single h (x.coeff h) := fun x =>
      MonoidAlgebra.ext (by
        rw [MonoidAlgebra.coeff_sum]
        simp only [MonoidAlgebra.coeff_single]
        exact (Finsupp.univ_sum_single _).symm)
    have he0 : D.ntypes.e0 = ∑ g : p.P.Gp,
        MonoidAlgebra.single (e g) (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)) := by
      rw [hsum D.ntypes.e0, ← Equiv.sum_comp e.toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hc g]
      rfl
    have hK : Representation.asAlgebraHom ((repAt p i).comp (MonoidHom.id (G0g D.nd))) D.ntypes.e0 =
        Representation.asAlgebraHom (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi)
          (∑ g, MonoidAlgebra.single g (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g))) := by
      rw [he0, map_sum, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      have hee : (p.R.eG.trans p.cG).symm (e g) = g := MulEquiv.symm_apply_apply _ _
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, repAt_apply, hee]
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _ ⊓ (LinearMap.ker (eGood p.R.toRealDat i)).restrictScalars _) = _
    have hEG : eGood p.R.toRealDat i = ∑ g, ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g *
        (((p.R.toRealDat.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (p.R.toRealDat.FW i).ρ g := by
      unfold eGood Formalism.IndefR.Arith.FormsL.eOp; rfl
    rw [hB.2, typeSubspace_eq_iInf_ker, hEG, hA.2]
    rw [hEig, hK]
end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

set_option maxHeartbeats 1000000 in

theorem exists_rep_def : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (π : Γ →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X) (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧ ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) V) (Fm.D x ι).ntypes.e0) : Submodule ℂ V) := by
  intro hP hG
  have h1 := GlobalTheory.T.half_heisenberg_free_action_decomposition hP hG
  have h2 := hG
  unfold Gram at h2
  unfold Lifts at h1 h2 ⊢
  refine (h1.and h2).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩ := h
  obtain ⟨x0, e⟩ := e1.and e2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨a1, a2⟩ := e x hx hle ι p hp
  exact point_read p i hp (a2 i) (a1 i hi)

end GlobalTheory.DefRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegerRingActionsPrincipallyPolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FinAct

theorem finite_oActs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)), letI := H.starRing;
    Set.Finite {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a} := by
  intro E _ _ _ H K _ _ _ P
  letI := H.starRing
  have h₂ := GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.2
  choose cn hcn using GlobalTheory.exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  set g := P.g
  set M := 4 ^ g * g.factorial * (2 * s.sup cn) + 1 with hM
  have hM1 : 1 ≤ M := Nat.le_add_left _ _
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ 4 ^ g * g.factorial * (2 * s.sup cn) := by gcongr
      _ < M := Nat.lt_succ_self _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hK : (M : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let T := {x : baseOver (Sp K) ⟶ P.A // x ^ M = 1}
  haveI : Finite T := GlobalTheory.AbTorsionFinite.finite_torsion K P.A P.isAb M hM1
  classical
  let F : (𝓞 E → (P.A ⟶ P.A)) → (s → T → Option T) := fun act a x =>
    if h : (x.1 ≫ act a) ^ M = 1 then some ⟨_, h⟩ else none
  refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
  rintro act₁ ⟨ρ₁, h₁⟩ act₂ ⟨ρ₂, h₂'⟩ hF
  have tor : ∀ (ρ : P.OAct (𝓞 E)) (a : 𝓞 E) (x : T), (x.1 ≫ ρ.act a) ^ M = 1 := fun ρ a x => by
    have := ρ.hom a
    have e := map_pow (IsMonHom.monoidHom (ρ.act a) (baseOver (Sp K))) x.1 M
    rw [x.2, map_one] at e
    exact e.symm
  have onS : ∀ a ∈ s, ρ₁.act a = ρ₂.act a := fun a ha => by
    have := h₂ g (cn a) M (key _ (Finset.le_sup ha)) K hK P P rfl rfl (Iso.refl _)
      (ThetaPtDet.isPolIso_refl P) (𝓞 E) ρ₁ ρ₂ a (hcn a) fun y hy => by
        have e := congrFun (congrFun hF ⟨a, ha⟩) ⟨y, hy⟩
        simp only [F, h₁, h₂'] at e
        rw [dif_pos (h₁ a ▸ tor ρ₁ a ⟨y, hy⟩), dif_pos (h₂' a ▸ tor ρ₂ a ⟨y, hy⟩)] at e
        have e' := congrArg Subtype.val (Option.some_injective _ e)
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, h₁, h₂']
        exact e'
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using this
  have add₁ : ∀ a b, ρ₁.act (a + b) = ρ₁.act a * ρ₁.act b := ρ₁.map_add
  have add₂ : ∀ a b, ρ₂.act (a + b) = ρ₂.act a * ρ₂.act b := ρ₂.map_add
  let f₁ : 𝓞 E →+ Additive (P.A ⟶ P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (ρ₁.act a))
    fun a b => by rw [add₁]; rfl
  let f₂ : 𝓞 E →+ Additive (P.A ⟶ P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (ρ₂.act a))
    fun a b => by rw [add₂]; rfl
  have hf : f₁ = f₂ := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha =>
      congrArg Additive.ofMul (onS a ha)
  funext a
  rw [← h₁, ← h₂']
  exact Additive.ofMul.injective (DFunLike.congr_fun hf a)

end GlobalTheory.UMin.FinAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsBalancedFormsUptoAut
section
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.MinSysTypeBal

theorem finite_minimiser_systems_upTo_aut : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y]
    [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ b ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : Y ≃ₗ[O] Y, ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → pull e.toLinearMap b (μ cl) (μ cl) ≤ pull e.toLinearMap b α α) →
    μ ∈ S := by
  intro O _ bar φ Y _ _ _ _ hX n N _ _ eb
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone bar φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ Y)) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ Y) x x
  let T : ι → Finset ((Fin n → ZMod N) → Y) := fun i =>
    if h : P i then Classical.choose (GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb i.1.val _ (fun j x y => (h.1.mem j).1 x y)
      (fun j y => h.1.nonneg j y) h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hb hpos
  obtain ⟨m, γ, k, cf, hcone, hk, hcf, hsum⟩ := GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hX b hb hpos
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j l hjl => by
    have h := congrArg Subtype.val hjl
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, (k : ℤ) * b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    have := LinearMap.congr_fun₂ hsum y y
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have h3 := hpos _ hex
    have h4 := hbyy (e x)
    simp [hz] at h4
    rcases h4 with h4 | h4
    · omega
    · omega
  have hmem : μ ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb i.1.val _ (fun j x y => (hPi.1.mem j).1 x y)
      (fun j y => hPi.1.nonneg j y) hPi.2) (pull e.toLinearMap b) k cf hk hcf ?_ μ h1 h2
    ext a c
    have := LinearMap.congr_fun₂ hsum (e a) (e c)
    simpa [i, γ', pull_apply, LinearMap.sum_apply] using this
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysTypeBal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariantsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_mem_range_fractionFieldMap_galoisInvariants : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) → y ∈ (fracMap ρ hρ).range := by
  first | exact @GlobalTheory.Mum.GenDesc.fixed_mem_range | exact GlobalTheory.Mum.GenDesc.fixed_mem_range | (intros; apply GlobalTheory.Mum.GenDesc.fixed_mem_range <;> assumption)
end

