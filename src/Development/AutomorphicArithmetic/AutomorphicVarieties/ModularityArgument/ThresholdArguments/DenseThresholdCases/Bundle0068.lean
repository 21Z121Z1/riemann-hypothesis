import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0051
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocalLanglandsGLOfPrints
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0052
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0050
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0059
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreO
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Th
namespace UpperTheory.V.Th.NormTraceLemmas
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : HV.Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
private theorem locP_of (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : _root_.UpperTheory.V.Pa.LocPAlt :=
  ⟨P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩
private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]
private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2
private theorem unip_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (hM : (M.map (residue O)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n + m) - 1) i j ∈ maximalIdeal O ^ m := by
  have hl : l.Prime := Fact.out
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h0 := Matrix.aeval_self_charpoly (M.map (residue O))
  rw [hM] at h0
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h0
  have h1 : (residue O).mapMatrix (M ^ l ^ n) = 1 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self hl.one_lt (n := n)).le
    have h4 := sub_pow_char_pow_of_commute l n (Commute.one_right (M.map (residue O)))
    rw [one_pow] at h4
    rw [map_pow, ← sub_eq_zero]
    refine h4.symm.trans ?_
    rw [hd, pow_add, h0, zero_mul]
  have h2 : ∀ k, (residue O).mapMatrix (M ^ l ^ (n + k)) = 1 := fun k => by
    rw [pow_add, pow_mul, map_pow, h1, one_pow]
  induction m generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ l, pow_mul, ← mul_geom_sum, Matrix.mul_apply, pow_succ]
    refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih i a) ?_
    have h3 : (residue O).mapMatrix (∑ t ∈ Finset.range l, (M ^ l ^ (n + k)) ^ t) = 0 := by
      simp only [map_sum, map_pow (residue O).mapMatrix (M ^ l ^ (n + k)), h2, one_pow]
      simp
    exact (residue_eq_zero_iff _).1 (congrFun (congrFun h3 a) j)
private theorem rhoPLO (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CharP (ResidueField O) l] (n : ℕ) (ρ : F.G₀ →* GL (Fin n) O)
    (hc : ∀ i j, AdicCont (maximalIdeal O) fun g => mat ρ g i j) (H : OpenNormalSubgroup F.Γ)
    (hH : ∀ g ∈ H, ∃ h : F.η g = 1, ((mat ρ ⟨g, h⟩).map (residue O)).charpoly = (Polynomial.X - 1) ^ n)
    (g : F.G₀) (hg : (g : F.Γ) ∈ PL l H.toSubgroup) : ρ g = 1 := by
  have key : ∀ (m : ℕ) (i j : Fin n), (mat ρ g - 1) i j ∈ maximalIdeal O ^ m := by
    intro m
    let π := Ideal.Quotient.mk (maximalIdeal O ^ m)
    let Km : Subgroup F.G₀ := (π.mapMatrix.toMonoidHom.comp (mat ρ)).toHomUnits.ker
    have hKm : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j) := by
      intro a
      rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one, ← map_one π.mapMatrix,
        ← Matrix.ext_iff]
      rfl
    have hKm' : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, (mat ρ a - 1) i j ∈ maximalIdeal O ^ m := by
      intro a
      simp only [hKm, Matrix.sub_apply, π, Ideal.Quotient.eq]
    have ho : IsOpen (Km : Set F.G₀) := by
      have : (Km : Set F.G₀) = ⋂ i, ⋂ j, {a | π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j)} := by
        ext a
        simp only [SetLike.mem_coe, hKm, Set.mem_iInter, Set.mem_setOf_eq]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hc i j m).isOpen_fiber _
    let K' : Subgroup F.Γ := Km.map F.η.ker.subtype
    have ho' : IsOpen (K' : Set F.Γ) := F.η_open.isOpenMap_subtype_val _ ho
    haveI : Finite (F.Γ ⧸ K') := Subgroup.quotient_finite_of_isOpen K' ho'
    haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hc : IsOpen (K'.normalCore : Set F.Γ) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K'.normalCore_isClosed (K'.isClosed_of_isOpen ho'))
    let U : OpenNormalSubgroup F.Γ := ⟨⟨K'.normalCore, hc⟩, K'.normalCore_normal⟩
    have hU : ∀ h ∈ H.toSubgroup, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨n + m, fun b => ?_⟩
      obtain ⟨h1, h2⟩ := hH (b * h * b⁻¹) (H.isNormal'.conj_mem h hh b)
      refine ⟨(⟨b * h * b⁻¹, h1⟩ : F.G₀) ^ l ^ (n + m), ?_, ?_⟩
      · rw [SetLike.mem_coe, hKm', map_pow]
        exact unip_pow l O n m _ h2
      · simp only [Subgroup.coe_subtype, SubgroupClass.coe_pow, conj_pow]
    have h3 : (g : F.Γ) ∈ K'.normalCore := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg U) hU
    obtain ⟨a, ha, hag⟩ := K'.normalCore_le h3
    obtain rfl : a = g := Subtype.ext hag
    exact (hKm' a).1 ha
  apply Units.ext
  ext1 i j
  have h0 : (mat ρ g - 1) i j ∈ (⨅ m : ℕ, maximalIdeal O ^ m) := Ideal.mem_iInf.2 fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot, Matrix.sub_apply,
    sub_eq_zero] at h0
  exact h0
private theorem red_unip {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (x : B →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (h : u.D.map x.toRingHom = GDet.ofRep (mat ρ))
    (g : F.G₀) (hg : ∀ i, r.chib i g = 1) : ((mat ρ g).map (residue O)).charpoly = (Polynomial.X - 1) ^ n := by
  have e0 : (residue O).comp x.toRingHom = (res O B : B →+* ResidueField O) := RingHom.ext fun a =>
    ((res O O).commutes (x a)).symm.trans (res_map x a)
  have e3 : (GDet.ofRep (mat ρ)).map (residue O) = r.Dbar := by
    rw [← h, ← u.red, ← e0]
    rfl
  rw [map_ofRep, Resid.Dbar] at e3
  have e4 := congrArg (·.chi (MonoidAlgebra.single g 1)) e3
  simp only [chi_ofRep] at e4
  refine e4.trans ?_
  have e5 : W.diagRep r.chib g = 1 := by
    change Matrix.diagonal _ = _
    simp only [hg, Units.val_one, Matrix.diagonal_one]
  rw [e5, Matrix.charpoly_one, Fintype.card_fin]
end UpperTheory.V.Th.NormTraceLemmas
open UpperTheory.V.Th.NormTraceLemmas UpperTheory.V.Pa UpperTheory.V.W UpperTheory.V.Alg in
theorem UpperTheory.V.Th.core_o_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Th.OrdinaryMainCase := by
  intro hN l _ L Ω _ _ _ _ _ _ s V0 c n r B J y x h q sg al hS hn hLev hJ hAr hmap hN4 hsg hdet δ hδ h0
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  haveI := coef_isCoef l c
  haveI := IsCoef.char (l := l) (O := c.O)
  haveI := IsCoef.finite (l := l) (O := c.O)
  haveI := IsCoef.complete (l := l) (O := c.O)
  obtain ⟨b, hb, hγ, hctrl⟩ := hLev
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := (arPl hC l L Ω s V0 c.O n r hS).2 q sg fun j => (hsg j).1
  obtain rfl : T.sg = sg := funext hTs
  have hI := (ipEq l L Ω s V0 c.O n r).1
  have hgen : GenBy c.O (pairVals (pairOf B.u)) := fun N b => by
    obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
    refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
    rintro _ (⟨a, g, -, -, rfl⟩ | e)
    · exact Or.inl ⟨a, g, rfl⟩
    · exact Or.inr e
  have hmap' : (pairOf B.u).Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ := hmap
  have hker : ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1 := by
    refine rhoPLO l (globOf r V0).frame c.O n y.ρ y.cont T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    exact ⟨e1, red_unip (pairOf B.u) x y.ρ hmap'.1 ⟨g, e1⟩ e2⟩
  have heig : Eig y T al := fun j => (hsg j).2
  exact count l _ (globOf r V0) T n c.O (residOf r) B.B (pairOf B.u) J _ b y x al s.odd hn
    ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
    (_root_.UpperTheory.V.Th.has_operator_statement (locP_of hN) l L Ω s V0 c.O n r B J _ b hb T Pl) hgen hmap' hJ
    (etOf l _ (globOf r V0) n c.O (residOf r) B.B (pairOf B.u) J _ b y x hn hmap' hgen (hctrl x h hAr)) hker heig
    (b1O hC l L Ω s V0 c n r T Pl y al hS (W.locCFT hN.aut.art hC l L Ω s) hn hker hN4 heig hdet)
    δ hδ fun k => h0 _ _ _ (hγ k)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNumJE
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z.Desc.V0
section SlopeTestRemainingChoices
open Formalism.MainNotions.N
variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
private theorem inv_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) (r : Γ →* GL (Fin n) k) (M : Submodule k (Fin n → k)) :
    IsInv (r.comp φ) M ↔ IsInv r M :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := hφ g; exact h g, fun h g => h (φ g)⟩
private theorem ss_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) {r : Γ →* GL (Fin n) k} (h : IsSSRep r) :
    IsSSRep (r.comp φ) := fun M hM => by
  obtain ⟨M', h1, h2⟩ := h M ((inv_comp hφ r M).1 hM)
  exact ⟨M', (inv_comp hφ r M').2 h1, h2⟩
private theorem irr_of_comp (φ : Γ' →* Γ) {r : Γ →* GL (Fin n) k} (h : Af.IsIrr (r.comp φ)) : Af.IsIrr r :=
  ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M hM hi => h.2.2 M hM fun g => hi (φ g)⟩
private theorem ss_of_irr {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp
private theorem irr_iso {r r' : Γ →* GL (Fin n) k} (e : Af.RepIso r r') (h : Af.IsIrr r) : Af.IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let E : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hE : ∀ v, E v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : IsInv r (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have := hM g _ hv
    change (r' g : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec v) ∈ M at this
    change (P : Matrix (Fin n) (Fin n) k).mulVec _ ∈ M
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, hP, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec] at this
  have hm : M = (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))).map (E : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective E.surjective M).symm
  rcases h.2.2 _ le_top hi with h0 | h0
  · left; rw [hm, h0, Submodule.map_bot]
  · right; rw [hm, h0, Submodule.map_top, LinearEquiv.range]
private theorem iso_of_det {r r' : Γ →* GL (Fin n) k} (h : IsSSRep r) (h' : IsSSRep r')
    (e : W.GDet.ofRep (W.mat r) = W.GDet.ofRep (W.mat r')) : Af.RepIso r' r := by
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat r) (W.mat r') h h' fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat r')).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm
private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩
private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl
private theorem datEnd {O A B M : Type} [CommRing O] [CommRing A] [IsDomain A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] (j : A →ₐ[O] B) (φ : B →+* Module.End A M)
    (hj : ∀ a, φ (j a) = algebraMap A _ a) (J : Ideal B) (hJ : ∀ b, b ∈ J ↔ φ b = 0) (hr : J.IsRadical) :
    ∃ _ : Module B M, (∀ (b : B) (m : M), b • m = φ b m) ∧ UpperTheory.V.J.Dat j J M := by
  letI : Module B M := Module.compHom M φ
  have h0 : ∀ (b : B) (m : M), b • m = φ b m := fun _ _ => rfl
  have h1 : Module.annihilator B M = J := by
    ext b
    rw [Module.mem_annihilator, hJ, LinearMap.ext_iff]
    rfl
  refine ⟨inferInstance, h0, fun a m => ?_, inferInstance, inferInstance, hr, fun p _ => by rw [h1], fun c hc a ha => ?_⟩
  · rw [h0, hj]
    rfl
  · rw [hJ] at ha ⊢
    rw [map_mul, hj] at ha
    ext m
    have h2 : c • φ a m = 0 := LinearMap.congr_fun ha m
    refine (Module.Free.chooseBasis A M).repr.injective (Finsupp.ext fun i => ?_)
    have h3 := congrArg (fun v => (Module.Free.chooseBasis A M).repr v i) h2
    simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h3
    rw [(mul_eq_zero.1 h3).resolve_left hc, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]
private theorem datHecke {O A B N κ : Type} [CommRing O] [CommRing A] [IsDomain A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup N] [Module A N] (Y : Submodule A N) (op : κ → Module.End A N) [Fact (CommOn Y op)] [Module.Free A Y]
    [Module.Finite A Y] (j : A →ₐ[O] B) (f : B →+* heckeAlg Y op) (hj : ∀ a, f (j a) = algebraMap A _ a)
    (hr : (RingHom.ker f).IsRadical) :
    ∃ _ : Module B Y, (∀ (b : B) (m : Y), b • m = (f b).1 m) ∧ UpperTheory.V.J.Dat j (RingHom.ker f) Y :=
  datEnd j ((heckeAlg Y op).val.toRingHom.comp f) (fun a => congrArg Subtype.val (hj a)) _
    (fun _ => RingHom.mem_ker.trans Subtype.ext_iff) hr
private theorem datTop {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (j : A →ₐ[O] B) :
    UpperTheory.V.J.Dat j ⊤ PUnit :=
  ⟨fun _ _ => rfl, Module.Free.of_subsingleton A PUnit, ⟨⟨∅, Subsingleton.elim _ _⟩⟩, le_top, fun p _ => by
    rw [Module.annihilator_eq_top_iff.2 ⟨fun _ _ => rfl⟩], fun _ _ _ _ => Submodule.mem_top⟩
end SlopeTestRemainingChoices
private theorem unitN {l : ℕ} [Fact l.Prime] {c : Coef l} {A : Type} [CommRing A] [Algebra c.O A] {N : ℕ} (h : ¬ l ∣ N) :
    IsUnit (N : A) := by
  have h0 : IsUnit (N : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact (PadicInt.norm_natCast_eq_one_iff).2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)
  have h1 := (h0.map (algebraMap ℤ_[l] c.O)).map (algebraMap c.O A)
  simpa using h1
set_option maxHeartbeats 2000000 in
private theorem absDimE (hMu : MuZ) (hME : MuZE) (hSp : Spec2) (hU : UnitEv) (hP : _root_.UpperTheory.V.Z.J.D.PartRepAlt) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) {A : Type} [CommRing A]
    [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.IsWt θ) (ι : Qbar l ≃+* ℂ)
    (a₀ : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a₀ K) (H.op A))] {R : Type} [CommRing R] [Algebra c.O R]
    (D₀ : W.GDet n R H.Gq) (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a₀ K) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) {P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop} {I : Ideal (H.TK θ a₀ K)}
    {ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a₀ K)ˣ} (out : H.Out θ a₀ K P I (D₀.map f.toRingHom) ψ)
    [Module R (H.MK θ a₀ K)] (hs : ∀ (b : A) (m : H.MK θ a₀ K), b • m = j b • m)
    (hact : ∀ (b : R) (m : H.MK θ a₀ K), b • m = (f b).1 m)
    {G : Type} [Group G] {K₀ K₁ : Subgroup G} (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ) (hNK : NormK H K₀ K₁ β) (hE : IsE K₀ K₁ a N)
    (hu : IsUnit (N : A)) (e : Module.End A (H.MK θ a₀ K)) (hep : IsProj H θ β a N e)
    (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n) (hl : lam ∈ H.admitted)
    (har : H.Arith θ (x.comp j).toRingHom lam)
    (hρ : ∀ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ → Formalism.MainNotions.N.IsSSRep ρ →
      D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat ρ) → Af.IsIrr ρ) :
    _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt H θ ι lam K β a N (muE j (H.MK θ a₀ K) hs e x) := by
  obtain ⟨-, hfi, hfr⟩ := (hiComm L Ω l n c H hA A θ hθ K).2.2.2 a₀
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hss, -, hD, -⟩ := out.pt lam hl y (e1 ▸ har)
  have hi := hρ ρ hc hss ((map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD)
  obtain ⟨d, ξ, c0, sp, hsp, htr⟩ := hSp L Ω l n c H hA A θ hθ ι (x.comp j) lam har
  obtain ⟨hne, -⟩ := hMu L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp K a₀ R j f hf hs hact y e1
  have hmu := hME L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp htr K a₀ R j f hf hs hact y e1 G K₀ K₁ β a N hNK hE hu e hep
  have e2 : y.comp f = x := AlgHom.ext hy
  rw [e2] at hmu
  refine ⟨x.comp j, d, ξ, c0, sp, _, hsp, fun v i => ?_, hne, fun Y hY => ?_, hmu⟩
  · rw [RingEquiv.symm_apply_apply]
    exact hU L Ω l n c H hA A θ hθ ι K a₀ I _ ψ out.univ y v i
  · obtain ⟨g, hg⟩ := hP L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp K a₀ y e1 I _ ψ out.univ ρ hc hi hD Y hY
    exact irr_iso ⟨g, hg⟩ hi
set_option maxHeartbeats 1000000 in
private theorem irrOf {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {c : Coef l}
    {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r} (x : B.Pt) (hx : UpperTheory.V.J.IrrPt x)
    (ρ₀ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (hs : Formalism.MainNotions.N.IsSSRep ρ₀)
    (hD : B.u.D.map (x : B.B →+* Qbar l) = W.GDet.ofRep (W.mat ρ₀)) : Af.IsIrr ρ₀ := by
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  obtain ⟨ρ, -, hρ, hi⟩ := hx
  have hr : x.IsRep (ρ₀.comp V.pr) := by
    replace hD : x.D = W.GDet.ofRep (W.mat ρ₀) := hD
    change x.D.comap V.pr = _
    rw [hD]
    exact (AlgebraTools.Det.repApi (W.mat ρ₀)).2.2.2.2.2.2.1 V.pr
  have e : Af.RepIso (ρ₀.comp V.pr) ρ := iso_of_det (ss_of_irr hi) (ss_comp hpr hs) (hρ.symm.trans hr)
  exact irr_of_comp V.pr (irr_iso e.symm' hi)
set_option maxHeartbeats 2000000 in
theorem UpperTheory.V.Z.Desc.V0.numJE_alt :
    UpperTheory.V.Z.J.D.MuZ → MuZE → EEx → Spec2 → NormS → _root_.UpperTheory.V.Z.Desc.V0.ZEqDimEAlt → UpperTheory.V.Z.J.D.UnitEv → _root_.UpperTheory.V.Z.J.D.PartRepAlt → _root_.UpperTheory.V.Z.Desc.V0.NumJEAlt := by
  intro hMu hME hEx hSp hNS hZ hU hP H hM hC l _ L Ω _ _ _ _ _ _ s n hn V hV h4 Q c r ι B Λ R K J hdom hJ hrad
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact ⟨PUnit, inferInstance, inferInstance, inferInstance, datTop _, 0, ⟨by simp, fun _ _ => by simp⟩, fun x _ _ hx =>
      absurd (hx (Submodule.mem_top (x := 1))) (by simp)⟩
  have hA := _root_.UpperTheory.V.Hi.axU_s H.litN l L Ω s n hn V Q c R.m R.τ₀
  obtain ⟨-, hfi, hfr⟩ := (hiComm L Ω l n c (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt K).2.2.2 R.a
  obtain ⟨i3, hact, hdat⟩ := datHecke ((hset Q R.τ₀).MK R.θ R.a K) ((hset Q R.τ₀).op Λ.Λ) (Λ.toPair B.u) f.toRingHom hlam hrad
  obtain ⟨a, N, hE, hlN, hz⟩ := hZ H hM hC l L Ω s n hn V hV h4
  have hNK := hNS l L Ω s n hn V hV Q c R.m R.τ₀
  have hu : IsUnit (N : Λ.Λ) := unitN (c := c) hlN
  obtain ⟨e, hep, hee, hec⟩ := hEx L Ω l n c (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt K R.a _ _ _ (sec0 n s) a N hNK hE hu
  refine ⟨_, inferInstance, i3, inferInstance, hdat, e, ⟨hee, fun b m => ?_⟩, fun x y w hx hy ha hg ix iy => ?_⟩
  · rw [hact, hact]
    exact LinearMap.congr_fun (hec (f b)) m
  obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta w ha.1
  have out := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight H.litN L Ω l n c (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _)
    ((_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  have h := hz Q c r ι R.m R.τ₀ R.type Λ.Λ R.θ R.isWt lam K _ _
    (absDimE hMu hME hSp hU hP (hset Q R.τ₀) hA R.θ R.isWt ι R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out hdat.hs hact
      (sec0 n s) a N hNK hE hu e hep x hx lam (Set.mem_univ _) ((hb lam hl x).1.1 ha)
      fun ρ _ hs hD => irrOf x ix ρ hs hD)
    (absDimE hMu hME hSp hU hP (hset Q R.τ₀) hA R.θ R.isWt ι R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out hdat.hs hact
      (sec0 n s) a N hNK hE hu e hep y hy lam (Set.mem_univ _) ((hb lam hl y).2.1 hg).2.1
      fun ρ _ hs hD => irrOf y iy ρ hs hD)
  exact ⟨h.1, h.2.le⟩
end
end

