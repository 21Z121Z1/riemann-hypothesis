import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0376
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceFixedVectorSumSphericalImages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphAvg

open GlobalTheory.SplitWeil

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_lift {n : ℕ} (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i)
    (y : GL (Fin n) (s.w.adicCompletion L)) (hy : y ∈ KO (s.w.adicCompletion L) (Fin n)) :
    ∃ κ : GAf L n, κ ∈ Umax L n ∧ TrivOutside {s.v} κ ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ) = y := by
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous i hi
  have hle : ∀ x, ValuativeRel.valuation (s.w.adicCompletion L) x ≤ 1 → Valued.v (i.symm x) ≤ 1 :=
    fun x hx => (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  obtain ⟨u, rfl⟩ := hy
  set M := Matrix.GeneralLinearGroup.map i.symm.toRingHom
    (Matrix.GeneralLinearGroup.map (algebraMap _ (s.w.adicCompletion L)) u) with hM
  obtain ⟨κ, hκ, hloc⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s M
  refine ⟨κ, GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ hκ ?_ ?_, hκ, ?_⟩
  · intro a b
    rw [hloc]
    exact hle _ (u.val a b).2
  · intro a b
    rw [map_inv, hloc, hM, ← map_inv, ← map_inv]
    exact hle _ ((u⁻¹).val a b).2
  · rw [hloc, hM]
    ext a b
    simp

theorem exists_fixed_of_sum {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i)
    {ι : Type} [Fintype ι] (T : ι → σ.V →ₗ[ℂ] (GAf L n → W))
    (hT : ∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) (u : ι → σ.V) (f : GAf L n → W)
    (hf : f = ∑ j, T j (u j)) (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) :
    ∃ e : ι → σ.V, (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (KO (s.w.adicCompletion L) (Fin n))) ∧
      f = ∑ j, T j (e j) := by
  classical
  let H : Subgroup (GL (Fin n) (s.w.adicCompletion L)) :=
    { carrier := {g | ∀ j, σ.ρ g (u j) = u j}
      mul_mem' := fun {a b} ha hb j => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb j, ha j]
      one_mem' := fun j => by simp
      inv_mem' := fun {a} ha j => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        conv_lhs => rw [← ha j]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hHo : IsOpen (H : Set (GL (Fin n) (s.w.adicCompletion L))) := by
    have : (H : Set (GL (Fin n) (s.w.adicCompletion L))) = ⋂ j, {g | σ.ρ g (u j) = u j} := by
      ext g; simp [H]
    rw [this]
    exact isOpen_iInter_of_finite fun j => σ.smooth (u j)
  set K := KO (s.w.adicCompletion L) (Fin n) with hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp GlobalTheory.SplitFlip.isCompact_KO
  haveI : Finite (K ⧸ H.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hHo.preimage continuous_subtype_val)
  letI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  set N : ℂ := (Fintype.card (K ⧸ H.subgroupOf K) : ℂ) with hNdef
  have hN : N ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let e : ι → σ.V := fun j => N⁻¹ • ∑ q : K ⧸ H.subgroupOf K, σ.ρ ((q.out : K) : GL (Fin n) _) (u j)
  refine ⟨e, fun j => ?_, ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    simp only [e, map_smul, map_sum]
    congr 1
    have hstep : ∀ q : K ⧸ H.subgroupOf K, σ.ρ (k : GL (Fin n) _) (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) =
        σ.ρ (((k • q).out : K) : GL (Fin n) _) (u j) := by
      intro q
      have hq : (QuotientGroup.mk ((k • q).out) : K ⧸ H.subgroupOf K) = QuotientGroup.mk (k * q.out) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hmem := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf] at hmem
      have h1 : ((k * q.out : K) : GL (Fin n) (s.w.adicCompletion L)) =
          (((k • q).out : K) : GL (Fin n) (s.w.adicCompletion L)) *
            ((((k • q).out)⁻¹ * (k * q.out) : K) : GL (Fin n) (s.w.adicCompletion L)) := by
        rw [← Subgroup.coe_mul, mul_inv_cancel_left]
      rw [← Module.End.mul_apply, ← map_mul]
      change σ.ρ ((k * q.out : K) : GL (Fin n) _) (u j) = _
      rw [h1, map_mul, Module.End.mul_apply, hmem j]
    simp_rw [hstep]
    exact Equiv.sum_comp (MulAction.toPerm k) (fun (q : K ⧸ H.subgroupOf K) => σ.ρ ((q.out : K) : GL (Fin n) (s.w.adicCompletion L)) (u j))
  · choose κ hκU hκT hκ using fun (q : K ⧸ H.subgroupOf K) => exists_lift s i hi ((q.out : K) : GL (Fin n) _) q.out.2
    have key : ∀ q : K ⧸ H.subgroupOf K, ∑ j, T j (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) = f := by
      intro q
      rw [← hκ q]
      simp_rw [hT _ (κ q) (hκT q)]
      rw [← map_sum, ← hf, hfix _ (hκU q) (hκT q)]
    calc f = N⁻¹ • ∑ _q : K ⧸ H.subgroupOf K, f := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← hNdef,
            inv_mul_cancel₀ hN, one_smul]
      _ = N⁻¹ • ∑ q : K ⧸ H.subgroupOf K, ∑ j, T j (σ.ρ ((q.out : K) : GL (Fin n) _) (u j)) := by
          simp_rw [key]
      _ = ∑ j, T j (e j) := by
          simp only [e, map_smul, map_sum, ← Finset.smul_sum]
          rw [Finset.sum_comm]

end GlobalTheory.SphAvg

namespace GlobalTheory.SphAvg

theorem exists_sum_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i →
    (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) →
    ∀ f, f ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 →
    (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
    ∃ (m : ℕ) (T : Fin m → σ.V →ₗ[ℂ] (GAf L n → π.W)) (e : Fin m → σ.V),
      (∀ j, GlobalTheory.HeckeFrob.IsLocMap s σ i (T j)) ∧
      (∀ j, e j ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n))) ∧ f = ∑ j, T j (e j) := by
  intro L _ _ _ n π s σ i hi _ f hf hfix
  classical
  obtain ⟨c, hc, hcf⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hf
  choose u hu using hc
  have hsum : f = ∑ t : c.support, t.1.1 (u t.1) := by
    rw [← hcf, Finsupp.sum, ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl fun t _ => (hu t.1).symm
  obtain ⟨e, he, hfe⟩ := exists_fixed_of_sum s σ i hi (ι := c.support) (fun t => t.1.1)
    (fun t => t.1.2.2) (fun t => u t.1) f hsum hfix
  · refine ⟨c.support.card, fun j => (c.support.equivFin.symm j).1.1,
      fun j => e (c.support.equivFin.symm j), fun j => (c.support.equivFin.symm j).1.2.2,
      fun j => he _, ?_⟩
    rw [hfe]
    exact (Equiv.sum_comp c.support.equivFin.symm (fun t => t.1.1 (e t))).symm

end GlobalTheory.SphAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.BaseEnl

open GlobalTheory.Mem.BaseExt

section map

variable {L L' : Type} [Field L] [Field L'] [CharZero L] [CharZero L'] (ι : L →ₐ[ℚ] L')
  (K : IntermediateField ℚ L)

def toMap : K →+* K.map ι := (K.equivMap ι).toRingEquiv.toRingHom

theorem coe_toMap (x : K) : (toMap ι K x : L') = ι x := rfl

theorem toMap_surj : Function.Surjective (toMap ι K) := (K.equivMap ι).surjective

theorem image_map {E : Type} [Field E] (𝔞 : Ideal (𝓞 E)) (e : E → L) :
    extend (toMap ι K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : L) = e (a : E)}) =
      Submodule.span (𝓞 (K.map ι)) {x : K.map ι | ∃ a ∈ 𝔞, (x : L') = ι (e (a : E))} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, by rw [coe_toMap, hy]⟩
  · rintro ⟨a, ha, hx⟩
    obtain ⟨y, rfl⟩ := toMap_surj ι K x
    exact ⟨y, ⟨a, ha, ι.injective hx⟩, rfl⟩

end map

theorem exists_enl : ∀ (B : Base) (S : Finset ℂ), (∀ z ∈ S, IsAlgebraic ℚ z) →
    ∃ B' : Base, Enl B B' ∧ ∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S h
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.LL
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (S ∪ SE) (by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [h z hz, hSE z hz])
  have hEK := hE K (fun z hz => hS z (Finset.mem_union_right _ hz)) B.embLL
  have : NumberField K := {}
  let ι : B.LL →ₐ[ℚ] K := (B.embLL.codRestrict K hEK).toRatAlgHom
  have hι : ∀ x, K.val (ι x) = B.embLL x := fun _ => rfl
  have tr : ∀ (F : IntermediateField ℚ B.LL) (w : ℂ), (∃ z ∈ F, B.embLL z = w) →
      ∃ z ∈ F.map ι, K.val z = w := by
    rintro F w ⟨z, hz, rfl⟩
    exact ⟨ι z, ⟨z, hz, rfl⟩, rfl⟩
  have im : ∀ F : IntermediateField ℚ B.LL,
      (K.val : K →+* ℂ) '' (F.map ι : Set K) = B.embLL '' (F : Set B.LL) := by
    intro F
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · exact tr F w
  have hg0 := B.coeffGaloisSubfield_isGalois
  let f := toMap ι B.Ks
  refine ⟨{ toPre := B.toPre
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := (ι : B.LL →+* K).comp B.embE
            embE_φ₀ := by rw [← B.embE_φ₀]; rfl
            LL0 := B.LL0.map ι
            coeffGaloisSubfield_isGalois := @IsGalois.of_algEquiv ℚ B.LL0 _ _ (B.LL0.map ι) _ _ _ hg0 (B.LL0.equivMap ι)
            Ks := B.Ks.map ι
            Ks_le := IntermediateField.map_mono ι B.Ks_le
            E_le_Ks := fun x => ⟨B.embE x, B.E_le_Ks x, rfl⟩
            roots_Ks := fun N hN => tr _ _ (B.roots_Ks N hN)
            roots_Ks' := fun N hN => tr _ _ (B.roots_Ks' N hN)
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := tr _ _ B.rootOfUnity_eightQ_mem_coeffGaloisSubfield
            roots_LL := fun u => ?_ }, ⟨rfl, im _, im _, ?_⟩, ?_⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := B.capit 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_map ι B.Ks 𝔞 B.embE)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := B.kPsi j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g a))
    have e2 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g (B.host.conj a)))
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · obtain ⟨z, hz⟩ := B.roots_LL u
    exact ⟨ι z, hz⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨ι z, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (Finset.mem_union_left _ hz)⟩, rfl⟩

end GlobalTheory.Mem.BaseEnl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.LiftCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.RealWeil GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem actO_inv_cancel {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  have a : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  have b : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  unfold actO
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, a, Matrix.one_mul, Matrix.mul_assoc, b, Matrix.mul_one]

theorem eq_smul_of_inv_mul {G H M : Type} [Group G] [Group H] [AddCommGroup M] [Module ℂ M]
    (om : G × H →* Module.End ℂ M) (A : Module.End ℂ M) (g : G) (k : H) {c : ℂ} (hc : c ≠ 0) (f : M)
    (e : (om (g⁻¹, k⁻¹) * A) f = c • f) : om (g, k) f = c⁻¹ • A f := by
  have e := congrArg (om (g, k)) e
  rw [← Module.End.mul_apply, ← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel,
    Prod.mk_one_one, map_one, one_mul, map_smul] at e
  rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem weil_eq_smul_osc : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ Ω : GA D S × GA D T → GlobalTheory.RealWeil.BB ψ S T → GlobalTheory.RealWeil.BB ψ S T, GlobalTheory.RealWeil.IsOsc (GlobalTheory.RealWeil.rhoV hψ σ S T) (fun p v => GlobalTheory.RealWeil.mM θ S T p *ᵥ v) Ω → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → om (g, h) F.1 = c • ((Ω (g, h) F).1 : WO S T → ℂ) := by
  intro D θ σ h ψ hψ S T om hw Ω hΩ g hg k hk
  unfold IsOsc at hΩ
  obtain ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩ := hΩ
  have hθ := h.inf
  have sm := sm_of_theta (S := S) (T := T) h hψ
  have hfin : ∀ p {u : WO S T}, u.map (infPart D) = 0 → ∀ F, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F →
      Ω p (rhoB hψ u F) = rhoB hψ u (Ω p F) := fun p u hu F hF => hcomm p _ (rhoB_comm h hψ hu) F hF
  have hth : ∀ p F, IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (Ω p F).1 := by
    intro p F hF
    obtain ⟨U, hU, hl⟩ := hF.level
    refine theta_of_sm h hψ _ (hsm p F (sm F hF)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoB hψ u F = F := QB_ext fun x => by rw [coe_rhoB, hl u hu h0]
    rw [← coe_rhoB hψ, ← hfin p h0 F (sm F hF), e]
  obtain ⟨om', hom⟩ := exists_hom hψ Ω hth (fun p F F' h1 h2 => hadd p F F' (sm F h1) (sm F' h2))
    (fun p a F h1 => hsmul p a F (sm F h1)) (fun F h1 => hone F (sm F h1)) fun p p' F h1 => hmul p p' F (sm F h1)
  have lift : ∀ f, IsThetaFunO ψ S T f → ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    fun f hf => ⟨toB hψ f hf, coe_toB hψ f hf⟩
  have pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om' p f) := by
    intro p f hf
    obtain ⟨F, rfl⟩ := lift f hf
    rw [hom p F hf]
    exact hth p F hf
  have Heisenberg₂ : ∀ w f, IsThetaFunO ψ S T f →
      om' (g, k) (heisO ψ S T w f) = heisO ψ S T (actO S T g k w) (om' (g, k) f) := by
    intro w f hf
    obtain ⟨F, rfl⟩ := lift f hf
    obtain ⟨u, v, hu, rfl⟩ := exists_parts h w
    have h1 : IsThetaFunO ψ S T (rhoV hψ σ S T v F).1 := by
      rw [coe_rhoV]
      exact theta_heisO_real hθ hψ (real_iotaV h v) hf
    have h2 : IsThetaFunO ψ S T (rhoB hψ u (rhoV hψ σ S T v F)).1 := by
      rw [coe_rhoB]
      exact GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 h1 hu
    have e1 : actO S T g k (u + iotaV σ S T v) = u + iotaV σ S T (mM θ S T (g, k) *ᵥ v) := by
      rw [GlobalTheory.WeilVacMove.actO_add, actO_fin h hg hk hu, actO_iotaV h]
    rw [hom _ F hf, e1, ← coe_rhoB hψ _ F, ← coe_rhoB hψ _ (Ω (g, k) F), rhoB_add h hψ hu v F,
      rhoB_add h hψ hu _ (Ω (g, k) F), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm F hf)]
  obtain ⟨c, hc, hM⟩ := GlobalTheory.T.schur_lemma_thetaFunctions_from_matrixCoefficients D ψ hψ S T (om (g⁻¹, k⁻¹) * om' (g, k))
    (fun f hf => hw.om_pres _ _ (pres _ f hf))
    (fun w f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, Heisenberg₂ w f hf, hw.om_heis _ _ _ _ (pres _ f hf),
        actO_inv_cancel])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hw.om_unit μ 𝓕 hμ h𝓕 _ _ (pres _ f hf)]
      obtain ⟨F, rfl⟩ := lift f hf
      rw [hom _ F hf]
      exact lintegral_eq_of_norms hψ μ 𝓕 hμ h𝓕 fun H _ _ _ Φ hΦ =>
        hunit H Φ (fun v => hΦ _) _ F (sm F hf))
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun F hF => ?_⟩
  rw [← hom _ F hF]
  exact eq_smul_of_inv_mul om _ g k hc0 _ (hM F.1 hF)

end GlobalTheory.Mem.LiftCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem GlobalTheory.AlgWtF.tenRepF_isIrreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → (GlobalTheory.AlgWtF.tenRepF emb lam).IsIrreducible := by
  intro L _ _ _ n ι _ K _ _ emb lam hCM
  have hstab : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ γ : GQ L n, ∀ w ∈ W, GlobalTheory.AlgWtF.tenRepF emb lam γ w ∈ W) →
      ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W := by
    intro W hW g w hw
    have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ w ∈ W,
        Formalism.L2.DIV.rhoK lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w ∈ W := by
      intro γ₀ hγ₀ w hw
      obtain ⟨γ, rfl⟩ := GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto L n γ₀ hγ₀
      exact hW γ w hw
    by_contra hnot
    have hx : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) ∉
        W.map (Formalism.L2.DIV.VV K lam).subtype := by
      rintro ⟨y, hy, hyx⟩
      exact hnot (by rw [show Formalism.L2.DIV.rhoK lam g w = y from Subtype.ext hyx.symm]; exact hy)
    obtain ⟨ψ, hψx, hψW⟩ := Submodule.exists_le_ker_of_notMem hx
    obtain ⟨P, hP⟩ := GlobalTheory.T.weightAction_matrixCoeff_polynomial_in_entries K ι n lam (w : Formalism.L2.DIV.Pol K ι n) ψ
    let f : (ι ⊕ ι) × Fin n × Fin n → (L →+* K) × Fin n × Fin n :=
      fun v => (Sum.elim emb (fun τ => (emb τ).comp (IsCMField.complexConj L : L →+* L)) v.1, v.2)
    have hzero := GlobalTheory.T.zariskiDense_rationalPoints_definiteUnitary_charZero L n K (MvPolynomial.rename f P) ?_
    · obtain ⟨B, hBc, hBe⟩ := GlobalTheory.T.exists_unitary_extension_of_cmType_family L n ι K emb hCM g
      have h0 := hzero B hBc
      rw [MvPolynomial.eval_rename] at h0
      apply hψx
      have h1 : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) =
          Formalism.L2.DIV.actP lam g w := rfl
      rw [h1, hP g, ← h0]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, hBe]
      · simp only [f, Function.comp_apply, Sum.elim_inr]
        rw [hBc (emb τ), hBe τ]
        rfl
    · intro γ₀ hγ₀
      rw [MvPolynomial.eval_rename]
      have h2 := hrat γ₀ hγ₀ w hw
      have h3 : ψ (Formalism.L2.DIV.actP lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w) = 0 :=
        hψW ⟨_, h2, rfl⟩
      rw [hP] at h3
      rw [← h3]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, GlobalTheory.AlgWtF.embGLF]
      · have hinv : (((γ₀⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) =
            ReciprocityTheory.Aut.conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
          Units.inv_eq_of_mul_eq_one_right hγ₀
        simp only [f, Function.comp_apply, Sum.elim_inr, GlobalTheory.AlgWtF.embGLF, MonoidHom.pi_apply, ← map_inv,
          Matrix.GeneralLinearGroup.map_apply, hinv, ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply,
          RingHom.comp_apply]
  have hsimple : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    GlobalTheory.T.coefficientSpace_stable_eq_bot_or_top K ι n lam (fun τ => GlobalTheory.T.nablaSq_endomorphism_eq_sum_GL_operators K n (lam τ) (GlobalTheory.T.dualWeylModule_simple_charZero K n (lam τ)))
  haveI hnt : Nontrivial (Formalism.L2.DIV.VV K lam) := GlobalTheory.T.nontrivial_weylCoefficientSpace K ι n lam
  haveI : Nontrivial (Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, hx⟩ := exists_ne (0 : Formalism.L2.DIV.VV K lam)
    have hxt : x ∈ (⊤ : Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)).toSubmodule := trivial
    rw [← h'] at hxt
    exact hx hxt
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases hsimple W.toSubmodule (hstab W.toSubmodule (fun γ w hw => W.apply_mem_toSubmodule γ hw)) with h | h
  · left; exact Subrepresentation.ext h
  · right; exact Subrepresentation.ext h
end

