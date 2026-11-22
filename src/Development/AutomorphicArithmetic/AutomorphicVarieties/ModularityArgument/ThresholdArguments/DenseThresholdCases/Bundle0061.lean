import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.OpOfProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0056
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0059
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0017
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0016
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Sph
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0014
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0053
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0016
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0042
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0023
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0024
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0033

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevOpOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem opOf_proj {Λ Γ Q M : Type} [CommRing Λ] [Group Γ] [Group Q] [AddCommGroup M] [Module Λ M]
    (ρ : Representation Λ Q M) (e : Γ ≃* Q) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ.asModule) :
    Module.Projective (MonoidAlgebra Λ Γ) (Representation.asModule (ρ.comp e.toMonoidHom : Representation Λ Γ M)) := by
  let σ : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ Γ := (MonoidAlgebra.domCongr Λ Λ e.symm).toRingEquiv
  let ρ' : Representation Λ Γ M := ρ.comp e.toMonoidHom
  have key : ∀ a : MonoidAlgebra Λ Q, ρ'.asAlgebraHom (σ a) = ρ.asAlgebraHom a := fun a => by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | single g c => simp [σ, ρ']
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let f : ρ.asModule ≃ₛₗ[(σ : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ Γ)] ρ'.asModule :=
    { ρ.asModuleEquiv.toAddEquiv.trans ρ'.asModuleEquiv.symm.toAddEquiv with
      map_smul' := fun a m => by
        apply ρ'.asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul]
        simp [Representation.asModuleEquiv_map_smul, key] }
  exact Module.Projective.of_equiv f
private theorem opOf_dc {R G P : Type} [CommRing R] [Group G] [AddCommGroup P] [Module R P] (ρ : Representation R G P)
    (K K1 : Subgroup G) [Fintype (K ⧸ K1.subgroupOf K)] (m : P) (hm : m ∈ fixd ρ K1) :
    dc ρ K K1 1 m = ∑ g : K ⧸ K1.subgroupOf K, ρ (g.out : K) m := by
  let f : K ⧸ K1.subgroupOf K → MulAction.orbit K ((1 : G) : G ⧸ K1) := fun g =>
    ⟨((g.out : K) : G), g.out, congrArg QuotientGroup.mk (mul_one _)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 := QuotientGroup.eq.1 (congrArg Subtype.val hab)
      rw [← a.out_eq', ← b.out_eq']
      exact QuotientGroup.eq.2 h1
    · rintro ⟨_, k, rfl⟩
      refine ⟨(k : K ⧸ K1.subgroupOf K), Subtype.ext ?_⟩
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (k : K ⧸ K1.subgroupOf K))
      have h2 : (((k : K ⧸ K1.subgroupOf K).out : K) : G ⧸ K1) = ((k : G) : G ⧸ K1) := QuotientGroup.eq.2 h1
      exact h2.trans (congrArg (QuotientGroup.mk (s := K1)) (mul_one (k : G)).symm)
  unfold dc
  rw [← finsum_comp f hf, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K1 ((g.out : K) : G)
  show ρ (((g.out : K) : G) : G ⧸ K1).out m = _
  rw [hu, map_mul, Module.End.mul_apply, hm u u.2]
private theorem opOf_tr {Λ R G P Γ σ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group G] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] [Group Γ] [Finite Γ] (ρ : Representation R G P)
    (K K1 : Subgroup G) (hle : K1 ≤ K) [(K1.subgroupOf K).Normal]
    (ρ' : Representation Λ (K ⧸ K1.subgroupOf K) (fixd ρ K1))
    (hρ' : ∀ (u : K) f, (ρ' (u : K ⧸ K1.subgroupOf K) f : P) = ρ u f)
    (hP : Module.Projective (MonoidAlgebra Λ (K ⧸ K1.subgroupOf K)) ρ'.asModule)
    (e : Γ ≃* K ⧸ K1.subgroupOf K) (γ : σ → Γ) (hγ : Subgroup.closure (Set.range γ) = ⊤)
    (Y : σ → Module.End R (fixd ρ K1)) (hY : ∀ p m, ρ' (e (γ p)) m = m + Y p m)
    (tr : fixd ρ K1 →ₗ[R] fixd ρ K) (htr : ∀ m, (tr m : P) = dc ρ K K1 1 m) :
    Function.Surjective tr ∧ LinearMap.ker tr = ⨆ p, LinearMap.range (Y p) := by
  haveI : Finite (K ⧸ K1.subgroupOf K) := Finite.of_equiv Γ e.toEquiv
  letI := Fintype.ofFinite (K ⧸ K1.subgroupOf K)
  obtain ⟨h1, h2⟩ := projNorm Λ _ _ ρ' hP
  have hs : ∀ m, (tr m : P) = (∑ g, ρ' g m : fixd ρ K1) := fun m => by
    rw [htr, opOf_dc ρ K K1 m m.2, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hρ', QuotientGroup.out_eq']
  refine ⟨fun v => ?_, le_antisymm (fun m hm => ?_) (iSup_le fun p => ?_)⟩
  · obtain ⟨m, hm⟩ := h1 ⟨v, fixd_anti ρ hle v.2⟩ fun g => by
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      exact Subtype.ext ((hρ' u _).trans (v.2 u u.2))
    exact ⟨m, Subtype.ext (by rw [hs, hm])⟩
  · have h0 : ∑ g, ρ' g m = 0 := Subtype.ext (by rw [← hs, LinearMap.mem_ker.1 hm]; rfl)
    have hc : Subgroup.closure (Set.range fun p => e (γ p)) = ⊤ := by
      have := congrArg (Subgroup.map e.toMonoidHom) hγ
      rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _ e.surjective] at this
      exact this
    have h3 : (⨆ g ∈ Set.range fun p => e (γ p), LinearMap.range (ρ' g - 1)) ≤
        (⨆ p, LinearMap.range (Y p)).restrictScalars Λ := by
      refine iSup₂_le ?_
      rintro _ ⟨p, rfl⟩ _ ⟨v, rfl⟩
      refine Submodule.mem_iSup_of_mem (p := fun p => LinearMap.range (Y p)) p ⟨v, ?_⟩
      rw [LinearMap.sub_apply, hY, Module.End.one_apply, add_sub_cancel_left]
    exact h3 (h2 _ hc m h0)
  · rintro _ ⟨m, rfl⟩
    have h4 : tr (ρ' (e (γ p)) m) = tr m := Subtype.ext (by
      rw [hs, hs]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulRight (e (γ p))) _ _ fun g => ?_
      rw [Equiv.coe_mulRight, map_mul, Module.End.mul_apply])
    rw [hY, map_add] at h4
    exact add_eq_left.1 h4
private theorem opOf_gen {l q n : ℕ} (hl : l.Prime) (a : Fin q → ℕ) :
    Subgroup.closure (Set.range fun p : Fin q × Fin n => (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a)) = ⊤ := by
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  refine eq_top_iff.2 fun g _ => ?_
  rw [← Finset.univ_prod_mulSingle g]
  refine Subgroup.prod_mem _ fun s _ => ?_
  have h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [h1, Pi.mulSingle_pow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self s)) _
private theorem opOf_cop {L : Type} [Field L] [NumberField L] (w : Plc L) {l : ℕ} (hl : l.Prime)
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) : l.Coprime (resCard (w.adicCompletion L)) := by
  have h1 : Valued.v (l : w.adicCompletion L) = 1 := by
    have e : (l : w.adicCompletion L) = algebraMap L _ (algebraMap (𝓞 L) L l) := by simp
    rw [e]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans ?_
    exact (HeightOneSpectrum.valuation_of_algebraMap w _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hw)
  have h2 : valuation (w.adicCompletion L) (l : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 h1
  have h3 : IsUnit (l : 𝒪[w.adicCompletion L]) :=
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 (by simpa using h2)
  have h4 : (l : 𝓀[w.adicCompletion L]) ≠ 0 := by
    simpa using (h3.map (residue 𝒪[w.adicCompletion L])).ne_zero
  rw [hl.coprime_iff_not_dvd]
  intro hd
  letI := Fintype.ofFinite 𝓀[w.adicCompletion L]
  haveI := Fact.mk hl
  rw [resCard, Nat.card_eq_fintype_card] at hd
  exact h4 ((ringChar.spec _ _).2 (by
    have h5 := (prime_dvd_char_iff_dvd_card l).2 hd
    have h6 := CharP.char_is_prime 𝓀[w.adicCompletion L] (ringChar 𝓀[w.adicCompletion L])
    rw [(Nat.prime_dvd_prime_iff_eq hl h6).1 h5]))
private theorem opOf_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwC k n ⊤ := by
  have h1 : unitsC k C ≤ unitsC k ⊤ := Subgroup.map_mono (Subgroup.comap_mono le_top)
  have h2 : torC k n C ≤ torC k n ⊤ := fun t ht i hi => h1 (ht i hi)
  exact sup_le_sup_left (Subgroup.map_mono h2) _
private theorem opOf_tow {Λ R P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] (S : Submodule R P) : IsScalarTower Λ R S := inferInstance
theorem UpperTheory.V.Pa.Lev.opOf_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (ph ta : Fin q → (globOf r V).G₀) (N : ℕ), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → (∀ j, qj w j ≡ 1 [MOD l ^ N]) → ∃ A' : OpMod b h q N, OpRel A' (qj w) ph ta n.factorial := by
  intro hP l hl L Ω _ _ _ _ _ _ s V0 O _ _ _ hO _ n r B J D b V h q w A x δ hw hx hδ ph ta N hok hN
  have hq : ∀ j, IsUnit (qj w j : A.R) := fun j => by
    haveI := hO.char
    have h1 : IsUnit (qj w j : ResidueField O) :=
      (CharP.isUnit_natCast_iff hl.out).2 (hl.out.coprime_iff_not_dvd.1 (opOf_cop (w j) hl.out (hw j)))
    have h2 : IsUnit (qj w j : O) := by
      rw [← map_natCast (residue O)] at h1
      exact (isUnit_map_iff _ _).1 h1
    simpa using h2.map (algebraMap O A.R)
  obtain ⟨T⟩ := thEx L n q w l A.R A.P A.ρ x δ hq
  obtain ⟨hn, ρ', hρ', hpr⟩ := A.proj
  obtain ⟨e, he⟩ := delIso L n q w l δ hδ
  obtain ⟨hy, tr, htr, hu⟩ := trOf L n q w l A.R A.P A.ρ x δ T hδ
  obtain ⟨h1, h2⟩ := _root_.UpperTheory.V.Z.Win.T2.level_relation_one_two hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have h3 := _root_.UpperTheory.V.Pa.Lev.twoOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have hg : ∀ j i m, ρ' (e (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1))) m = T.act1 (1 + yV A.R j i) m := fun j i m => by
    obtain ⟨g, hg1, hg2⟩ := he j i
    exact Subtype.ext (by rw [hg2, hρ', hg1]; exact (hy j i m).symm)
  have hle : UIw1 l n w ≤ UIw n w := fun g hg j hj => opOf_le _ (hg j hj)
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ padicValNat l (qj w p.1 - 1)) := fun s => ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨hs, hk⟩ := opOf_tr A.ρ (UIw n w) (UIw1 l n w) hle ρ' hρ' hpr e
    (fun p : Fin q × Fin n => Pi.mulSingle p (Multiplicative.ofAdd 1)) (opOf_gen hl.out fun j => padicValNat l (qj w j - 1))
    (fun p : Fin q × Fin n => T.act1 (yV A.R p.1 p.2)) (fun p m => (hg p.1 p.2 m).trans (by rw [map_add, map_one]; rfl)) tr htr
  have ha : ∀ j, N ≤ padicValNat l (qj w j - 1) := fun j => by
    have h4 : 1 < qj w j := Finite.one_lt_card
    exact (padicValNat_dvd_iff_le (by omega)).1 ((Nat.modEq_iff_dvd' h4.le).1 (hN j).symm)
  exact ⟨{ rN := A.rN, compat := A.compat, R := A.R, p := A.p, segmentWeightExponent := A.segmentWeightExponent, β := A.β, β_pair := A.β_pair
           M1 := fixd A.ρ (UC n w fun _ => ellC l _), tow1 := opOf_tow _, fin1 := A.fin, Mw := fixd A.ρ (UC n w fun _ => ⊤)
           act1 := T.act1, actw := T.actw, a := fun j => padicValNat l (qj w j - 1), le_a := ha
           ρ := ρ'.comp e.toMonoidHom, ρ_gen := hg, proj := opOf_proj ρ' e hpr
           tr := tr, tr_surj := hs, tr_ker := hk, tr_u := hu }, h3, h1, h2⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartU
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z.Desc.P in
theorem UpperTheory.V.Z.Desc.P.partX_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∃ Y : (hset Q τ₀).PartAltAlt ι lam ξ, (Y.Y = YOf Q ι τ₀ e ξ σ ∧ _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r ∧ (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧ (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (Y.r.comp V.pr) w τ)) ∧ (Af.IsIrr (Y.r.comp V.pr) →
      ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧
        (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧
        ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), π.IsLocComp w τ →
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) := by
  intro PH l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY
  have P := PH.toClassicalTheorems
  have hAx := _root_.UpperTheory.V.Hi.axU_s P.litN l L Ω s n hn V Q c m τ₀
  have hund : ∀ {A : ValuationSubring Ω} {w : Plc L}, IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 (Lp L))) :=
    fun hA y => hA (algebraMap (𝓞 (Lp L)) (𝓞 L) y)
  have hwv : ∀ v, (s.w v).under (𝓞 (Lp L)) = v := fun v =>
    HeightOneSpectrum.ext (Ideal.ext fun y => (hund (s.hw v) y).symm.trans (s.hA v y))
  have hl : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  have hsp : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∈ V.S' → IsSplitAt w := fun w hw =>
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hw) w rfl
  have hspS : ∀ v ∈ s.S, IsSplitAt (s.w v) := fun v hv => hsp _ (by rw [hwv]; exact V.sub hv)
  have hspQ : ∀ q, IsSplitAt (Q.wq q) := fun q => hsp _ (by rw [Q.range]; exact Or.inr ⟨q, rfl⟩)
  have hin : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → w.under (𝓞 (Lp L)) ∈ V.S' := fun w hw =>
    V.sub (Or.inl ((hl w).1 hw))
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr := partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY
  have hwt := partUR2Wt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY
  have hex : ∀ w : Plc L, IsSplitAt w → ∃ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧
        (IsUnramU σ w → Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w n)) := fun w hw => by
    obtain ⟨τ, -, h1, h2⟩ := GlobalTheory.DefU.exists_locComp_split L n ⟨σ, hσ⟩ w hw
    refine ⟨τ, h1, fun h => ?_⟩
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (h2.1 h)
    exact ⟨v, h0, fun u hu => by simpa using hv ⟨u, hu⟩⟩
  choose loc hloc hfix using hex
  obtain ⟨R, HT, hRc, hRs, hRu, hW, hLH, hpair, hcusp⟩ :=
    _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH PH L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ
  obtain ⟨ρ, hρc, rfl, hform⟩ := UpperTheory.exists_descent_to_level_group_of_unramified l L Ω s n V c R hRc fun w hw A hA =>
    hRu w (mt (hin w) hw) (hunr w hw) A hA
  have hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ := fun w hw τ hτ => (hLH w hw τ hτ).1
  have hHG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Desc.P.HtGT (ρ.comp V.pr) HT w τ := fun w hw τ hτ => (hLH w hw τ hτ).2
  have hall : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∃ τ, _root_.UpperTheory.V.Z.Desc.P.HtGT (ρ.comp V.pr) HT w τ :=
    fun w hw => ⟨_, hHG w (hsp w (hin w hw)) _ (hloc _ (hsp w (hin w hw)))⟩
  have hsat : ∀ w : (hset Q τ₀).Wp, ∃ a : ℕ → ℂ, a 0 = 1 ∧
      (∀ j, ∀ v ∈ fixd (loc w.1 w.2.2).ρ (KO (w.1.adicCompletion L) (Fin n)), sphOp (loc w.1 w.2.2).ρ j v = a j • v) ∧
      ∀ (B : ValuationSubring Ω) (g : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) g →
        (ρ (V.pr g⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) a := fun w => by
    obtain ⟨b, hb'⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results P L n w.1 _).1 (hfix w.1 w.2.2 (hunr _ w.2.1))
    obtain ⟨-, a, h0, h1, h2⟩ := satT L n w.1 _ b hb'
    have hw := mt (hin w.1) w.2.1
    refine ⟨a, h0, h1, fun B g hB hg => ?_⟩
    rw [← h2]
    exact (_root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P L Ω l ι n _ hRc w.1 hw _ b hb'
      (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG w.1 w.2.2 _ (hloc _ _)) hw) B hB).2 g hg
  choose a ha0 ha1 ha2 using hsat
  refine ⟨{ Y := YOf Q ι τ₀ e ξ σ
            le := inf_le_left
            ne := hY
            σl := fun v => loc (s.w v.1) (hspS _ (Or.inl v.2))
            isoL := fun v => partUR2IsoL l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ v _ (hloc _ _)
            σq := fun q => loc (Q.wq q) (hspQ q)
            isoQ := fun q => partUR2IsoQ l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hAx q _ (hloc _ _)
            a := a
            a_zero := ha0
            sph := fun w j => partUR2Sph l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hAx w.1 w.2.1 w.2.2 _ (hloc _ _) j _
              (ha1 w j)
            r := ρ
            cont := hρc
            ss := fun M hM => ?_
            frob := ha2
            atL := fun v => _root_.UpperTheory.V.Z.Desc.P.ordinary_at_l_of_local_global_hodge_tate_weights P.litN (s.hw v.1) lam hall (hHG _ (hspS _ (Or.inl v.2)) _ (hloc _ _))
              (hLG _ (hspS _ (Or.inl v.2)) _ (hloc _ _)) fun j => hW _ _ (hwt ⟨v, j⟩)
            atQ := fun q => _root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG _ (hspQ q) _ (hloc _ _)) (hAx.Q_away q) },
    ⟨rfl, ⟨?_, fun t ht u => ?_, fun hi => ?_, ?_⟩, fun v => hloc _ _, hLG⟩, fun hi => ?_⟩
  · obtain ⟨M', h1, h2⟩ := hRs M fun g => hM (V.pr g)
    refine ⟨M', fun g => ?_, h2⟩
    obtain ⟨g, rfl⟩ := hpr g
    exact h1 g
  · obtain ⟨P', hP'⟩ := hpair s.c s.hc
    exact ⟨P', hform P' hP'⟩
  · have hS : ∀ u : s.St, (u : Plc (Lp L)) ∈ s.S := fun u => Or.inr (Or.inl u.2)
    obtain ⟨rc, hrc⟩ : ∃ rc : IrrGL ((s.w u).adicCompletion L) → WD (s.hw u), _root_.UpperTheory.Zero.LLC.IsRecT (s.hw u) rc := P.exists_reciprocity_dense (s.hw u)
    have hT := _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY _ (hτ t ht)
      (fun u => loc (s.w u) (hspS _ (hS u))) (fun u => hloc _ _) u rc hrc
    have hu : ((l : ℕ) : 𝓞 L) ∉ (s.w u).asIdeal := fun h => s.St_l u u.2 (by simpa only [hwv] using (hl _).1 h)
    obtain ⟨g, hg⟩ := UpperTheory.exists_conj_inertia_diagonal_of_isTypeWD l L Ω ι n _ _ (s.hw u) hu (ρ.comp V.pr)
      (fun i => W.pushCh (algebraMap c.O (Qbar l)) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))) _
      (_root_.UpperTheory.V.Z.Desc.P.woTypeT (_root_.UpperTheory.V.Z.Desc.P.lgAwayT (hLG _ (hspS _ (hS u)) _ (hloc _ _)) hu _ (s.hw u) rc hrc)
        (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp V.pr)) hT) hT
    refine ⟨g, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨x, hx⟩
  · obtain ⟨π, h1, h2, h3, h4, -⟩ := hcusp ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => by
      obtain ⟨g, rfl⟩ := hpr g
      exact hI g⟩
    exact ⟨π, h1, h2, h3, fun v j => h4 _ _ (hwt ⟨v, j⟩)⟩
  · exact ⟨σ, hσ, hLG, hwt, hunr, fun w hw => ⟨_, hloc w hw⟩, loc _ (hspS _ (Or.inr (Or.inr rfl))), hloc _ _,
      partUR2V0 l L Ω s n hn V Q c ι m τ₀ lam d e ξ hb σ hσ hY _ (hloc _ _)⟩
  · obtain ⟨π, h1, h2, h3, -, h5, h6⟩ := hcusp hi
    exact ⟨π, h1, h2, h3, h5, h6⟩
theorem UpperTheory.V.Z.Desc.P.partU_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∃ Y : (hset Q τ₀).PartAltAlt ι lam ξ, Y.Y = YOf Q ι τ₀ e ξ σ ∧ _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam Y.r ∧ (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧ ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (Y.r.comp V.pr) w τ :=
  fun PH l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY =>
    (_root_.UpperTheory.V.Z.Desc.P.partX_alt PH l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ hb σ hσ hY).imp fun _ h => h.1
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigidEndTwoWOfPrintedAdjointLifting
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private irr2 pair2 freeRes from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.CharpolyPowTwoByTwo
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.rigid_end_two_w_of_printed_adjoint_lifting :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.GalN.V.RigidityEndomorphismWeightTwo := by
  intro hH hAd Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hΨσ hF A _ _ r hr hII h11 K _ _ _ _ hK2 hK W hWc hW hdet haut hWit hfree θ hθ R hR
  obtain ⟨L, _, _, _, _, g₂, Φ, C₀, ⟨k⟩, hok, hbig, hseed⟩ := hF
  haveI := Db.algClo L Ω
  haveI := Db.algClo K Ω
  obtain ⟨-, ka, hka, hrig⟩ := _root_.UpperTheory.V.Th.linked_rigid_of_printed_adjoint_lifting hH hAd Ω l ι c N e ψ η σ g₂ B M H L Φ C₀ k hok hbig hseed
  have hof := UpperTheory.V.Z.Keep.ordFlag2 Ω l c N e ψ η σ g₂ B M H L Φ C₀ k hok A r
  generalize Chr.Psi l e (Chr.dirG ℚ Ω ψ) = Ψ at *
  have hl : l ∣ M := (dvd_mul_right l N).trans H.dvd
  have hσ : σ * σ = 1 := Db.cc_sq H.cc
  have hmk := Pr.marks_of_link k hok hl hσ hΨσ
  have hLη := Db.galL_le k
  obtain ⟨_, _⟩ := Db.algKL K L Ω (hK ▸ hLη)
  obtain ⟨_, hsol⟩ := Db.galKL K L k.ab
  haveI := Db.locHom c A
  haveI := (isNoetherianRing_iff_ideal_fg A).2 fun I => (IsPrincipalIdealRing.principal I).fg
  haveI : Normal ℚ L := k.ab.toIsGalois.to_normal
  have hb : U3.Block η r := fun g hg a b hab => Subtype.ext (hII.1 g hg a b hab)
  have hg₂ : g₂ ∈ η.ker := hmk.ηg
  have hgs : U3.gstar σ g₂ ∈ η.ker := by
    show η (σ * g₂⁻¹ * σ) = 1
    rw [map_mul, map_mul, map_inv, hmk.ηg, hmk.ηc]
    simp
  have hr' : Pr.OrdPt l η Ψ σ g₂ B r :=
    ⟨hr.red, hr.cont, ⟨hr.norm.atc,
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero],
      by rw [U3.zmat, Matrix.sub_apply, hb _ hg₂ _ _ (by decide), hb _ hgs _ _ (by decide), sub_zero]⟩, hr.away, hr.ord⟩
  have hFl : Flagged (W.comp (Base.galEmb ℚ K Ω)) := Dn.flagAll_of K Ω l 2 _ fun w hw =>
    let ⟨A', a1, κ, a2⟩ := hof hr' hb h11 K hK _ (fun s => hW _ (hK.ge (Base.galEmb_mem ℚ K Ω s))) w hw
    ⟨A', a1, κ, a2.choose_spec.2.1⟩
  obtain ⟨ρ', h1, h2, h3⟩ := Pr.exists_nrep2 k hok hl hσ r hr' hb
  have hηL : ∀ s : G L Ω, η (Base.galEmb ℚ L Ω s) = 1 := fun s => hLη (Base.galEmb_mem ℚ L Ω s)
  have hηK : ∀ s : G K Ω, η (Base.galEmb ℚ K Ω s) = 1 := fun s => hK.ge (Base.galEmb_mem ℚ K Ω s)
  let χ : G ℚ Ω →* (ResidueField A)ˣ := (Units.map ((residue A).comp (algebraMap c.O A)).toMonoidHom).comp Ψ
  have hU : U3.MatIrr ((Base.galOf ℚ L Ω).subgroupOf η.ker) (Pr.gm (W.comp η.ker.subtype)) := by
    refine irr2 (W.comp η.ker.subtype) (fun V hV => hII.2 V fun g hg v hv => ?_) (A.val : A →+* PadicAlgCl l)
      Subtype.val_injective (residue A) (χ.comp η.ker.subtype) (fun g => (r g).mat 0 0 + (r g).mat 2 2) (fun g => ?_) (fun g => ?_)
      _ (u := ⟨g₂, hg₂⟩) ?_ ?_ ?_
    · have := hV ⟨g, hg⟩ trivial v hv
      beta_reduce
      rw [← hW g hg]
      exact this
    · show _ = (W g).val.trace
      rw [hW g g.2, Matrix.trace_fin_two, map_add]
      rfl
    · have e2 : ∀ i, residue A ((r g).mat i i) = residue A (algebraMap c.O A ((U3.r0 η Ψ g).mat i i)) := fun i =>
        Ideal.Quotient.eq.2 (hr.red.red g i i)
      rw [map_add, e2, e2, ← map_inv]
      show _ = residue A (algebraMap c.O A (Ψ g : c.Oˣ)) + residue A (algebraMap c.O A (Ψ (g : G ℚ Ω)⁻¹ : c.Oˣ))
      simp [U3.GG.mat, U3.tor_val, U3.wt1]
    · rw [Subgroup.mem_subgroupOf, k.gal]
      exact ⟨k.g0.1, hg₂⟩
    · show (W g₂).val.det = 1
      rw [hdet, hmk.ηg]
      simp
    · intro h
      refine (hmk.Ψg.map ((residue A).comp (algebraMap c.O A))).ne_zero ?_
      rw [map_sub, map_pow, map_one, sub_eq_zero]
      have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val] at h'
      exact h'
  have hirr : Af.IsIrr (W.comp (Base.galEmb ℚ L Ω)) :=
    Db.irr_of_matIrr (by norm_num) (Base.galOf ℚ L Ω) (fun g => (W g).val)
      (fun V hV => hU V fun g hg v hv => hV g hg v hv) (Base.galEmb ℚ L Ω) (Base.range_galEmb ℚ L Ω).ge _ fun _ => rfl
  obtain ⟨J, hJ⟩ := pair2 (κ := Qbar l)
  have hpair : ∀ s : G ℚ Ω, η s = 1 →
      (W s).val.transpose * (J * (W σ)⁻¹).val * (W (σ * s * σ⁻¹)).val = (J * (W σ)⁻¹).val := fun s hs => by
    have e1 : J * (W σ)⁻¹ * W (σ * s * σ⁻¹) = J * W s * (W σ)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    rw [Matrix.mul_assoc, ← Units.val_mul, e1, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, hdet,
      hs, Units.val_mul]
    simp
  have halg : Af.IsAlgChar ι (1 : G ℚ Ω →* (Qbar l)ˣ) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hH ℚ Ω l ι).1 _ continuous_const fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact ⟨A, hA, 0, 1, one_pos, fun s _ => by simp⟩
  have hautL : Af.IsAut ι (W.comp (Base.galEmb ℚ L Ω)) :=
    (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hH) ℚ K L Ω hsol ⟨inferInstance, Or.inr ⟨hK2, inferInstance⟩⟩ inferInstance
      inferInstance l ι 2 (by norm_num) (W.comp (Base.galEmb ℚ K Ω)) 1 (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr halg
      (fun _ _ _ _ => rfl) ⟨σ, J * (W σ)⁻¹, H.cc, fun s s' hs => by
        have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
        simp⟩).1 ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH K Ω l ι 2 _).2.1.2 haut)
  have hcsd : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (W.comp (Base.galEmb ℚ L Ω)) ka) := by
    obtain ⟨hc, art, χ, a, h'⟩ := hka.alg
    have hCL := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hH L Ω l ι 2 _).2.1.1 hautL
    have hWL : _root_.UpperTheory.V.Z.Win.WitA ι (W.comp (Base.galEmb ℚ L Ω)) :=
      _root_.UpperTheory.V.Z.Win.Dn.automorphy_up_base_change (r := W.comp (Base.galEmb ℚ K Ω)) L hH hsol (by norm_num) (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hirr
        ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, 1, σ, J * (W σ)⁻¹, halg,
          fun _ _ _ _ => rfl, H.cc, fun s s' hs => by
            have hs' : Base.galEmb ℚ K Ω s' = σ * Base.galEmb ℚ K Ω s * σ⁻¹ := hs
            rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hs', hpair _ (hηK s)]
            simp⟩ haut hFl hWit
    refine _root_.UpperTheory.GalN.V.mkCsd'_alt ?_ fun _ => _root_.UpperTheory.V.Z.Win.Dn.twist'_alt hH.toClassicalTheorems ⟨χ, hc, art, a, h'⟩ hc hWL
    refine _root_.UpperTheory.GalN.V.csdOf0_alt hH ℚ L Ω inferInstance l ι 2 (by norm_num) _ σ (J * (W σ)⁻¹) H.cc
      (_root_.UpperTheory.V.Af.twist_invariance_automorphic hH L Ω l ι 2 _ ka hautL ⟨χ, hc, art, a, h'⟩) fun s s' hs => ?_
    have hs' : Base.galEmb ℚ L Ω s' = σ * Base.galEmb ℚ L Ω s * σ⁻¹ := hs
    have hp := hpair _ (hηL s)
    rw [← hs'] at hp
    rw [MonoidHom.zpow_apply, ← hka.conj s s' hs', Units.val_mul (ka s)]
    simp only [Af.tw_val, MonoidHom.comp_apply, Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, hp]
    rw [mul_comm, mul_smul]
  obtain ⟨s, V, ρ, a1, a2, a3⟩ := hrig A ρ' h1 h3 (W.comp (Base.galEmb ℚ L Ω))
    (fun s => by rw [h2, MonoidHom.comp_apply, hW _ (hηL s)]; rfl) hirr hcsd (freeRes L W hfree)
  refine adDown Ω l K L hK2 (hK ▸ hLη) s V 2 _ _ R (hWc.comp (Base.galEmbTop ℚ K Ω).1.continuous) hR ρ ka
    (fun g t ht => ?_) (fun g g' t hg ht => ?_) a3
  · rw [a1]
    show _ • (W (Base.galEmb ℚ L Ω g)).val = _ • (W (Base.galEmb ℚ K Ω t)).val
    rw [ht]
  · have : θ (Base.galEmb ℚ K Ω t) = 1 := Units.ext (by rw [hθ, hηK]; simp)
    rw [← a2 g g' hg]
    exact mul_eq_left.2 this
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGalExW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Z.Sym.W.galois_exists_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.GalExWAlt := by
  intro P L Ω _ _ _ _ _ _ l _ ι hl hE n hn σ hσ
  obtain ⟨r, HT, hc, hs, -, -, hLG, hp, hi⟩ := P.gal L Ω hE l hl ι n hn σ hσ
  refine ⟨r, ⟨hc, _root_.UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut P.af.litN L hE n hn σ hσ,
    fun w hw τ hτ => (hLG w hw τ hτ).1, hp⟩, fun h => ?_⟩
  obtain ⟨π, h1, h2, h3, -, h4, h5⟩ := hi h
  exact ⟨π, h1, h2, h3, h4, h5⟩
end
end

