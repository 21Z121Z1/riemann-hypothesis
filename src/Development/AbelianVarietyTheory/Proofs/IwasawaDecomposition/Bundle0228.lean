import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualAtScaled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtremalUnitVectorSameHighestImage
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.DataCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquare
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMinorProductTranslateJointLowestWeight
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0186
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalVCutIdemOfNotMem
section
noncomputable section

namespace GlobalTheory.LevelClosure

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter Topology

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Classical in

def cutIdem (T : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun v => if v ∈ T then 1 else 0, Eventually.of_forall fun v => by
    by_cases h : v ∈ T
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem evalV_cutIdem_of_mem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 1 := by
  classical
  exact if_pos h

theorem evalV_cutIdem_of_notMem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 0 := by
  classical
  exact if_neg h

theorem tendsto_cutIdem_mul (a : Af F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutIdem T * a) atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ principal S := by
    rw [le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T =>
    ⟨fun v => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v, by
      rw [eventually_principal]
      intro w hw
      by_cases h : w ∈ T
      · simp only [evalV_cutIdem_of_mem h, one_mul]; exact hw
      · simp only [evalV_cutIdem_of_notMem h, zero_mul]; exact zero_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [eventually_principal]; exact fun w hw => hw⟩
  have hf : Tendsto f atTop (𝓝 a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v
    rw [evalV_cutIdem_of_mem this, one_mul]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem tendsto_cutIdem_smul (z : Af F ⊗[F] E) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => (cutIdem T : Af F) • z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  induction z using TensorProduct.induction_on with
  | zero => simpa using tendsto_const_nhds
  | add x y hx hy => simpa only [smul_add] using hx.add hy
  | tmul a x =>
    have h := (tendsto_cutIdem_mul a).smul_const ((1 : Af F) ⊗ₜ[F] x)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def cutPt (T : Finset (HeightOneSpectrum (𝓞 F))) : GAd σ J →* GAd σ J := (embAt σ J T).comp (projAt σ J T)

omit [NumberField E] in
theorem map_smul_cut (v : HeightOneSpectrum (𝓞 F)) (c : Af F) (z : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (c • z) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c • Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a x => simp [TensorProduct.smul_tmul']

omit [NumberField E] in
theorem cutPt_entry (T : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) (i j : Fin n) :
    (matHom _ σ J (projFin σ J (cutPt σ J T g))).1 i j =
      (cutIdem T : Af F) • ((matHom _ σ J (projFin σ J g)).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
        (1 : Matrix (Fin n) (Fin n) _) i j := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
  have e : ∀ g : GAd σ J, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((matHom _ σ J (projFin σ J g)).1 i j) = (matHom _ σ J (proj σ J v g)).1 i j := fun g => by
    rw [← projFinLoc_projFin]; rfl
  have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _ =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _
  rw [map_add, map_smul_cut, map_sub, e, e, e1]
  by_cases hv : v ∈ T
  · have : proj σ J v (cutPt σ J T g) = proj σ J v g := proj_embAt σ J T _ ⟨v, hv⟩
    rw [this, evalV_cutIdem_of_mem hv, one_smul, sub_add_cancel]
  · have : proj σ J v (cutPt σ J T g) = 1 := (mem_atPts.1 (embAt_mem σ J T _)).2 v hv
    rw [this, evalV_cutIdem_of_notMem hv, zero_smul, zero_add, map_one, Units.val_one]

theorem tendsto_projFin_cutPt (g : GAd σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => projFin σ J (cutPt σ J T g)) atTop (𝓝 (projFin σ J g)) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have h : ∀ g : GAd σ J, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (matHom _ σ J (projFin σ J (cutPt σ J T g))).1) atTop (𝓝 (matHom _ σ J (projFin σ J g)).1) := fun g => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [cutPt_entry]
    have := (tendsto_cutIdem_smul ((matHom _ σ J (projFin σ J g)).1 i j -
      (1 : Matrix (Fin n) (Fin n) _) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
    rwa [sub_add_cancel] at this
  rw [(isEmbedding_matHom _ σ J).tendsto_nhds_iff, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h g).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h g⁻¹
  simp only [map_inv] at h2
  exact h2

theorem tendsto_cutPt {g : GAd σ J} (hg : g ∈ finPts σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutPt σ J T g) atTop (𝓝 g) := by
  have e : ∀ g ∈ finPts σ J, ofFin σ J (projFin σ J g) = g := fun g hg =>
    ext_inf_fin σ J (by simp [mem_finPts.1 hg]) (by simp)
  have h := ((continuous_ofFin σ J).tendsto _).comp (tendsto_projFin_cutPt σ J g)
  rw [e g hg] at h
  exact h.congr fun T => e _ (mem_atPts.1 (embAt_mem σ J T _)).1

theorem mem_of_isClosed {H : Subgroup (GAd σ J)} (hH : IsClosed (H : Set (GAd σ J))) {g : GAd σ J}
    (hg : g ∈ finPts σ J) (h : ∀ v, emb σ J v (proj σ J v g) ∈ H) : g ∈ H :=
  hH.mem_of_tendsto (tendsto_cutPt σ J hg) (Eventually.of_forall fun T =>
    Subgroup.noncommProd_mem H (f := fun v : T => emb σ J v (proj σ J v g))
      (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => h v)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ksph_le_of_isClosed : ∀ (D : D7) (V : HSp D) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (H : Subgroup (GA D V)), IsClosed (H : Set (GA D V)) → (∀ v, v ∉ Z → ∀ ε, IsPlaceIdem D v ε → ∀ g ∈ KsphC V ∅, SuppPl ε V g → g ∈ H) → ∀ k ∈ KsphC V Z, k ∈ H := by
  intro D V Z H hH h k hk
  rw [KsphC_eq] at hk
  obtain ⟨h1, h2, h3⟩ := mem_levelOff.1 hk
  refine mem_of_isClosed D.sp.cm.sig V.gram hH h1 fun v => ?_
  by_cases hv : v ∈ Z
  · rw [h2 v hv, map_one]; exact one_mem _
  · have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleFin v 1)) :=
      ⟨_, rfl, evalV_singleFin_self v 1, fun _ hu => evalV_singleFin_ne hu 1⟩
    exact h v hv _ hε _ ((Model.emb_mem_KsphC_iff V v _).2 (h3 v hv)) ((Model.suppF_iff V hε _).2 ⟨_, rfl⟩)

end GlobalTheory.LevelClosure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLocalPairMapAdelic
section
noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem pm_mulsF_of_mem (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hh : h ∈ S.Uloc v) : MulsF S v hv 1 h := by
  rw [S.UlocAlt v hv] at hh
  obtain ⟨hg, h2⟩ := (Subgroup.mem_inf.1 hh).2
  exact ⟨hg, fun x => by rw [one_smul]; exact h2 x⟩

theorem pm_mulsF_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {a b : ℤ} {g h : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hg : MulsF S v hv a g) (hh : MulsF S v hv b h) :
    MulsF S v hv (b * a) (g * h) := by
  obtain ⟨ha, ha'⟩ := hg
  obtain ⟨hb, hb'⟩ := hh
  refine ⟨Subgroup.mul_mem _ ha hb, fun x => ?_⟩
  have h1 := ha' ⟨h.1 *ᵥ x.1, (hb x.1).1 x.2⟩
  have h2 := hb' x
  rw [← h2, ← h1, mul_smul]
  congr 3
  apply Subtype.ext
  simp [Matrix.mulVec_mulVec]

theorem pm_gen (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : Type} [Field k] {C : Type} (y : C → GA σ J)
    (hy : Function.Surjective (fun c => (Quotient.mk'' (y c) : Cls S)))
    (q : C → Pr (𝓞 E) (Fin n → E) k)
    (h1 : ∀ (c c' : C) (γ : GL (Fin n) E) (a : ℤ), MulsF S v hv a (bc (prV (E := E) v)
      ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1)) →
      (q c').act (glE γ) = (q c).dil (a : k))
    (h2 : ∀ (c c' : C) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → (q c').act (glE γ) = q c →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1) ∈ S.Uloc v) :
    ∃ p : GA σ J → Pr (𝓞 E) (Fin n → E) k, PMap S v hv p ∧ (∀ c, p (y c) = q c) ∧
      ∀ x, ∃ c γ, p x = (q c).act (glE γ) := by
  have hpres : ∀ x : GA σ J, ∃ (c : C) (γ : GL (Fin n) E) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      γ ∈ UJ (σ : E →+* E) J ∧ κ ∈ S.U ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ := by
    intro x
    obtain ⟨c, hc⟩ := hy (Quotient.mk'' x)
    obtain ⟨hh', hhm, kk, hkm, heq⟩ := (DoubleCoset.eq _ _ _ _).1 hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhm)
    refine ⟨c, γ, kk.1, hγ, Subgroup.mem_subgroupOf.1 hkm, ?_⟩
    rw [heq, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]
  choose cc gg kk hgg hkk hx using hpres
  have hloc : ∀ κ ∈ S.U, bc (prV (E := E) v) κ ∈ S.Uloc v := fun κ hκ => ((S.U_eq κ).1 hκ).2 v
  have hmov : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ⁻¹ * γ') * (y c').1) =
        bc (prV (E := E) v) κ * bc (prV (E := E) v) δ * (bc (prV (E := E) v) κ')⁻¹ := by
    intro c c' γ γ' κ κ' δ h
    rw [← map_inv, ← map_mul, ← map_mul, map_mul (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))), map_inv]
    congr 1
    have h' := eq_mul_inv_of_mul_eq h
    rw [mul_assoc, mul_assoc, h']
    group
  have hact : ∀ (c' : C) (γ γ' : GL (Fin n) E),
      ((q c').act (glE (γ⁻¹ * γ'))).act (glE γ) = (q c').act (glE γ') := by
    intro c' γ γ'
    rw [Pr.act_act, ← glE_mul, mul_inv_cancel_left]
  have key : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (a : ℤ),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      MulsF S v hv a (bc (prV (E := E) v) δ) →
      (q c').act (glE γ') = ((q c).act (glE γ)).dil (a : k) := by
    intro c c' γ γ' κ κ' δ a hκ hκ' h hδ
    have hm := pm_mulsF_mul S v hv (pm_mulsF_mul S v hv (pm_mulsF_of_mem S v hv _ (hloc κ hκ)) hδ)
      (pm_mulsF_of_mem S v hv _ (inv_mem (hloc κ' hκ')))
    rw [one_mul, mul_one, ← hmov c c' γ γ' κ κ' δ h] at hm
    rw [← hact c' γ γ', h1 c c' _ a hm, Pr.act_dil]
  have key1 : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ →
      (q c').act (glE γ') = (q c).act (glE γ) := by
    intro c c' γ γ' κ κ' hκ hκ' h
    have := key c c' γ γ' κ κ' 1 1 hκ hκ' (by rw [h, mul_one])
      (pm_mulsF_of_mem S v hv _ (by rw [map_one]; exact one_mem _))
    rwa [Int.cast_one, Pr.dil_one] at this
  refine ⟨fun x => (q (cc x)).act (glE (gg x)), ⟨fun γ _ x x' h => ?_, fun x δ => ⟨fun h => ?_, fun h => ?_⟩,
    fun x δ a h => ?_⟩, fun c => ?_, fun x => ⟨_, _, rfl⟩⟩
  · show (q (cc x')).act _ = ((q (cc x)).act _).act _
    rw [Pr.act_act, ← glE_mul]
    refine key1 _ _ _ _ (kk x) (kk x') (hkk x) (hkk x') ?_
    rw [← hx x', h, map_mul]
    conv_lhs => rw [hx x]
    simp only [mul_assoc]
  · have h' : (q (cc (x * δ))).act (glE (gg (x * δ))) = (q (cc x)).act (glE (gg x)) := h
    rw [← hact _ (gg x)] at h'
    have h3 := h2 _ _ _ (mul_mem (inv_mem (hgg x)) (hgg (x * δ))) (Pr.act_injective _ h')
    rw [hmov _ _ _ _ (kk x) (kk (x * δ)) δ.1 (by rw [← hx x, ← hx (x * δ)]; rfl)] at h3
    have h4 := mul_mem (mul_mem (inv_mem (hloc _ (hkk x))) h3) (hloc _ (hkk (x * δ)))
    rwa [← mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left] at h4
  · have := key _ _ _ _ (kk x) (kk (x * δ)) δ.1 1 (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl)
      (pm_mulsF_of_mem S v hv _ h)
    rwa [Int.cast_one, Pr.dil_one] at this
  · exact key _ _ _ _ (kk x) (kk (x * δ)) δ.1 a (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl) h.2.2
  · have := key1 c (cc (y c)) 1 (gg (y c)) 1 (kk (y c)) (one_mem _) (hkk _)
      (by rw [← hx (y c), map_one, one_mul, mul_one])
    rwa [glE_one, Pr.act_refl] at this

end Gen

set_option maxHeartbeats 1000000 in

theorem exists_pmap : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ v : (D.mem u).A.vT, ∃ p : GA (sigD D) (gramN D i hi) → Pr (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) ((D.mem u).A.Fv v), PMap K.lev (A.eV v).1 (A.eV v).2 p ∧ (∀ c, p (K.y c) = pc P v c) ∧ ∀ x, (p x).Ok (A.res v) := by
  intro D u A i hi P K fMe hF hJ v
  obtain ⟨p, h1, h2, h3⟩ := pm_gen K.lev (A.eV v).1 (A.eV v).2 K.y K.y_bij.2 (pc P v)
    (GlobalTheory.T.classPair_moved_of_multipliesLocalFunctional D u A i hi P K fMe hF v) (GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel D u A i hi P K fMe hF hJ v)
  refine ⟨p, h1, h2, fun x => ?_⟩
  obtain ⟨c, γ, h⟩ := h3 x
  rw [h]
  exact (pc_ok P v c).act _

end GlobalTheory.LevelHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtremalUnitVectorSameHighestImageStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extremalUnitVector_same_highestImage : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Type) [AddCommGroup X] [Module ℂ X] (ε : Fin n → Bool) (lam μ : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π : Matrix (Fin n) (Fin n) ℂ → (X →ₗ[ℂ] X)) (L : Submodule ℂ H) (φ : H →ₗ[ℂ] X) (v : H), IsURepOn (UJset ε) σ → L ≤ lowKSub ε lam σ → IsKStableOn ε σ L → (∀ k ∈ Formalism.REAL.Kset ε, ∀ x ∈ L, φ (σ k x) = π k (φ x)) → v ∈ L → ‖v‖ = 1 → (∀ t : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) (φ v) = Complex.exp (((∑ a, μ a * t a : ℝ) : ℂ) * Complex.I) • φ v) → (∀ (ν : Fin n → ℝ) (y : X), y ∈ Submodule.span ℂ {z | ∃ k ∈ Formalism.REAL.Kset ε, z = π k (φ v)} → y ≠ 0 → (∀ t : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) y = Complex.exp (((∑ a, ν a * t a : ℝ) : ℂ) * Complex.I) • y) → ∑ a : Fin n, ν a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) ≤ ∑ a : Fin n, μ a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ))) → ∃ x ∈ L, ‖x‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) x ∧ φ x = φ v := by
  first | exact @GlobalTheory.ExtRep.exists_extremal_same_image | exact GlobalTheory.ExtRep.exists_extremal_same_image | (intros; apply GlobalTheory.ExtRep.exists_extremal_same_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harishChandraType_dualWeylModuleFockNorm : ∀ (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n), ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), Formalism.MainNotions.S.IsHCTypeU n (fun i => (lam.w i : ℝ) + ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ)) π ∧ Function.Injective e ∧ (∀ x, e x ∈ Formalism.BasicNotions.nablaSq ℂ n lam) ∧ ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ x, e (π (g : Matrix (Fin n) (Fin n) ℂ) x) = Formalism.BasicNotions.sqAct ℂ n lam g (e x) := by
  first | exact @GlobalTheory.NablaType.exists_isHCTypeU_nablaSq | exact GlobalTheory.NablaType.exists_isHCTypeU_nablaSq | (intros; apply GlobalTheory.NablaType.exists_isHCTypeU_nablaSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitaryStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_of_same_harishChandraParam_unitary : ∀ (k : ℕ) (u : Fin k → ℝ) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁)) (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), Formalism.MainNotions.S.IsHCTypeU k u π₁ → Formalism.MainNotions.S.IsHCTypeU k u π₂ → ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  first | exact @GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | exact GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | (intros; apply GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasureStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnitaryAdelicVolumeMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  first | exact @GlobalTheory.Mem.VolExists.exists_isVolMeasF | exact GlobalTheory.Mem.VolExists.exists_isVolMeasF | (intros; apply GlobalTheory.Mem.VolExists.exists_isVolMeasF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquareStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A)
    (v : ∀ e : ℕ, LB.Iso ((LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2)).pull (fstG I e P'.A).left)
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull ((β e).hom.left ≫ (fstG I e P.A).left))),
    (∀ e, (v e).IsGen) →
    (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) →
    (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
      (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z (fun _ => j) (fun _ => fun _ => j') =
        gw (v e) r z (fun _ => j) (fun _ => fun _ => j')) →
    ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso (LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2))
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen ∧
    ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
        (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
        gw w (r ≫ (fstG I e P'.A).left) z (fun _ => j) (fun _ => j') = gw (v e) r z (fun _ => j) (fun _ => fun _ => j') := by
  first | exact @GlobalTheory.exists_iso_of_compatible_thickenings_sq | exact GlobalTheory.exists_iso_of_compatible_thickenings_sq | (intros; apply GlobalTheory.exists_iso_of_compatible_thickenings_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabiliserSubgroupOutsidePlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_stabiliser_subgroup_outside_places : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ K : Subgroup (GA D V), (K : Set (GA D V)) = KsphC V S ∧ ∀ S', S ⊆ S' → KsphC V S' ⊆ KsphC V S := by
  first | exact @GlobalTheory.Mem.Ksph.exists_subgroup_ksph | exact GlobalTheory.Mem.Ksph.exists_subgroup_ksph | (intros; apply GlobalTheory.Mem.Ksph.exists_subgroup_ksph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMinorProductTranslateJointLowestWeightStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minorProduct_translate_jointLowestWeight : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), m ≤ n → (∀ τ, p τ + q τ = m) → (∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) → (∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) → (∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) → ∃ (κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (Δ' : PolF D m n), (∀ τ, κ τ ∈ Formalism.REAL.Kset (ε τ)) ∧ fact ε x₁ x₂ x₃ κ 1 Δ' = delta p q ap am ∧ IsBotFam ε (factK n ε x₁ x₂ x₃) (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) Δ' ∧ IsBotFam (fun _ => allPos n) (factU ε x₁ x₂ x₃) (fun τ j => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) Δ' := by
  first | exact @GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom | exact GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom | (intros; apply GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilOriented

theorem exists_extend {G M M' : Type} [Monoid G] [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (p : Submodule ℂ M) (E : M ≃ₗ[ℂ] M') (om : G →* Module.End ℂ p) :
    ∃ om' : G →* Module.End ℂ M', ∀ (g : G) (Φ : p), om' g (E Φ.1) = E (om g Φ).1 := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  let T : (p × q) ≃ₗ[ℂ] M' := (Submodule.prodEquivOfIsCompl p q hq).trans E
  have hT : ∀ Φ : p, T (Φ, 0) = E Φ.1 := fun Φ => by simp [T]
  refine ⟨{ toFun := fun g => T.toLinearMap ∘ₗ (LinearMap.prodMap (om g) LinearMap.id) ∘ₗ T.symm.toLinearMap
            map_one' := ?_
            map_mul' := fun a b => ?_ }, fun g Φ => ?_⟩
  · ext x
    simp
  · ext x
    simp
  · simp [← hT]

theorem lintegral_eq_of_integral_eq {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    {f f' : G → ℂ} (hf : Continuous f) (hf' : Continuous f') (hp : ∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖)
    (hp' : ∀ γ ∈ Γ, ∀ w, ‖f' (γ + w)‖ = ‖f' w‖) {μ : Measure G} {𝓕 : Set G} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h : ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖f' w‖ ^ 2 ∂μ) :
    ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f' w‖ₑ ^ 2 ∂μ := by
  have key := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov).2
  obtain ⟨N, hN⟩ := key f hf hp
  obtain ⟨N', hN'⟩ := key f' hf' hp'
  obtain ⟨h0, h1, h2, h3⟩ := hN μ 𝓕 hμ h𝓕
  obtain ⟨-, -, h2', h3'⟩ := hN' μ 𝓕 hμ h𝓕
  rw [h3, h3'] at h
  have : N = N' := NNReal.coe_injective (mul_left_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩) h)
  rw [h2, h2', this]

theorem norm_periodic {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) : ∀ γ ∈ ratL W V, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (hf.quasi γ w)
  rw [norm_mul, hψ.1.2.1, one_mul] at this
  exact this

theorem exists_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), admitted V W χ χ' → V.rank < W.rank → IsWeilOn ψ V W χ χ' om → ∃ omO : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ), IsWeilDatumO ψ V W χ χ' omO ∧ ∀ (p : GA D V × GA D W) (Φ : ThS ψ V W), omO p (fun x => Φ.1 (toTWsmall V W x)) = fun x => (om p Φ).1 (toTWsmall V W x) := by
  intro D ψ hψ V W χ χ' om ha hr hw
  obtain ⟨e, hc, hcs, he, hrat, hsm, hheis, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  let E : (WA V W → ℂ) ≃ₗ[ℂ] (WO V W → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.toEquiv
  obtain ⟨omO, hom⟩ := exists_extend (ThS ψ V W) E om
  have hom' : ∀ p (Φ : ThS ψ V W), omO p (fun x => Φ.1 (e x)) = fun x => (om p Φ).1 (e x) := hom
  have hsurj : ∀ f, IsThetaFunO ψ V W f → ∃ Φ : ThS ψ V W, f = fun x => Φ.1 (e x) := fun f hf => by
    have e1 : f = fun x => (fun y => f (e.symm y)) (e x) := by funext x; simp
    refine ⟨⟨fun y => f (e.symm y), mem_ThS.2 ((hth ψ _).1 ?_)⟩, e1⟩
    rw [← e1]; exact hf
  have hTh : ∀ Φ : ThS ψ V W, IsThetaFunO ψ V W fun x => Φ.1 (e x) := fun Φ => (hth ψ _).2 (mem_ThS.1 Φ.2)
  have hact : ∀ g h x, e (actO V W g h x) = actHom V W g h (e x) := fun g h x => by
    rw [he, he]; exact (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x
  refine ⟨omO, ⟨hψ, ha.2.1.1, ha.2.2.1.1, ha.2.2.2.1, ha.2.2.2.2, fun p f hf => ?_, fun g h w₀ f hf => ?_,
    fun γ hγ γ' hγ' f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_,
    fun ε hε g h hg hh x y hx hy => ?_⟩, fun p Φ => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']; exact hTh _
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    let Φ' : ThS ψ V W := ⟨Heisenberg₂ ψ V W (e w₀) Φ.1,
      mem_ThS.2 (GlobalTheory.Mem.ThetaClosed.isThetaFun_heis hψ (mem_ThS.1 Φ.2) _)⟩
    rw [hheis, hom', hheis, hact, ← hw.Heisenberg₂ g h (e w₀) Φ Φ' rfl]
    exact hom' _ Φ'
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    simp only [map_zero]
    exact hw.aut γ hγ γ' hγ' Φ
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    simp only [hom']
    exact hw.cont Φ (e w)
  · obtain ⟨Φ, rfl⟩ := hsurj f hf
    rw [hom']
    obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨j1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D V W
    have : BorelSpace (WA V W) := ⟨rfl⟩
    have : BorelSpace (WO V W) := ⟨rfl⟩
    obtain ⟨ν, hν, hF, hint⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WO V W) e.symm hcs
      (by simpa using hc) (ratL V W) (ratL W V) (fun x => by rw [← hrat, e.apply_symm_apply]) μ 𝓕 hμ h𝓕
    refine lintegral_eq_of_integral_eq (ratL W V) hK hcov (hTh _).cont (hTh _).cont (norm_periodic hψ (hTh _))
      (norm_periodic hψ (hTh _)) hμ h𝓕 ?_
    rw [← hint, ← hint]
    simp only [e.apply_symm_apply]
    exact hw.unit ν _ hν hF p Φ
  · obtain ⟨r, hr0, hℓ⟩ := hw.split ε hε g h hg hh x y hx hy
    refine ⟨r, hr0, fun ℓ hinv f hf => ?_⟩
    obtain ⟨Φ, rfl⟩ := hsurj f hf
    have := hℓ (ℓ ∘ₗ E.toLinearMap ∘ₗ (ThS ψ V W).subtype) (fun u hu Ψ Ψ' hΨ => ?_) Φ
    · rw [hom']
      unfold splitFac at this
      rw [if_pos hr.le] at this
      exact this
    · have hu' : cA D ε • e.symm u = e.symm u := by
        apply e.injective
        rw [hsm, e.apply_symm_apply]
        exact Matrix.ext hu
      have := hinv (e.symm u) (fun i j => congrFun (congrFun hu' i) j) _ (hTh Ψ)
      rw [hheis, e.apply_symm_apply, ← hΨ] at this
      exact this
  · simp only [← he]
    exact hom' p Φ

end GlobalTheory.Mem.WeilOriented
end

