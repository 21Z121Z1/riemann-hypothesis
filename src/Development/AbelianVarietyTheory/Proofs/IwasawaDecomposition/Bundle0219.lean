import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

theorem exists_haar_prod {G H I : Type} [Fintype I] {U : I → Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    [Group H] [TopologicalSpace H] [∀ i, Group (U i)] [∀ i, TopologicalSpace (U i)]
    [∀ i, IsTopologicalGroup (U i)] [∀ i, MeasurableSpace (U i)] [∀ i, BorelSpace (U i)]
    [∀ i, SecondCountableTopology (U i)] [∀ i, LocallyCompactSpace (U i)]
    (ν : ∀ i, Measure (U i)) [∀ i, (ν i).IsHaarMeasure] (e : G ≃ₜ* (∀ i, U i) × H) (K : Subgroup H)
    (hKo : IsOpen (K : Set H)) (hKc : IsCompact (K : Set H)) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ B : ∀ i, Set (U i), (∀ i, MeasurableSet (B i)) →
      μ {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = ∏ i, ν i (B i) := by
  let j : H →* G := (e.symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : Topology.IsEmbedding j :=
    e.symm.toHomeomorph.isEmbedding.comp (isEmbedding_prodMkRight (1 : ∀ i, U i))
  haveI : IsTopologicalGroup H := hj.isInducing.topologicalGroup j
  haveI : SecondCountableTopology H := hj.secondCountableTopology
  haveI : T2Space H := hj.t2Space
  haveI : LocallyCompactSpace H :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let K0 : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨K, hKc⟩, by
      show (interior (K : Set H)).Nonempty
      rw [hKo.interior_eq]; exact ⟨1, K.one_mem⟩⟩
  let m : Measure ((∀ i, U i) × H) := (Measure.pi ν).prod (Measure.haarMeasure K0)
  haveI : m.IsHaarMeasure := inferInstanceAs (((Measure.pi ν).prod (Measure.haarMeasure K0)).IsHaarMeasure)
  refine ⟨m.map e.symm, e.symm.isHaarMeasure_map m, fun B hB => ?_⟩
  have hme : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  rw [hme.map_apply]
  have : e.symm ⁻¹' {h | (e h).2 ∈ K ∧ ∀ i, (e h).1 i ∈ B i} = (Set.univ.pi B) ×ˢ (K : Set H) := by
    ext x
    simp [and_comm]
  rw [this, Measure.prod_prod, Measure.pi_pi]
  have h1 : Measure.haarMeasure K0 (K : Set H) = 1 := Measure.haarMeasure_self
  rw [h1, mul_one]

theorem mat_mul {P Q : ℕ} (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

theorem mat_one {P Q : ℕ} : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem exists_upq_mul {P Q M : ℕ} (A A' : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (B B' : Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ) (h1 : A * B = 1) (h2 : B * A = 1) (h3 : A' * B' = 1)
    (h4 : B' * A' = 1) (h : Aᴴ * Formalism.UG.Jpq P Q * A = A'ᴴ * Formalism.UG.Jpq P Q * A') :
    ∃ u : UpqT P Q, UpqT.mat u * A = A' := by
  let g : GL (Fin P ⊕ Fin Q) ℂ := ⟨A' * B, A * B',
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h2, Matrix.one_mul, h3],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc B', h4, Matrix.one_mul, h1]⟩
  have hg : g ∈ Formalism.UG.Upq P Q := by
    show (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Formalism.UG.Jpq P Q
    calc (A' * B)ᴴ * Formalism.UG.Jpq P Q * (A' * B) = Bᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * B := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (A * B)ᴴ * Formalism.UG.Jpq P Q * (A * B) := by
          rw [← h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq P Q := by rw [h1]; simp
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq P Q), ?_⟩
  show A' * B * A = A'
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem exists_isVolMeasF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E cm
  have hθ := GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E cm.sig hcm
  choose θ hθ1 hθ2 using fun i => hθ (τ i)
  have hA := fun i => GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hW (τ i))
  choose A hA1 using fun i => (hA i).2.1
  obtain ⟨e1, he1⟩ := GlobalTheory.T.unitaryGroup_realPoints_equiv_pi_indefiniteUnitary F E cm.sig W.rank W.gram I τ θ (fun ρ => (W.sig (τ ρ)).1)
    (fun ρ => (W.sig (τ ρ)).2) A hcm hτ hθ1 (fun i => hW (τ i)) hA1
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E cm.sig W.rank W.gram
  obtain ⟨L, hL, hLfg, hLsp⟩ := GlobalTheory.Mem.Vol.latC_full_lattice E W
  obtain ⟨K, hK, hKo, hKc⟩ := GlobalTheory.T.completedLattice_stabilizer_compact_open F E cm.sig W.rank W.gram L hLfg hLsp
  obtain ⟨-, hsc, ht2⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  have hinj := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective
  haveI := cd.haar
  let e : HA (AF F) cm.sig W.gram ≃ₜ*
      (∀ i, UpqT (W.sig (τ i)).1 (W.sig (τ i)).2) × HA (Af F) cm.sig W.gram :=
    e0.trans
      { e1.toMulEquiv.prodCongr (MulEquiv.refl _) with
        continuous_toFun := e1.continuous_toFun.prodMap continuous_id
        continuous_invFun := e1.continuous_invFun.prodMap continuous_id }
  have hee : ∀ h, e h = (e1 (e0 h).1, (e0 h).2) := fun h => rfl
  obtain ⟨μ, hμ, hμB⟩ := exists_haar_prod (fun i => cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2) e K hKo hKc
  refine ⟨μ, hμ, ⟨θ, hθ1⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ' = θ := funext fun i => hθ2 i _ (hθ' i)
  refine ⟨⟨A, hA1⟩, fun A' hA' B hB => ?_⟩
  have hu : ∀ i, ∃ u : UpqT (W.sig (τ i)).1 (W.sig (τ i)).2, UpqT.mat u * A i = A' i := by
    intro i
    obtain ⟨C, h1, h2⟩ := (hA i).2.2 _ (hA1 i)
    obtain ⟨C', h3, h4⟩ := (hA i).2.2 _ (hA' i)
    exact exists_upq_mul _ _ C C' h1 h2 h3 h4 ((hA1 i).trans (hA' i).symm)
  choose u hu using hu
  have key := hμB (fun i => (fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i))
    (fun i => measurable_const_mul _ (measurable_mul_const _ (hB i)))
  have hcj : ∀ i, cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2
      ((fun g => u i * g) ⁻¹' ((fun g => g * (u i)⁻¹) ⁻¹' B i)) =
      cd.cd (W.sig (τ i)).1 (W.sig (τ i)).2 (B i) := by
    intro i
    haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant _ _ _ (cd.haar (W.sig (τ i)).1 (W.sig (τ i)).2)
    rw [measure_preimage_mul, measure_preimage_mul_right]
  rw [Finset.prod_congr rfl (fun i _ => hcj i)] at key
  rw [← key]
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, hee, Set.mem_preimage]
  rw [hK, (he0 h).1, hL]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h1 : UpqT.mat (e1 (e0 h).1 i) * A i = A i * infMat cm.sig W.gram (θ' i) h := by
    rw [he1, (he0 h).2]; rfl
  have h2 : UpqT.mat (u i * e1 (e0 h).1 i * (u i)⁻¹) * A' i = A' i * infMat cm.sig W.gram (θ' i) h := by
    have h3 : UpqT.mat (u i)⁻¹ * A' i = A i := by
      rw [← hu i, ← Matrix.mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mul]
    rw [mat_mul, mat_mul, Matrix.mul_assoc, h3, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hu i]
  constructor
  · rintro ⟨b, hb, hbe⟩
    obtain ⟨C', h3, -⟩ := (hA i).2.2 _ (hA' i)
    have : b = u i * e1 (e0 h).1 i * (u i)⁻¹ := by
      apply hinj
      have h5 := congrArg (· * C') (hbe.trans h2.symm)
      simpa only [Matrix.mul_assoc, h3, Matrix.mul_one] using h5
    exact this ▸ hb
  · intro hb
    exact ⟨_, hb, h2⟩

end GlobalTheory.Mem.VolExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnSwap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilSwap

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck

variable {D : D7}

def trEquiv (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) : ThS ψ V W ≃ₗ[ℂ] ThS ψ W V where
  toFun Φ := ⟨fun y => Φ.1 y.transpose, mem_ThS.2 (isThetaFun_transpose ψ V W hne _ (mem_ThS.1 Φ.2))⟩
  invFun Φ := ⟨fun x => Φ.1 x.transpose, mem_ThS.2 (isThetaFun_transpose ψ W V hne.symm _ (mem_ThS.1 Φ.2))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem heis_transpose (ψ : AddChar (AF D.host.F) ℂ) {V W : HSp D} (hne : V.rank ≠ W.rank) (u : WA V W)
    (f : WA W V → ℂ) :
    (fun x : WA V W => Heisenberg₂ ψ W V u.transpose f x.transpose) = Heisenberg₂ ψ V W u (fun x => f x.transpose) := by
  funext x
  simp only [Heisenberg₂, symplH_transpose V W hne, Matrix.transpose_add]

def swapRep {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) : GA D W × GA D V →* Module.End ℂ (ThS ψ W V) :=
  ((trEquiv ψ hne).conjRingEquiv.toMonoidHom.comp om).comp (MulEquiv.prodComm (M := GA D W) (N := GA D V)).toMonoidHom

theorem swapRep_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (hne : V.rank ≠ W.rank)
    (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)) (h : GA D W) (g : GA D V) (Φ : ThS ψ W V) :
    swapRep hne om (h, g) Φ = trEquiv ψ hne (om (g, h) ((trEquiv ψ hne).symm Φ)) := rfl

theorem exists_isWeilOn_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (χ χ' : IdC D) (om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)), V.rank ≠ W.rank → IsWeilOn ψ V W χ χ' om → ∃ om' : GA D W × GA D V →* Module.End ℂ (ThS ψ W V), IsWeilOn ψ W V χ' χ om' ∧ ∀ (g : GA D V) (h : GA D W) (Φ : ThS ψ V W) (Φ' : ThS ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) → ∀ x : WA V W, (om' (h, g) Φ').1 x.transpose = (om (g, h) Φ).1 x := by
  intro D ψ _ V W χ χ' om hne H
  refine ⟨swapRep hne om, ⟨fun h g w₀ Φ Φ' e => ?_, fun γ hγ γ' hγ' Φ => ?_, fun Φ w => ?_,
    fun μ 𝓕 hμ h𝓕 p Φ => ?_, fun e he h g hh hg y x hy hx => ?_⟩, fun g h Φ Φ' e x => ?_⟩
  · have k := H.Heisenberg₂ g h w₀.transpose ((trEquiv ψ hne).symm Φ) ((trEquiv ψ hne).symm Φ') (by
      show (fun x : WA V W => Φ'.1 x.transpose) = _
      rw [e]
      exact heis_transpose ψ hne w₀.transpose Φ.1)
    rw [swapRep_apply, swapRep_apply]
    show (fun y : WA W V => (om (g, h) _).1 y.transpose) = _
    rw [k, actHom_swap W V hne.symm]
    exact heis_transpose ψ hne.symm _ _
  · exact H.aut γ' hγ' γ hγ ((trEquiv ψ hne).symm Φ)
  · exact (H.cont ((trEquiv ψ hne).symm Φ) w.transpose).comp continuous_swap
  · haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
    haveI : IsTopologicalAddGroup (WA W V) := Pi.topologicalAddGroup
    haveI : BorelSpace (WA V W) := ⟨rfl⟩
    haveI : BorelSpace (WA W V) := ⟨rfl⟩
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage (WA V W) (WA W V)
      (Matrix.transposeAddEquiv _ _ _) continuous_id.matrix_transpose continuous_id.matrix_transpose
      (ratL V W) (ratL W V) (fun x => ⟨fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩,
        fun ⟨γ, hγ⟩ => ⟨γ.transpose, congrArg Matrix.transpose hγ⟩⟩) μ 𝓕 hμ h𝓕
    rw [← h3 fun w => ‖(swapRep hne om p Φ).1 w‖ ^ 2, ← h3 fun w => ‖Φ.1 w‖ ^ 2]
    exact H.unit ν _ h1 h2 (p.2, p.1) ((trEquiv ψ hne).symm Φ)
  · obtain ⟨r, hr, k⟩ := H.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ Φ => ?_⟩
    rw [splitFac_swap V W hne]
    exact k (ℓ.comp (trEquiv ψ hne).toLinearMap) (fun u hu Ψ Ψ' e' =>
      hℓ u.transpose (fun i j => hu j i) (trEquiv ψ hne Ψ) (trEquiv ψ hne Ψ') (by
        show (fun y : WA W V => Ψ'.1 y.transpose) = _
        rw [e']
        exact heis_transpose ψ hne.symm u.transpose Ψ.1)) ((trEquiv ψ hne).symm Φ)
  · have : (trEquiv ψ hne).symm Φ' = Φ := Subtype.ext (funext e)
    rw [swapRep_apply, this]
    rfl

end GlobalTheory.Mem.WeilSwap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.ThetaClosed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck GlobalTheory.FockCompare

variable {D : D7}

theorem exists_open_ker {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (φ : G →+ AF D.host.F)
    (hφ : Continuous φ) :
    ∃ K : AddSubgroup G, IsOpen (K : Set G) ∧ ∀ w ∈ K, fstA D.host.F (φ w) = 0 → ψ (φ w) = 1 := by
  let q : G →+ AF D.host.F :=
    (AddMonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp ((AddMonoidHom.snd (Ainf D.host.F) (Af D.host.F)).comp φ)
  let K : AddSubgroup G :=
    { carrier := {w | ψ (q w) = 1}
      zero_mem' := by
        show ψ _ = 1
        rw [map_zero, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        have ha' : ψ _ = 1 := ha
        have hb' : ψ _ = 1 := hb
        show ψ _ = 1
        rw [map_add, AddChar.map_add_eq_mul, ha', hb', one_mul]
      neg_mem' := fun {a} ha => by
        have ha' : ψ _ = 1 := ha
        show ψ _ = 1
        have := AddChar.map_add_eq_mul ψ (q a) (q (-a))
        rw [← map_add, add_neg_cancel, map_zero, ψ.map_zero_eq_one, ha', one_mul] at this
        exact this.symm }
  refine ⟨K, K.isOpen_of_mem_nhds (g := 0) ?_, fun w hw h0 => ?_⟩
  · have h1 : Continuous fun w : G => (φ w).2 := continuous_snd.comp hφ
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA D.host.F 0 a) = 1})
      (by rw [map_zero]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  · have h4 : φ w = q w := Prod.ext h0 rfl
    rw [h4]
    exact hw

theorem isThetaFun_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {f : WA V W → ℂ}
    (hf : IsThetaFun ψ V W f) (u : WA V W) : IsThetaFun ψ V W (Heisenberg₂ ψ V W u f) := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  have hc : Continuous ψ := hψ.1.1
  let φ₁ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W w u) fun a b => symplH_add_left V W a b u
  let φ₂ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W u w) fun a b => symplH_add_right V W u a b
  have c₁ : Continuous φ₁ := ThetaCont.continuous_symplH V W continuous_id continuous_const
  have c₂ : Continuous φ₂ := ThetaCont.continuous_symplH V W continuous_const continuous_id
  refine ⟨heis_quasi ψ V W u f hf.quasi, ?_, (hc.comp c₁).mul (hf.cont.comp (continuous_id.add continuous_const)),
    fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K₁, hK₁, h₁⟩ := exists_open_ker hc hψ.1.2.1 φ₁ c₁
    obtain ⟨K₂, hK₂, h₂⟩ := exists_open_ker hc hψ.1.2.1 φ₂ c₂
    refine ⟨U ⊓ (K₁ ⊓ K₂), hU.inter (hK₁.inter hK₂), fun w hw hw' => ?_⟩
    have e₁ : ψ (symplH V W w u) = 1 := h₁ w hw.2.1 (by
      show fstA D.host.F (_ * sympl V W w u) = 0
      rw [map_mul, (sympl_parts D V W w u).2 (Or.inl hw'), mul_zero])
    have e₂ : ψ (symplH V W u w) = 1 := h₂ w hw.2.2 (by
      show fstA D.host.F (_ * sympl V W u w) = 0
      rw [map_mul, (sympl_parts D V W u w).2 (Or.inr hw'), mul_zero])
    conv_rhs => rw [← hUf w hw.1 hw']
    rw [heis_heis, heis_heis, e₁, e₂, add_comm]
  · obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
    let χ : (Fin k → ℝ) →+ ℂ := lam.comp (φ₁.comp L)
    have hχ : ContDiff ℝ ∞ χ := GlobalTheory.WeilVacMove.contDiff_additive χ (hl.comp (c₁.comp hL))
    have : (fun t => Heisenberg₂ ψ V W u f (w + L t)) =
        fun t => ψ (symplH V W w u) * Complex.exp (χ t) * f (w + u + L t) := by
      funext t
      have e : ψ (symplH V W (L t) u) = Complex.exp (χ t) := hlam _ (by
        show sndA D.host.F (_ * sympl V W (L t) u) = 0
        rw [map_mul, (sympl_parts D V W (L t) u).1 (Or.inl (hLf t)), mul_zero])
      rw [Heisenberg₂, symplH_add_left, AddChar.map_add_eq_mul, e, add_right_comm]
    rw [this]
    exact (contDiff_const.mul hχ.cexp).mul (hf.smooth k L hL hLf (w + u))

theorem thetaFun_closed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (f : WA V W → ℂ), (f ∈ ThS ψ V W ↔ IsThetaFun ψ V W f) ∧ (IsThetaFun ψ V W f → ∀ w₀, IsThetaFun ψ V W (Heisenberg₂ ψ V W w₀ f)) ∧ (V.rank ≠ W.rank → IsThetaFun ψ V W f → IsThetaFun ψ W V (fun x => f x.transpose)) := by
  intro D ψ hψ V W f
  refine ⟨⟨fun h => ?_, fun h => Submodule.subset_span h⟩, fun hf u => isThetaFun_heis hψ hf u,
    fun hne hf => isThetaFun_transpose ψ V W hne f hf⟩
  obtain ⟨M, hM⟩ := exists_thetaSubmodule D ψ V W
  exact (hM f).1 (Submodule.span_le.2 (fun g hg => (hM g).2 hg) h)

end GlobalTheory.Mem.ThetaClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqUnitOfContinuousComplexRoot
section
open Polynomial

namespace GlobalTheory.ContRoot

open GlobalTheory.AffinePoints

theorem nonempty_algHom (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem exists_monic_prime_dvd (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    {n : ℕ} (hn : 0 < n) (u : B) :
    ∃ P : B[X], P.Monic ∧ Prime P ∧ 0 < P.natDegree ∧ P ∣ X ^ n - C u := by
  let L := AlgebraicClosure (FractionRing B)
  have hinj : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B (FractionRing B) L]
    exact (algebraMap (FractionRing B) L).injective.comp (IsFractionRing.injective B _)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).2 hinj
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B L u) hn
  have h0 : aeval β (X ^ n - C u : B[X]) = 0 := by simp [hβ]
  have hint : IsIntegral B β := ⟨_, monic_X_pow_sub_C u hn.ne', h0⟩
  exact ⟨minpoly B β, minpoly.monic hint, minpoly.prime_of_isIntegrallyClosed hint,
    minpoly.natDegree_pos hint, minpoly.isIntegrallyClosed_dvd hint h0⟩

theorem exists_pow_eq_of_continuous_root : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (n : ℕ) (u : Bˣ) (ρ : (B →ₐ[ℂ] ℂ) → ℂ), 0 < n → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen V → (∀ a : B, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V) → (∀ ψ : B →ₐ[ℂ] ℂ, ρ ψ ^ n = ψ (u : B)) → ∃ b : B, b ^ n = u := by
  intro B _ _ _ _ n u ρ hn hc hρ
  have hρc : Continuous ρ := GlobalTheory.RootConst.continuous_of_holomorphic_families B ρ hc
  have := GlobalTheory.isIntegrallyClosed_of_smooth ℂ B
  obtain ⟨P, hm, hp, hd, hdvd⟩ := exists_monic_prime_dvd B hn (u : B)
  have hdom : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hp
  have hft : Algebra.FiniteType ℂ (AdjoinRoot P) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have hconn := GlobalTheory.RootConst.preconnectedSpace_algHom (AdjoinRoot P)
  let φ : B →ₐ[ℂ] AdjoinRoot P := IsScalarTower.toAlgHom ℂ B (AdjoinRoot P)
  have hroot : AdjoinRoot.root P ^ n = φ u := by
    have h := (AdjoinRoot.mk_eq_zero (f := P)).2 hdvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h
  have hu : ∀ ψ : B →ₐ[ℂ] ℂ, ψ u ≠ 0 := fun ψ => (u.isUnit.map ψ).ne_zero
  have hρ0 : ∀ ψ, ρ ψ ≠ 0 := fun ψ h => hu ψ (by rw [← hρ, h, zero_pow hn.ne'])
  have hcont : Continuous fun χ : AdjoinRoot P →ₐ[ℂ] ℂ =>
      χ (AdjoinRoot.root P) / ρ (comap φ χ) :=
    (continuous_eval _).div (hρc.comp (continuous_comap φ)) fun _ => hρ0 _
  have hconst := GlobalTheory.RootConst.eq_of_pow_eq_one hcont hn fun χ => by
    rw [div_pow, ← map_pow, hroot, hρ, comap_apply]
    exact div_self (hu (comap φ χ))
  obtain ⟨ψ⟩ := nonempty_algHom B
  have key : ∀ z, (P.map (ψ : B →+* ℂ)).IsRoot z → ∃ χ : AdjoinRoot P →ₐ[ℂ] ℂ,
      comap φ χ = ψ ∧ χ (AdjoinRoot.root P) = z := by
    intro z hz
    have hz' : P.eval₂ (ψ : B →+* ℂ) z = 0 := by rw [← eval_map]; exact hz
    refine ⟨AdjoinRoot.liftAlgHom P ψ z hz', ?_, by simp⟩
    ext b
    simp [φ]
  have huniq : ∀ z w, (P.map (ψ : B →+* ℂ)).IsRoot z → (P.map (ψ : B →+* ℂ)).IsRoot w →
      z = w := by
    intro z w hz hw
    obtain ⟨χ, h1, h2⟩ := key z hz
    obtain ⟨χ', h1', h2'⟩ := key w hw
    have h := hconst χ χ'
    simp only [h1, h1', h2, h2'] at h
    exact (div_left_inj' (hρ0 ψ)).1 h
  have hsep : (P.map (ψ : B →+* ℂ)).Separable := by
    refine (separable_X_pow_sub_C (n := n) (ψ u) (Nat.cast_ne_zero.2 hn.ne') (hu ψ)).of_dvd ?_
    simpa using Polynomial.map_dvd (ψ : B →+* ℂ) hdvd
  have hne : P.map (ψ : B →+* ℂ) ≠ 0 := (hm.map _).ne_zero
  have hdeg : P.natDegree ≤ 1 := by
    rw [← hm.natDegree_map (ψ : B →+* ℂ),
      (IsAlgClosed.splits (P.map (ψ : B →+* ℂ))).natDegree_eq_card_roots,
      ← Multiset.toFinset_card_of_nodup (nodup_roots hsep)]
    refine Finset.card_le_one.2 fun a ha b hb => huniq a b ?_ ?_
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 ha)
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 hb)
  have h1 : P = X + C (P.coeff 0) := hm.eq_X_add_C (le_antisymm hdeg hd)
  refine ⟨-P.coeff 0, ?_⟩
  have h2 : P.eval (-P.coeff 0) = 0 := by
    rw [congrArg (eval (-P.coeff 0)) h1]; simp
  have h3 := eval_eq_zero_of_dvd_of_eval_eq_zero hdvd h2
  simpa [sub_eq_zero] using h3

end GlobalTheory.ContRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRepEqBlocks
section
open MeasureTheory Topology

noncomputable section

namespace GlobalTheory.SphCyclic

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix ValuativeRel

def eqBlocks (j t : ℕ) : (Σ _ : Fin j, Fin t) ≃ Fin (j * t) :=
  (Equiv.sigmaEquivProd (Fin j) (Fin t)).trans finProdFinEquiv

theorem val_eqBlocks {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) = s + t * a := rfl

theorem eqBlocks_div {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) / t = a := by
  rw [val_eqBlocks, Nat.add_mul_div_left _ _ s.pos, Nat.div_eq_of_lt s.2, zero_add]

theorem eqBlocks_mod {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) % t = s := by
  rw [val_eqBlocks, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.2]

theorem modExp_eqBlocks {j t : ℕ} (a : Fin j) :
    modExp (fun _ : Fin j => Fin t) a = (j * t : ℤ) - t - 2 * (a : ℕ) * t := by
  have h1 : (Finset.univ.filter fun b => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b => b < a) = Finset.Iio a := by ext; simp
  rw [modExp, h1, h2, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, Fintype.card_fin,
    nsmul_eq_mul, nsmul_eq_mul]
  have := a.2
  rw [show ((j - 1 - a : ℕ) : ℤ) = j - 1 - (a : ℕ) by omega]
  ring

theorem mem_parab_eqBlocks {R : Type} [CommRing R] {j t : ℕ} {b : GL (Fin (j * t)) R}
    (hb : ∀ x y, y < x → b.val x y = 0) : b ∈ parab R (eqBlocks j t) := by
  refine mem_parab_iff.2 fun a a' s s' h => hb _ _ ?_
  rw [Fin.lt_def, val_eqBlocks, val_eqBlocks]
  have h1 : t * (a' + 1) ≤ t * a := Nat.mul_le_mul_left _ h
  have := s'.2
  rw [mul_add, mul_one] at h1
  omega

theorem det_block {R : Type} [CommRing R] {j t : ℕ} {b : GL (Fin (j * t)) R}
    (hb : ∀ x y, y < x → b.val x y = 0) (u : Fin (j * t) → Rˣ) (hu : ∀ x, (u x : R) = b.val x x) (a : Fin j) :
    GeneralLinearGroup.det (leviProj R (eqBlocks j t) ⟨b, mem_parab_eqBlocks hb⟩ a) =
      ∏ s, u (eqBlocks j t ⟨a, s⟩) := by
  ext
  rw [GeneralLinearGroup.val_det_apply, det_of_upperTriangular, Units.coe_prod]
  · exact Finset.prod_congr rfl fun s _ => (hu _).symm
  · intro s s' h
    refine hb _ _ ?_
    rw [Fin.lt_def, val_eqBlocks, val_eqBlocks]
    exact Nat.add_lt_add_right h _

theorem exists_rep_eqBlocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (j t : ℕ) [MeasurableSpace (GL (Fin (j * t)) k)]
    [BorelSpace (GL (Fin (j * t)) k)] (ν : ℕ → kˣ →* ℂˣ) (hu : ∀ a x, ‖(ν a x : ℂ)‖ = 1) (hν : ∀ a, IsUnram (ν a))
    (H : Type) [Group H] [TopologicalSpace H] :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
      (ρ : H × GL (Fin (j * t)) k →* (V ≃ₗᵢ[ℂ] V)),
      (∀ x, IsOpen {g | ρ g x = x}) ∧
      (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∃ v : V, ‖v‖ = 1 ∧ (∀ h, ∀ x ∈ KO k (Fin (j * t)), ρ (h, x) v = v) ∧
        ∃ (φ : GL (Fin (j * t)) k → ℂ) (κ : Measure (GL (Fin (j * t)) k)),
          (∀ (b : GL (Fin (j * t)) k) (u : Fin (j * t) → kˣ), (∀ x y, y < x → b.val x y = 0) →
            (∀ x, (u x : k) = b.val x x) → ∀ g, φ (b * g) = (∏ x : Fin (j * t), (ν (x / t) (u x) : ℂ) *
              (nabs k (u x) ^ ((((j * t : ℕ) : ℝ) - t) / 2 - ((x / t : ℕ) : ℝ) * t) : ℝ)) * φ g) ∧
          (∀ x, ∀ y ∈ KO k (Fin (j * t)), φ (x * y) = φ x) ∧ φ 1 = 1 ∧ κ.IsHaarMeasure ∧
          κ (KO k (Fin (j * t))) = 1 ∧
          ∀ g, inner ℂ v (ρ (1, g) v) = ∫ x in (KO k (Fin (j * t)) : Set (GL (Fin (j * t)) k)), φ (x * g) ∂κ := by
  obtain ⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6⟩ :=
    exists_rep_blocks k (eqBlocks j t) (fun a => ν a) (fun a => hu a) (fun a => hν a) H
  refine ⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, h4, φ, κ, fun b u hb hbu g => ?_, h6⟩
  rw [h5 ⟨b, mem_parab_eqBlocks hb⟩ g, ← val_deltaHalf, deltaHalf_apply, Units.coe_prod, ← Finset.prod_mul_distrib,
    ← (eqBlocks j t).prod_comp, Fintype.prod_sigma]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [det_block hb u hbu, map_prod, map_prod, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [eqBlocks_div, mul_comm, ← val_absPow_ofReal, modExp_eqBlocks]
  congr 3
  push_cast
  ring

end GlobalTheory.SphCyclic
end
end

