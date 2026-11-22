import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0540
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0532
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeStabilizerTwistAndLevelAway
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.CellLevels

variable {D : D7}

private theorem congGrp_mono' (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := by
  intro g hg
  unfold congGrp at hg ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg ⊢
  rw [← Ideal.Quotient.factor_comp_mk h, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hg, map_one]

private theorem idAt_mono_decorated_lattice {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : idAt D P ≤ idAt D P' := by
  intro x hx
  unfold idAt at hx ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx ⊢
  exact ⟨hx.1, fun w => hx.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

theorem grpAt_le_of_imp (V : HSp D) {P P' : Pl D → Prop} (h : ∀ v, P v → P' v) : grpAt V P ≤ grpAt V P' := by
  unfold grpAt
  exact congGrp_mono' V (idAt_mono_decorated_lattice h)

def commProd {G : Type*} [Group G] (A B : Subgroup G) (h : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b) : Subgroup G where
  carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    rw [mul_assoc, ← mul_assoc b, h b hb a' ha']; simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by rw [_root_.mul_inv_rev, h _ (B.inv_mem hb) _ (A.inv_mem ha)]⟩

private theorem idAt_inf_le_idAt_and (P P' : Pl D → Prop) : idAt D P ⊓ idAt D P' ≤ idAt D (fun p => P p ∧ P' p) := by
  intro x hxx
  have hx := (Ideal.mem_inf.1 hxx).1
  have hx' := (Ideal.mem_inf.1 hxx).2
  unfold idAt at hx hx' ⊢
  rw [Ideal.mem_inf, Submodule.mem_iInf] at hx hx' ⊢
  refine ⟨hx.1, fun w => ?_⟩
  by_cases hp : P w.1
  · exact hx'.2 ⟨w.1, fun h' => w.2 ⟨hp, h'⟩⟩
  · exact hx.2 ⟨w.1, hp⟩

private theorem congGrp_inf_le_congGrp_inf (V : HSp D) (I J : Ideal (AE D)) : congGrp V I ⊓ congGrp V J ≤ congGrp V (I ⊓ J) := by
  intro g hg
  have hI := (Subgroup.mem_inf.1 hg).1
  have hJ := (Subgroup.mem_inf.1 hg).2
  unfold congGrp at hI hJ ⊢
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hI hJ ⊢
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have eI := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hI i j
  have eJ := (Matrix.GeneralLinearGroup.ext_iff _ _).1 hJ i j
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply] at eI eJ ⊢
  split_ifs at eI eJ ⊢ with hij
  · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem] at eI eJ ⊢
    exact Ideal.mem_inf.2 ⟨eI, eJ⟩

private theorem mem_grpAt_and_of_mem_grpAt (V : HSp D) {P P' : Pl D → Prop} {g : GA D V} (h : g ∈ grpAt V P) (h' : g ∈ grpAt V P') :
    g ∈ grpAt V (fun p => P p ∧ P' p) := by
  unfold grpAt at h h' ⊢
  exact congGrp_mono' V (idAt_inf_le_idAt_and P P') (congGrp_inf_le_congGrp_inf V _ _ ⟨h, h'⟩)

private theorem inK_congr_of_iff {V : HSp D} {L : Lat V} {P P' : Pl D → Prop} (h : ∀ p, P p ↔ P' p) (κ : GA D V) :
    InK V L P κ ↔ InK V L P' κ := by
  rw [show P = P' from funext fun p => propext (h p)]

private theorem mem_grpAt_of_inK {V : HSp D} {L : Lat V} {P : Pl D → Prop} {κ : GA D V} (h : InK V L P κ) : κ ∈ grpAt V P := by
  unfold InK at h
  exact h.1

theorem levels : ∀ (D : D7) (V : HSp D) (L : Lat V) (gP Q : Finset (Pl D)) (JG : Subgroup (GA D V)), IsSelfDualC V L → Disjoint Q gP → JG ≤ grpAt V (· ∈ gP) → IsCompact (JG : Set (GA D V)) → IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) → ∃ K₁ K₂ : Subgroup (GA D V), (∀ g, g ∈ K₁ ↔ InK V L (· ∈ Q) g) ∧ K₁ ≤ grpAt V (· ∈ Q) ∧ K₂ ≤ grpAt V (· ∉ Q) ∧ IsCompact (K₁ : Set (GA D V)) ∧ IsCompact (K₂ : Set (GA D V)) ∧ IsOpen ((K₁.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) ∧ IsOpen ((K₂.subgroupOf (grpAt V (· ∉ Q)) : Subgroup _) : Set (grpAt V (· ∉ Q))) ∧ (∀ g, g ∈ K₂ ↔ ∃ κ, InK V L (fun p => p ∉ gP ∧ p ∉ Q) κ ∧ ∃ k ∈ JG, g = κ * k) ∧ ∀ g, (∃ a ∈ K₁, ∃ b ∈ K₂, g = a * b) ↔ ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g = κ * k := by
  intro D V L gP Q JG hL hdisj hJle hJc hJo
  obtain ⟨-, -, -, hQcle, -, -, -, -, hKQ, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q
  obtain ⟨-, -, -, -, hPcomm, ⟨e, he⟩, -, -, -, -⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V gP
  have hQP : ∀ p, p ∈ Q → p ∉ gP := fun p hp => Finset.disjoint_left.mp hdisj hp

  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hKQ L hL (· ∈ Q)

  obtain ⟨⟨K₃, hK₃, hK₃c, hK₃o⟩, -⟩ := hKQ L hL (fun p => p ∉ gP ∧ p ∉ Q)
  have hpq : ∀ p, (p ∉ gP ∧ p ∈ Q) ↔ p ∈ Q := fun p => ⟨And.right, fun h => ⟨hQP p h, h⟩⟩

  have hsplit : ∀ κ, InK V L (· ∉ gP) κ ↔
      ∃ a b, InK V L (· ∈ Q) a ∧ InK V L (fun p => p ∉ gP ∧ p ∉ Q) b ∧ κ = a * b := by
    intro κ
    refine ((hKQ L hL (· ∉ gP)).2 κ).trans ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).1 ha, hb, rfl⟩
    · rintro ⟨a, b, ha, hb, rfl⟩
      exact ⟨a, b, (inK_congr_of_iff (P := fun p => p ∉ gP ∧ p ∈ Q) (P' := (· ∈ Q)) hpq a).2 ha, hb, rfl⟩
  have hK₁le : K₁ ≤ grpAt V (· ∈ Q) := fun g hg => mem_grpAt_of_inK ((hK₁ g).1 hg)
  have hK₃le : K₃ ≤ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := fun g hg => mem_grpAt_of_inK ((hK₃ g).1 hg)
  have hJQ : grpAt V (· ∈ gP) ≤ grpAt V (· ∉ Q) := grpAt_le_of_imp V fun p hp hq => hQP p hq hp

  have hc : ∀ b ∈ JG, ∀ a ∈ K₃, b * a = a * b := fun b hb a ha =>
    hPcomm b (hJle hb) a (grpAt_le_of_imp V (fun p hp => hp.1) (hK₃le ha))
  have hmem : ∀ g, g ∈ commProd K₃ JG hc ↔ ∃ a ∈ K₃, ∃ b ∈ JG, g = a * b := fun g => Iff.rfl
  refine ⟨K₁, commProd K₃ JG hc, hK₁, hK₁le, ?_, hK₁c, ?_, hK₁o, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (hmem g).1 hg
    exact mul_mem (grpAt_le_of_imp V (fun p hp => hp.2) (hK₃le ha)) (hJQ (hJle hb))
  · have hset : (commProd K₃ JG hc : Set (GA D V)) =
        (fun p : GA D V × GA D V => p.1 * p.2) '' ((K₃ : Set (GA D V)) ×ˢ (JG : Set (GA D V))) := by
      ext g
      rw [SetLike.mem_coe, hmem, Set.mem_image]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [hset]
    exact (hK₃c.prod hJc).image continuous_mul
  ·
    obtain ⟨φ, hφc, hφ, hφ1⟩ : ∃ φ : grpAt V (· ∉ Q) → grpAt V (· ∈ gP) × grpAt V (· ∉ gP),
        Continuous φ ∧ (∀ g : grpAt V (· ∉ Q), (g : GA D V) = ((φ g).1 : GA D V) * (φ g).2) ∧ φ 1 = 1 := by
      refine ⟨fun g => e.symm ⟨g, hQcle g.2⟩, ?_, ?_, ?_⟩
      · exact e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
      · intro g
        rw [← he, Homeomorph.apply_symm_apply]
      · rw [Homeomorph.symm_apply_eq]
        apply Subtype.ext
        rw [he]
        simp

    have h3 : ∀ g : grpAt V (· ∉ Q), ((φ g).2 : GA D V) ∈ grpAt V (fun p => p ∉ gP ∧ p ∉ Q) := by
      intro g
      have e2 : ((φ g).2 : GA D V) = ((φ g).1 : GA D V)⁻¹ * g := by
        rw [hφ g, inv_mul_cancel_left]
      refine mem_grpAt_and_of_mem_grpAt V (φ g).2.2 ?_
      rw [e2]
      exact mul_mem (inv_mem (hJQ (φ g).1.2)) g.2
    obtain ⟨ψ, hψc, hψ⟩ : ∃ ψ : grpAt V (· ∉ Q) → grpAt V (fun p => p ∉ gP ∧ p ∉ Q),
        Continuous ψ ∧ ∀ g : grpAt V (· ∉ Q), (ψ g : GA D V) = (φ g).2 :=
      ⟨fun g => ⟨(φ g).2, h3 g⟩, (continuous_subtype_val.comp (continuous_snd.comp hφc)).subtype_mk _, fun _ => rfl⟩
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    have hU : ψ ⁻¹' ((K₃.subgroupOf (grpAt V (fun p => p ∉ gP ∧ p ∉ Q)) : Subgroup _) :
        Set (grpAt V (fun p => p ∉ gP ∧ p ∉ Q))) ∩
        (fun g => (φ g).1) ⁻¹' ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) ∈
        nhds (1 : grpAt V (· ∉ Q)) := by
      refine IsOpen.mem_nhds ((hK₃o.preimage hψc).inter (hJo.preimage (continuous_fst.comp hφc))) ⟨?_, ?_⟩
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ, hφ1]
        exact K₃.one_mem
      · rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hφ1]
        exact JG.one_mem
    refine Filter.mem_of_superset hU ?_
    rintro g ⟨h1, h2⟩
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, hψ] at h1
    rw [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf] at h2
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmem]
    refine ⟨(φ g).2, h1, (φ g).1, h2, ?_⟩
    rw [hφ g]
    exact hPcomm _ (φ g).1.2 _ (φ g).2.2
  · intro g
    rw [hmem]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, (hK₃ a).1 ha, b, hb, rfl⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      exact ⟨κ, (hK₃ κ).2 hκ, k, hk, rfl⟩
  · intro g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨κ, hκ, k, hk, rfl⟩ := (hmem b).1 hb
      exact ⟨a * κ, (hsplit _).2 ⟨a, κ, (hK₁ a).1 ha, (hK₃ κ).1 hκ, rfl⟩, k, hk, (mul_assoc a κ k).symm⟩
    · rintro ⟨κ, hκ, k, hk, rfl⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := (hsplit κ).1 hκ
      exact ⟨a, (hK₁ a).2 ha, b * k, (hmem _).2 ⟨b, (hK₃ b).2 hb, k, hk, rfl⟩, mul_assoc a b k⟩

end GlobalTheory.CellLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTwistRationalLevelElementsSameCharactersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistRational_levelElements_same_characters : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  first | exact @GlobalTheory.AdForm.RatApprox.approx | exact GlobalTheory.AdForm.RatApprox.approx | (intros; apply GlobalTheory.AdForm.RatApprox.approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitMultipliersLineInMovedLatticeSplit
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineIdeal

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem exists_dominant {k : ℕ} (f : Fin k → Fv F v) (hf : ∃ j, f j ≠ 0) :
    ∃ j, f j ≠ 0 ∧ ∀ c : Fv F v,
      (∀ i, c * f i ∈ v.adicCompletionIntegers F) ↔ c * f j ∈ v.adicCompletionIntegers F := by
  obtain ⟨j0, hj0⟩ := hf
  haveI : Nonempty (Fin k) := ⟨j0⟩
  obtain ⟨j, hj⟩ := Finite.exists_max fun i => ‖f i‖₊
  refine ⟨j, fun h0 => hj0 ?_, fun c => ⟨fun h => h j, fun h i => ?_⟩⟩
  · have := hj j0
    rw [h0, nnnorm_zero] at this
    exact nnnorm_eq_zero.1 (le_antisymm this zero_le)
  · rw [← nnnorm_le_one_iff_mem] at h ⊢
    rw [nnnorm_mul] at h ⊢
    exact (mul_le_mul_of_nonneg_left (hj i) zero_le).trans h

theorem exists_unit_gen (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {k : ℕ} {u l : Fin k → Fv F v ⊗[F] E}
    (hl : ∑ j, l j * u j = 1) :
    ∃ α : (Fv F v ⊗[F] E)ˣ, ∀ c : Fv F v ⊗[F] E,
      (∀ j, c * u j ∈ intLoc F E v) ↔ ((α⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * c ∈ intLoc F E v := by
  have hne : ∀ ρ : E →ₐ[F] Fv F v, ∃ j, splitProj ρ (u j) ≠ 0 := fun ρ => by
    by_contra hc
    push_neg at hc
    have := congrArg (splitProj ρ) hl
    rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by rw [map_mul, hc j, mul_zero]] at this
    exact zero_ne_one this
  obtain ⟨j1, h1, hj1⟩ := exists_dominant (fun j => splitProj τ (u j)) (hne τ)
  obtain ⟨j2, h2, hj2⟩ := exists_dominant (fun j => splitProj (τ.comp σ) (u j)) (hne _)
  beta_reduce at h1 h2 hj1 hj2
  refine ⟨⟨(splitAlgEquiv h τ).symm ((splitProj τ (u j1))⁻¹, (splitProj (τ.comp σ) (u j2))⁻¹),
    (splitAlgEquiv h τ).symm (splitProj τ (u j1), splitProj (τ.comp σ) (u j2)), ?_, ?_⟩, fun c => ?_⟩
  · rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]
    exact map_one _
  · rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]
    exact map_one _
  · show _ ↔ (splitAlgEquiv h τ).symm (splitProj τ (u j1), splitProj (τ.comp σ) (u j2)) * c ∈ intLoc F E v
    simp only [mem_intLoc_iff_split h τ, map_mul, splitProj_symm, splitProj_comp_symm, forall_and]
    rw [hj1 (splitProj τ c), hj2 (splitProj (τ.comp σ) c), mul_comm (splitProj τ c),
      mul_comm (splitProj (τ.comp σ) c)]

end Local

set_option maxHeartbeats 1600000 in

theorem exists_unit_mult_latLoc : ∀ (D : D7) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), Nonempty (D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) → ∀ (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Submodule.IsLattice D.host.E L → ∀ (g : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) (ε : Fin n → D.host.E), ε ≠ 0 → ∃ α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec g.val (c • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D v hτ n L hL g ε hε
  obtain ⟨τ⟩ := hτ
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := D.host.F) (Fv D.host.F v) h1
  let w : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E := g.val *ᵥ fun i => (1 : Fv D.host.F v) ⊗ₜ[D.host.F] ε i
  obtain ⟨l, hl⟩ : ∃ l : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    refine ⟨Pi.single i ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (ε i)⁻¹) ᵥ* (g⁻¹ : GL (Fin n) _).val, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ (by simpa using hi)]
    rfl
  let u := Φ.map (inclR (F := D.host.F) (Fv D.host.F v)) *ᵥ w
  have hl' : ∑ j, (l ᵥ* S.map (inclR (F := D.host.F) (Fv D.host.F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, hl]
  have key : ∀ a : Fv D.host.F v ⊗[D.host.F] D.host.E,
      a • w ∈ latLoc D.host.F L v ↔ ∀ j, a * u j ∈ intLoc D.host.F D.host.E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  obtain ⟨α, hα⟩ := exists_unit_gen (isCMExt_host D) τ hl'
  refine ⟨α, fun c => ?_⟩
  have hcw : g.val *ᵥ (c • fun i => (1 : Fv D.host.F v) ⊗ₜ[D.host.F] ε i) = c • w := Matrix.mulVec_smul _ _ _
  rw [hcw, key, hα]

end GlobalTheory.LineIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProofStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionByZeroAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.ExtAll D := by
  first | exact @GlobalTheory.FinPl.ExtAllPf.ext_all | exact GlobalTheory.FinPl.ExtAllPf.ext_all | (intros; apply GlobalTheory.FinPl.ExtAllPf.ext_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyRowsColumnsValidStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_rows_columns_valid : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → f.c.Is ∧ (f.ColOK → ∀ t, (f.t t).Is) := by
  first | exact @GlobalTheory.Fam.IsFam.main | exact GlobalTheory.Fam.IsFam.main | (intros; apply GlobalTheory.Fam.IsFam.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMatrixEntryIntegralOfKeepsStandardLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteMatrix_entry_integral_of_keeps_standardLattice : ∀ (D : D7) (S : HSp D) {n : ℕ} (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S), (∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → ∀ κ : GA D S, GlobalTheory.FinPl.Moves S κ L L (fun _ => True) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (r s : Fin n), Formalism.UG.prV (E := D.host.E) v (GlobalTheory.AdForm.finM S hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E v := by
  first | exact @GlobalTheory.FinPl.MovesEntries.finM_entry_int | exact GlobalTheory.FinPl.MovesEntries.finM_entry_int | (intros; apply GlobalTheory.FinPl.MovesEntries.finM_entry_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorSchrodingerModelIsKFiniteStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_schrodingerModel_isKFinite : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → FiniteDimensional ℂ (Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}) := by
  first | exact @GlobalTheory.StdUnn.KFin.fock_kfinite | exact GlobalTheory.StdUnn.KFin.fock_kfinite | (intros; apply GlobalTheory.StdUnn.KFin.fock_kfinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameColumnsUnitScaling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimSplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_sec_mul' (p : SplitPt D k) (a : AE D) (t : k) :
    cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, cA_cA]

theorem colMul_split (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) {a : AE D}
    (ha : a ∈ idAt D (· = q.v)) :
    colMul d.jX i a = (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * q.pr (cA D (incA D (d.e r i)))))) := by
  funext r
  change a * incA D (d.e r i) = _
  conv_lhs => rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q ha]
  rw [add_mul, sec_mul_right, cA_sec_mul' q, Pi.add_apply]

theorem mul_unit_mem_iff {b u : k} (hu : valuation k u = 1) : b * u ∈ 𝒪[k] ↔ b ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]

theorem colMul_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (i : Fin ρ) (y₁ y₂ : Y) (u₁ u₂ : k), IsSelfDualC S L → IntIn q S F L → valuation k u₁ = 1 → valuation k u₂ = 1 → (∀ r, F.β r y₁ = u₁ * q.pr (incA D (d.e r i))) → (∀ l, ∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (d.e t i))) = if l = y₂ then u₂ else 0) → ∀ a : AE D, (GlobalTheory.FinPl.colMul d.jX i a ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S S₀ ρ d L Y _ _ F i y₁ y₂ u₁ u₂ hL hF hu₁ hu₂ hcol₁ hcol₂ a
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hu₁
    exact zero_ne_one hu₁
  have hu₂i : u₂ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hu₂.le
  have key : ∀ a ∈ idAt D (· = q.v), (colMul d.jX i a ∈ latV S L (· = q.v) ↔
      q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
    intro a ha
    rw [colMul_split q d i ha, decomp hL]
    refine and_congr ?_ ?_
    · have h1 : (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) =
          fun r => q.sec ((F.β *ᵥ Pi.single y₁ (q.pr a * u₁⁻¹)) r) := by
        funext r
        congr 1
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol₁]
        field_simp
      rw [h1, ← hF]
      constructor
      · intro h
        have := h y₁
        rw [Pi.single_eq_same] at this
        rwa [mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])] at this
      · intro h j
        by_cases hj : j = y₁
        · subst hj
          rw [Pi.single_eq_same, mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])]
          exact h
        · rw [Pi.single_eq_of_ne hj]
          exact zero_mem _
    · rw [csec_mem_iff hL]
      set b := q.pr (cA D a) with hb
      have hsum : ∀ y : Y → k, ∑ r, ∑ t, (F.β *ᵥ y) r * q.pr (cA D (incA D (HSpace.gram S r t))) *
          (b * q.pr (cA D (incA D (d.e t i)))) = b * u₂ * y y₂ := by
        intro y
        have hr : b * u₂ * y y₂ = ∑ l, y l * b * (∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) *
            q.pr (cA D (incA D (d.e t i)))) := by
          simp only [hcol₂, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        rw [hr]
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
        symm
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm.trans
          (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun l _ => ?_))
        ring
      constructor
      · intro h
        have h2 := h (F.β *ᵥ Pi.single y₂ 1) ((hF _).1 fun j => by
          by_cases hj : j = y₂
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _)
        rw [hsum, Pi.single_eq_same, mul_one, mul_unit_mem_iff hu₂] at h2
        exact h2
      · intro hb' x hx
        have hx' : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
        rw [hx'] at hx ⊢
        rw [hsum]
        exact mul_mem (mul_mem hb' hu₂i) ((hF _).2 hx y₂)
  constructor
  · intro h
    have ha := GlobalTheory.FinPl.SuppShift.idAt_of_colMul d h
    exact (GlobalTheory.SplitIntComp.mem_intAt_iff q ha).2 ((key a ha).1 h)
  · intro h
    exact (key a h.1).2 ((GlobalTheory.SplitIntComp.mem_intAt_iff q h.1).1 h)

end GlobalTheory.PrimSplitLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueSuccPlacesOuterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedIntegralValue_succ_places_outer : ∀ (D : D7) (r : ℕ), ValQr D r → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ μ₁ ρ₁ μ₂ ρ₂, Norm (fun i => Q i.succ) μ₁ ρ₁ μ₂ ρ₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) := by
  first | exact @GlobalTheory.QValOuter.outer | exact GlobalTheory.QValOuter.outer | (intros; apply GlobalTheory.QValOuter.outer <;> assumption)
end

