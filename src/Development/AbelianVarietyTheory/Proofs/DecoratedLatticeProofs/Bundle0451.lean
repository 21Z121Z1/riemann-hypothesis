import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastPeriodFactorizationOfClassData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PerXCls

variable {D : D7}

abbrev finfF (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GinfC_iff (V : HSp D) (g : GA D V) : g ∈ GinfC V ↔ (Formalism.L2.Theta.mt V g).map (finfF D) = 1 := by
  show finHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n) (y : Mx D n k) (hm : m.map (finfF D) = 1) :
    (x ⬝ m ⬝ y).map (finfF D) = (x ⬝ y).map (finfF D) := by
  have e1 : (x ⬝ m ⬝ y).map (finfF D) = x.map (finfF D) ⬝ m.map (finfF D) ⬝ y.map (finfF D) := by
    rw [Matrix.map_mul (f := finfF D), Matrix.map_mul (f := finfF D)]
  have e2 : (x ⬝ y).map (finfF D) = x.map (finfF D) ⬝ y.map (finfF D) := Matrix.map_mul (f := finfF D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GinfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GinfC A) :
    o.emb (a, 1) ∈ GinfC S := by
  rw [mem_GinfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finfF D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one,
    ← Matrix.map_add _ (map_add (finfF D)), o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trc_apply {V : HSp D} (e : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc e f x = ∑ g ∈ e.support, e g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsm : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact hadd hx hy
  | zero => simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsm (h x) c

theorem ontoUni_of_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (hab : a = b)
    (r : K → ι → Matrix (Fin a) (Fin a) ℂ)
    (hr : OntoUni (fun k τ => (r k τ).reindex (finCongr hab) (finCongr hab))) : OntoUni r := by
  subst hab
  simpa using hr

end GlobalTheory.SeeSaw.PerXCls

open GlobalTheory.SeeSaw.PerXCls in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.SeeSaw.perX_of_clsPinD : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), c.Is → (∀ s, (t s).Is) →
    ClsPinD t → PerX t := by
  intro D c 𝒯 t hc ht hP
  obtain ⟨ρ, hρ, hA⟩ := hP
  intro n h y v
  have hU : OntoUni (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) :=
    ontoUni_of_reindex ρ.hT (fun k : GinfC c.T => inB c.θ c.T ρ.BT k.1) hρ.uniT
  obtain ⟨_, _, _, ν, hν1, hν2, hcls⟩ := integral_eq_classSum D c.θ c.T ρ.BT hc.inf hU
  obtain ⟨hN, hInt, hBr, hne, hblk⟩ := hρ.low n h
  have hemb : ∀ k : GinfC c.T, (c.oT n h).emb (k.1, 1) ∈ GinfC (c.X n) := fun k => orth_emb_mem_GinfC _ k.2
  let y0 : FrN D (ρ.N n) := ρ.fr n y
  have hdet : ∀ (k : GinfC c.T) τ, IsUnit ((ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ).det) := by
    intro k τ
    rw [Matrix.det_mul]
    have hu := (hρ.uni n h.le).uni ⟨_, hemb k⟩ τ
    exact (Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.mp hu)).mul (y0.2 τ)
  let yk : GinfC c.T → FrN D (ρ.N n) := fun k => ⟨fun τ => ρ.r n h.le ((c.oT n h).emb (k.1, 1)) τ * y0.1 τ, hdet k⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.unitaryAverage_translate_eq_smul_branchingMap D.what₂.Tau (ρ.N n) ρ.NT hN (fun _ => 1) (fun _ => 1) (ρ.lam n) ρ.sg hInt (ρ.low n h) hBr
    hne (GinfC c.T) ν (fun k => ρ.rT k.1) hρ.uniT y0 yk
    (fun k => ⟨_, fun τ => hblk k.1 k.2 τ, fun τ => rfl⟩) (ρ.J v 1) (hρ.J v).1 (fun k => ρ.J v k.1)
    (fun k z z' hz => (hρ.J v).2 k.1 k.2 z z' hz)
  refine ⟨a, fun s ψ hψ F => ?_⟩
  obtain ⟨⟨A, hA1⟩, B, hB⟩ := hA s
  obtain ⟨hvol, hstab, hsum⟩ := hcls c.volT B.U B.cl B.h hB.reps
  have rdtr := GlobalTheory.T.seesaw_scalar_forms_laws_on_class_data D c (t s) ρ A hc hρ hA1.1 n h.le ψ hψ
  obtain ⟨J, χ, hCT⟩ := (ht s).CT
  have hF : IsContAut c.T (F.1 v) := isContAut_multT (hCT F.2) v
  have key : ∀ β, ∫ h' in c.volT.𝓕, trc ((t s).eT n h β) (F.1 v) h' * (t s).rd n β ψ y ((c.oT n h).emb (h', 1)) ∂c.volT.μ =
      (volLev c.volT B.U : ℂ) * ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        (a * B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
    intro β
    obtain ⟨hr1, -, hr3, hr4⟩ := rdtr β
    rw [hsum]
    · congr 1
      refine Finset.sum_congr rfl fun a' _ => ?_
      congr 1
      have hpt : ∀ k : GinfC c.T, trc ((t s).eT n h β) (F.1 v) (B.h a' * k.1) *
          (t s).rd n β ψ y ((c.oT n h).emb (B.h a' * k.1, 1)) =
          B.ell n h β a' F (ρ.J v k.1) * (fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1))) (yk k) := by
        intro k
        rw [hB.top n h F v β a' k.1 k.2]
        congr 1
        have hm : (c.oT n h).emb (B.h a' * k.1, 1) = (c.oT n h).emb (B.h a', 1) * (c.oT n h).emb (k.1, 1) := by
          rw [← map_mul]; simp
        rw [hm]
        refine hr3 y _ _ _ (hemb k) ?_
        intro τ
        rw [Equiv.apply_symm_apply]
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact ha _ (hr4 _) _
    · refine Continuous.mul ?_ ((hr1 y).2.comp ((c.oT n h).continuous_emb.comp (continuous_id.prodMk continuous_const)))
      have : trc ((t s).eT n h β) (F.1 v) = fun x => ∑ g ∈ ((t s).eT n h β).support, (t s).eT n h β g * F.1 v (x * g) :=
        funext fun x => trc_apply _ _ x
      rw [this]
      exact continuous_finset_sum _ fun g _ => continuous_const.mul (hF.2.comp (continuous_mul_right g))
    · intro γ hγ g
      rw [trc_apply, trc_apply]
      congr 1
      · refine Finset.sum_congr rfl fun g' _ => ?_
        rw [mul_assoc, hF.1 γ hγ]
      · have hm : (c.oT n h).emb (γ * g, 1) = (c.oT n h).emb (γ, 1) * (c.oT n h).emb (g, 1) := by
          rw [← map_mul]; simp
        rw [hm, (hr1 y).1 _ ((c.oT n h).emb_mem_GQ hγ (GQ _).one_mem)]
    · intro κ hκ g
      exact hB.inv n h ψ hψ F v y β g κ hκ
  have htl := hB.tail n h ψ hψ F
  unfold Tup.perT
  rw [Finset.sum_congr rfl fun β _ => key β]
  calc _ = a * ((volLev c.volT B.U : ℂ) * ∑ β, ∑ a', ((stabOrd B.U (B.h a') : ℕ) : ℂ)⁻¹ *
        B.ell n h β a' F (ρ.low n h fun z => (t s).rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (B.h a', 1)))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun a' _ => by ring
    _ = _ := by rw [htl]; ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepMove

section Lattices

open GlobalTheory.FinPl hiding Pl

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mt_mul₀ (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one₀ (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv] at e
  exact e.symm

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves S g L M P)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : mt S g *ᵥ z ∈ latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_eq (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h u = HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹) := rfl

theorem actO_mem_latO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [actO_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  rw [actO_eq, actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.mul_one]

end Lattices

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem isHalf_actO (g : GA D S) (h : GA D T) {e : AE D} {u : WO S T} (hu : IsHalf e u) : IsHalf e (actO S T g h u) := by
  intro i j
  rw [actO_eq]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hu k l]
  ring

theorem vac_move (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T}
    (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M')
    {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S} {h : GA D T} (hg : GlobalTheory.FinPl.Moves S g Λ M P) (hh : GlobalTheory.FinPl.Moves T h Λ' M' P)
    {f : WO S T → ℂ} (hf : GlobalTheory.FinPl.Vac ψ S T Λ Λ' P f) : GlobalTheory.FinPl.Vac ψ S T M M' P (om (g, h) f) := by
  have back : ∀ u : WO S T, actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := actO_actO_inv g h
  have mem : ∀ u ∈ latO S T (M : Set _) (M' : Set _) P, actO S T g⁻¹ h⁻¹ u ∈ latO S T (Λ : Set _) (Λ' : Set _) P :=
    fun u hu => actO_mem_latO hM hΛ hM' hΛ' (moves_inv hg) (moves_inv hh) hu
  refine ⟨hW.om_pres _ _ hf.1, fun u hu => ?_, fun e he u hu hh' => ?_⟩
  · have h1 := hf.2.1 _ (mem u hu)
    have h2 : (2 • actO S T g⁻¹ h⁻¹ u : WO S T) = actO S T g⁻¹ h⁻¹ (2 • u) := by
      rw [actO_eq, actO_eq, two_nsmul, two_nsmul, Matrix.mul_add, Matrix.add_mul]
    have h3 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ (2 • u)) f hf.1
    rw [back, ← h2, h1] at h3
    exact h3.symm
  · have h1 := hf.2.2 e he _ (mem u hu) (isHalf_actO g⁻¹ h⁻¹ hh')
    have h3 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ u) f hf.1
    rw [back, h1] at h3
    exact h3.symm

theorem vacO_ne_zero {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hall⟩ := hf.2.norm
  have := hall p hp
  simp [nrm2] at this

theorem om_ne_zero (p : GA D S × GA D T) {f : WO S T → ℂ} (hf : f ≠ 0) : om p f ≠ 0 := by
  intro h0
  apply hf
  have : om p⁻¹ (om p f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  rw [← this, h0, map_zero]

theorem gen (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T}
    (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M')
    {g : GA D S} {h : GA D T} (hgf : g ∈ GfC S) (hhf : h ∈ GfC T)
    (hg : GlobalTheory.FinPl.Moves S g Λ M fun _ => True) (hh : GlobalTheory.FinPl.Moves T h Λ' M' fun _ => True)
    {sS sT} (BS BT) {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT (Λ : Set _) (Λ' : Set _) f) :
    (∀ P, ∀ x ∈ GinfC S, ∀ x' ∈ GinfC T, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True)
      (om (x * g, x' * h) (pureTensorO ψ θ S T sS sT BS BT f P))) ∧
      om (g, h) (pureTensorO ψ θ S T sS sT BS BT f 1) ≠ 0 := by
  have hθ : IsInfFam θ := hf.2.inf
  refine ⟨fun P x hx x' hx' => ?_, ?_⟩
  · have hv : GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) (om (g, h) f) :=
      vac_move hW hΛ hM hΛ' hM' hg hh ⟨hf.2.theta, hf.2.lat⟩
    have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT g h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgf, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hhf, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgf, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hhf, Matrix.one_mul]) f hf.2.theta P
    have e1 : ((x * g, x' * h) : GA D S × GA D T) = (x, x') * (g, h) := rfl
    rw [e1, map_mul, Module.End.mul_apply, hfin.2]
    exact (GlobalTheory.FockComb.om_pureTensorO_comb D ψ θ S T χS χT om hθ hW sS sT BS BT 0 (om (g, h) f) 0 0
      (fun u hu => by simp at hu) hv.1 GlobalTheory.OrientedHeis.theta_zero 1 (one_mem _) 1 (one_mem _)
      (by rw [map_zero, zero_smul]) P x hx x' hx').2 M M' hv
  · rw [GlobalTheory.FiniteFock.pureTensorO_one]
    exact om_ne_zero _ (vacO_ne_zero hf)

end Gen

theorem fock_vac_moved : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((pk W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P))) ∧ (pk W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j hj g g' hg hg' M M' hM hM' hm hm'
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sd : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((pk W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  exact gen (W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj) (sd j (by omega)) hM (sd (j + 1) hj) hM' hg hg' (hm _) (hm' _) _ _
    (W.Q.charW.base.chain.vY W.P.A3.A.μ0 j hj).1

end GlobalTheory.StepMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.SplitTransfer

theorem seg_map_inv {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ) :
    (GlobalTheory.LFun.seg w x t).map (·⁻¹) = GlobalTheory.LFun.seg w x⁻¹ t := by
  have hr : (Finset.range t).image (fun i => t - 1 - i) = Finset.range t := by
    ext i
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro hi; exact ⟨t - 1 - i, by omega, by omega⟩
  have hinj : Set.InjOn (fun i => t - 1 - i) (Finset.range t : Set ℕ) := fun a ha b hb e => by
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at e
    omega
  unfold GlobalTheory.LFun.seg
  conv_rhs => rw [← hr, Finset.image_val_of_injOn hinj, Multiset.map_map]
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  have hi' : i < t := Finset.mem_range.1 hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  apply Units.ext
  simp only [Units.val_inv_eq_inv_val, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

set_option maxHeartbeats 1600000 in

theorem transferOn_isSplit : ∀ D : D7, TransferOn D fun v => IsSplit (E := D.host.E) v := by
  intro D ψ S T χS χT om hW t ht v hv hunr w h U hU f hf X _ _ ρ x B hx X' _ _ ρ' b hb hne
  obtain ⟨eS, heS⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D S v w h).1 hv
  obtain ⟨eT, heT⟩ := (GlobalTheory.T.exists_unitaryCharts_allFinitePlaces_frameLattice D T v w h).1 hv
  have hxS := hx.isSatVecGL hv heS
  obtain ⟨hfix, hH⟩ := GlobalTheory.T.latticeVacuum_heckeIdentity_splitPlace_charts D ψ S T χS χT om hW t ht v w h hv hunr eS eT heS heT (f : WO S T → ℂ) hf
  obtain ⟨hcS, hsS⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w S.rank
  obtain ⟨hcT, hsT⟩ := GlobalTheory.T.integral_GL_commensurated_doubleCosetCardInvSymm D.host.E w T.rank
  let σF : Representation ℂ (GL (Fin S.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom
  let πF : Representation ℂ (GL (Fin T.rank) (w.adicCompletion D.host.E)) (WO S T → ℂ) :=
    ((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom
  have eσ : ∀ g, σF g = om (embV S v (eS.symm g), embV T v 1) := fun g => by simp [σF]
  have eπ : ∀ g, πF g = om (embV S v 1, embV T v (eT.symm g)) := fun g => by simp [πF]
  let σU := σF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eσ]; exact hU _ _ u hu
  let πU := πF.subrepresentation U fun g u hu => by rw [Submodule.mem_comap, eπ]; exact hU _ _ u hu
  let ρS := ρ.comp eS.symm.toMonoidHom
  let ρT := ρ'.comp eT.symm.toMonoidHom

  have hKS : ∀ k ∈ KGL w S.rank, eS.symm k ∈ Kv S v := fun k hk => (heS.2 (eS.symm k)).2 (by simpa using hk)
  have hKT : ∀ k ∈ KGL w T.rank, eT.symm k ∈ Kv T v := fun k hk => (heT.2 (eT.symm k)).2 (by simpa using hk)
  have hfS : f ∈ fixed σU (KGL w S.rank) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change σF k (f : WO S T → ℂ) = f
    rw [eσ]; exact hfix _ (hKS k hk) _ (one_mem _))
  have hfT : f ∈ fixed πU (KGL w T.rank) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
    change πF k (f : WO S T → ℂ) = f
    rw [eπ]; exact hfix _ (one_mem _) _ (hKT k hk))
  have hequiv : ∀ g (u : U), (b.flip x) (πU g u) = ρT g ((b.flip x) u) := fun g u => by
    have e := hb 1 (eT.symm g) u x
    rw [show ρ 1 x = x by simp] at e
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
    change b (πU g u) x = ρ' (eT.symm g) (b u x)
    rw [← e]
    congr 2
    exact Subtype.ext (by change πF g (u : WO S T → ℂ) = _; rw [eπ])
  have hinv : ∀ g (u : U) y, b (σU g u) (ρS g y) = b u y := fun g u y => by
    have e := hb (eS.symm g) 1 u y
    rw [show ρ' 1 (b u y) = b u y by simp] at e
    rw [← e]
    congr 2
    exact Subtype.ext (by change σF g (u : WO S T → ℂ) = _; rw [eσ])
  have hbfix : b f x ∈ fixed ρT (KGL w T.rank) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    have e := hequiv k f
    rw [GlobalTheory.LGrp.mem_fixed.1 hfT k hk] at e
    exact e.symm
  have hcard : (stepPar χS χT t (fun _ => B) w).card = T.rank := by
    simp [stepPar, GlobalTheory.LFun.seg, hxS.2.2.1, ht]
  have hB'inv : (stepPar χS χT t (fun _ => B) w).map (·⁻¹) =
      (B.map (·⁻¹)).map ((val (F := D.host.F) χS w)⁻¹ * ((val (F := D.host.F) χT w)⁻¹)⁻¹ * ·) +
        GlobalTheory.LFun.seg w (val (F := D.host.F) χS w)⁻¹ t := by
    rw [stepPar, Multiset.map_add, seg_map_inv, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun c _ => ?_
    simp only [Function.comp_apply, mul_inv]
  refine Or.inl ⟨hv, eT, heT, (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w T.rank X' ρT (b f x) _ hne hbfix hcard).2 fun ϖ hϖ k hk => ?_⟩
  have hsubT : ∀ g (y : U), U.subtype (πU g y) = πF g (U.subtype y) := fun g y => rfl
  have hsubS : ∀ g (y : U), U.subtype (σU g y) = σF g (U.subtype y) := fun g y => rfl
  have hInvT : (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) ∈ Hecke ℂ (KGL w T.rank) :=
    (GlobalTheory.T.hecke_operator_move_across_invariant_bilinear _ (KGL w T.rank) hcT hsT ℂ ℂ ℂ 1 1 0 (fun _ _ _ => by simp) 0 (zero_mem _) 0 (zero_mem _) _
      (Tj_mem_hecke hϖ k)).1
  let cf : ℕ → ℂ := fun j => if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) *
    (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) *
    (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k *
    (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0
  have hH' : heckeVec πF (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σF (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) :=
    hH ϖ hϖ k hk
  have e1 : U.subtype (heckeVec πU (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) =
      heckeVec πF (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (U.subtype f) :=
    map_heckeVec hcT hInvT U.subtype hsubT f
  have e2 : ∀ j, U.subtype (heckeVec σU (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) =
      heckeVec σF (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) (U.subtype f) := fun j =>
    map_heckeVec hcS (Tj_mem_hecke hϖ j) U.subtype hsubS f
  have hT : heckeVec πU (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f =
      ∑ j ∈ Finset.range (S.rank + 1), cf j • heckeVec σU (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
    apply U.injective_subtype
    rw [e1, hH', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, e2 j]
  have hmove : ∀ j ∈ Finset.range (S.rank + 1), b (heckeVec σU (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f) x =
      satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by
    intro j hj
    rw [(GlobalTheory.T.hecke_operator_move_across_invariant_bilinear _ _ hcS hsS U X X' σU ρS b hinv f hfS x hxS.2.1 _ (Tj_mem_hecke hϖ j)).2,
      (GlobalTheory.T.satake_vector_iff_inverse_doubleCosets D.host.E w S.rank X ρS x B hxS.1 hxS.2.1 hxS.2.2.1).1 hxS ϖ hϖ j
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), map_smul]
  have hsym := GlobalTheory.T.satake_esymm_scaled_multiset_add_segment D.host.E w S.rank t k (B.map (·⁻¹)) (val (F := D.host.F) χS w)⁻¹
    (val (F := D.host.F) χT w)⁻¹ (by rw [Multiset.card_map, hxS.2.2.1]) (ht ▸ hk)
  calc heckeVec ρT (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) (b f x)
      = b (heckeVec πU (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f) x :=
        (map_heckeVec hcT hInvT (b.flip x) hequiv f).symm
    _ = ∑ j ∈ Finset.range (S.rank + 1), cf j • satEig (qV D.host.E w) S.rank (B.map (·⁻¹)) j • b f x := by
        rw [hT, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_smul, LinearMap.smul_apply, hmove j hj]
    _ = satEig (qV D.host.E w) T.rank ((stepPar χS χT t (fun _ => B) w).map (·⁻¹)) k • b f x := by
        simp_rw [smul_smul]
        rw [← Finset.sum_smul]
        congr 1
        rw [hB'inv, ht, hsym]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        simp only [cf]
        split_ifs
        · rw [ht]
          simp only [Units.val_inv_eq_inv_val, inv_inv, mul_inv]
        · rfl

end GlobalTheory.ChainOnto.SplitTransfer
end
end

