import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFrameResidue
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HTLine.GenInd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem embK_mem {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (τ : E →+* ℂ) (a : 𝓞 E) :
    embK c τ a ∈ c.V W := by
  show ((embK c τ a : c.F) : ℂ) ∈ W
  rw [embK_coe]
  have h1 : IsIntegral ℤ (τ (a : E)) := (NumberField.RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom
  have h2 : IsIntegral W (τ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

theorem natCast_mem_max {l : Level H} (c : Coeff l) {W : ValuationSubring ℂ} {p : ℕ} (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.V W) ∈ IsLocalRing.maximalIdeal (c.V W) := by
  obtain ⟨h0, h1⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 hW
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
  intro hu
  let g : c.V W →+* W := (c.F.val.toRingHom.comp (c.V W).subtype).codRestrict W (fun x => x.2)
  apply h1
  have := hu.map g
  rw [map_natCast] at this
  convert this using 1
  exact Subtype.ext (by simp)

theorem exists_ext {F : Type} [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ)
    (hp : (p : V) ∈ IsLocalRing.maximalIdeal V) {k : Type} [Field k] (g : V →+* k) (hk : (p : k) ≠ 0) :
    ∃ f : F →+* k, ∀ v : V, f v = g v := by
  have hker : RingHom.ker g = ⊥ := by
    by_contra h
    have hm : (RingHom.ker g).IsMaximal := Ideal.IsPrime.isMaximal (RingHom.ker_isPrime g) h
    have he := IsLocalRing.eq_maximalIdeal hm
    apply hk
    have : (p : V) ∈ RingHom.ker g := he ▸ hp
    simpa using this
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun x hx => by
    have : x ∈ RingHom.ker g := hx
    rwa [hker] at this
  exact ⟨IsFractionRing.lift hinj, fun v => IsFractionRing.lift_algebraMap (K := F) hinj v⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem dualMap_epsMul {R k : Type} [CommRing R] [CommRing k] (ψ : R →+* k) (r : R) :
    (dualMap ψ).comp (epsMul r) = (epsMul (ψ r)).comp (dualMap ψ) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul]
  · simp [dualMap, epsMul, mul_comm]

variable {X : Scheme.{0}} {t : SAB H X}

theorem ind_of_basis {R k : Type} [CommRing R] [Field k] {x : Sp R ⟶ X} {n m : ℕ}
    {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hv : GlobalTheory.LineNorm.IsTanBasis t x v) (e : Fin m ↪ Fin n)
    (ψ : R →+* k) : Pull.Ind t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ v (e i)) := by
  classical
  have hT : ∀ j, IsTanAtG t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v j) := fun j => GlobalTheory.LieMet.isTan_map ψ rfl (hv.1 j)
  refine ⟨fun i => hT (e i), fun cf cf' w h h' => ?_⟩
  let V : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap ψ ≫ x) t.G := fun j => GlobalTheory.LieMet.tanOf (hT j)
  have hs : ∀ d : Fin m → k, ∑ j, Function.extend e d 0 j • V j = ∑ i, d i • V (e i) := fun d => by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun j _ hj => by
      rw [Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => hj (Finset.mem_map.2 ⟨i, Finset.mem_univ _, hi⟩)),
        Pi.zero_apply, zero_smul]), Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by rw [e.injective.extend_apply]
  have hc : ∀ d, IsCombAtG t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ v (e i)) d w →
      IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (Function.extend e d 0) w := fun d hd => by
    have h1 := (Pull.comb_iff (fun i => V (e i)) d w).1 hd
    exact (Pull.comb_iff V _ w).2 (by rw [hs]; exact h1)
  have hw : IsTanAtG t (spMap ψ ≫ x) w := by
    rw [(Pull.comb_iff (fun i => V (e i)) cf w).1 h]; exact GlobalTheory.LieMet.isTan_tv _
  have := (hv.2 k ψ w hw).unique (hc cf h) (hc cf' h')
  funext i
  have h2 := congrFun this (e i)
  rwa [e.injective.extend_apply, e.injective.extend_apply] at h2

theorem ind_concat {Dw : Datum H} {l : Level H} (c : Coeff l) {k : Type} [Field k] (f : c.F →+* k) {x : Sp k ⟶ X}
    (u : Vecs Dw t k) (hE : ∀ τ i (a : 𝓞 E), u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i)
    (hI : ∀ τ, Pull.Ind t x (u τ)) :
    Pull.Ind t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) := by
  classical
  refine ⟨fun i => (hI _).1 _, fun cf cf' w h h' => ?_⟩
  let _ : Algebra c.F k := f.toAlgebra
  let U : (y : GlobalTheory.ShFam.Pad.Letter Dw) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G := fun y => GlobalTheory.LieMet.tanOf ((hI y.1).1 y.2)
  let e := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have hc : ∀ cf w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
      cf w ↔ w = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (∑ y, cf (e.symm y) • U y)).left := fun cf w => by
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    exact GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun i => U (e i)) cf w
  have hτ : ∀ τ cf w, IsCombAtG t x (u τ) cf w ↔ w = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (∑ i, cf i • U ⟨τ, i⟩)).left :=
    fun τ cf w => GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun i => U ⟨τ, i⟩) cf w
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := k) t.act
  have hEv : ∀ τ (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) v ↔ ∀ a : 𝓞 E,
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ (t.act.act a).left =
        spMap (epsMul (f (embK c τ a))) ≫ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left := fun τ v =>
    forall_congr' fun a => ⟨fun h => congrArg (fun z => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv z).left) h,
      fun h => GlobalTheory.LieMet.tan_ext h⟩
  have hS : ∀ τ (a : Fin (Dw.mult τ) → k), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) (∑ i, a i • U ⟨τ, i⟩) :=
    fun τ a s => by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hEv τ (U ⟨τ, i⟩)).2 (hE τ i) s, smul_comm]
  have h1 := GlobalTheory.LieMet.tan_ext (((hc cf w).1 h).symm.trans ((hc cf' w).1 h'))
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
  funext i
  obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective i
  have h2 := congrArg (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ) h1
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _),
    ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _)] at h2
  exact congrFun ((hI τ).2 _ _ _ ((hτ τ _ _).2 rfl)
    ((hτ τ _ _).2 (congrArg (fun z => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv z).left) h2))) i

end GlobalTheory.HTLine.GenInd

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.HTLine.GenInd.ind_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (k : Type) [Field k] (ψ : Γ(Z.X, U) →+* k), (p : k) ≠ 0 → (∀ τ, Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (w.bc ψ τ)) ∧ Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (fun i : Fin (letters Dw).length => w.bc ψ ((letters Dw).get i).1 ((letters Dw).get i).2) := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z U hU w hw k _ ψ hk
  obtain ⟨b, hb⟩ : ∃ b : Z.i.c.V W →+* Γ(Z.X, U), hU.fromSpec ≫ Z.s = spMap b := by
    refine ⟨(Spec.preimage (hU.fromSpec ≫ Z.s)).hom, ?_⟩
    exact (Spec.map_preimage (hU.fromSpec ≫ Z.s)).symm
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff (W := W) Z.i.c hp.ne_zero hW
  obtain ⟨f, hf⟩ := GlobalTheory.HTLine.GenInd.exists_ext (Z.i.c.V W) p (GlobalTheory.HTLine.GenInd.natCast_mem_max Z.i.c hW) (ψ.comp b) hk
  have hE : ∀ τ i (a : 𝓞 E), w.bc ψ τ i ≫ ((Y Z.i).t.act.act a).left =
      spMap (epsMul (f (embK Z.i.c τ a))) ≫ w.bc ψ τ i := by
    intro τ i a
    have h := GlobalTheory.HTLine.GenInd.embK_mem Z.i.c W τ a
    have h1 := GlobalTheory.T.integral_frame_valuation_bound E H Dw Xo p W Y i₀ Z U hU w hw b hb τ i a h
    have h2 : f (embK Z.i.c τ a) = ψ (b ⟨_, h⟩) := hf ⟨_, h⟩
    show spMap (dualMap ψ) ≫ w τ i ≫ _ = spMap (epsMul _) ≫ spMap (dualMap ψ) ≫ w τ i
    rw [h1, h2, ← Category.assoc, ← Category.assoc, GlobalTheory.HTLine.GenInd.spMap_comp',
      GlobalTheory.HTLine.GenInd.spMap_comp', GlobalTheory.HTLine.GenInd.dualMap_epsMul]
  have hI : ∀ τ, Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (w.bc ψ τ) := by
    intro τ
    obtain ⟨n, v, e, hve, hvt, hvu⟩ := hw.1 τ
    have hB := GlobalTheory.T.isTanBasis_of_unique_combination E H _ (Y Z.i).t _ (hU.fromSpec ≫ Z.π) n v hvt hvu
    have h3 := GlobalTheory.HTLine.GenInd.ind_of_basis hB e ψ
    simp only [hve] at h3
    exact h3
  refine ⟨hI, ?_⟩
  exact GlobalTheory.HTLine.GenInd.ind_concat (t := (Y Z.i).t) (x := spMap ψ ≫ hU.fromSpec ≫ Z.π) (Dw := Dw) Z.i.c f (w.bc ψ) hE hI
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictFaceOfSmoothConePolyhedralFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.FaceStrict

theorem exists_retract_balForms : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X], ∃ ρ : LinearMap.BilinForm ℤ X →ₗ[ℤ] balForms bar X, ∀ β : balForms bar X, ρ β = β := by
  intro O _ _ bar X _ _ _
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ X
  let P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    { toFun := fun β => β.compl₁₂ π π, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hP : Function.Injective P := fun β β' h => by
    ext a b
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    exact LinearMap.congr_fun₂ h a b
  haveI : Module.Finite ℤ (LinearMap.BilinForm ℤ X) := Module.Finite.of_injective P hP
  haveI : NoZeroSMulDivisors ℤ (LinearMap.BilinForm ℤ X ⧸ balForms bar X) := by
    refine ⟨fun {k x} hkx => ?_⟩
    obtain ⟨β, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hkx
    by_cases hk : k = 0
    · exact Or.inl hk
    right
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨h1, h2⟩ := hkx
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · have := h1 y z
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hk this
    · have := h2 a y z
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hk this
  haveI : Module.Free ℤ (LinearMap.BilinForm ℤ X ⧸ balForms bar X) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (balForms bar X).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  have hmem : ∀ x, (LinearMap.id - σ ∘ₗ (balForms bar X).mkQ :
      LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X) x ∈ balForms bar X := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hσ ((balForms bar X).mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply (balForms bar X) (σ _), this]
    exact sub_self _
  refine ⟨(LinearMap.id - σ ∘ₗ (balForms bar X).mkQ).codRestrict (balForms bar X) hmem, fun β => ?_⟩
  · apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 β.2, map_zero, sub_zero]

theorem exists_decomp_bounded : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar φ X →
    ∃ b : ℝ, ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X) (c : Fin n → ℝ),
      (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, 0 ≤ c i) ∧
      toReal β = ∑ i, c i • toReal (u i) ∧ φ.evalZ β = ∑ i, c i * φ.evalZ (u i) := by
  intro O _ _ _ _ bar φ X _ _ _ hP
  classical
  obtain ⟨S, hS, hcov⟩ := hP.finite
  refine ⟨∑ x ∈ hS.toFinset, |φ.evalZ x|, fun β hβ hp => ?_⟩
  have hR : toReal β ∈ psdCone bar X := by
    simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; simpa using hβ)
      (fun i y => by fin_cases i; simpa using hp y) (fun i => by fin_cases i; simp)
  obtain ⟨e, n, γ', c, hcell, hS', hc, he⟩ := hcov _ hR
  refine ⟨n, fun i => pull e.symm.toLinearMap (γ' i), c, fun i => pull_mem _ (hcell.mem i),
    fun i y => hcell.nonneg i _, fun i => ?_, hc, ?_, ?_⟩
  · rw [evalZ_pull φ e.symm.surjective]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |φ.evalZ x|) (fun x _ => abs_nonneg _)
      (hS.mem_toFinset.2 (hS' i)))
  · ext a b
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [LinearMap.sum_apply] using this
  · rw [← evalR_toReal, ← evalR_pullR φ (r := e.toLinearMap) e.surjective, he,
      (linearOn_iff φ γ').1 hcell.linear c hc]
    simp [evalZ_pull φ e.symm.surjective]

theorem isStrict_face_of_isCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar φ X → Dominates bar X →
    ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m), IsCone bar φ γ →
    IsStrict bar φ fun i => γ (s i) := by
  intro O _ _ _ _ bar φ X _ _ _ hP hD m m' γ s hγ
  classical
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨ρ, hρ⟩ := exists_retract_balForms O bar X
  obtain ⟨ψ, hψ⟩ := hγ.basis.exists_dual
  set T : Finset (Fin m) := Finset.univ.filter fun i => i ∉ Set.range s with hT
  set h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (∑ i ∈ T, ψ i) ∘ₗ ρ with hh
  have hγh : ∀ i, h (γ i) = if i ∈ T then 1 else 0 := fun i => by
    have e : ρ (γ i) = ⟨γ i, hγ.mem i⟩ := hρ ⟨γ i, hγ.mem i⟩
    simp only [hh, LinearMap.comp_apply, e, LinearMap.sum_apply, hψ]
    simp
  have hpos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have e3 : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos e3 e2) e1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hD ℓ (-h) hpos
  obtain ⟨b, hb⟩ := exists_decomp_bounded O bar φ X hP
  set B : ℕ := ⌈b⌉₊ with hB
  set K : ℕ := C + C * N * B + 1 with hK
  have cell : ∀ u ∈ balForms bar X, (∀ y, 0 ≤ u y y) → φ.evalZ u ≤ b →
      0 ≤ (K : ℝ) * ((ℓ u : ℝ) - N * φ.evalZ u) + h u ∧
      ((K : ℝ) * ((ℓ u : ℝ) - N * φ.evalZ u) + h u = 0 → (ℓ u : ℝ) = N * φ.evalZ u ∧ h u = 0) := by
    intro u hu hp hub
    obtain ⟨n, hn⟩ := hP.integral u hu hp
    have hle : (N : ℝ) * φ.evalZ u ≤ ℓ u := h2 u hu hp
    rw [hn] at hle hub ⊢
    have hle' : (N : ℤ) * n ≤ ℓ u := by exact_mod_cast hle
    have hnB : n ≤ (B : ℤ) := by
      have : (n : ℝ) ≤ B := hub.trans (Nat.le_ceil b)
      exact_mod_cast this
    have hCu := hC u hu hp
    rw [LinearMap.neg_apply] at hCu
    rcases (sub_nonneg.2 hle').eq_or_lt with ha | ha
    · have heq : (ℓ u : ℤ) = N * n := by linarith
      obtain ⟨k, c, hk, hc⟩ := h3 u hu hp (by rw [hn]; exact_mod_cast heq.symm)
      have hhu : 0 ≤ h u := by
        have e := congrArg h hc
        simp only [map_nsmul, map_sum, hγh] at e
        have hs : 0 ≤ ∑ i, c i • (if i ∈ T then (1 : ℤ) else 0) :=
          Finset.sum_nonneg fun i _ => by split_ifs <;> simp
        rw [← e, nsmul_eq_mul] at hs
        by_contra hneg
        push_neg at hneg
        have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) hneg
        linarith
      have e1 : (ℓ u : ℝ) = N * n := by exact_mod_cast heq
      have e2 : (0 : ℝ) ≤ h u := by exact_mod_cast hhu
      refine ⟨by rw [e1]; linarith, fun h0 => ⟨e1, ?_⟩⟩
      rw [e1] at h0
      have : ((h u : ℤ) : ℝ) = 0 := by linarith
      exact_mod_cast this
    · have key : (1 : ℤ) ≤ K * (ℓ u - N * n) + h u := by
        have hK' : (K : ℤ) = C + C * N * B + 1 := by simp [hK]
        rw [hK']
        have a1 : (0 : ℤ) ≤ (C * N * B + 1) * (ℓ u - N * n - 1) := mul_nonneg (by positivity) (by linarith)
        have a2 : (0 : ℤ) ≤ C * N * (B - n) := mul_nonneg (by positivity) (by linarith)
        nlinarith
      have : (1 : ℝ) ≤ K * ((ℓ u : ℝ) - N * n) + h u := by exact_mod_cast key
      exact ⟨by linarith, fun h0 => by linarith⟩
  have dec : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      0 ≤ (K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β ∧
      ((K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β = 0 → (ℓ β : ℝ) = N * φ.evalZ β ∧ h β = 0) := by
    intro β hβ hp
    obtain ⟨n, u, c, hu, hup, hub, hc, hR, hφ⟩ := hb β hβ hp
    have lin : ∀ g : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (g β : ℝ) = ∑ i, c i * g (u i) := fun g => by
      have := sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) Function.injective_id g (u := u) (w := ![β]) (a := c)
        (b := ![1]) (by simpa using hR.symm)
      simpa using this.symm
    have hF : (K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β =
        ∑ i, c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) := by
      have e : ∀ i, c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) =
          K * (c i * ℓ (u i)) - K * N * (c i * φ.evalZ (u i)) + c i * h (u i) := fun i => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← lin, ← hφ]
      ring
    have hF0 : ∀ i, 0 ≤ c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) := fun i =>
      mul_nonneg (hc i) (cell (u i) (hu i) (hup i) (hub i)).1
    refine ⟨hF ▸ Finset.sum_nonneg fun i _ => hF0 i, fun h0 => ?_⟩
    rw [hF] at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hF0 i).1 h0
    have hz' : ∀ i, c i * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) = 0 ∧ c i * (h (u i) : ℝ) = 0 := fun i => by
      rcases mul_eq_zero.1 (hz i (Finset.mem_univ _)) with h5 | h5
      · simp [h5]
      · obtain ⟨e1, e2⟩ := (cell (u i) (hu i) (hup i) (hub i)).2 h5
        simp [e1, e2]
    have e1 : (ℓ β : ℝ) - N * φ.evalZ β = ∑ i, c i * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) := by
      rw [lin ℓ, hφ, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 := lin h
    rw [Finset.sum_eq_zero fun i _ => (hz' i).1] at e1
    rw [Finset.sum_eq_zero fun i _ => (hz' i).2] at e2
    exact ⟨by linarith, by exact_mod_cast e2⟩
  refine ⟨K * N, K • ℓ + h, Nat.mul_pos (by omega) hN, fun j => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · have hs : s j ∉ T := by simp [hT]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hγh, if_neg hs, nsmul_eq_mul, add_zero]
    push_cast
    rw [h1]
    ring
  · have := (dec β hβ hp).1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    push_cast
    linarith
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at he
    push_cast at he
    obtain ⟨e1, e2⟩ := (dec β hβ hp).2 (by linarith)
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp e1.symm
    have hzT : ∀ i ∈ T, c i = 0 := by
      have e := congrArg h hc
      simp only [map_nsmul, map_sum, hγh, e2, smul_zero] at e
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by split_ifs <;> simp).1 e.symm
      intro i hi
      have := hz i (Finset.mem_univ _)
      rw [if_pos hi, nsmul_eq_mul, mul_one] at this
      exact_mod_cast this
    refine ⟨k, fun j => c (s j), hk, ?_⟩
    rw [hc]
    have e3 : ∑ i, c i • γ i = ∑ i ∈ Finset.univ.map s, c i • γ i :=
      (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [hzT i (by simpa [hT, Finset.mem_map] using hi), zero_smul]).symm
    rw [e3, Finset.sum_map]

end GlobalTheory.PolFan.FaceStrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicDual_family_linearIndependent_rank_eq_two_mul : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  first | exact @GlobalTheory.familyIsotropicDual_linearIndependent_and_card | exact GlobalTheory.familyIsotropicDual_linearIndependent_and_card | (intros; apply GlobalTheory.familyIsotropicDual_linearIndependent_and_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetEvaluationPowerSeriesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_evaluation_power_series : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (R : Type) [CommRing R] (I : Ideal R), I.FG → ∀ f : R →+* C, (∀ r, ‖f r‖ ≤ 1) → (∀ r ∈ I, ‖f r‖ < 1) → ∀ (W : Type) [CommRing W] [Algebra R W] [Module.Finite R W] (ρ : Type) [Fintype ρ] [DecidableEq ρ] (m : ℕ) (κ : W →+* Jet C ρ m), (∀ r, κ (algebraMap R W r) = algebraMap C (Jet C ρ m) (f r)) → ∀ (X : Type) (s : W) (t : X → W), (∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) → ∀ (u : Jet C ρ m) (g : X → MvPowerSeries ρ C), (∀ α, psJet m (g α) = u * κ (t α)) → (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → Summable fun α => MvPowerSeries.coeff n (g α)) ∧ ∀ g₀ : MvPowerSeries ρ C, (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → HasSum (fun α => MvPowerSeries.coeff n (g α)) (MvPowerSeries.coeff n g₀)) → psJet m g₀ = u * κ s := by
  first | exact @GlobalTheory.AdicConverge.converge | exact GlobalTheory.AdicConverge.converge | (intros; apply GlobalTheory.AdicConverge.converge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepAtlasPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_atlas_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → Planar D.Em f q → ∀ (Z₁ : Mdl Y i₀) (h : Z₁.X ⟶ X'), MapsTo Z₁ A' h → IsMap Z₁ Z (h ≫ f) → t.k ∈ Z₁.ty t.σ → t.Holds Z₁ := by
  first | exact @GlobalTheory.GrCl.RowCombination.holds_of_planar | exact GlobalTheory.GrCl.RowCombination.holds_of_planar | (intros; apply GlobalTheory.GrCl.RowCombination.holds_of_planar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepHoldsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_holds_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z₁.X) (α : D.C.A), ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α → ∃ (n' : ℕ) (a : Matrix (Fin n') (Fin (D.C.n α)) R) (a' : Matrix (Fin (D.C.n α)) (Fin n') R), a * a' = 1 ∧ a' * a = 1 ∧ ∀ (τ : (Y Z₁.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z₁.i).t (Y Z.i).t τ) (u : Vecs Dw (Y Z₁.i).t K), LocM.IsTrans Z.i Z₁.i τ mu → Z₁.FlagAt (spMap (algebraMap R K) ≫ z) u → ∀ (y : Sp K ⟶ Z.X), y = spMap (algebraMap R K) ≫ z ≫ g₀ → ∀ (hy : ⊤ ≤ y ⁻¹ᵁ D.C.B α) (v : TanM (y ≫ Z.π) (Y Z.i).t.G) (i : Fin (Dw.mult t.σ)), (i : ℕ) < t.k → (tv v).left = u t.σ i ≫ mu.φ → ∀ j : Fin n', t.k ≤ (j : ℕ) → ∑ l, algebraMap R K (a j l) * D.crd α K y hy v l = 0 := by
  first | exact @GlobalTheory.GrCl.Annih.annih | exact GlobalTheory.GrCl.Annih.annih | (intros; apply GlobalTheory.GrCl.Annih.annih <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

theorem GlobalTheory.lbIso_of_generic_normal_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (H : Scheme.{0}) (p : H ⟶ Sp R) (e : Sp R ⟶ H), Smooth p → QuasiCompact p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ L M : LB H, L.IsLB → M.IsLB → LBIso (L.pull (pullback.fst p (jK R))) (M.pull (pullback.fst p (jK R))) → LBIso L M := by
  intro R _ _ _ hN hI H p e hs _ hg he L M hL hM h
  haveI : IsNoetherianRing R := hN
  haveI : IsIntegrallyClosed R := hI
  have hD := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  obtain ⟨t, ht⟩ := GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂
    DVR.isDominant_jK inferInstance (Over.mk p) e (LB.div M L) he hs hg hD
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hD _)) ((IsoExtend.lbIso_pull_iff_gen L M _).1 h)
  have h0 := (CechPic.cls_eq_zero_iff hD).2 ⟨t, ht⟩
  rw [CechPic.cls_div hM hL, sub_eq_zero] at h0
  exact (CechPic.cls_eq_iff hL hM).1 h0.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_real_combinations_of_independent : ∀ (g r d : ℕ) (x : Fin r → Fin g → ℂ) (e : Fin d → Fin r → ℝ), LinearIndependent ℝ x → LinearIndependent ℝ e → LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  first | exact @GlobalTheory.linearIndependent_real_combination | exact GlobalTheory.linearIndependent_real_combination | (intros; apply GlobalTheory.linearIndependent_real_combination <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomainStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  first | exact @GlobalTheory.FlagFibreInt.lintegral_dens_glue | exact GlobalTheory.FlagFibreInt.lintegral_dens_glue | (intros; apply GlobalTheory.FlagFibreInt.lintegral_dens_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_form_on_chart_ring : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y) {tC : SAB H (Sp (ChartRing k m e))} (_ : SABMap tC Y.t (ξ ≫ genι Y)) (PC : PELUnif (maximalIdeal (ChartRing k m e)) tC) (γ : Fin m → LinearMap.BilinForm ℤ PC.D.toPre.X), IsMonomial PC.D.toPre (bdParam k m e) γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (ϖ : W), Irreducible ϖ → ∀ (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Y.j → ∀ (be : LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ϖ' : V), Irreducible ϖ' → ∀ (f : W →+* V) (ψ : ChartRing k m e →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y → ∀ (r : ℕ) (u : Vˣ), f ϖ = u * ϖ' ^ r → ∀ (n : Fin m → ℕ) (v : Fin m → Vˣ), (∀ i, ψ (bdParam k m e i) = v i * ϖ' ^ n i) → ∃ ε : P.D.toPre.X ≃ₗ[𝓞 E] PC.D.toPre.X, ∀ y, (r : ℤ) * be y y = ∑ i, (n i : ℤ) * γ i (ε y) (ε y) := by
  first | exact @GlobalTheory.TraitChartForm.main | exact GlobalTheory.TraitChartForm.main | (intros; apply GlobalTheory.TraitChartForm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExtensionConeTransferStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_positive_polFan_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ' : InvFun (𝓞 E)), IsPolFan H.bar q φ' → NoSelfInt H.bar q φ' → IsTwInv H φ' → ∃ φ'' : InvFun (𝓞 E), IsPolFan H.bar q φ'' ∧ NoSelfInt H.bar q φ'' ∧ IsTwInv H φ'' ∧ IsPosFn H φ'' ∧ (∀ (n k : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), φ''.toFun n (fun a b => k * B a b) = k * φ''.toFun n B) ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ'' γ → IsCone H.bar φ' γ := by
  first | exact @GlobalTheory.PolFan.OffDom.exists_extension | exact GlobalTheory.PolFan.OffDom.exists_extension | (intros; apply GlobalTheory.PolFan.OffDom.exists_extension <;> assumption)
end

