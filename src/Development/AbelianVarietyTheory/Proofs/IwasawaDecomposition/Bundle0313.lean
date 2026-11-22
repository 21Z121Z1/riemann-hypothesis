import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjInvolutive
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem longElt_invT_involution : ∀ (R : Type) [CommRing R] (n : ℕ) (g : GL (Fin n) R), longElt n R * GlobalTheory.CuspRep.invT n R (longElt n R * GlobalTheory.CuspRep.invT n R g * longElt n R) * longElt n R = g := by
  intro R _ n g
  have hw : longElt n R * longElt n R = 1 := Units.ext (antidiag_mul_self n R)
  have hii : ∀ h : GL (Fin n) R, GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R h) = h := fun h => by
    apply Units.ext
    show (h.valᵀ)ᵀ = h.val
    exact Matrix.transpose_transpose _
  have hwT : GlobalTheory.CuspRep.invT n R (longElt n R) = longElt n R := by
    apply Units.ext
    show (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0)ᵀ = Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    congr 1
    exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  rw [map_mul, map_mul, hii, hwT, ← mul_assoc, ← mul_assoc, hw, one_mul, mul_assoc, hw, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentBorel
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.UnipFlip

theorem longElt_conj_apply {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ((longElt n R : Matrix (Fin n) (Fin n) R) * A * (longElt n R : Matrix (Fin n) (Fin n) R)) i j
      = A i.rev j.rev := by
  simp only [Matrix.mul_apply, longElt, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro b _ hb; rw [if_neg]; intro e; exact hb (by rw [e, Fin.rev_rev])
  · simp

theorem inv_apply_succ {R : Type} [CommRing R] {n : ℕ} {u : GL (Fin n) R} (hu : u ∈ unipB R (Fin n))
    (p q : Fin n) (h : (q : ℕ) = p + 1) :
    ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p q = - (u : Matrix (Fin n) (Fin n) R) p q := by
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  rw [mem_unipB] at hu hv
  have hpq : p ≠ q := by intro e; subst e; omega
  have key := congrFun (congrFun (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R)) (mul_inv_cancel u)) p) q
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_ne hpq] at key
  rw [Fintype.sum_eq_add p q hpq] at key
  · rw [hu.2 p, hv.2 q, one_mul, mul_one] at key
    linear_combination key
  · intro c ⟨hcp, hcq⟩
    rcases lt_or_gt_of_ne hcp with hlt | hgt
    · rw [hu.1 p c hlt, zero_mul]
    · have : q < c := by
        have h1 : (p : ℕ) < c := hgt
        have h2 : (c : ℕ) ≠ q := fun e => hcq (Fin.ext e)
        show (q : ℕ) < c
        omega
      rw [hv.1 c q this, mul_zero]

theorem longElt_invT_conj_unipB : ∀ (R : Type) [CommRing R] (n : ℕ) (u : GL (Fin n) R), u ∈ unipB R (Fin n) →
    longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipB R (Fin n) ∧
      superDiag (longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R) = -superDiag u := by
  intro R _ n u hu
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  have hval : ∀ i j : Fin n,
      ((longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
        = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j.rev i.rev := by
    intro i j
    rw [Units.val_mul, Units.val_mul]
    rw [longElt_conj_apply]
    rfl
  rw [mem_unipB] at hv
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval]; exact hv.1 _ _ (Fin.rev_lt_rev.2 hij)
    · rw [hval]; exact hv.2 _
  · simp only [superDiag, Finset.sum_filter]
    simp_rw [hval]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun p => ?_
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun q => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]

    have hiff : ((q.rev : Fin n) : ℕ) = (p.rev : ℕ) + 1 ↔ (p : ℕ) = q + 1 := by
      simp only [Fin.val_rev]; have := p.isLt; have := q.isLt; omega
    by_cases h : (p : ℕ) = q + 1
    · rw [if_pos h, if_pos (hiff.2 h), inv_apply_succ hu p.rev q.rev (hiff.2 h)]
    · rw [if_neg h, if_neg (mt hiff.1 h), neg_zero]

end GlobalTheory.UnipFlip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadical
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThetaRad

theorem mem_unipRad_iff_entries {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, blk e j ≤ blk e i → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨d, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    rcases hij.lt_or_eq with hlt | rfl
    · rw [mem_parab_iff.1 hp c d i j hlt, Matrix.one_apply_ne]
      intro hh
      have := congrArg Sigma.fst (e.injective hh)
      exact hlt.ne' this
    · rw [hd]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun c i j => ?_⟩
    · rw [h i j hij.le, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]

theorem blk_stdBlocks_two {a b n : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    blk (stdBlocks ![a, b] h) p = if (p : ℕ) < a then 0 else 1 := by
  obtain ⟨⟨c, i⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [blk_apply, stdBlocks_val]
  fin_cases c
  · simpa using i.2
  · simp

theorem longElt_conj_apply {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) (i j : Fin n) :
    ((longElt n R * g * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      (g : Matrix (Fin n) (Fin n) R) i.rev j.rev := by
  simp only [longElt, Units.val_mul, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev (fun x _ hx => by rw [if_neg (fun hh => hx (by rw [hh, Fin.rev_rev])), mul_zero]) (by simp)]
  simp

end GlobalTheory.ThetaRad

theorem GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  intro R _ n a b h h' u hu
  have hn : a + b = n := by simpa [Fin.sum_univ_two] using h
  have hv := GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 (inv_mem hu)
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.2 fun i j hij => ?_
  rw [GlobalTheory.ThetaRad.longElt_conj_apply]
  change ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ i.rev j.rev = _
  rw [Matrix.transpose_apply]
  rw [hv j.rev i.rev ?_]
  · simp [Matrix.one_apply, Fin.rev_inj, eq_comm]
  · rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two] at *
    have hi := i.2; have hj := j.2
    simp only [Fin.val_rev] at *
    split_ifs at hij ⊢ <;> first | exact le_refl _ | decide | (exfalso; omega) | (exfalso; revert hij; decide)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeRestrictionInjectiveOnMultiplicity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LowRes

theorem multW_lowRes_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), ∀ w ∈ (y.L F.lv2).MultW i, w ∘ₗ (y.L F.lv2).embK i = 0 → w = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hP _ y i w hw hK
  have hM := hP.char.base.models
  set M := R.MW i (sg0 D A3.A)
  let w' : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap M := PiTensorProduct.lift.symm w'
  have hU : U ∈ Mult R.θ M _ _ := (Mult.mem_multT _ _ _ _ w').1 hw
  have h0 : U = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ M R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ U hU (fun v => by
        have e := LinearMap.congr_fun hK (PiTensorProduct.tprod ℂ v)
        have e2 : w' (PiTensorProduct.map (fun τ => (lowT M τ).subtype) (PiTensorProduct.tprod ℂ v)) = 0 := e
        rw [PiTensorProduct.map_tprod] at e2
        have e3 : PiTensorProduct.lift U (PiTensorProduct.tprod ℂ (fun τ => (lowT M τ).subtype (v τ))) = 0 := by
          rw [show PiTensorProduct.lift U = w' from LinearEquiv.apply_symm_apply _ w']; exact e2
        rw [PiTensorProduct.lift.tprod] at e3
        exact e3)
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  show w' = 0
  rw [← hUw, h0, map_zero]

end GlobalTheory.Mem.R3.Rw.LowRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureLeOfCover
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselIntegrable

theorem measure_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] {𝓕 K : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hK : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) : μ 𝓕 ≤ μ K := by
  rw [h.measure_eq_tsum K]
  refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hK n
  exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩

theorem norm_besChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) {A B : HSp D}
    {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (n : GA D B) : ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
    rw [e]
    exact hψ _
  · exact norm_one

theorem besInt : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, BesInt D := by
  intro hP D θ hθ ψ hψ A B ι hι d μ 𝓕 hq μN 𝓕N hμN h𝓕N s hs φ F hφ hF hA
  obtain ⟨-, a2, a3, a4, a5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, b2, b3, b4, b5, -, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have : Countable (NFlagQ B d.e) :=
    Function.Injective.countable (f := fun x : NFlagQ B d.e => (⟨x.1.1, x.2⟩ : GQ B))
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ B => z.1) h))
  have : SecondCountableTopology (NFlag B d.e) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨⟨K, hK, hcov⟩, -⟩ := GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B d.ρ d.e d.e_iso
  have hfin : μN 𝓕N < ⊤ := (measure_le_of_cover _ μN h𝓕N hcov).trans_lt hK.measure_lt_top
  obtain ⟨C, hC⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ hF.1 hF.2
  obtain ⟨s', hs', hs'', -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  have hsc : Continuous s := by
    rw [show s = s' from funext fun h => (hs'' h _).1 (hs h)]
    exact hs'
  have hχ := (GlobalTheory.T.besselCharacter_generic_character_laws D ψ hψ A B ι hι d).2.2.1
  have hb : ∀ (h : GA D A) (n : NFlag B d.e), ‖star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B))‖ ≤ ‖φ h‖ * C := fun h n => by
    rw [norm_mul, norm_mul, norm_star, norm_star, norm_besChar hψ.1.2.1, mul_one]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have hc : Continuous fun p : GA D A × NFlag B d.e => star (φ p.1) * F ((p.2 : GA D B) * s p.1 * (d.y : GA D B)) *
      star (besChar ψ d (p.2 : GA D B)) :=
    ((hφ.cont.comp continuous_fst).star.mul (hF.1.cont.comp
      (((continuous_subtype_val.comp continuous_snd).mul (hsc.comp continuous_fst)).mul continuous_const))).mul
      (hχ.comp continuous_snd).star
  refine ⟨fun h => Measure.integrableOn_of_bounded (M := ‖φ h‖ * C) hfin.ne
    (hc.comp (Continuous.prodMk_right h)).measurable.aestronglyMeasurable (.of_forall (hb h)), ?_⟩
  have hcusp : IsCuspForm θ A φ := ⟨hφ, hA.elim (fun h r C hC => absurd hC (h r C)) id⟩
  have hint := GlobalTheory.Mem.Th.petInt_of_cuspRapidDecay hP D θ hθ A μ 𝓕 hq (fun _ => 1) φ (isAutFunSm_const θ A 1) hcusp
  simp only [star_one, one_mul] at hint
  have : IsFiniteMeasure (μN.restrict 𝓕N) := isFiniteMeasure_restrict.2 hfin.ne
  refine Integrable.mono' ((hint.norm.mul_const C).mul_const (μN.real 𝓕N))
    (hc.stronglyMeasurable.integral_prod_right' (ν := μN.restrict 𝓕N)).aestronglyMeasurable (.of_forall fun h => ?_)
  exact norm_setIntegral_le_of_norm_le_const hfin fun n _ => hb h n

end GlobalTheory.Mem.BesselIntegrable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_multT_of_equivariant' : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ) (L : SmT M →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → V.SigOK → AllPlus M → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → FiniteDimensional ℂ (SmT M) → Function.Injective (inclT M) → IsTensAct M π → (∀ x, IsAutFun V (L x)) → (∀ x, ∀ k ∈ J, ∀ g, L x (g * k) = χ k * L x g) → (∀ τ u x, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x)) → L ∈ MultT θ M J χ := by
  first | exact @GlobalTheory.DefLiftMult.mem_multT_of_equivariant | exact GlobalTheory.DefLiftMult.mem_multT_of_equivariant | (intros; apply GlobalTheory.DefLiftMult.mem_multT_of_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjection
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

set_option maxHeartbeats 4000000 in

theorem pr_lvC_eq_lv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) v (c : ((I.rec7 l Z).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i (le_of_succ_m h2) c) (z' : LdG (I.rec7 l Z) i (le_of_succ_m h2) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (I.rec7 l Z) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  intro B X I hI hP l Z H F hS hC u i h1 h2 v c
  have hi := le_of_succ_m h2
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hL⟩ := hsp i hi
  have hlat := (hL u I.mu0).1 c
  obtain ⟨hF, hFC⟩ := hS u
  have hcl : clsCrd (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hlat
  have hres := hF.res
  have hsep := sepElt_of_ok l.pr u
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hLd : Ld (I.rec7 l Z) u i hi c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.Lsh := by
    show dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (clsCrd (I.rec7 l Z) u i hi c) = _
    rw [hg, hcl]
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ _
  have hPv : (F u).atT.Pv v = (show (B.primes X).vT u from v).1.asIdeal := by
    ext x
    show (F u).atT.res v x = 0 ↔ _
    rw [hres]
    exact Ideal.Quotient.eq_zero_iff_mem (I := (show HeightOneSpectrum (𝓞 B.fields.E) from v.1).asIdeal)
  have hLk : Formalism.L2.Forms.Lk (F u).atT i hi v c = (((I.stp u I.mu0 i).rep c).1.1.deco).1.LshKer v := by
    rw [lv_LshKer_eq _ hsep v]
    show clsCrd (I.rec7 l Z) u i hi c ⊔ (F u).atT.Pv v • Ld (I.rec7 l Z) u i hi c = _
    rw [hLd, hcl, hPv]
    rfl
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 (I.rec7 l Z).host.E, s = cO B.fields.E ((B.primes X).piT u) := ⟨_, rfl⟩
  have hu : (F u).atT.res v s ≠ 0 := by
    rw [hres, hs]
    exact fun h => hsep.off v (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hd : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Ld (I.rec7 l Z) u i hi c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.N := fun x hx => by
    rw [hs]
    exact (((I.stp u I.mu0 i).rep c).1.1.deco).2.smul_Lsh_mem_N hsep.conj (hLd ▸ hx)
  have hk : ∀ x : Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E, x ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c →
      s • x ∈ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v := fun x hx => by
    rw [hs]
    exact (le_sup_left : _ ≤ (((I.stp u I.mu0 i).rep c).1.1.deco).1.dnN v) (lv_smul_LshKer_mem _ hsep v (hLk ▸ hx))
  refine ⟨fun z z' e => ?_, fun z z' e => ?_⟩
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.pr i hi v c (s • ⟨x', hx⟩) (hd x' hx)
    have e2 := (hFC.1 i h1 h2).1 v c (s • ⟨x', hx'⟩) (hd x' hx)
    rw [((F u).lv i hi).pr_smul] at e1
    rw [((F u).lvC i h1 h2).pr_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)
  · obtain ⟨x, hx⟩ := z
    obtain ⟨x', hx'⟩ := z'
    have e' : x' = x := e
    subst e'
    have e1 := hF.prk i hi v c (s • ⟨x', hx⟩) (hk x' hx)
    have e2 := (hFC.1 i h1 h2).2 v c (s • ⟨x', hx'⟩) (hk x' hx)
    rw [((F u).lv i hi).prk_smul] at e1
    rw [((F u).lvC i h1 h2).prk_smul] at e2
    exact smul_right_injective _ hu (e2.trans e1.symm)

end GlobalTheory.Mem.Col2.HAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinorsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_laplacian_kills_product_of_minors : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ n) → ∀ τ (a b : Fin m), p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n)) = 0 := by
  first | exact @GlobalTheory.MinorHarmonic.laplacian_delta | exact GlobalTheory.MinorHarmonic.laplacian_delta | (intros; apply GlobalTheory.MinorHarmonic.laplacian_delta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetric
section
noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
open scoped Matrix ComplexOrder

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem map_conj_bVV {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (i : VVIdx lam) :
    MvPolynomial.map ((starRingEnd ℂ).comp φ) (bVV K lam i : VV K lam).1 = MvPolynomial.map φ (bVV K lam i : VV K lam).1 := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [bVV_coe, hQ, MvPolynomial.map_map, MvPolynomial.map_map]
  rw [RingHom.ext_int (((starRingEnd ℂ).comp φ).comp (Int.castRingHom K)) (φ.comp (Int.castRingHom K))]

theorem map_smul_pol {K : Type} [Field K] {σ : Type} (φ : K →+* ℂ) (r : K) (p : MvPolynomial σ K) :
    MvPolynomial.map φ (r • p) = φ r • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem pairB_conj_map {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (y : VV K lam) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map φ y.1)) (MvPolynomial.map φ y.1) =
      star (fun i => φ ((bVV K lam).repr y i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map φ *ᵥ (fun i => φ ((bVV K lam).repr y i)) := by
  have hy : y.1 = ∑ i, (bVV K lam).repr y i • (bVV K lam i : VV K lam).1 := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]
    rw [Submodule.coe_sum]
    rfl
  rw [MvPolynomial.map_map, hy]
  simp only [map_sum, map_smul_pol, map_conj_bVV, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← GlobalTheory.PeriodOnStep.map_pairB, dotProduct, Matrix.mulVec, Matrix.map_apply, GlobalTheory.TestLat.Compare.gramB, Matrix.of_apply, pairBK_apply,
    Pi.star_apply, RingHom.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem herm_mk {K : Type} [Field K] {ι : Type} [Fintype ι] (M : Matrix ι ι K) (φ : K →+* ℂ) (hM : (M.map φ).PosDef)
    (a : ι → K) :
    star (fun i => (InfinitePlace.mk φ).embedding (a i)) ⬝ᵥ M.map (InfinitePlace.mk φ).embedding *ᵥ
        (fun i => (InfinitePlace.mk φ).embedding (a i)) =
      star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h]
    have hr := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => φ (a i))
    have hc : starRingEnd ℂ (star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i))) =
        star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) :=
      Complex.conj_eq_iff_im.2 (Complex.nonneg_iff.1 hr).2.symm
    rw [← hc]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
      map_mul, starRingEnd_apply, star_star]

theorem normAt_sq_eq_cSum {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V) :
    ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) =
      cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  have h0 := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH B.wts I.Ch I.sel (I.tup a) I.Ps hX).2 (InfinitePlace.mk B.embLL)
  refine (h0 (x : (MtildeH B.wts I.Ch hX I.sel (I.tup a) I.Ps).V)).trans ?_
  rw [cSum_apply]
  unfold GSD.ipAt
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold cTerm
  rw [GSD.wt_eq]
  congr 1
  rw [GlobalTheory.PeriodClassSum.pairAt_eq, GlobalTheory.PeriodClassSum.row_gramV]
  exact (herm_mk _ _ (GlobalTheory.PeriodClassSum.gramB_posDef _ _) _).trans (pairB_conj_map _ _ _).symm

end GlobalTheory.Mem.Df
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTupleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_twistPlace_referenceTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  first | exact @GlobalTheory.Mem.Col2.TC.not_underQ_mu0 | exact GlobalTheory.Mem.Col2.TC.not_underQ_mu0 | (intros; apply GlobalTheory.Mem.Col2.TC.not_underQ_mu0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundlesStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → ∀ A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ B ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ h h' : Mat m K, Bears S₁ φ₁ A h p → Bears S₁ φ₁ B h' p → Bears S₂ φ₂ B h' q → Bears S₂ φ₂ A h q := by
  first | exact @GlobalTheory.FlagBundle.Bears.transfer | exact GlobalTheory.FlagBundle.Bears.transfer | (intros; apply GlobalTheory.FlagBundle.Bears.transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExtStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (x : Sp k ⟶ X.X) (p₁ : Sp k ⟶ Y₁.X) (p₂ : Sp k ⟶ Y₂.X), CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap σ ≫ x) (spMap σ ≫ p₁) (spMap σ ≫ p₂) := by
  first | exact @GlobalTheory.FlagBundle.coBear_spMap | exact GlobalTheory.FlagBundle.coBear_spMap | (intros; apply GlobalTheory.FlagBundle.coBear_spMap <;> assumption)
end

