import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameAtSmallPlace
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.TameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Groups

variable {G Γ : Type} [Group G] [Group Γ]

def conjIn (H J : Subgroup G) (g : G) : Subgroup G where
  carrier := {x | x ∈ H ∧ g⁻¹ * x * g ∈ J}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have := J.mul_mem ha' hb'
    convert this using 1
    group
  one_mem' := by
    refine ⟨H.one_mem, ?_⟩
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have := J.inv_mem ha'
    convert this using 1
    group

def conjInEquiv (H J : Subgroup G) (g : G) : {γ : H // g⁻¹ * (γ : G) * g ∈ J} ≃ conjIn H J g where
  toFun γ := ⟨γ.1.1, γ.1.2, γ.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_conj (ι : Γ →* G) (J : Subgroup G) {I : Type} (y : I → G) (hrep : Bridge.IsReps ι J y)
    (hfin : ∀ i, Finite (Bridge.stab ι J (y i))) (g : G) : Finite {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := by
  obtain ⟨c, ⟨γ₀, k, hg⟩, -⟩ := hrep g
  haveI := hfin c
  let f : Bridge.stab ι J (y c) → {γ : ι.range // g⁻¹ * (γ : G) * g ∈ J} := fun s =>
    ⟨⟨ι (γ₀ * s * γ₀⁻¹), γ₀ * s * γ₀⁻¹, rfl⟩, by
      have hs : (y c)⁻¹ * ι s * (y c) ∈ J := by
        have := s.2
        simpa [Bridge.stab, Subgroup.mem_comap, MulAut.conj_apply] using this
      have := J.mul_mem (J.mul_mem (J.inv_mem k.2) hs) k.2
      convert this using 1
      rw [hg]
      simp only [map_mul, map_inv]
      group⟩
  refine Finite.of_surjective f ?_
  rintro ⟨⟨_, a, rfl⟩, ha⟩
  refine ⟨⟨γ₀⁻¹ * a * γ₀, ?_⟩, ?_⟩
  · have := J.mul_mem (J.mul_mem k.2 ha) (J.inv_mem k.2)
    simp only [Bridge.stab, Subgroup.mem_comap, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
    convert this using 1
    rw [hg]
    simp only [map_mul, map_inv]
    group
  · apply Subtype.ext
    apply Subtype.ext
    show ι (γ₀ * (γ₀⁻¹ * a * γ₀) * γ₀⁻¹) = ι a
    congr 1
    group

end Groups

set_option maxHeartbeats 1600000 in

theorem rat_eq_one {D : D7} (V : TH.HSp D) (l : ℕ) (hl : l.Prime) (hN : V.rank + 1 < l)
    (hirr : Irreducible (Polynomial.cyclotomic l D.host.E)) (x : Bridge.Gf V) (hx : x ∈ (Bridge.ratF V).range)
    (hxl : x ^ l = 1) : x = 1 := by
  obtain ⟨q, rfl⟩ := hx
  have hq := q.2
  simp only [Formalism.L2.Theta.GQ, GlobalTheoryTheory.GenusMassVolumes.HFinIn, Subgroup.mem_subgroupOf, GlobalTheoryTheory.GenusMassVolumes.HFin, Subgroup.mem_map] at hq
  obtain ⟨u, -, hu⟩ := hq
  let φ : D.host.E →+* GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F))
  have key : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val = u.val.map φ := by
    have hu' : (q.1 : Formalism.L2.Theta.GA D V).1 =
        Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) u := hu.symm
    have h1 : ((Bridge.ratF V q : Bridge.Gf V) : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
        Formalism.UG.bc (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
          (q.1 : Formalism.L2.Theta.GA D V).1 := rfl
    rw [h1, hu']
    ext i j
    rfl
  rcases subsingleton_or_nontrivial (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) with hs | hs
  · apply Subtype.ext
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _
  · have hφ : Function.Injective φ := φ.injective
    have h2 := congrArg (fun z : Bridge.Gf V => (z : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val) hxl
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one] at h2
    rw [key] at h2
    have h3 : φ.mapMatrix (u.val ^ l) = φ.mapMatrix 1 := by
      rw [map_pow, map_one, RingHom.mapMatrix_apply]
      exact h2
    have hu1 : u.val ^ l = 1 := Matrix.map_injective hφ h3
    have hu2 : u.val = 1 :=
      GlobalTheory.no_order_l_of_cyclotomic_irreducible D.host.E l V.rank _ hl hirr hN hu1
    apply Subtype.ext
    apply Units.ext
    rw [key, hu2]
    have h4 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ = 1 := Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)
    rw [h4]
    rfl

theorem tameAt_of_smallAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m)
    (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (hNr : P.Nr = (Vc D j).rank) (hS : SmallAt p j P w) :
    TameAt p j w := by
  obtain ⟨hl, hN, hd, -, -⟩ := hS
  intro g
  have hfin : Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} :=
    finite_conj (Bridge.ratF (Vc D j)) (levJ p j (p.R.mu w)) (p.R.B.L j (p.R.mu w)).pres.y (p.R.B.L j (p.R.mu w)).pres.reps
      (fun c => Finite.of_equiv _ ((p.R.B.L j (p.R.mu w)).pres.stabI c).toEquiv) g
  refine ⟨hfin, ?_⟩
  intro hdvd
  haveI : Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime := ⟨hl⟩
  rw [Nat.card_congr (conjInEquiv _ _ g)] at hdvd
  haveI : Finite (conjIn (Bridge.ratF (Vc D j)).range (levJ p j (p.R.mu w)) g) := Finite.of_equiv _ (conjInEquiv _ _ g)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (Formalism.EigenvalueLevelCeiling.plc w) hdvd
  have hirr := GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr D.host.E (Formalism.EigenvalueLevelCeiling.plc w) hl hd
  have hxl : (x : Bridge.Gf (Vc D j)) ^ (Formalism.EigenvalueLevelCeiling.plc w) = 1 := by
    rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one]
    rfl
  have h1 := rat_eq_one (Vc D j) (Formalism.EigenvalueLevelCeiling.plc w) hl (hNr ▸ hN) hirr x x.2.1 hxl
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, orderOf_one] at hx
  exact hl.one_lt.ne hx

theorem tameSt : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  unfold GlobalTheory.ExpTie.InRange GlobalTheory.BigOn.AtPts Formalism.MainNotions.Closed GlobalTheory.BigTop.EvPt
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ => ?_⟩⟩⟩
  intro j P W hD _ w _ _ hS
  exact tameAt_of_smallAt p j P w hD.Nr hS

end GlobalTheory.TameStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEV0EqICPqRows
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BigTop.Fun

open Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData
open scoped InnerProductSpace Matrix

theorem iC_cpt_eq_theta_toR {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (z : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding z) = X.Θ t (X.jR t (cr.toR X.zs b t z)) := by
  conv_rhs => rw [pi_eq_sum_univ z]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, iC, lin, Fintype.linearCombination_apply, cpt]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 4
  ext j
  simp [Pi.single_apply, eq_comm]

theorem theta_jR_eq_zero_of_perp {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hJ : X.JIsoR cv) (hZ : X.RatZ) (t : Bs.Tup) (x : A.FR t) (hx : ∀ w ∈ X.Z t, cv.hR t w x = 0) :
    X.Θ t (X.jR t x) = 0 := by
  have hperp : ∀ m ∈ Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))), ⟪m, X.jR t x⟫_ℂ = 0 := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨w, hw, rfl⟩ := hm
      rw [hJ t w x, hx w hw, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  refine ext_inner_left ℂ fun e => ?_
  rw [inner_zero_right, ← LinearMap.adjoint_inner_left]
  apply hperp
  rw [hZ.1 t]
  exact LinearMap.mem_range_self _ _

theorem sub_zE_Pq_mem_U {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (hs : Function.Surjective (B.Pq ℓ Z).mulVec)
    (y : Fin (B.nV ℓ) → K) : y - (B.zE ℓ Z).mulVec ((B.Pq ℓ Z).mulVec y) ∈ B.U ℓ Z := by
  set E := B.zE ℓ Z with hE
  set H := B.HV ℓ with hH
  have hdet : IsUnit (Eᴴ * H * E).det := by
    by_contra hu
    have h0 : B.Pq ℓ Z = 0 := by
      show (Eᴴ * H * E)⁻¹ * (Eᴴ * H) = 0
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.zero_mul]
    apply hu
    have hd : B.dZ ℓ Z = 0 := by
      by_contra hne
      obtain ⟨i⟩ : Nonempty (Fin (B.dZ ℓ Z)) := ⟨⟨0, Nat.pos_of_ne_zero hne⟩⟩
      obtain ⟨x, hx⟩ := hs (Pi.single i 1)
      rw [h0, Matrix.zero_mulVec] at hx
      have := congrFun hx i
      simp at this
    have : IsEmpty (Fin (B.dZ ℓ Z)) := ⟨fun i => by have := i.2; omega⟩
    rw [Matrix.det_isEmpty]
    exact isUnit_one
  have hO := (Formalism.DivisionValues.exponent_index_lattice.isOrthProj_formula H E hdet).2
  intro z hz
  obtain ⟨c, rfl⟩ : ∃ c, E.mulVec c = z := by
    have h := (Formalism.L2.DIV.subspace_image_spec K _ (B.Z0 ℓ Z)).2
    have : z ∈ LinearMap.range (subE (B.Z0 ℓ Z)).mulVecLin := by rw [h]; exact hz
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩
  rw [Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have : Eᴴ *ᵥ (H *ᵥ (y - E *ᵥ (B.Pq ℓ Z *ᵥ y))) = (Eᴴ * H * (1 - E * B.Pq ℓ Z)) *ᵥ y := by
    simp only [Matrix.mulVec_sub, Matrix.mul_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_one, Matrix.mul_assoc]
  rw [this]
  show star c ⬝ᵥ (Eᴴ * H * (1 - E * ((Eᴴ * H * E)⁻¹ * (Eᴴ * H)))) *ᵥ y = 0
  rw [hO, Matrix.zero_mulVec, dotProduct_zero]

theorem csum_goodPart_perp_eq_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (s : ℕ) (hB : B.Ok s) (v0 : InfinitePlace K) (hv : Formalism.DivisionValues.IsConjAt v0) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (hZ : ∀ g, Z ≤ Z.comap (B.r g))
    (u : Fin (B.nV ℓ) → K) (hu : u ∈ B.U ℓ Z) (w : B.S.Forms) (hw : w ∈ Z) :
    B.S.csum (w : B.S.Cl → B.S.V) ((B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u) : B.S.Forms) : B.S.Cl → B.S.V) = 0 := by
  classical
  have hpe := good_at_spec K v0 hv G ℓ.X hX ℓ.P ℓ.ψ
  obtain ⟨hO, hEP⟩ := orthogonal_projection_spec K v0 hv B.S (hB.hpos v0) G B.r hB.act _ hpe.idem hpe.selfAdj
  have hadj := group_action_matrix_adjoint K B.S G B.r hB.act (goodAt ℓ.X ℓ.P ℓ.ψ)
  rw [hpe.selfAdj] at hadj
  have hE : B.vE ℓ = B.S.cutE B.r (goodAt ℓ.X ℓ.P ℓ.ψ) := rfl
  set Gm := B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) with hGm
  set E := B.vE ℓ with hEdef
  set x := B.S.basis.equivFun w with hx
  have hw' : (w : B.S.Cl → B.S.V) = B.S.I x := by simp [CSD.I, x]
  have hv' : ((B.S.basis.equivFun.symm (E.mulVec u) : B.S.Forms) : B.S.Cl → B.S.V) = B.S.I (E.mulVec u) := rfl
  rw [hw', hv', CSD.csum_sum, ← Formalism.DivisionValues.RationalHermitianForm.hform_apply]
  have hGE : Gm *ᵥ (E *ᵥ u) = E *ᵥ u := by
    have hO1 : B.S.cutPr B.r (goodAt ℓ.X ℓ.P ℓ.ψ) * E = 1 := hO.1
    rw [← hEP, Matrix.mulVec_mulVec, ← hE, Matrix.mul_assoc, hO1, Matrix.mul_one]
  rw [← hGE]
  have hmove : Formalism.DivisionValues.hform B.S.H x (Gm *ᵥ (E *ᵥ u)) = Formalism.DivisionValues.hform B.S.H (Gm *ᵥ x) (E *ᵥ u) := by
    rw [Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.mulVec_mulVec, ← hadj,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  set z' := B.S.cutPr B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ x with hz'def
  have hGx : Gm *ᵥ x = E *ᵥ z' := by rw [← hEP, ← Matrix.mulVec_mulVec, hE]
  have hz' : z' ∈ B.Z0 ℓ Z := by
    show (E.mulVecLin z') ∈ B.coord Z
    rw [Matrix.mulVecLin_apply, ← hGx]
    refine ⟨B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) w, ?_, ?_⟩
    · show (B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) w) ∈ Z
      simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t hw)
    · simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hGm,
        CSD.gaMat, Matrix.sum_mulVec, Matrix.smul_mulVec]
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 1
      show B.S.basis.equivFun (B.r t w) = (LinearMap.toMatrix B.S.basis B.S.basis (B.r t)) *ᵥ (B.S.basis.equivFun w)
      rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  rw [hmove, hGx, ← Formalism.L2.DIV.hform_cut]
  have hP : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hH : Eᴴ * B.S.H * E = (Nat.card ℓ.P : K) • B.HV ℓ := by
    simp only [hEdef, BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, smul_smul, mul_inv_cancel₀ hP, one_smul]
  rw [hH, Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot, Matrix.smul_mulVec, dotProduct_smul, ← Formalism.DivisionValues.RationalHermitianForm.hform_eq_dot,
    hu z' hz', smul_zero]

set_option maxHeartbeats 1000000 in

theorem theta_eV0_eq_iC_Pq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), (p.R.toCx3 p.F).Θ t ((p.R.toCx3 p.F).jR t (eV0 p t y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp t y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  rw [iC_cpt_eq_theta_toR, TieModel.toR_eq]
  let y' : Fin ((p.P.A3.A.fam.R t).nV (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)) → D.what₂.LL := y
  have hu := sub_zE_Pq_mem_U (p.P.A3.A.fam.R t) (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) ((p.R.toCx3 p.F).zs.Z t)
    ((hCx.wf false).Pq_surj t) y'
  have h := theta_jR_eq_zero_of_perp _ p.F.cv hCx.jIsoR hCx.ratZ t (eV0 p t (y' - ((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y))) (fun w hw =>
    csum_goodPart_perp_eq_zero (p.P.A3.A.fam.R t) 1 (hp.ok.ok2.what₂ t) _ hp.ok.ok2.conj _ hp.ok.ok2.irr _
      (fun g => Submodule.map_le_iff_le_comap.mp (hCx.stable.1 t (Sum.inr g))) _ hu w hw)
  erw [(eV0 p t).map_sub] at h
  have h2 := ((p.R.toCx3 p.F).jR t).map_sub (eV0 p t y') (eV0 p t (((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y)))
  erw [h2, map_sub] at h
  exact sub_eq_zero.mp h

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopNodeFormWeightAbsLeLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize.WtSize

theorem wtOf_abs_le {n : ℕ} {E : Finset ℚ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ E, |(x : ℝ)| ≤ B) (i : Fin n) :
    |(((wtOf n E).w i : ℤ) : ℝ)| ≤ B + n + 1 := by
  unfold wtOf
  split_ifs with h
  · show |((⌊GlobalTheory.SignedHC.highestWeight E h.1 i⌋ : ℤ) : ℝ)| ≤ _
    set y := GlobalTheory.SignedHC.highestWeight E h.1 i with hy
    have hy' : (y : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 i : ℝ) - (((n : ℝ) - 1) / 2 - ((i : ℕ) : ℝ)) := by
      rw [hy]; unfold GlobalTheory.SignedHC.highestWeight; push_cast; ring
    have hd := hB _ (GlobalTheory.SignedHC.descEnum_mem E h.1 i)
    have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
    have f1 : ((⌊y⌋ : ℤ) : ℝ) ≤ y := by exact_mod_cast Int.floor_le y
    have f2 : (y : ℝ) < ⌊y⌋ + 1 := by exact_mod_cast Int.lt_floor_add_one y
    rw [abs_le] at hd ⊢
    constructor <;> linarith [hd.1, hd.2]
  · show |((((0 : Fin n → ℤ) i : ℤ)) : ℝ)| ≤ _
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
    linarith

end GlobalTheory.InfSize.WtSize

namespace GlobalTheory.InfSize.WtSize

theorem weightX_abs_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (τ : D.what₂.Tau) {x : ℚ}
    (hx : x ∈ (num D 1 τ).weightX D.R.m) : |(x : ℝ)| ≤ 5 * large₂.sc.b := by
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have hs' := hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs'
  have hS := large₂.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have htN : D.R.t + 1 ≤ bigN D := by
    unfold bigN
    have := Nat.le_mul_of_pos_left (D.R.t + sLen D + 1) (by omega : 0 < D.R.m)
    omega
  have hsN : sLen D ≤ gap D 1 := by omega
  have hγ0 : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : (0 : ℝ) ≤ D.R.m := by positivity
  have htR : (D.R.t : ℝ) + 1 ≤ large₂.sc.b := by
    have h1 : ((D.R.t + 1 : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast htN.trans hNg
    push_cast at h1
    linarith
  have hsR : (sLen D : ℝ) ≤ large₂.sc.b := by
    have h1 : (sLen D : ℝ) ≤ gap D 1 := by exact_mod_cast hsN
    linarith
  have hmγ : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by positivity
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, hl1, hl2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    have ev : (D.hc τ).v ⟨0, by omega⟩ = ((num D 1 τ).v 2 : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨0, by omega⟩
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨0, by omega⟩
    rw [ev] at v0 v1
    have ha : (num D 1 τ).a i = ((num D 1 τ).v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) := rfl
    have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v 2 : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v 2 : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    rw [ha]
    push_cast
    have p1 : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ0
    have p2 : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, hi2, hik, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have hik' : i ≤ D.R.k := hik
    have ev : (D.hc τ).v ⟨i - 2, by omega⟩ = ((num D 1 τ).v (i - 2 + 2) : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨i - 2, by omega⟩
    rw [show i - 2 + 2 = i by omega] at ev
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨i - 2, by omega⟩
    rw [ev] at v0 v1
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v i : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v i : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    unfold GlobalTheory.SignedHC.GridData.vHalf
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hs τ hi1 hi2
    have ec : (num D 1 τ).cen i = cen D 1 τ i := rfl
    have es : (num D 1 τ).s = sLen D := rfl
    rw [ec, es]
    have hs1 : (((sLen D - 1 : ℕ)) : ℝ) ≤ large₂.sc.b := by
      have : ((sLen D - 1 : ℕ) : ℝ) ≤ sLen D := by exact_mod_cast Nat.sub_le _ _
      linarith
    have ha' : (a : ℝ) + 1 ≤ ((sLen D - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have c0' : (0 : ℝ) ≤ (cen D 1 τ i : ℝ) := by exact_mod_cast c0
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have hl2' : l ≤ D.R.m := hl2
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hs τ (j := l - 1) (by omega)
    rw [show l - 1 + 1 = l by omega] at e0 e1
    have et : (num D 1 τ).t = D.R.t := rfl
    rw [et]
    have ha' : (a : ℝ) + 1 ≤ (D.R.t : ℝ) + 1 := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have e0' : (0 : ℝ) ≤ ((num D 1 τ).e l : ℝ) := by exact_mod_cast e0
    push_cast
    rw [abs_le]; constructor <;> linarith

theorem wt_top_abs_le : ∃ K1 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), sc.cGap = 1 → ∀ τ i, |(((wt G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ K1 * large₂.sc.b := by
  refine ⟨7, fun D large₂ hs T L sc G hc τ i => ?_⟩
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have h4 := (isLeast_gap D 1).1.2.1
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have hn := GlobalTheory.DefRank.rank_le_bigN G (.top D.R.m) (show D.R.m ≤ D.R.m from le_rfl)
  have hnb : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ large₂.sc.b := by
    have : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast hn.trans hNg
    linarith
  have e : wt G (.top D.R.m) τ = wtOf (G.V (.top D.R.m)).rank ((num D 1 τ).weightX D.R.m) := by
    show wtOf _ (GlobalTheory.SignedHC.entries (Node.par D sc.cGap (.top D.R.m) τ)) = _
    rw [hc]
    exact congrArg _ (GlobalTheory.SignedHC.entries_plus _)
  rw [e]
  have := wtOf_abs_le (B := 5 * large₂.sc.b) (by linarith) (fun x hx => weightX_abs_le hs τ hx) i
  linarith

end GlobalTheory.InfSize.WtSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeightStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  first | exact @GlobalTheory.CuspEmb.twoLevels_mul_mem_SS | exact GlobalTheory.CuspEmb.twoLevels_mul_mem_SS | (intros; apply GlobalTheory.CuspEmb.twoLevels_mul_mem_SS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsPullMemStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_pull_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ) (h : U), F ∈ M.SS la → M.pull h F ∈ M.SS la := by
  first | exact @GlobalTheory.CuspEmb.pull_mem_SS | exact GlobalTheory.CuspEmb.pull_mem_SS | (intros; apply GlobalTheory.CuspEmb.pull_mem_SS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsRestrictHolInvariantStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelCuspForms_restrict_holInvariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → M.res F ∈ HA M := by
  first | exact @GlobalTheory.CuspEmb.res_mem_HA | exact GlobalTheory.CuspEmb.res_mem_HA | (intros; apply GlobalTheory.CuspEmb.res_mem_HA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainTransporterMemDomain
section
set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

namespace GlobalTheory.TwoLevelsDom

theorem lact_tr_mem_dom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom :=
  fun M g c _x hx => GlobalTheory.CuspEmb.lact_tr_mem M g c hx

end GlobalTheory.TwoLevelsDom
end

