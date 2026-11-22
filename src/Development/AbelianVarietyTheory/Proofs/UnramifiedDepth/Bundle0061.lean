import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0059
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0057
import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateModuleEigenspaceDimEqLieAlgebraSum

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartCokernelLengthLeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_cokernel_length_le : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp), H.P = 0 → H.PL = 0 → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (rm : ℕ), (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ cw : NNReal, HasLen v O (htCoker H w.e w.bar) cw ∧ (v (algebraMap O C (p : O)) : ℝ) ^ (((w.n : ℝ) * rm) / ((p : ℝ) - 1)) ≤ cw := by
  first | exact @GlobalTheory.ChF.abelian_coker_bound | exact GlobalTheory.ChF.abelian_coker_bound | (intros; apply GlobalTheory.ChF.abelian_coker_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CommGroupCoboundaryRelationIdentity
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.TangentCob

section Schemes
variable {X Y : Scheme.{0}}

theorem top_le_stalk_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) :
    ⊤ ≤ (Y.fromSpecStalk y ≫ f) ⁻¹ᵁ U ↔ f y ∈ U := by
  refine (top_le_iff_cpt (A := Y.presheaf.stalk y) _ U).trans ?_
  rw [Scheme.Hom.comp_apply,
    show Y.fromSpecStalk y (cpt (Y.presheaf.stalk y)) = y from Scheme.fromSpecStalk_closedPoint]

theorem valR_stalk (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    valR (A := Y.presheaf.stalk y) (Y.fromSpecStalk y ≫ f) U a = gs f y U a := by
  rw [gs_eq f y U h]
  exact (GlobalTheory.HolHom.valR_comp (A := Y.presheaf.stalk y) _ f U a).trans
    (GlobalTheory.FormalValue.valR_fromSpecStalk y (f ⁻¹ᵁ U) h _)

theorem exists_unit (p : Y ⟶ X) (e : Γ(Y, ⊤)) (he : e * e = 0) (U : X.Opens) (a : Γ(X, U)) :
    ∃ u : Γ(Y, p ⁻¹ᵁ U)ˣ, ∀ y, p y ∈ U →
      (gm (𝟙 Y) y (p ⁻¹ᵁ U) u).val = 1 + gs (𝟙 Y) y ⊤ e * gs p y U a := by
  let e' : Γ(Y, p ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op).hom e
  have he' : e' * e' = 0 := by rw [← map_mul, he, map_zero]
  let b : Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom a
  refine ⟨⟨1 + e' * b, 1 - e' * b, by linear_combination (-(b * b)) * he', by linear_combination (-(b * b)) * he'⟩,
    fun y hy => ?_⟩
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ U := hy
  rw [← gs_unit _ y _ hy']
  show gs (𝟙 Y) y (p ⁻¹ᵁ U) (1 + e' * b) = _
  rw [gs_add _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_pull (𝟙 Y) p y U hy, Category.id_comp,
    gs_eq _ y _ hy', map_one, map_one]

theorem commGroup_coboundary_relation_identity {G : Type} [CommGroup G] {a b c d f g u v : G} (h : a * v = b * u) (h₁ : c * d = f)
    (h₂ : g * a = f) : g * u = c ^ (1 : ℤ) * b ^ (-1 : ℤ) * (d * v) := by
  rw [zpow_one, zpow_neg, zpow_one, _root_.mul_mul_mul_comm, h₁, ← h₂, _root_.mul_assoc, _root_.mul_left_comm a,
    h, inv_mul_cancel_left]

theorem exists_isGen (L : LB X) (hL : L.IsLB) (m p : Y ⟶ X) (e : Γ(Y, ⊤)) (he : e * e = 0) (H : ∀ j, Γ(X, L.U j))
    (hmp : ∀ (y : Y) (U : X.Opens), p y ∈ U → m y ∈ U)
    (h : ∀ (y : Y) (j j' : L.ι), p y ∈ L.U j → p y ∈ L.U j' → gs m y (L.U j ⊓ L.U j') (L.g j j').val =
      gs p y (L.U j ⊓ L.U j') (L.g j j').val *
        (1 + gs (𝟙 Y) y ⊤ e * (gs p y (L.U j) (H j) - gs p y (L.U j') (H j')))) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![m, p] ![1, -1]), c.IsGen := by
  choose u hu using fun j => exists_unit p e he (L.U j) (H j)
  have h0 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → m y ∈ L.U (j 0) :=
    fun j y hy => LB.wchart_le L ![m, p] j 0 hy
  have h1 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → p y ∈ L.U (j 1) :=
    fun j y hy => LB.wchart_le L ![m, p] j 1 hy
  let s : ∀ j : Fin 2 → L.ι, Γ(Y, LB.wchart L ![m, p] j)ˣ := fun j =>
    res (show LB.wchart L ![m, p] j ≤ m ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) from
      fun y hy => ⟨h0 j y hy, hmp y _ (h1 j y hy)⟩) (pullU m _ (L.g (j 0) (j 1))) *
    res (show LB.wchart L ![m, p] j ≤ p ⁻¹ᵁ L.U (j 1) from fun y hy => h1 j y hy) (u (j 1))
  have hs : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → gm (𝟙 Y) y _ (s j) =
      gm m y _ (L.g (j 0) (j 1)) * gm (𝟙 Y) y _ (u (j 1)) := fun j y hy => by
    have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L ![m, p] j := hy
    rw [map_mul, gm_res _ y _ hy', gm_res _ y _ hy',
      gm_pull (𝟙 Y) m y (L.U (j 0) ⊓ L.U (j 1)) ⟨h0 j y hy, hmp y _ (h1 j y hy)⟩, Category.id_comp]
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L ![m, p] j ⊓ LB.wchart L ![m, p] j' := hy
  refine ((gm_res _ y _ hy' _).trans (hs j y hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L ![m, p] ![1, -1] (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy' _).trans (hs j' y hy.2)))).symm)
  have a0 := h0 j y hy.1
  have a1 := h1 j y hy.1
  have b0 := h0 j' y hy.2
  have b1 := h1 j' y hy.2
  have key : gm m y _ (L.g (j 1) (j' 1)) * gm (𝟙 Y) y _ (u (j' 1)) =
      gm p y _ (L.g (j 1) (j' 1)) * gm (𝟙 Y) y _ (u (j 1)) := by
    apply Units.ext
    have hee : gs (𝟙 Y) y ⊤ e * gs (𝟙 Y) y ⊤ e = 0 := by
      rw [← gs_mul (𝟙 Y) y ⊤ trivial, he, gs_eq (𝟙 Y) y ⊤ trivial, map_zero, map_zero]
    rw [Units.val_mul, Units.val_mul, hu _ y a1, hu _ y b1, ← gs_unit m y (L.U (j 1) ⊓ L.U (j' 1)) ⟨hmp y _ a1, hmp y _ b1⟩,
      ← gs_unit p y (L.U (j 1) ⊓ L.U (j' 1)) ⟨a1, b1⟩, h y _ _ a1 b1]
    linear_combination (gs p y (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val *
      (gs p y (L.U (j 1)) (H (j 1)) - gs p y (L.U (j' 1)) (H (j' 1))) * gs p y (L.U (j' 1)) (H (j' 1))) * hee
  have c1 := gm_cocycle hL m y a0 b0 (hmp y _ b1)
  have c2 := gm_cocycle hL m y a0 (hmp y _ a1) (hmp y _ b1)
  rw [Fin.prod_univ_two]
  exact commGroup_coboundary_relation_identity key c1 c2

end Schemes

variable {k : Type} [CommRing k] {B : Over (Sp k)}

theorem exists_alg (D : Type) [CommRing D] [Algebra k D] {S : Type} [CommRing S] (r : Sp S ⟶ (algOver k D ⊗ B).left) :
    ∃ (_ : Algebra k S) (φ : D →ₐ[k] S) (r' : algOver k S ⟶ algOver k D ⊗ B), r'.left = r ∧
      r' ≫ fst _ _ = algOverHom φ ∧ ∀ d : D, φ d =
        valR (r ≫ (fst (algOver k D) B).left) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d) := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of D) (S := CommRingCat.of S) (r ≫ (fst (algOver k D) B).left)
  letI : Algebra k S := (ψ.hom.comp (algebraMap k D)).toAlgebra
  refine ⟨this, ⟨ψ.hom, fun _ => rfl⟩, Over.homMk r ?_, rfl, Over.OverMorphism.ext hψ.symm, fun d => ?_⟩
  · rw [← Over.w (fst (algOver k D) B), ← Category.assoc]
    erw [← hψ]
    exact (Spec.map_comp _ _).symm
  · erw [← hψ]
    have := GlobalTheory.HolHom.valR_spMap ψ.hom (𝟙 (Sp D)) ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d)
    rw [Category.comp_id, GlobalTheory.HolHom.valR_eq (𝟙 (Sp D)) ⊤ le_top] at this
    refine Eq.trans ?_ this.symm
    refine congrArg ψ.hom ?_
    simp [GlobalTheory.HolHom.evalHom, Scheme.Hom.appLE]

end GlobalTheory.TangentCob

namespace GlobalTheory
open TangentCob

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndomorphismPairW0Statement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endomorphism_pair_w0 : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∃ W W' : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C, IsEnd (Y.rawSelf p) V W W' ∧ W + W' = 1 ∧ (∀ (v : Fin 2 × Fin dd → C) (x : Fin 2 × Fin dd), W.mulVec v x = linAct (Y.B.A.act Y.w0) (fun i => v (x.1, i)) x.2) ∧ ∑ col : Fin 2, inCol col (un1 (Y.B.hL C Y.h Y.w0)) = hEnd (Y.rawSelf p) 1 W := by
  first | exact @GlobalTheory.ActionEndSelf.exists_endomorphism_w0 | exact GlobalTheory.ActionEndSelf.exists_endomorphism_w0 | (intros; apply GlobalTheory.ActionEndSelf.exists_endomorphism_w0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsChOfTors
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem apply_eq_zero_of_killed {R : Type} [CommRing R] {d : ℕ} {F : Fin d → PS R 2 d} {N : ℕ}
    {φ : PS R 1 d →ₐ[R] R} (h : Killed F N φ) {f : PS R 1 d}
    (hf : f ∈ Ideal.span (Set.range (mulF F N))) : φ f = 0 := by
  have hle : Ideal.span (Set.range (mulF F N)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact h j
  exact hle hf

private theorem killed_pow_mono {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (p : ℕ) {m n : ℕ}
    (hmn : m ≤ n) {φ : PS R 1 d →ₐ[R] R} (h : Killed F.F (p ^ m) φ) : Killed F.F (p ^ n) φ := by
  intro j
  apply apply_eq_zero_of_killed h
  have hn : p ^ n = p ^ (n - m) * p ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [hn]
  exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow R d F).2.2.1 _ _ (Ideal.subset_span ⟨j, rfl⟩)

private theorem addOf_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  unfold addOf ev
  have h : (fun q : Fin 2 × Fin d => (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) q.1 q.2)
      = MvPowerSeries.X := by
    funext ⟨a, b⟩
    fin_cases a <;> rfl
  rw [h, MvPowerSeries.subst_self]
  rfl

private theorem hasSubst_law {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) :
    MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![F.F] : Fin 1 → Pt R 2 d) q.1 q.2) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  rintro ⟨a, b⟩
  fin_cases a
  exact F.const b

theorem exists_isCh_of_tors : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Tors p F.F φ → Tors p F.F φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, IsCh F.F u ∧ ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH κ hmul hone
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  choose w hw using fun k : ℕ => GlobalTheory.T.exists_series_eq_character_on_torsion p C v O hv d F hFH k κ
    (fun φ φ' ψ h h' hs => hmul φ φ' ψ ⟨k, h⟩ ⟨k, h'⟩ hs) hone
  obtain ⟨hsep, hsepT⟩ := GlobalTheory.T.formalGroup_series_separated_by_torsion p C v O hv d F hFH
  have hsame : ∀ {m n : ℕ}, m ≤ n → ∀ φ, Killed F.F (p ^ m) φ → φ (w m) = φ (w n) := by
    intro m n hmn φ h
    apply hinj
    rw [hw m φ h, hw n φ (killed_pow_mono F p hmn h)]
  set J : Ideal (PS O 1 d) := (Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* PS O 1 d) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS O 1 d)) with hJ
  have hcomp : IsAdicComplete J (PS O 1 d) :=
    (mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2 inferInstance
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → w m ≡ w n [SMOD (J ^ m • ⊤ : Submodule (PS O 1 d) (PS O 1 d))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h1 := hsep m (w m - w n) (fun φ h => by rw [map_sub, hsame hmn φ h, sub_self])
    have h2 : Ideal.span (Set.range (mulF F.F (p ^ m))) ≤ J ^ (m + 1) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow O d F).2.2.2 p m j
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (h2 h1)
  obtain ⟨u, hu⟩ := hcomp.toIsPrecomplete.prec hcauchy
  have hval : ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
    rintro φ ⟨k, hk⟩
    rw [← hw k φ hk]
    congr 1
    have hH : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
    rw [← sub_eq_zero]
    apply hH.haus
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    obtain ⟨N, hN⟩ := (GlobalTheory.T.formalDisc_points_valuationIntegers p C v O hv (Fin 1 × Fin d)).2.2 φ n
    have h1 := hu (max N k)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := hN _ (Ideal.pow_le_pow_right (le_max_left N k) h1)
    rw [map_sub, ← hsame (le_max_right N k) φ hk] at h2
    rw [← neg_sub]
    exact neg_mem h2
  obtain ⟨inst, hsum, hzero, hkill⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  refine ⟨u, ⟨?_, ?_⟩, hval⟩
  · apply hinj
    rw [← hzero u, hval _ ⟨0, (hkill _ _).1 (smul_zero _)⟩, hone _ hzero, map_one]
  · rw [addOf_pt, ← sub_eq_zero]
    apply GlobalTheory.T.eq_zero_of_forall_pair_points_valuationIntegers p C v O hv d (Tors p F.F) hsepT
    intro Φ φ φ' h0 h1 hφ hφ'
    let ψ : PS O 1 d →ₐ[O] O := Φ.comp (MvPowerSeries.substAlgHom (hasSubst_law F))
    have hψ : ∀ f, Φ (ev (n := 2) ![F.F] f) = ψ f := by
      intro f
      simp only [ψ, AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]
      rfl
    have hs : IsSum F.F φ φ' ψ := ⟨Φ, h0, h1, hψ⟩
    have hT : Tors p F.F ψ := by
      obtain ⟨k, hk⟩ := hφ
      obtain ⟨k', hk'⟩ := hφ'
      refine ⟨max k k', (hkill _ _).1 ?_⟩
      rw [(hsum _ _ _).1 hs, smul_add, (hkill _ _).2 (killed_pow_mono F p (le_max_left k k') hk),
        (hkill _ _).2 (killed_pow_mono F p (le_max_right k k') hk'), add_zero]
    apply hinj
    rw [map_sub, map_mul, hψ, h0, h1, map_sub, map_mul, hval _ hT, hval _ hφ, hval _ hφ',
      hmul _ _ _ hφ hφ' hs, sub_self, map_zero]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecond
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowKernel

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_sum {ι : Type} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  V.v.map_lt_sum (by simp) h

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_int_mul hb ha

theorem mm_ge {a : C} (h : V.MM a) : V.Ge 0 a := le_of_lt h

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_div {a b : C} (hb : b ≠ 0) (h : V.v b ≤ V.v a) : V.Ge 0 (a / b) := by
  show (0 : WithTop ℝ) ≤ V.v (a / b)
  have e : V.v a = V.v (a / b) + V.v b := by rw [← V.v.map_mul, div_mul_cancel₀ a hb]
  have hb' : V.v b ≠ ⊤ := by simpa using hb
  rw [e] at h
  exact (WithTop.add_le_add_iff_right hb').mp (by simpa using h)

theorem card_add_le {σ : Type} [Fintype σ] (p : σ → Prop) [DecidablePred p] {N M : ℕ}
    (A : Fin N → σ → C) (B : Fin M → σ → C) (hA : IndepMod V A) (hAp : ∀ ν s, ¬ p s → A ν s = 0)
    (hB : IsSat V B) (hBp : ∀ μ s, ¬ p s → B μ s = 0) (hAB : ∀ ν μ, V.MM (∑ s, A ν s * B μ s)) :
    N + M ≤ (Finset.univ.filter p).card := by
  classical
  obtain ⟨-, W, hW, hBW⟩ := hB
  let F : Fin N ⊕ Fin M → {s // p s} → C := Sum.elim (fun ν s => A ν s.1) (fun μ s => W s.1 μ)
  have hF : LinearIndependent C F := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ s, p s → ∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ = 0 := by
      intro s hs
      have := congrFun hg ⟨s, hs⟩
      simpa [F, Fintype.sum_sum_type, Finset.sum_apply] using this
    have h2 : ∀ μ', g (Sum.inr μ') = -∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
      intro μ'
      have h3 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = 0 :=
        Finset.sum_eq_zero fun s _ => by
          by_cases hs : p s
          · rw [h1 s hs, zero_mul]
          · rw [hBp μ' s hs, mul_zero]
      have h4 : ∑ s, (∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = g (Sum.inr μ') := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ μ, ∑ s, g (Sum.inr μ) * W s μ * B μ' s = g (Sum.inr μ) * if μ' = μ then 1 else 0 := by
          intro μ
          rw [← hBW μ' μ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        simp [this]
      have h5 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s) * B μ' s = ∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun s _ => by ring
      simp only [add_mul, Finset.sum_add_distrib] at h3
      rw [h4, h5] at h3
      linear_combination h3
    have h6 : ∀ ν, g (Sum.inl ν) = 0 := by
      by_contra hc
      push_neg at hc
      obtain ⟨ν1, hν1⟩ := hc
      obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (g (Sum.inl ν)))
        ⟨ν1, Finset.mem_univ _⟩
      have h0 : g (Sum.inl ν0) ≠ 0 := by
        intro h0
        have := hmin ν1 (Finset.mem_univ _)
        rw [h0, V.v.map_zero, top_le_iff] at this
        exact hν1 (by simpa using this)
      have hint : ∀ ν, V.Ge 0 (g (Sum.inl ν) / g (Sum.inl ν0)) := fun ν =>
        ge_div h0 (hmin ν (Finset.mem_univ _))
      have key := hA (fun ν => g (Sum.inl ν) / g (Sum.inl ν0)) hint (fun s => by
        by_cases hs : p s
        · have e : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
              ∑ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) * W s μ := by
            have e1 : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
                (g (Sum.inl ν0))⁻¹ * ∑ ν, g (Sum.inl ν) * A ν s := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e2 : ∀ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) =
                -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) := by
              intro μ
              rw [h2 μ, mul_neg, neg_neg, Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e3 : ∑ μ, -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) * W s μ =
                -((g (Sum.inl ν0))⁻¹ * ∑ μ, g (Sum.inr μ) * W s μ) := by
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun ν _ => by ring
            simp only [e2]
            rw [e1, e3]
            linear_combination (g (Sum.inl ν0))⁻¹ * h1 s hs
          rw [e]
          exact mm_sum fun μ _ => mm_mul_int (mm_sum fun ν _ => mm_int_mul (hint ν) (hAB ν μ)) (hW s μ)
        · simp only [hAp _ s hs, mul_zero, Finset.sum_const_zero]
          exact mm_zero) ν0
      simp only [div_self h0] at key
      exact not_mm_one key
    intro i
    cases i with
    | inl ν => exact h6 ν
    | inr μ => rw [h2 μ]; simp [h6]
  have := hF.fintype_card_le_finrank
  simpa [Fintype.card_subtype] using this

theorem mm_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.MM a) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact mm_int_mul ((mm_ge h).pow m) h

theorem independenceBoundCondition_of_rankMaximalCondition : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H := by
  intro C _ V d _ I _ κ _ X hL hR H h2 hA g a ha N w x hgood hV hind
  classical
  haveI := hL.closed
  have hstep := CharacteristicFromRanks.alt_step X.big hR.big_compl hA
  have hb1 : X.big (1 - g) (a + 1) := (hR.big_compl g (a + 1)).2 fun h => (hstep g a).1 h ha
  have hb2 : ¬ X.big (1 - g) (a + 1 + 1) := fun h => (hstep (1 - g) (a + 1)).1 h hb1
  obtain ⟨M, w', x', hgood', hsupp, hsat, hcard⟩ :=
    GlobalTheory.T.exists_saturated_good_vectors_small_corank C V d (I (1 - g)) (JJ I (1 - g)) (RawChart.cart (H (1 - g))) (a + 1)
  have c1 := hR.rk_big (1 - g) (a + 1) hb1
  have c2 := hR.rk_small (1 - g) (a + 1 + 1) hb2
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  have hind' : IndepMod V (fun ν => (RawChart.cart (H g)).c0' (x ν)) := by
    intro c hc hmm
    choose co hco using fun ν => IsAlgClosed.exists_pow_nat_eq (c ν) (Nat.pos_of_ne_zero hl)
    have hcoi : ∀ ν, V.Ge 0 (co ν) := fun ν => ge_of_pow hl (by rw [hco]; exact hc ν)
    have hG := Cart.Good.comb Finset.univ (fun ν _ => hcoi ν) (fun ν _ => hgood ν)
    have h3 := h2 hA g a ha _ _ hG (fun q => by
      rw [Cart.c0'_comb]
      simp only [hco]
      exact hmm q)
    have h4 := hind co hcoi (fun k => by simpa [Finset.sum_apply] using h3 k)
    intro ν
    rw [← hco ν]
    exact mm_pow hl (h4 ν)
  have key := card_add_le (V := V) (fun c : I (1 - g) => X.ty (1 - g) c = a + 1)
    (fun ν => (RawChart.cart (H g)).c0' (x ν)) w' hind'
    (fun ν s hs => by
      have := (hgood ν).1.2.2 1 (Sum.inr s) (by simpa [RawChart.cart, RawChart.tyC] using hs)
      simp [Cart.c0', this])
    hsat (fun μ s hs => hsupp μ s hs)
    (fun ν μ => GlobalTheory.T.goodCurves_pairing_mem_maxIdeal C V d I κ X hL H g a (a + 1) (w ν) (x ν) (w' μ) (x' μ) (hgood ν) (hgood' μ) (hV ν))
  have hcard' : X.n + X.j ≤ M + X.j' := by
    rw [← c1, ← c2]
    convert hcard <;> rfl
  have key' : N + M ≤ X.n + X.j := by
    rw [← c1]
    convert key
  omega

end GlobalTheory.RowKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowExponentPartMemGaugedCurveLogarithmsStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powExponentPart_mem_gaugedCurveLogarithms : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ a ∈ Cv X V g, ((fun i => typ V.l (a.1 i), fun q => typ V.l (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.typ_mem_Cv | exact GlobalTheory.RowLaw.typ_mem_Cv | (intros; apply GlobalTheory.RowLaw.typ_mem_Cv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateModuleEigenspaceDimEqLieAlgebraSumStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_eigenspace_dim_eq_lieAlgebra_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (τ : OE →+* C), eigDim C (fun a : OE => (H.ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) τ = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ + eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) := by
  first | exact @GlobalTheory.ChF.eigDim_tate | exact GlobalTheory.ChF.eigDim_tate | (intros; apply GlobalTheory.ChF.eigDim_tate <;> assumption)
end

