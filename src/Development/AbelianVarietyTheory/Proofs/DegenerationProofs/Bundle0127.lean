import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitMapSnd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0118
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqZeroOfPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.LatChar

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩
  rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem mem_span_iff {p : ℕ} [Fact p.Prime] {J A : Type} [Fintype J] [Nonempty J] (B : Matrix J J (PadicAlgCl p))
    (hB : B.det ≠ 0) (T : Set A) (v : A → J → PadicAlgCl p) (κ : ℝ) (hκ : 0 < κ)
    (hle : ∀ a ∈ T, ∀ i, ‖B.mulVec (v a) i‖ ≤ κ)
    (hdet : ∀ c : J → OO p, (∀ a ∈ T, ‖∑ i, (c i : PadicAlgCl p) * B.mulVec (v a) i‖ < κ) →
      ∀ i, ‖(c i : PadicAlgCl p)‖ < 1) (e : J → PadicAlgCl p) :
    e ∈ Submodule.span (OO p) (Set.range B) ↔ ∀ a ∈ T, ‖e ⬝ᵥ v a‖ ≤ κ := by
  have key : ∀ (c : J → PadicAlgCl p) (w : J → PadicAlgCl p),
      (B.vecMul c) ⬝ᵥ w = ∑ i, c i * B.mulVec w i := fun c w => (Matrix.dotProduct_mulVec c B w).symm
  have hvec : ∀ c : J → OO p, ∑ i, c i • B i = B.vecMul fun i => (c i : PadicAlgCl p) := fun c => by
    ext j
    rw [Finset.sum_apply]
    rfl
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => B i) _).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ a ha
    rw [hvec, key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hκ.le fun i _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_OO_iff _).1 (c i).2)).trans (hle a ha i)
  · intro h
    obtain ⟨c, rfl⟩ : ∃ c, B.vecMul c = e := ⟨B⁻¹.vecMul e, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.vecMul_one]⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖c i‖
    by_cases h1 : ‖c i₀‖ ≤ 1
    · exact ⟨fun i => ⟨c i, (mem_OO_iff _).2 ((hi₀ i).trans h1)⟩, hvec _⟩
    exfalso
    rw [not_le] at h1
    have h0 : 0 < ‖c i₀‖ := one_pos.trans h1
    have h0' : c i₀ ≠ 0 := norm_pos_iff.1 h0
    have := hdet (fun i => ⟨c i / c i₀, (mem_OO_iff _).2 (by
      rw [norm_div]; exact (div_le_one h0).2 (hi₀ i))⟩) (fun a ha => by
        have h2 := h a ha
        rw [key] at h2
        have e : ∑ i, c i / c i₀ * B.mulVec (v a) i = (∑ i, c i * B.mulVec (v a) i) / c i₀ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        show ‖∑ i, c i / c i₀ * B.mulVec (v a) i‖ < κ
        rw [e, norm_div, div_lt_iff₀ h0]
        exact h2.trans_lt (lt_mul_of_one_lt_right hκ h1)) i₀
    simp [div_self h0'] at this

theorem mem_lattice_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)) (κ : ℝ), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → u.Link σ b → b.det ≠ 0 → 0 < κ → (∀ a ∈ l.yy.ker, IsGreatest (Set.range fun i => ‖(b.map (algebraMap _ (PadicAlgCl p))).mulVec (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i‖) κ) → ∀ e : S.J → PadicAlgCl p, e ∈ Submodule.span (OO p) (Set.range (b.map (algebraMap _ (PadicAlgCl p)))) ↔ ∀ a ∈ l.yy.ker, ‖e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩)‖ ≤ κ := by
  intro L o Ω _ _ _ _ S ρ p _ y₀ u l σ cls md b κ hBig hy hL hb hκ hmax e
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre L o Ω S ρ p y₀ u).2.2.2.1, hBig.1, hBig.2.1⟩
  obtain ⟨hN, htor, -⟩ := GlobalTheory.T.specialFibre_torsion_eq_reductions L o Ω S ρ p y₀ u l σ cls md hy
  have pb : IsPullback md.r md.Φ.G.hom u.G.hom (rPt p ≫ spMap u.j) := md.cart.1
  have hs : Smooth u.G.hom := md.smooth.smooth
  have : Smooth md.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  refine mem_span_iff _ ?_ (l.yy.ker : Set S.Gam) (fun a i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) κ hκ
    (fun a ha i => (hmax a ha).2 ⟨i, rfl⟩) (fun c hc => ?_) e
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hb
  have hev : ∀ v : S.J → kb p, MvPolynomial.eval v (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) *
      MvPolynomial.X i) = ∑ i, IsLocalRing.residue (OO p) (c i) * v i := fun v => by simp
  have hz := GlobalTheory.T.form_vanishes_of_torsion_torusExtension L.1 L.2.1 (kb p) md.Φ S.g S.N (S.r * S.N) _ S.J _ md.F md.pol hB md.good md.dim hN 1
    (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) * MvPolynomial.X i)
    (Nat.mul_pos (pow_pos (by have := hB.four; omega) _) (Nat.factorial_pos _))
    (MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X _ i).C_mul _) ?_
  · have h0 := lin_eq_zero md.Φ md.good (fun i => IsLocalRing.residue (OO p) (c i)) fun v hv =>
      (hev v).symm.trans (hz v hv)
    intro i
    exact (not_isUnit_OO_iff _).1 fun hu => (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu (congrFun h0 i)
  intro x hx
  obtain ⟨a, ha, z, a', hz, hg, hA, hr⟩ := htor x hx
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists md.isLB σ z
  obtain ⟨⟨i₀, -, hi₀⟩, x', hx', hc'⟩ := GlobalTheory.T.exists_unit_weightZero_integral_coords L.1 L.2.1 p u.V u.j u.G S.g S.N (S.r * S.N) _ l.q _ S.J σ cls
    md hB z w hz hw
  have hxx : x'.left = x.left := pb.hom_ext (hx'.trans hr) ((Over.w x').trans (Over.w x).symm)
  refine ⟨_, hxx ▸ hc', ?_⟩
  have h1 := hL a' _ (hA ▸ (GlobalTheory.T.torsionValues_coords_operator_permute L o Ω S ρ).1 _ y₀ a)
  have h2 := CrdCalc.crd_map (OO p).subtype hw
  rw [show spMap (OO p).subtype ≫ z = u.toG a' from hg] at h2
  obtain ⟨t, ht⟩ := CrdCalc.crd_unique h2 h1
  have hn : κ ≤ ‖(t : PadicAlgCl p)‖ := by
    obtain ⟨i, hi⟩ := (hmax a ha).1
    rw [← hi]
    beta_reduce
    rw [ht i, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 (w i).2)
  have h3 := hc a ha
  have e3 : ∑ i, (c i : PadicAlgCl p) * (b.map (algebraMap _ (PadicAlgCl p))).mulVec
      (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i = t * ((∑ i, c i * w i : OO p) : PadicAlgCl p) := by
    rw [show ((∑ i, c i * w i : OO p) : PadicAlgCl p) = (OO p).subtype (∑ i, c i * w i) from rfl, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht i, map_mul, mul_left_comm]
    rfl
  rw [e3, norm_mul] at h3
  have h4 : ‖((∑ i, c i * w i : OO p) : PadicAlgCl p)‖ < 1 := by
    by_contra h5
    exact absurd h3 (not_lt.2 (hn.trans (le_mul_of_one_le_right (norm_nonneg _) (not_lt.1 h5))))
  rw [hev]
  have h5 : IsLocalRing.residue (OO p) (∑ i, c i * w i) = 0 := by
    by_contra h6
    exact (not_isUnit_OO_iff _).2 h4 ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h6)
  simpa using h5

end GlobalTheory.ZH.LatChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcFOver
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcExt
open GlobalTheory.TorusExt

theorem exists_arcF_over : Laws → BrGtSt → BrWpSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), (∀ x, f (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ A : ArcF D R F, ∃ A' : ArcF D R F', A'.D₀ = A.D₀ ∧ A.Over f A' := by
  intro hL hGt hWp E _ _ _ H D R _ _ F F' _ _ _ _ _ _ _ f hf₀ A
  have hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext hf₀
  obtain ⟨J', hg, hJ₀⟩ := exists_gauge f A.D₀.P.isLB A.ν.good
  obtain ⟨N', ν', e₁, hth⟩ := GlobalTheory.GaugeValues.exists_numOf hL R A.D₀ A.even A.bimult F' J' hg A.ν.th A.ν.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = A.ν.J ψ := e₁ ▸ hJ₀
  have G := (hGt R A.D₀ A.even A.bimult F A.N A.ν).2.2.2.2
  have G' := (hGt R A.D₀ A.even A.bimult F' N' ν').2.2.2.2
  let I := numHom f hf A.ν ν' hJ hth
  have hw : ∀ k, 1 ≤ k → ∀ (p p' : QkPt A.D₀ F k) (z : F), WeilQkIs A.D₀ F k p p' z →
      WeilQkIs A.D₀ F' k (qkExt A.bimult f hf p) (qkExt A.bimult f hf p') (f z) := fun k hk p p' z h => by
    obtain ⟨q, hq, -⟩ := (G k).1 p
    obtain ⟨q', hq', -⟩ := (G k).1 p'
    obtain ⟨r, hr, -⟩ := (G' k).1 (qkExt A.bimult f hf p)
    obtain ⟨r', hr', -⟩ := (G' k).1 (qkExt A.bimult f hf p')
    have a := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq hr
    have a' := numHom_qPt f hf A.bimult A.ν ν' hJ hth hq' hr'
    rw [hWp R A.D₀ A.even A.bimult F' N' ν' k hk _ _ _ _ _ hr hr',
      (GlobalTheory.T.hom_transport_alt F F' f A.N N' I).2.2.2.1 k q q' r r' a.1 a.2 a'.1 a'.2,
      (hWp R A.D₀ A.even A.bimult F A.N A.ν k hk _ _ _ _ _ hq hq').1 h]
    rfl
  choose q' hq' using fun (n : ℕ) (a : D.La) => ((G' n).1 (qkExt A.bimult f hf (A.I.ev n a))).exists
  refine ⟨{ D₀ := A.D₀, oa := A.oa, even := A.even, bimult := A.bimult, w0 := A.w0, ρ := f A.ρ
            ρ_sq := by rw [← map_pow, A.ρ_sq, map_neg]; simp
            det := fun σ => ?_
            I := tateExt f hf A.bimult hL A.I hw, N := N', ν := ν', q := q', hq := hq', closed := inferInstance },
    rfl, I, rfl, fun _ _ => rfl, fun a y => ?_, fun n a _ => ?_⟩
  · obtain ⟨τ, rfl⟩ := DetExtend.exists_factor f σ
    obtain ⟨n, h₁, h₂⟩ := A.det τ
    have := A.D₀.P.isAb.smooth
    refine ⟨n, ?_, h₂.trans (by
      by_cases h : τ H.rt = A.ρ
      · rw [if_pos h, if_pos (show f.comp τ H.rt = f A.ρ from congrArg f h)]
      · rw [if_neg h, if_neg (show ¬ f.comp τ H.rt = f A.ρ from fun e => h (f.injective e))])⟩
    have e : spMap ((algebraMap (FractionRing R) F').comp (algebraMap R _)) =
        spMap f ≫ spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
      rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hf]
    rw [e]
    exact (DetExtend.lieMult_extend f _ _ τ n).2 h₁
  · refine ν'.eX.injective ((eX_numHom f hf A.ν ν' hJ hth _).trans ?_)
    show A.ν.eX (A.ν.eX.symm _) = ν'.eX (ν'.eX.symm (a • ν'.eX (I.e y)))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, eX_numHom]
  · have h := numHom_qPt f hf A.bimult A.ν ν' hJ hth (A.hq n a) (hq' n a)
    exact ⟨q' n a, h.1, h.2, (N'.qEq_equivalence n).refl _⟩

end GlobalTheory.ArcExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_cExt :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (K : Type) [Field K] [Algebra (FractionRing W) K] [Algebra.IsAlgebraic (FractionRing W) K], ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (gam : K →+* C), (∀ x, gam (algebraMap (FractionRing W) K x) = algebraMap (FractionRing W) C x) ∧ CExt W (IsLocalRing.maximalIdeal W) C := by
  intro W _ _ _ K _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπm : π ∈ IsLocalRing.maximalIdeal W := hmax ▸ Ideal.mem_span_singleton_self π
  obtain ⟨C, i1, i2, i3, i4, i5, h1, h2⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing W (FractionRing W) hπ.ne_zero hπm
      (r := 1 / 2) (by norm_num) (by norm_num)
  have hle : ∀ r : W, ‖algebraMap (FractionRing W) C (algebraMap W _ r)‖ ≤ 1 :=
    fun r => (h1 _).2 ⟨r, rfl⟩
  let g : K →ₐ[FractionRing W] C := IsAlgClosed.lift
  refine ⟨C, i1, i2, i3, i4, i5, g.toRingHom, fun x => g.commutes x, hle, fun r hr => ?_⟩
  rw [hmax, Ideal.mem_span_singleton] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [map_mul, map_mul, norm_mul, h2]
  have := hle s
  linarith

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegDataPsiOfSectionNonzeroFibres
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
namespace GlobalTheory.PsiRing

theorem ne_zero_of_secCmp {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)} {xe : D'.X ≃+ D.X}
    (hw : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α}
    (h : SecCmp D D' β v xe f f') (h' : ∀ α, ∃ j, (f' α).f j ≠ 0) (α : D.X) : ∃ j, (f α).f j ≠ 0 := by
  obtain ⟨x, rfl⟩ := xe.surjective α
  by_contra h0
  push Not at h0
  obtain ⟨j, hj⟩ := h' x
  refine hj (ThetaScalar.eq_zero_of_sval D'.P.isLB _ (fun y J' hJ' => ?_) j)
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB y
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (((snd (𝟙_ _) D'.P.A).left ≫ β) ≫ D.P.A.hom)
  let p : T ⟶ D.P.A := Over.homMk ((snd (𝟙_ _) D'.P.A).left ≫ β) rfl
  have e := h x _ (𝟙 _) (lift (toUnit T) p).left
    ((congrArg (fun q => q.left) (lift_snd (toUnit T) p)).trans (Category.id_comp _).symm) y J J' hJ hJ'
  rw [ThetaScalar.sval_eq_zero _ h0 _ y hJ] at e
  exact (Units.mul_right_eq_zero _).1 e.symm

theorem exists_generic_map {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V}
    (hφ : Function.Injective φ) : ∃ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ := by
  have hi : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hφ
  obtain ⟨g, e⟩ : ∃ g : FractionRing R →+* FractionRing V,
      g.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
    ⟨IsLocalization.lift (M := nonZeroDivisors R) (g := (algebraMap V (FractionRing V)).comp φ) fun y =>
      IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (nonZeroDivisors.coe_ne_zero y)), IsLocalization.lift_comp _⟩
  have e' : spMap g ≫ jK R = jK V ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  exact ⟨spMap g, e'⟩

theorem exists_degData_of_thetaNZ : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ φ : R →+* V, Function.Injective φ → (IsLocalRing.maximalIdeal V).comap φ = I → ∀ (D : DegPre R) (D' : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G') (U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), Under U' U₀.toUnifPre → ThetaNZ G U.P.L.L → ∃ (psi : _) (h : _) (Dd : DegData R I) (hD : IsPullDeg φ (withPsi D psi h) D'.toPre), Dd.toPre = withPsi D psi h ∧ hD.e.hom.left ≫ pullback.fst _ _ = C.β ∧ HEq hD.w C.v ∧ hD.xe = C.xe := by
  intro h₁ h₂ hE R _ _ _ I hA V _ _ _ hV φ hφ hI D D' A A' G _ _ G' _ _ U U' U₀ F C hU hθ
  obtain ⟨hR, -, -, hP, -⟩ := hA
  have := hV.1
  have hV' : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : IsLocalRing.maximalIdeal V ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  have hIm : I.map φ ≤ IsLocalRing.maximalIdeal V := Ideal.map_le_iff_le_comap.2 hI.ge
  obtain ⟨hσ₁, hσ₂⟩ := GlobalTheory.T.fibrewiseNonzeroSection_prod_and_baseChange R V I _ φ D D'.toPre A G A' G' U U' F C
  obtain ⟨σ, hσ⟩ := hσ₁ hθ
  obtain ⟨f, hf, -⟩ := CompleteBaseExpansion.main h₁ h₂ hE R I hR hP.ne_top D A G U 1 σ
  obtain ⟨σ', f', hf', hσσ, hff⟩ := ExpCmp.expT_cmp R V I _ φ hIm D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := GlobalTheory.T.psiRel_of_expT' h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 := by
    refine GlobalTheory.T.forall_term_ne_zero_of_psiRelation V D'.toPre f' hrel' ?_
    obtain ⟨T, y, z, J, α, hJ, -, -, hu⟩ := GlobalTheory.T.exists_expansionTerm_unit_closedFibre V _ hm D'.toPre A' G' U' 1 σ' f' hf' (hσ₂ 1 σ σ' hσσ hσ)
    refine ⟨α, ?_⟩
    by_contra h0
    push Not at h0
    rw [ThetaScalar.sval_eq_zero _ h0 _ z hJ] at hu
    exact not_isUnit_zero hu
  obtain ⟨psi, h, hrel⟩ := exists_psi_psiRel h₁ h₂ R D f (ne_zero_of_secCmp C.pbB.1.w hcmp hne')
  let E : DegPre R := withPsi D psi h
  have hrelE : PsiRel E (𝟙_ _) f := hrel
  have hrig : RigCmp φ E D'.toPre C.β C.v := GlobalTheory.T.rigidification_comparison_uniformisation R V I _ φ hm hIm D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := exists_generic_map hφ
  have hpsi : PsiCmp E D'.toPre C.β C.v C.xe gam :=
    GlobalTheory.T.psiCmp_of_secCmp' R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp hrelE hrel' (hne' 0) gam hgam
  have hev : E.PsiEven :=
    GlobalTheory.T.psiEven_descend_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    GlobalTheory.T.tauBimult_of_baseChange' h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨hD, hD₁, hD₂, hD₃⟩ :=
    GlobalTheory.T.exists_isPullDeg_of_comparison R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi hbi
  obtain ⟨ga, a, hS⟩ := exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hS χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hS hrelE hth χ q (b χ) hq (hb χ)
  have hbI : ∀ χ : D.X, χ ≠ 0 → b χ ∈ I := fun χ hχ => by
    obtain ⟨x, rfl⟩ := C.xe.surjective χ
    obtain ⟨m, hm₁, hm₂⟩ := GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi ga a hS x _
      (D'.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
    refine hI.le (Ideal.mem_comap.2 ?_)
    exact (congrArg (· ∈ IsLocalRing.maximalIdeal V) hm₂).mpr (Ideal.mul_mem_left _ _ hm₁)
  have hqu : IsUnit q := by
    obtain ⟨T, y, z, J, α, hJ, hz, h0, hu⟩ := GlobalTheory.T.exists_expansionTerm_unit_closedFibre R I hP.ne_top D A G U 1 σ f hf hσ
    by_cases hα : α = 0
    · subst hα
      rw [hq _ _ z J hJ, show (lift (toUnit T) y).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom from Over.w _] at hu
      by_contra hn
      exact cst_not_isUnit T.hom z hz hn (isUnit_of_mul_isUnit_left hu)
    · rw [hb α T y z J hJ, h0 _ (hbI α hα), MulZeroClass.zero_mul] at hu
      exact absurd hu not_isUnit_zero
  obtain ⟨q, rfl⟩ := hqu
  have hin : ∀ (χ : D.X) (J : Ideal R), b χ ∈ J → E.PsiIn χ J := fun χ J hJ =>
    (PsiScalIn.main_local E ga a hS χ J).2 ⟨(q⁻¹).val * b χ, J.mul_mem_left _ hJ, by
      rw [map_mul]
      refine (congrArg (_ * ·) (hab χ).symm).trans ?_
      rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]⟩
  refine ⟨psi, h, ⟨E, hev, hbi, fun χ hχ => hin χ I (hbI χ hχ), fun n => ?_⟩, hD, rfl, hD₁, hD₂, hD₃⟩
  obtain ⟨s, hs⟩ := GlobalTheory.T.expansionCoef_mem_adic_pow R I hP.ne_top D A G U σ f th hf hth n
  refine s.finite_toSet.subset fun χ hχ => ?_
  by_contra hn
  exact hχ (hin χ _ (Ideal.pow_le_pow_right (Nat.le_succ n) (hs χ hn _ _ (hb χ))))

end GlobalTheory.PsiRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesIsoFieldPullbackStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationValuesIso_fieldPullback : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K) (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing K) F], ArcPull.Compat φ F → ∀ (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧ ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' → IsPullGtF φ hD F g g' → I.Rel c' c := by
  first | exact @GlobalTheory.ValuesPullIso.exists_values_iso | exact GlobalTheory.ValuesPullIso.exists_values_iso | (intros; apply GlobalTheory.ValuesPullIso.exists_values_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetFactor
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.PointDescentFactorization

theorem exists_finset_factor {R Ω : Type} [CommRing R] [Field Ω] (g : ℚ →+* R) (hg : g.FiniteType)
    (φ : R →+* Ω) :
    ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (↑s : Set Ω) ⊆ Set.range β →
      ∃ ψ : R →+* k, β.comp ψ = φ := by
  classical
  letI : Algebra ℚ R := g.toAlgebra
  have hft : Algebra.FiniteType ℚ R := hg
  obtain ⟨t, ht⟩ := hft.out
  refine ⟨t.image φ, fun k _ β hs => ?_⟩
  have hq : ∀ q : ℚ, φ (g q) ∈ β.fieldRange := by
    intro q
    have h := map_ratCast (φ.comp g) q
    rw [Rat.cast_id, RingHom.comp_apply] at h
    rw [h]
    exact SubfieldClass.ratCast_mem _ q
  have hall : ∀ x : R, φ x ∈ β.fieldRange := by
    intro x
    have hx : x ∈ Algebra.adjoin ℚ (t : Set R) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap q => exact hq q
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨(β.rangeRestrictFieldEquiv.symm.toRingHom).comp (φ.codRestrict β.fieldRange hall), ?_⟩
  ext x
  have h := β.rangeRestrictFieldEquiv.apply_symm_apply ⟨φ x, hall x⟩
  exact congrArg Subtype.val h

theorem point_descends {Ω : Type} [Field Ω] {X : Scheme}
    (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℚ) [LocallyOfFiniteType p]
    (a : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ X) :
    ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (↑s : Set Ω) ⊆ Set.range (⇑β : k → Ω) →
      ∃ b : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k ⟶ X, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β ≫ b = a := by
  let x₀ : (Spec (CommRingCat.of Ω)) := IsLocalRing.closedPoint Ω
  obtain ⟨R, j, hj, hx⟩ : ∃ (R : CommRingCat.{0}) (j : Spec R ⟶ X), IsOpenImmersion j ∧
      a x₀ ∈ Set.range j := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := a x₀) (U := ⊤) trivial
    exact ⟨_, hU.fromSpec, inferInstance, by rw [hU.range_fromSpec]; exact hxU⟩
  have hr : Set.range a ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    have : y = x₀ := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [this]; exact hx
  let a' := IsOpenImmersion.lift j a hr
  have ha' : a' ≫ j = a := IsOpenImmersion.lift_fac j a hr
  obtain ⟨φ, hφ⟩ := Spec.map_surjective a'
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ p)
  have hl : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
  have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).mp hl
  obtain ⟨s, hs⟩ := exists_finset_factor g.hom hft φ.hom
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hs k β hβ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ j, ?_⟩
  rw [← ha', ← hφ, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  exact hψ

end GlobalTheory.PointDescentFactorization
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLimitPointTateIsoSequenceStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limitPoint_tateIso_sequence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : ℕ → TateIso D k Q act e), ∃ I' : TateIso D k Q act e, ∀ M, 0 < M → ∀ j₀, ∃ j, j₀ ≤ j ∧ I'.ev M = (I j).ev M ∧ I'.ζ M = (I j).ζ M := by
  first | exact @GlobalTheory.Ex.TateLimit.exists_limit | exact GlobalTheory.Ex.TateLimit.exists_limit | (intros; apply GlobalTheory.Ex.TateLimit.exists_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoMoveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateIso_of_isPolIso : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (φ : o.P.A ≅ o'.P.A), IsPolIso o.P o'.P φ → (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) → ∃ I' : (letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ o'.P.A) (fun a g => g ≫ o'.oa.act a) (fun n g g' c => WeilIs o'.P.A o'.P.L n g g' (unitOn c))), I'.ζ = o.I.ζ ∧ (∀ M a, I'.ev M a = o.I.ev M a ≫ φ.hom) ∧ ∀ m v, o.Theta m v → Full.Theta { o' with I := I' } m v := by
  first | exact @GlobalTheory.FullMove.exists_tateIso_move | exact GlobalTheory.FullMove.exists_tateIso_move | (intros; apply GlobalTheory.FullMove.exists_tateIso_move <;> assumption)
end

