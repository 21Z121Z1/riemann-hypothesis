import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorMoveArgsOriginEqBoxIndicator
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.OriginBoxVac

section Alg
variable {k : Type} [Field k] [ValuativeRel k]

theorem unit_mul_mem_integer_iff (u : kˣ) (x : k) :
    (u : k) * x ∈ 𝒪[k] ↔ valuation k x ≤ valuation k ((u⁻¹ : kˣ) : k) := by
  have hu : valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    ← one_mul (valuation k (u : k))⁻¹, le_mul_inv_iff₀ (zero_lt_iff.2 hu), mul_comm]

theorem scale_eq (ϖ : kˣ) (a A B : ℤ) (x : k) :
    (((ϖ ^ a)⁻¹ : kˣ) : k) * (((ϖ ^ A : kˣ) : k) * x * (((ϖ ^ B)⁻¹ : kˣ) : k)) =
      ((ϖ ^ (A - B - a) : kˣ) : k) * x := by
  have h : ϖ ^ (A - B - a) = (ϖ ^ a)⁻¹ * ϖ ^ A * (ϖ ^ B)⁻¹ := by
    rw [_root_.zpow_sub, _root_.zpow_sub]; group
  rw [h, Units.val_mul, Units.val_mul]; ring

theorem scaled_mem_iff (ϖ : kˣ) (a A B : ℤ) (x : k) :
    (((ϖ ^ a)⁻¹ : kˣ) : k) * (((ϖ ^ A : kˣ) : k) * x * (((ϖ ^ B)⁻¹ : kˣ) : k)) ∈ 𝒪[k] ↔
      valuation k x ≤ valuation k ((ϖ ^ (a - A + B) : kˣ) : k) := by
  rw [scale_eq, unit_mul_mem_integer_iff, ← _root_.zpow_neg, show -(A - B - a) = a - A + B by ring]

end Alg

theorem basePt_zero_of_var {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) :
    basePt c (0 : Matrix n n' k) r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp [basePt, Free, Kept] at h ⊢ <;> omega

end GlobalTheory.OriginBoxVac

namespace GlobalTheory.OriginBoxVac

theorem moveArgs_one_entry {k : Type} [Field k] (G : Grid k) (g : G.VertexGroup) (z : G.Args) (b : Edge)
    (dt : Fin (G.rank b.tgt) → kˣ) (ds : Fin (G.rank b.src) → kˣ) (ht : g b.tgt = diagGL dt)
    (hsrc : g b.src = diagGL ds) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    G.moveArgs .one g z b r s = (dt r : k) * z b r s * ((ds s)⁻¹ : kˣ) := by
  have h1 : ((g b.src)⁻¹).val = diagonal fun i => (((ds i)⁻¹ : kˣ) : k) := by rw [hsrc]; rfl
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val]
  rw [h1, ht, diagGL_val, diagonal_transpose, diagonal_transpose, mul_diagonal, diagonal_mul]

end GlobalTheory.OriginBoxVac

namespace GlobalTheory.OriginBox
open GlobalTheory.OriginBoxVac

theorem indicator_moveArgs_origin {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup)
    (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) (e : Vars G) :
    Set.indicator {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}
      (1 : G.Args → ℂ) (G.moveArgs .one g (fill hs 0 0 e)) = (box G ϖ a a').indicator (1 : Vars G → ℂ) e := by
  classical
  set M := G.moveArgs .one g (fill hs 0 0 e) with hMdef
  have hM : ∀ (j : ℕ) (r : Fin (G.rank (G.m, j))) (s : Fin (G.rank (G.m, j + 1))), M (.theta G.m j) r s =
      ((ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) r : kˣ) : k) * downMap hs 0 e j s r *
        (((ϖ ^ vtxExp a a' (G.m - 1 - (j + 1)) (topRank G (j + 1)) s)⁻¹ : kˣ) : k) := by
    intro j r s
    rw [hMdef, moveArgs_one_entry G g _ (.theta G.m j)
      (fun x => ϖ ^ vtxExp a a' (G.m - 1 - j) (topRank G j) x)
      (fun x => ϖ ^ vtxExp a a' (G.m - 1 - (j + 1)) (topRank G (j + 1)) x) (hg j) (hg (j + 1)),
      fill_theta, transpose_apply]
  have hE : ∀ (j : ℕ) (hj : j < G.m - 1) (r' : Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1))
      (s' : Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)),
      M (.theta G.m j) (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega) r')
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega) s') =
      ((ϖ ^ auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) r' : kˣ) : k) * stepPt ((0 : ColArgs G) j) (e ⟨j, hj⟩) s' r' *
        (((ϖ ^ auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) s')⁻¹ : kˣ) : k) := by
    intro j hj r' s'
    rw [hM, show G.m - 1 - j = G.m - 2 - j + 1 by omega, vtxExp_frame,
      show G.m - 1 - (j + 1) = G.m - 2 - j by omega, vtxExp_frame]
    congr 2
    simp only [downMap, dif_pos hj, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]

  have hbox : ∀ (j : ℕ) (hj : j < G.m - 1) (r' : Fin (topRank G j) ⊕ Fin (G.m - 2 - j + 1))
      (s' : Fin (topRank G (j + 1)) ⊕ Fin (G.m - 2 - j)) (hv : Free ((G.m - 2 - j) / 2 + 1) (s', r') ∨ Kept (s', r')),
      (((ϖ ^ a)⁻¹ : kˣ) : k) * M (.theta G.m j) (frame (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega) r')
        (frame (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega) s') ∈ 𝒪[k] ↔
      valuation k (e ⟨j, hj⟩ ⟨(s', r'), hv⟩) ≤ valuation k ((ϖ ^ boxExp G a a' ⟨j, hj⟩ ⟨(s', r'), hv⟩ : kˣ) : k) := by
    intro j hj r' s' hv
    rw [hE, scaled_mem_iff]
    simp only [stepPt, Matrix.add_apply, of_apply, dif_pos hv, Pi.zero_apply, basePt_zero_of_var s' r' hv, zero_add]
    rfl
  have key : (∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * M b i j ∈ 𝒪[k]) ↔ e ∈ box G ϖ a a' := by
    constructor
    · intro H j _ v _
      have hb : Edge.theta G.m j ∈ oppositePath G.m := by have := j.2; simp [oppositePath]; omega
      exact (hbox j j.2 v.1.2 v.1.1 v.2).1 (H _ hb _ _)
    · intro he b hb r s
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, -, rfl⟩ | ⟨j, hj, rfl⟩
      · have h0 : M (.ex i G.m) = 0 := by
          simp only [hMdef, Grid.moveArgs, fill_ex, Pi.zero_apply, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]
        simp [h0]
      · rcases Nat.lt_or_ge j (G.m - 1) with hj' | hj'
        · obtain ⟨r', rfl⟩ := (frame (a := topRank G j) (c := G.m - 2 - j + 1) (b := G.rank (G.m, j)) (by have := topRank_add hs j; omega)).surjective r
          obtain ⟨s', rfl⟩ := (frame (a := topRank G (j + 1)) (c := G.m - 2 - j) (b := G.rank (G.m, j + 1)) (by have := topRank_add hs (j + 1); omega)).surjective s
          by_cases hv : Free ((G.m - 2 - j) / 2 + 1) (s', r') ∨ Kept (s', r')
          · exact (hbox j hj' r' s' hv).2 (he ⟨j, hj'⟩ trivial ⟨(s', r'), hv⟩ trivial)
          · rw [hE j hj', scale_eq]
            simp only [stepPt, Matrix.add_apply, of_apply, dif_neg hv, add_zero, Pi.zero_apply]
            rcases s' with s' | l <;> rcases r' with r' | i
            · simp [basePt]
            · simp [basePt]
            · simp [basePt]
            · simp only [basePt, fromBlocks_apply₂₂, of_apply]
              split_ifs with hli
              · have h0 : auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j + 1) (Sum.inr i : Fin (topRank G j) ⊕ _) -
                    auxiliaryVectorUniformizerExponent a a' (G.m - 2 - j) (Sum.inr l : Fin (topRank G (j + 1)) ⊕ _) - a = 0 := by
                  simp only [auxiliaryVectorUniformizerExponent, hli]; push_cast; ring
                rw [h0]; simp
              · simp
        · have hjm : j + 1 = G.m := by omega
          have h0 : M (.theta G.m j) r s = 0 := by
            rw [hM]; simp [downMap, show ¬ j < G.m - 1 by omega, hjm]
          simp [h0]
  by_cases he : e ∈ box G ϖ a a'
  · rw [Set.indicator_of_mem he]
    exact Set.indicator_of_mem (s := {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}) (key.2 he) _
  · rw [Set.indicator_of_notMem he]
    exact Set.indicator_of_notMem (s := {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]}) (fun h => he (key.1 h)) _

end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldMaximalIdealDvdUniformizer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FixInertUnram

theorem mem_nonunits_iff' {F : Type} [Field F] (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← A.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ ((Valuation.pos_iff _).2 hx)]
    simp [hx]

theorem div_uniformizer_mem : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π →
    ∀ x : Ω, x ∈ IntermediateField.fixedField (inertia K V) → x ∈ V.nonunits →
      x / algebraMap K Ω (algebraMap R K π) ∈ V := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ x hx hxV
  let L : IntermediateField K Ω :=
    (FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)).toIntermediateField
  have hxL : x ∈ L := FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set Ω) rfl
  let W : ValuationSubring L := V.comap (algebraMap L Ω)
  have hW : IsAbove R K W.toSubring := by
    unfold IsAbove at hV ⊢
    rw [← hV]
    ext y
    rfl
  let y : L := ⟨x, hxL⟩
  have hfix : ∀ τ ∈ inertia K W, τ y = y := by
    intro τ hτ
    obtain ⟨σ, hσ, he⟩ := GlobalTheory.T.exists_inertia_element_restricting_to_finite_galois R K Ω V hV L τ hτ
    apply Subtype.ext
    rw [← he y]
    exact (IntermediateField.mem_fixedField_iff _ _).1 hx σ hσ
  have hyW : y ∈ W.nonunits := by
    rw [mem_nonunits_iff'] at hxV ⊢
    rcases hxV with h | h
    · exact Or.inl (Subtype.ext h)
    · refine Or.inr fun h' => h ?_
      have : ((y⁻¹ : L) : Ω) ∈ V := h'
      simpa using this
  have key := GlobalTheory.T.inertia_fixed_pos_valuation_dvd_uniformiser R K L W hW π hπ y hfix hyW
  have : ((y / algebraMap K L (algebraMap R K π) : L) : Ω) ∈ V := key
  simpa using this

end GlobalTheory.FixInertUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexCoordsPrincipalLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

noncomputable section

namespace GlobalTheory.PrimIn

theorem iC_principal_injective : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → (R.toCx3 F).zs.InBlock → ∀ t, Function.Injective ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F _hOk hC _hIB t
  have hj : GlobalTheory.QPosCompare.IsForm ((R.toCx3 F).jR t) :=
    GlobalTheory.TwistPlacesObj.isForm_tw _ R.toRealDat.emb0 (GlobalTheory.QPosCompare.isForm_jX hC.base.models t)
  exact GlobalTheory.TwistPlacesObj.lin_injective ((R.toCx3 F).Θ t) hj
    ((A3.A.fam.R t).toF (A3.A.fam.lvl ⊥ 1) ((R.toCx3 F).zs.Z t))
    (BlockDat.toF_injective _ _ _) (fun y => GlobalTheory.TwistPlacesObj.toF_mem _ _ _ y)

end GlobalTheory.PrimIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDefiniteUnitaryQuotientEqClassSum
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDictClassSum

section Compact

open Formalism.MainNotions.StandardLattice Matrix
open scoped TensorProduct ComplexOrder MatrixOrder

theorem negDef_of_signature {n q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G 0 q) : (-G).PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq 0 q = -1 := by
    ext (i | i) (j | j)
    · exact i.elim0
    · exact i.elim0
    · exact j.elim0
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
  have h2 : (star P.1 * (-G).reindex e e * P.1).PosDef := by
    have e1 : (-G).reindex e e = -(G.reindex e e) := by ext i j; simp
    have : star P.1 * (-G).reindex e e * P.1 = 1 := by
      have hP' : star P.1 * G.reindex e e * P.1 = Formalism.UG.Jpq 0 q := hP
      rw [e1, Matrix.mul_neg, Matrix.neg_mul, hP', h1, neg_neg]
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

theorem exists_bound_definite {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  rcases hG with hG | hG
  · exact GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
  · obtain ⟨R, hR⟩ := GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
    refine ⟨R, fun g hg => hR g ?_⟩
    rw [Matrix.mul_neg, Matrix.neg_mul, hg]

variable {D : D7}

theorem definite_gramAt (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.what₂.Tau) :
    (gramAt D V τ).PosDef ∨ (-gramAt D V τ).PosDef := by
  have h1 := hs (tauE D τ)
  rcases hd (tauE D τ) with h | h
  · left; rw [h] at h1; exact GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  · right; rw [h] at h1; exact negDef_of_signature h1

theorem exists_compact_def (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D) (GlobalTheory.DefiniteQuotient.gram_hermND V)
      (Formalism.L2.G.gram_totDef D.sp.cm V hs hd)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (GlobalTheory.DefiniteQuotient.gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_definite (definite_gramAt V hs hd τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, k, hγ, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group

end Compact

set_option maxHeartbeats 4000000 in

theorem integral_eq_classSum : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → Function.Injective ι → ι.range = GfC V →
  (∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n) →
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → Links.IsMeasDef V K μ 𝓕 →
  ∀ Φ : GA D V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun V K Φ →
    Finite (Cls D n J) ∧ Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ) (GlobalTheory.AutomorphicL2Unitary.autMeasure V μ) ∧
    ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V μ =
      ∑ᶠ x : Cls D n J, ((gam D J x.out : ℂ))⁻¹ * Φ (ι x.out) := by
  intro D V n ι J K μ 𝓕 hV hinj hran hrat hK hJ hμ Φ hΦ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.1
  haveI : μ.IsHaarMeasure := hμ.1.1
  have hF : IsFundamentalDomain (GQ V) 𝓕 μ := hμ.2
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) Φ := hΦ.left
  let Ψ : Formalism.MainNotions.StandardLatticesGL3.GA D n →* Bridge.Gf V := (finHom V).rangeRestrict.comp ι
  have hΨi : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ι x ∈ GinfC V := congrArg Subtype.val hx
    have h2 : ι x ∈ GfC V := by rw [← hran]; exact ⟨x, rfl⟩
    exact hinj ((GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V h2 h1).trans (map_one ι).symm)
  have hΨs : Function.Surjective Ψ := by
    intro g
    obtain ⟨α, hα, e⟩ := GlobalTheory.Mem.FinPartLift.exists_gfC_finHom_eq V g
    rw [← hran] at hα
    obtain ⟨x, rfl⟩ := hα
    exact ⟨x, Subtype.ext e⟩
  have hratΨ : ∀ x, x ∈ ratG D n ↔ ∃ γ : GQ V, Bridge.ratF V γ = Ψ x := by
    intro x
    rw [← hrat x]
    constructor
    · rintro ⟨γ, hγ, h⟩; exact ⟨⟨γ, hγ⟩, Subtype.ext h⟩
    · rintro ⟨γ, h⟩; exact ⟨γ, γ.2, congrArg Subtype.val h⟩
  have hJΨ : ∀ x, x ∈ J ↔ Ψ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K := fun x =>
    (hJ x).symm.trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.mem_levelFin (ι x)).symm
  have hΨdef : ∀ x, Ψ x = (finHom V).rangeRestrict (ι x) := fun _ => rfl
  clear_value Ψ
  obtain ⟨e, he⟩ : ∃ e : Formalism.MainNotions.StandardLatticesGL3.GA D n ≃* Bridge.Gf V, ∀ x, e x = Ψ x :=
    ⟨MulEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩, fun _ => rfl⟩
  have hre : ∀ y, Ψ (e.symm y) = y := fun y => (he _).symm.trans (e.apply_symm_apply y)

  obtain ⟨C, hC, hCe⟩ := exists_compact_def V hV.1 hV.2
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover_of_compact (GQ V) (finHom V).rangeRestrict
    (finHom V).rangeRestrict_surjective (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) hK.1 hC hCe
  have hsurj : Function.Surjective fun a : Fin m => (DoubleCoset.mk (ratG D n) J (e.symm (c a)) : Cls D n J) := by
    intro q
    obtain ⟨a, γ, k, hk⟩ := hc (Ψ q.out)
    refine ⟨a, ?_⟩
    show DoubleCoset.mk (ratG D n) J (e.symm (c a)) = q
    conv_rhs => rw [← DoubleCoset.out_eq' _ _ q]
    rw [DoubleCoset.eq]
    refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
      (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
    apply hΨi
    simp only [map_mul, hre]
    exact hk
  haveI hfin : Finite (Cls D n J) := Finite.of_surjective _ hsurj
  haveI : Fintype (Cls D n J) := Fintype.ofFinite _

  have hreps : Bridge.IsReps (Bridge.ratF V) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) (fun q : Cls D n J => Ψ q.out) := by
    intro g
    refine (hΨs g).elim fun x hx => ?_
    rw [← hx]
    refine ⟨DoubleCoset.mk (ratG D n) J x, ?_, ?_⟩
    · obtain ⟨h, k, hh, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (ratG D n) J x
      obtain ⟨γ, hγ⟩ := (hratΨ h⁻¹).1 (inv_mem hh)
      refine ⟨γ, ⟨Ψ k⁻¹, (hJΨ _).1 (inv_mem hk)⟩, ?_⟩
      show Ψ x = Bridge.ratF V γ * Ψ (DoubleCoset.mk (ratG D n) J x).out * Ψ k⁻¹
      rw [hγ, hout, ← map_mul Ψ, ← map_mul Ψ]
      congr 1
      group
    · rintro q ⟨γ, k, hq⟩
      rw [← DoubleCoset.out_eq' _ _ q, DoubleCoset.eq]
      refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
        (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
      apply hΨi
      simp only [map_mul, hre]
      exact hq
  obtain ⟨-, hIO, hsum⟩ := GlobalTheory.DefiniteClassSum.classSumIntegral D V hV K hK μ 𝓕 hμ (Cls D n J)
    (fun q => Ψ q.out) hreps (fun q => ι q.out) (fun q => (hΨdef _).symm) Φ hΦ

  have hcard : ∀ x, Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.classGroupAt V K (Ψ x)) = gam D J x := by
    intro x
    unfold gam
    refine Nat.card_eq_of_bijective (fun γ => ⟨e.symm (Bridge.ratF V γ.1), (hratΨ _).2 ⟨γ.1, (hre _).symm⟩,
      (hJΨ _).2 ?_⟩) ⟨?_, ?_⟩
    · simp only [map_mul, map_inv, hre]
      exact (Bridge.mem_stab _).1 γ.2
    · intro a b hab
      have h1 := congrArg (fun s : {γ : Formalism.MainNotions.StandardLatticesGL3.GA D n // γ ∈ ratG D n ∧ x⁻¹ * γ * x ∈ J} => Ψ s.1) hab
      simp only [hre] at h1
      exact Subtype.ext (GlobalTheory.FormInner.ratF_injective V h1)
    · rintro ⟨y, hy1, hy2⟩
      refine ((hratΨ y).1 hy1).elim fun γ hγ => ?_
      refine ⟨⟨γ, (Bridge.mem_stab _).2 ?_⟩, ?_⟩
      · rw [hγ, ← map_inv Ψ, ← map_mul Ψ, ← map_mul Ψ]
        exact (hJΨ _).1 hy2
      · apply Subtype.ext
        apply hΨi
        exact (hre _).trans hγ
  refine ⟨hfin, ?_, ?_⟩
  · have h1 : MemLp (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ)) 1 (μ.restrict 𝓕) := by
      rw [hL.lift_descend]; exact memLp_one_iff_integrable.2 hIO
    exact memLp_one_iff_integrable.1 ((GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hF).2 h1)
  · show ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ = _
    rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hF]
    simp only [hL.descend_mk]
    rw [hsum, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcard]

end GlobalTheory.NormDictClassSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalThetaSecondVariableDiagonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_diagonalTheta_secondVariable_diagonal : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (κ ⊕ κ), ∀ x : κ → AF F,
      ∫ y in 𝓕₁, GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) ∂μ =
        (μ.real 𝓕₁ : ℂ) * ∑' η : κ → F, Φ (Sum.elim ((fun i => algebraMap F (AF F) (η i)) + x)
          ((fun i => algebraMap F (AF F) (η i)) + x)) := by
  first | exact @GlobalTheory.ThetaDiagUnfold.integral_thetaSum_schr_diag | exact GlobalTheory.ThetaDiagUnfold.integral_thetaSum_schr_diag | (intros; apply GlobalTheory.ThetaDiagUnfold.integral_thetaSum_schr_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsFormStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_sub_of_isForm' : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld), A.IsForm α → A.IsForm β →
    A.integral (α - β) = A.integral α - A.integral β := by
  first | exact @GlobalTheory.CxForm.HolAtlas.integral_sub_of_isForm | exact GlobalTheory.CxForm.HolAtlas.integral_sub_of_isForm | (intros; apply GlobalTheory.CxForm.HolAtlas.integral_sub_of_isForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharPStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  first | exact @GlobalTheory.SerreTateProperness.main | exact GlobalTheory.SerreTateProperness.main | (intros; apply GlobalTheory.SerreTateProperness.main <;> assumption)
end

